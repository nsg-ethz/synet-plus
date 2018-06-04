#!/usr/bin/env python

"""
The main class for netcomplete
"""

import logging
import random
from collections import Iterable

from ipaddress import IPv4Network
from ipaddress import IPv6Network
import z3

from synet.synthesis.connected import ConnectedSyn
from synet.synthesis.new_propagation import EBGPPropagation
from synet.synthesis.ospf_heuristic import OSPFSyn as OSPFCEGIS

from synet.utils.bgp_utils import compute_next_hop_map
from synet.utils.bgp_utils import extract_all_next_hops
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.fnfree_smt_context import SolverContext
from synet.utils.fnfree_smt_context import desanitize_smt_name

from tekton.gns3 import GNS3Topo
from tekton.graph import NetworkGraph
from tekton.utils import is_empty


def setup_logging():
    # create logger
    logger = logging.getLogger('synet')
    logger.setLevel(logging.DEBUG)

    # create console handler and set level to debug
    ch = logging.StreamHandler()
    ch.setLevel(logging.DEBUG)

    # create formatter
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')

    # add formatter to ch
    ch.setFormatter(formatter)

    # add ch to logger
    logger.addHandler(ch)


class UnImplementableRequirements(Exception):
    def __init__(self, msg):
        super(UnImplementableRequirements, self).__init__(msg)


class SketchError(Exception):
    def __init__(self, msg):
        super(SketchError, self).__init__(msg)


class RequirementError(Exception):
    def __init__(self, msg):
        super(RequirementError, self).__init__(msg)


class NetCompleteConfigs(object):
    def __init__(self,
                 auto_enable_ospf_process=False,
                 default_ospf_process_id=100,
                 auto_enable_ospf_link_costs=True,
                 bgp_smt='smt.smt2',
                 ):
        """

        :param auto_enable_ospf_process: Run OSPF on all routers that are part
                of OSPF requirements, even if not enabled by the sketch
        :param default_ospf_process_id: in case auto_enable_ospf_process, use this process ID
        :param auto_enable_ospf_link_costs: Set symbolic link
                costs on all links that are part of OSPF requirements, even if
                not enabled by the sketch
        :param bgp_smt: a filename to dump the SMT formula for BGP. To disable set to None
        """
        self.auto_enable_ospf_process = auto_enable_ospf_process
        self.default_ospf_process_id = default_ospf_process_id
        self.auto_enable_ospf_link_costs = auto_enable_ospf_link_costs
        self.bgp_smt = bgp_smt


class NetComplete(object):
    def __init__(self, reqs, topo, external_announcements, netcompplete_config=None):
        self.log = logging.getLogger('%s.%s' % (
            self.__module__, self.__class__.__name__))
        assert not reqs or isinstance(reqs, Iterable)
        assert isinstance(topo, NetworkGraph)
        assert not external_announcements or isinstance(external_announcements, Iterable)
        if not netcompplete_config:
            netcompplete_config = NetCompleteConfigs()
        assert isinstance(netcompplete_config, NetCompleteConfigs)
        self.reqs = reqs
        self.topo = topo
        self.connected_syn = ConnectedSyn([], self.topo, full=True)
        self.external_announcements = external_announcements
        self.configs = netcompplete_config
        self._bgp_ctx = None
        self._bgp_synthesizer = None
        self._bgp_solver = None

    @property
    def bgp_ctx(self):
        """The Announcement context used for the BGP solver"""
        return self._bgp_ctx

    @property
    def bgp_synthesizer(self):
        """The BGP synthesizer"""
        return self._bgp_synthesizer

    @property
    def bgp_solver(self):
        """The SMT Solver used for BGP"""
        return self._bgp_solver

    @property
    def bgp_reqs(self):
        """All BGP requirements"""
        return [req for req in self.reqs if req.protocol == Protocols.BGP]

    @property
    def ospf_reqs(self):
        """All OSPF requirements"""
        return [req for req in self.reqs if req.protocol == Protocols.OSPF]

    @property
    def static_reqs(self):
        """All Static requirements"""
        return [req for req in self.reqs if req.protocol == Protocols.Static]

    @property
    def announcements(self):
        return self.external_announcements

    def _create_context(self, create_as_paths=False):
        """
        Create the context to hold symbolic variables used in BGP synthesis
        :param create_as_paths:
        :return: SolverContext
        """
        next_hops_map = compute_next_hop_map(self.topo)
        next_hops = extract_all_next_hops(next_hops_map)
        peers = [node for node in self.topo.routers_iter()
                 if self.topo.is_bgp_enabled(node)]
        print "PEER", peers
        print "NEXTHOPS", next_hops
        ctx = SolverContext.create_context(self.announcements,
                                           peer_list=peers,
                                           next_hop_list=next_hops,
                                           create_as_paths=create_as_paths)
        return ctx

    def synthesize_connected(self):
        if not self.connected_syn.synthesize():
            msg = "Couldn't establish basic connectivity"
            raise UnImplementableRequirements(msg)
        return True

    def synthesize_bgp(self):
        self._bgp_ctx = self._create_context(create_as_paths=False)
        self._bgp_synthesizer = EBGPPropagation(self.bgp_reqs, self.topo, self._bgp_ctx)
        # Compute BGP Propagation
        unmatching_order = self.bgp_synthesizer.compute_dags()
        if unmatching_order:
            msg = "Unimplementable BGP requirements; " \
                  "the following BGP selection order cannot be met: " \
                  "{}".format(unmatching_order)
            raise UnImplementableRequirements(msg)
        self.bgp_synthesizer.synthesize()
        #SMT Solving
        self._bgp_solver = z3.Solver(ctx=self._bgp_ctx.z3_ctx)
        if self.bgp_ctx.check(self.bgp_solver, track=True, out_smt=self.configs.bgp_smt) != z3.sat:
            msg = "Unimplementable BGP requirements;" \
                  "Possibly change the requirements or loosen the sketch." \
                  "The following constraints couldn't be satisfied:" \
                  "{}".format(self.bgp_solver.unsat_core())
            raise UnImplementableRequirements(msg)
        self.bgp_synthesizer.update_network_graph()
        return True

    def _check_ospf_path(self, req):
        """
        Checks if the OSPF path synthesizable
        :return:
        """
        not_enabled_nodes = []
        errors = []
        for node in req.path:
            if not self.topo.is_local_router(node):
                # OSPF is enabled only on local routers, not external peers
                msg = "Node '{}' is not configured to be a local router." \
                      "From OSPF requirement {}".format(node, req)
                errors.append(msg)
            elif not self.topo.is_ospf_enabled(node):
                if self.configs.auto_enable_ospf_process:
                    # OSPF process is not enabled on the router
                    # But NetComplete is allowed to enable it
                    self.topo.enable_ospf(node,
                                          self.configs.default_ospf_process_id)
                else:
                    # NetComplete is not allowed to enable it
                    not_enabled_nodes.append(node)
        if not_enabled_nodes:
            msg = "Nodes are on OSPF path but OSPF process" \
                  " is not enabled on them: {}".format(not_enabled_nodes)
            errors.append(msg)
        if errors:
            return False, errors
        return True, None

    def _check_req(self, req):
        errors = []
        for node in req.path:
            if not self.topo.has_node(node):
                msg = "Node doesn't exist in the network topology." \
                      "Node: {} from requirement {}".format(node, req)
                errors.append(msg)
            elif not self.topo.is_local_router(node):
                msg = "Node '{}' is not configured to be a local router." \
                      "From requirement {}".format(node, req)
                errors.append(msg)
        if req.protocol == Protocols.OSPF:
            check, msg = self._check_ospf_path(req)
            if not check:
                errors.append(check)
        elif req.protocol == Protocols.BGP:
            pass
        elif req.protocol == Protocols.Static:
            pass
        else:
            raise ValueError("Unknown protocol value {} for requirement {}".
                             format(req.protocol, req))
        if not self._check_announce_prefix(req.path[-1], req.dst_net, req.protocol):
            errors.append("Node {} doesn't announce prefix {} "
                          "for requirement {}".format(node, req.dst_net, req))
        if errors:
            return False, errors
        return True, None

    def _check_announce_prefix(self, node, prefix, protocol):
        if protocol == Protocols.OSPF:
            if is_empty(prefix):
                self.log.warn("Using unknown prefix to node %s", node)
                return True
            if not self.topo.is_ospf_enabled(node):
                return False
            if prefix not in self.topo.get_ospf_networks(node):
                return False
        else:
            raise ValueError("Unknown protocol value {}".format(protocol))
        return True

    def _check_reqs(self):
        results = []
        for req in self.ospf_reqs:
            if isinstance(req, PathReq):
                results.append(self._check_req(req))
        all_good = all([check for check, _ in results])
        if all_good:
            return True, None
        else:
            return False, [msg for _, msg in results]

    def _check_ospf_announced(self, router, iface):
        """Return True if the address is announced over OSPF"""
        addr = self.topo.get_interface_loop_addr(router, iface)
        assert not is_empty(addr)
        routers = [(router, iface)]
        # Maybe the neighbor is announcing it
        for neighbor in self.topo.neighbors(router):
            if not self.topo.is_router(neighbor):
                continue
            if iface != self.topo.get_edge_iface(router, neighbor):
                continue
            routers.append((neighbor, self.topo.get_edge_iface(neighbor, router)))
        for router, iface in routers:
            if not self.topo.is_ospf_enabled(router):
                continue
            for network in self.topo.get_ospf_networks(router):
                if not isinstance(network, (IPv4Network, IPv6Network)):
                    if iface == network:
                        return True
                elif addr in network:
                    return True
        return False

    def _check_static_local(self, router, iface):
        return False

    def _check_next_hops(self):
        not_announced = []
        for node, attrs in self.bgp_synthesizer.ibgp_propagation.nodes(data=True):
            for ann in attrs['box'].selected_sham:
                if not ann.permitted.get_value():
                    # Announcement has been dropped
                    continue
                next_hop = ann.next_hop
                if not next_hop.is_concrete:
                    continue
                next_hop = desanitize_smt_name(next_hop.get_value())
                if next_hop == desanitize_smt_name(self.bgp_ctx.origin_next_hop):
                    continue
                next_router, next_iface = next_hop.split("-")[0], '/'.join(next_hop.split("-")[1:])
                path = [k.path for k, v in attrs['box'].anns_map.iteritems() if v == ann][0]
                pretty = "{}:{}".format(next_router, next_iface)
                print "XXXXX NEXT HOP at {} is {}, Path {}".format(node, pretty, path)
                if node == next_router:
                    # Next hop is is one the same router
                    continue
                elif self.topo.has_edge(node, next_router) and next_iface == self.topo.get_edge_iface(next_router, node):
                    # Or Next is directly connected
                    continue
                else:
                    if not (self._check_static_local(next_router, next_iface) or
                            self._check_ospf_announced(next_router, next_iface)):
                        not_announced.append((node, next_router, next_iface))
        if not_announced:
            return False, not_announced
        return True, []

    def _check_bgp_peer_connected(self):
        not_announced = []
        for node in self.topo.routers_iter():
            if not self.topo.is_bgp_enabled(node):
                continue
            for neighbor in self.topo.get_bgp_neighbors(node):
                remote_iface = self.topo.get_bgp_neighbor_iface(node, neighbor)
                if self.topo.has_edge(node, neighbor):
                    phys_iface = self.topo.get_edge_iface(neighbor, node)
                    if phys_iface != remote_iface and \
                            not (self._check_static_local(neighbor, remote_iface) or
                                 self._check_ospf_announced(neighbor, remote_iface)):
                        not_announced.append((node, neighbor, remote_iface))
        if not_announced:
            return False, not_announced
        return True, []

    def synthesize_ospf(self):
        check, msg = self._check_reqs()
        if not check:
            raise SketchError(msg)
        seed = 0
        ospfRand = random.Random(seed)
        path_gen = 100
        ospf = OSPFCEGIS(network_graph=self.topo,
                         gen_paths=path_gen,
                         random_obj=ospfRand)
        for req in self.ospf_reqs:
            ospf.add_req(req)
        ospf.synthesize()
        ospf.update_network_graph()

    def synthesize(self):
        self.synthesize_connected()
        if self.bgp_reqs:
            self.synthesize_bgp()

        self.synthesize_ospf()
        self.synthesize_connected()
        if self.bgp_reqs:
            ret1, not_ann1 = self._check_next_hops()
            if not_ann1:
                tmp = [
                    "{}->{}:{}-{}".format(s, x, y, self.topo.get_interface_loop_addr(x, y))
                    for s, x, y in not_ann1
                ]
                err = "The following next hop IP addresses" \
                      " are not announced via IGP protocol, " \
                      "Hence the BGP requirements cannot be satisfied " \
                      "(consider announcing them in OSPF or static routes)" \
                      ": {}".format(tmp)
                raise SketchError(err)
            ret1, not_ann2 = self._check_bgp_peer_connected()
            if not_ann2:
                tmp = [
                    "{}->{}:{}-{}".format(s, x, y, self.topo.get_interface_loop_addr(x, y))
                    for s, x, y in not_ann1
                ]
                err = "The following peering IP addresses" \
                      " are not announced via IGP protocol, " \
                      "Hence the BGP requirements cannot be satisfied " \
                      "(consider announcing them in OSPF or static routes)" \
                      ": {}".format(tmp)
                raise SketchError(err)
        return True

    def write_configs(self, output_dir, prefix_map=None, gns3_config=None):
        writer = GNS3Topo(graph=self.topo, prefix_map=prefix_map,
                          gns3_config=gns3_config)
        writer.write_configs(out_folder=output_dir)
