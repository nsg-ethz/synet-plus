#!/usr/bin/env python
"""
Synthesize configurations for eBGP protocol
"""

import multiprocessing

import networkx as nx
import z3
import logging

from synet.synthesis.bgp import BGP
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.graph import NetworkGraph
from synet.utils.common import Req
from synet.utils.common import PathReq
from synet.utils.common import PathOrderReq
from synet.utils.common import KConnectedPathsReq
from synet.utils.common import PreferredPathReq
from synet.utils.common import Protocols
from synet.utils.common import ECMPPathsReq
from synet.utils.bgp_utils import get_propagated_info
from synet.utils.smt_context import SMTASPathLenWrapper
from synet.utils.smt_context import SMTASPathWrapper
from synet.utils.smt_context import SMTCommunityWrapper
from synet.utils.smt_context import SMTContext
from synet.utils.smt_context import SMTLocalPrefWrapper
from synet.utils.smt_context import SMTNexthopWrapper
from synet.utils.smt_context import SMTOriginWrapper
from synet.utils.smt_context import SMTPeerWrapper
from synet.utils.smt_context import SMTPermittedWrapper
from synet.utils.smt_context import SMTPrefixWrapper
from synet.utils.smt_context import get_as_path_key
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import VALUENOTSET
from synet.utils.bgp_utils import PropagatedInfo
from synet.utils.bgp_utils import NotValidBGPPropagation
from synet.utils.bgp_utils import ForwardingLoopError
from synet.utils.bgp_utils import ConflictingPreferences
from synet.utils.bgp_utils import write_dag


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


def dag_can_add(dag, node):
    """Return True if the node is not marked strict"""
    if dag.node[node]['strict'] is True:
        return False
    return True


def dag_add_node(dag, node, is_strict=None, ordered=None,
                 unordered=None, unselected=None,
                 is_final=False, igp_pass=None):
    """Add a node to a dag"""
    if not is_strict:
        is_strict = VALUENOTSET
    if ordered is None:
        ordered = []
    if unordered is None:
        unordered = set([])
    if unselected is None:
        unselected = set([])
    if igp_pass is None:
        igp_pass = set([])
    dag.add_node(node, strict=is_strict, ordered=ordered,
                 unordered=unordered, unselected=unselected,
                 is_final=is_final, igp_pass=igp_pass)


class EBGPPropagation(object):
    """Computes the BGP route propagation graph"""

    def __init__(self, reqs, network_graph, allow_igp=False, parallel=False):
        """
        :param reqs: Path requirements
        :param network_graph: NetworkGraph
        :param allow_igp: if True IGP costs are considered
        :param parallel: if True boxes are synthesized in parallel
        """
        self.log = logging.getLogger('%s.%s' % (
            self.__module__, self.__class__.__name__))
        assert isinstance(network_graph, NetworkGraph)
        self.network_graph = network_graph
        self.reqs = []
        self.parallel = parallel
        self.allow_igp = allow_igp
        self.propagation_dags = {}
        self.forwarding_dags = {}
        self.union_graph = None
        self.prefix_list = []
        self.peer_list = []
        self.communities_list = []
        self.all_anns, self.prefix_peers = self.collect_announcements()
        # Node -> neighbor -> nexthop
        self.next_hop_map = self.compute_next_hop_map()
        # Extract list of next hops
        self.next_hop_list = []
        for node in self.next_hop_map:
            for neighbor in self.next_hop_map[node]:
                next_hop = self.next_hop_map[node][neighbor]
                if next_hop not in self.next_hop_list:
                    self.next_hop_list.append(next_hop)
        # Adding reqs
        for req in reqs:
            self.add_path_req(req)

        for node in self.network_graph.routers_iter():
            if 'syn' not in self.network_graph.node[node]:
                self.network_graph.node[node]['syn'] = {'anns': {}}

        self.compute_dags()
        self.union_graphs()
        self.peer_list = list([node for node in self.network_graph.routers_iter()])
        self.as_path_list = self.collect_as_paths()

        self.general_context = self.get_general_context()
        self.boxes = []
        # Prefix -> list of peers that announces it

        for node in self.network_graph.routers_iter():
            #if not self.network_graph.is_bgp_enabled(node):
            #    continue
            box = BGP(
                node=node,
                network_graph=self.network_graph,
                propagation_graph=self.union_graph,
                general_ctx=self.general_context,
                next_hop_map=self.next_hop_map,
                allow_igp=allow_igp
            )
            self.boxes.append(box)
            self.network_graph.node[node]['syn']['box'] = box

    def collect_announcements(self):
        """
        Get a dict of all learned announcement from peers and a dict
        of peer->list of announcements by that peer
        Additionally ['syn']['anns'] that is a list of announcement is added
        to each BGP routers with the announcements it's providing
        :return
        """
        all_anns = {}
        prefix_peers = {}
        for node in self.network_graph.peers_iter():
            anns = self.network_graph.get_bgp_advertise(node)
            if 'syn' not in self.network_graph.node[node]:
                self.network_graph.node[node]['syn'] = {}
            if 'anns' not in self.network_graph.node[node]['syn']:
                self.network_graph.node[node]['syn']['anns'] = {}
            for ann in anns:
                prefix = ann.prefix
                if prefix not in prefix_peers:
                    prefix_peers[prefix] = []
                prefix_peers[prefix].append(node)
                name = "%s_%s" % (node, prefix)
                assert name not in all_anns, \
                    "Announcement name is duplicated %s" % name
                all_anns[name] = ann
                self.network_graph.node[node]['syn']['anns'][name] = ann
        self.log.info("Total number of announcement is %d with total %d prefixes",
                      len(all_anns), len(prefix_peers))
        return all_anns, prefix_peers

    def synthesize_next_hop(self, node, neighbor):
        """
        Synthesizes a next hop interface between two router
        :return the name of the interface (on the neighbor)
        """
        # TODO: Synthesize proper next hop
        asnum1 = self.network_graph.get_bgp_asnum(node)
        asnum2 = self.network_graph.get_bgp_asnum(neighbor)
        if asnum1 != asnum2 and \
                self.network_graph.has_edge(neighbor, node):
            iface = self.network_graph.get_edge_iface(neighbor, node)
        else:
            loopbacks = self.network_graph.get_loopback_interfaces(neighbor)
            if not loopbacks:
                iface = 'lo0'
                self.network_graph.set_loopback_addr(
                    neighbor, iface, VALUENOTSET)
            else:
                iface = loopbacks.keys()[0]
        self.log.debug("Synthesized next hop: %s->%s: %s", node, neighbor, iface)
        return iface

    def compute_next_hop_map(self):
        """
        Compute the possible next hop values in the network
        :return dict [node][neighbor]->next_hop
        """
        next_hop_map = {}
        for node in self.network_graph.routers_iter():
            if node not in next_hop_map:
                next_hop_map[node] = {}
            if not self.network_graph.get_bgp_asnum(node):
                # BGP is not configured on this router
                continue
            neighbors = self.network_graph.get_bgp_neighbors(node)
            for neighbor in neighbors:
                iface = self.network_graph.get_bgp_neighbor_iface(node, neighbor)
                if is_empty(iface):
                    iface = self.synthesize_next_hop(node, neighbor)
                self.network_graph.set_bgp_neighbor_iface(node, neighbor, iface)
                assert iface, "Synthesize connected first"
                iface = iface.replace("/", "-")
                nxt = "%s-%s" % (neighbor, iface)
                next_hop_map[node][neighbor] = nxt
        return next_hop_map

    def collect_as_paths(self):
        """
        Get all the known AS Path
        :return: list of AS_PATHS raw values
        """
        # First AS Paths given by announcements
        all_list = self.all_anns.values()
        # Second AS Paths computed by propagation
        for node in self.union_graph.nodes_iter():
            all_list += get_propagated_info(
                self.union_graph, node, prefix=None, from_node=None)
        # Collect
        as_path_list = []
        for item in all_list:
            as_path = item.as_path
            if as_path not in as_path_list:
                as_path_list.append(as_path)
        return as_path_list

    def get_general_context(self):
        """
        Creates the SMT context that contains all the known announcements
        :return: SMTContext
        """
        name = 'general_ctx'
        prefix_list = self.prefix_list
        peer_list = self.peer_list
        as_path_list = [get_as_path_key(p) for p in self.as_path_list]
        next_hope_list = self.next_hop_list
        communities_list = self.communities_list
        all_anns = self.all_anns

        # Ann Type
        (ann_sort, announcements) = z3.EnumSort('AnnSort', all_anns.keys())

        # Create a map ann_name -> ann_var
        ann_map = dict([(str(ann), ann) for ann in announcements])
        ann_var_map = dict([(ann_map[ann], all_anns[str(ann)]) for ann in ann_map])

        # Basic functions
        local_pref_fun = z3.Function('LocalPref', ann_sort, z3.IntSort())
        permitted_fun = z3.Function('PermittedFun', ann_sort, z3.BoolSort())
        as_path_len_fun = z3.Function('AsPathLenFunc', ann_sort, z3.IntSort())

        # Functions with custom range

        # Prefixes
        read_list = [ann.prefix for ann in all_anns.values()
                     if not is_empty(ann.prefix)]
        # Make sure the list is uique
        prefix_list = list(set(read_list + prefix_list))
        (prefix_sort, prefixes) = z3.EnumSort('PrefixSort', prefix_list)
        prefix_map = dict([(str(prefix), prefix) for prefix in prefixes])
        prefix_map = prefix_map
        prefix_fun = z3.Function('PrefixFunc', ann_sort, prefix_sort)

        # Peers
        read_list = [x.peer for x in all_anns.values() if not is_empty(x.peer)]
        peer_list = list(set(read_list + peer_list))
        (peer_sort, peers) = z3.EnumSort('PeerSort', peer_list)
        peer_map = dict([(str(p), p) for p in peers])
        peer_map = peer_map
        peer_fun = z3.Function('PeerFun', ann_sort, peer_sort)

        # BGP announcement origins
        origin_list = BGP_ATTRS_ORIGIN.__members__.keys()
        (origin_sort, origins) = z3.EnumSort('OriginSort', origin_list)
        origin_map = dict([(str(p), p) for p in origins])
        for k, v in BGP_ATTRS_ORIGIN.__members__.iteritems():
            origin_map[v] = origin_map[k]
        origin_map = origin_map
        origin_fun = z3.Function('OriginFun', ann_sort, origin_sort)

        # AS path list
        read_list = [get_as_path_key(x.as_path) for x in all_anns.values()
                     if not is_empty(x.as_path)]
        as_path_list = list(set(read_list + as_path_list))
        (as_path_sort, as_paths) = z3.EnumSort('ASPathSort', as_path_list)
        as_path_map = dict([(str(p), p) for p in as_paths])
        as_path_map = as_path_map
        as_path_fun = z3.Function('AsPathFunc', ann_sort, as_path_sort)

        # Next Hop
        read_list = [x.next_hop for x in all_anns.values()
                     if not is_empty(x.next_hop)]
        next_hope_list = list(set(read_list + next_hope_list))
        (next_hop_sort, next_hops) = z3.EnumSort('NexthopSort', next_hope_list)
        next_hop_map = dict([(str(p), p) for p in next_hops])
        next_hop_map = next_hop_map
        next_hop_fun = z3.Function('NexthopFunc', ann_sort, next_hop_sort)

        # Create functions for communities
        read_list = all_anns.values()[0].communities.keys()
        communities_list = list(set(communities_list + read_list))
        communities_fun = {}
        for c in communities_list:
            name = 'Has_%s' % c.name
            communities_fun[c] = z3.Function(name, ann_sort, z3.BoolSort())

        return EBGPPropagation.create_context(name, all_anns, ann_map, ann_sort,
                                              prefix_fun, prefix_sort, prefix_map,
                                              peer_fun, peer_sort, peer_map,
                                              origin_fun, origin_sort, origin_map,
                                              as_path_fun, as_path_sort, as_path_map,
                                              as_path_len_fun,
                                              next_hop_fun, next_hop_sort, next_hop_map,
                                              local_pref_fun, permitted_fun, communities_fun)

    def add_path_req(self, req):
        """
        Add new requirement
        :param req: instance of PathReq
        :return: None
        """
        assert isinstance(req, Req)
        self.reqs.append(req)

    def add_path_req_to_dag(self, path_req, dag, path_order, strict, ecmp):
        """
        ADD a single PathReq to the forwarding DAG
        :param path_req: PathReq
        :param dag: nx.DiGraph()
        :param path_order: -1 for unordered, >= 0 for ordered
        :param strict: if True src node will allow more paths to be added
        :param ecmp: ECMP enabled
        :return: None
        """
        tmp_dag = nx.DiGraph()
        assert isinstance(path_req, PathReq)
        assert path_req.path
        rev_path = tuple(list(reversed(path_req.path)))
        for tmp in range(len(rev_path) - 1):
            tsrc = path_req.path[tmp]
            tdst = path_req.path[tmp + 1]
            if not tmp_dag.has_node(tsrc):
                p = rev_path[:]
                ordered = [set([tuple(p), ])][:]
                tmp_dag.add_node(tsrc, ordered=ordered)
            if not tmp_dag.has_node(tdst):
                p = rev_path[: len(rev_path) - tmp - 1][:]
                ordered = [set([tuple(p), ])][:]
                tmp_dag.add_node(tdst, ordered=ordered)
            tmp_dag.add_edge(tdst, tsrc)
        can, is_igp, path = self.can_propagate(path_req.dst_net, rev_path, tmp_dag)

        source = path[0][0]
        curr_path = (source,)
        if not dag.has_node(source):
            dag_add_node(dag, source)

        def add_p(src, dst, curr_propagation):
            if path_order >= 0:
                # Req Path is ordered
                curr_order = dag.node[dst]['ordered']
                if path_order <= len(curr_order) - 1:
                    # A Path already exists with the same preference
                    # Make sure it's the same path we're adding
                    is_err = False
                    if curr_propagation not in curr_order[path_order]:
                        if ecmp:
                            curr_order[path_order].add(curr_propagation)
                        else:
                            is_err = True
                    if is_err:
                        raise ConflictingPreferences(
                            node=dst, current_order=curr_order[path_order], new_pref=path_order,
                            new_req=path_req,
                            curr_propagation=curr_propagation)
                        raise NotValidBGPPropagation(err)
                else:
                    # No path with the same preference exists
                    # Make sure, that the node is allowed to accept other paths
                    exists = False
                    for tt in curr_order:
                        if curr_propagation in tt:
                            exists = True
                            break
                    if not exists and not dag_can_add(dag, dst) and dst != source:
                        err = "Cannot add to %s" % dst
                        raise NotValidBGPPropagation(err)

                    curr_order.append(set([curr_propagation]))
            else:
                assert not ecmp, "Cannot implement ECMP for unordered paths"
                if curr_propagation not in dag.node[dst]['unordered']:
                    if not dag_can_add(dag, dst):
                        err = "Cannot add a path without a preference for " \
                              "net {} at router {}, new path {}".format(
                            path_req.dst_net, dst, curr_propagation)
                        raise NotValidBGPPropagation(err)
                    dag.node[dst]['unordered'].add(curr_propagation)
            if src:
                assert self.network_graph.has_edge(dst, src)

        add_p(None, source, curr_path)
        for index, (src, dst, proto) in enumerate(path):
            curr_path = tuple(list(curr_path) + [dst])
            if not dag.has_node(dst):
                dag_add_node(dag, dst)
            dag.add_edge(dst, src)
            if proto == 'igp':
                continue
            #elif proto == 'ibgp' and index < (len(path) - 1):
            #    continue
            else:
                add_p(src, dst, curr_path)

        if not is_empty(strict):
            dag.node[path[-1][1]]['strict'] = strict
        return path

    def add_req_to_dag(self, req, dag):
        """
        Add a requirement to the forwarding DAG
        :param req: PathReq, KConnectedReq, etc...
        :param dag: nx.DiGraph
        :return: None
        """
        if isinstance(req, PathReq):
            path = self.add_path_req_to_dag(req, dag, 0, strict=req.strict, ecmp=False)
        elif isinstance(req, PathOrderReq):
            for index, path_req in enumerate(req.paths):
                self.add_path_req_to_dag(path_req, dag, index, req.strict, ecmp=False)
        elif isinstance(req, KConnectedPathsReq):
            for index, path_req in enumerate(req.paths):
                self.add_path_req_to_dag(path_req, dag, -1, req.strict, ecmp=False)
        elif isinstance(req, PreferredPathReq):
            self.add_path_req_to_dag(req.preferred, dag, 0, req.strict, ecmp=False)
            for index, path_req in enumerate(req.kconnected.paths):
                self.add_path_req_to_dag(path_req, dag, -1, req.strict, ecmp=False)
        elif isinstance(req, ECMPPathsReq):
            for index, path_req in enumerate(req.paths):
                self.add_path_req_to_dag(path_req, dag, 0, req.strict, ecmp=True)
        else:
            raise ValueError("Unrecognized req type %s" % type(req))

    def compute_propagated_info(self, prefix, propagation_path, dag, prop_igp=False):
        assert isinstance(propagation_path, tuple)
        source = propagation_path[0]
        ann_name = None
        announcement = None
        # Announcements by the start node in the path
        anns = self.network_graph.node[source]['syn']['anns']
        for ann_name, announcement in anns.iteritems():
            if str(announcement.prefix) == prefix and str(announcement.peer) == source:
                break
        assert announcement, "No announcement for prefix '%s' at the end of the path: %s\\n\tAll anns %s" % (prefix, str(propagation_path), str(anns))

        # BGP must start from BGP enabled router
        assert self.network_graph.is_bgp_enabled(source)
        can, is_igp, edges = self.can_propagate(prefix, propagation_path, dag)
        if prop_igp:
            #assert not can, edges
            assert edges[-1][-1] in ['igp', 'ibgp'], edges
        else:
            assert can, edges
            assert not is_igp, edges

        as_path = announcement.as_path + [self.network_graph.get_bgp_asnum(source)]
        path = [source]

        egress = source
        peer = source
        seen_ibgp = False
        last_proto = None
        for src, dst, protocol in edges:
            assert protocol in ['ebgp', 'ibgp', 'igp'],\
                "Unknown protocol (%s, %s, %s)" % (src, dst, protocol)
            if protocol == 'ibgp':
                if seen_ibgp:
                    protocol = 'igp'
                else:
                    seen_ibgp = True
                    if last_proto == 'ebgp':
                        peer = src
            if protocol == 'ebgp':
                if self.network_graph.is_bgp_enabled(src) and \
                        self.network_graph.is_bgp_enabled(dst):
                    peer = src
            if protocol == 'ebgp' or protocol == 'ibgp':
                asnum = self.network_graph.get_bgp_asnum(dst)
                as_path.append(asnum)
            if protocol == 'igp' and self.network_graph.get_bgp_asnum(src)\
                    and not seen_ibgp:
                peer = src
            if protocol == 'ebgp' and egress == source:
                egress = dst

            path.append(dst)
            last_proto = protocol
        return PropagatedInfo(
            egress=egress, ann_name=ann_name, peer=peer,
            as_path=as_path, as_path_len=len(as_path), path=path)

    def _check_selected(self, node, path, propagation_dag):
        """
        Return True if the path was selected for any reason by the node
        """
        if not propagation_dag.has_node(node):
            """Node is not the the graph"""
            return False
        for ecmp in propagation_dag.node[node]['ordered']:
            if path in ecmp:
                return True
        if path in propagation_dag.node[node]['unordered']:
            return True
        if not self.network_graph.is_bgp_enabled(node):
            return True
        return False

    def can_propagate(self, prefix, path, propagation_dag):
        self.log.debug("can_propagate for prefix '%s' with path: %s", prefix, path)
        assert isinstance(path, tuple)
        source = path[0]
        # BGP must start from BGP enabled router
        assert self.network_graph.is_bgp_enabled(source)
        # The route must be exported by the source
        #if not self._check_selected(source, path[0:1], propagation_dag):
        #    self.log.debug("  can_propagate.path dropped at source: %s", source)
        #    return False, False, None
        edges = []
        for i in range(1, len(path)):
            src = path[i - 1]
            dst = path[i]
            src_asnum = None
            dst_asnum = None
            if self.network_graph.is_bgp_enabled(src):
                src_asnum = self.network_graph.get_bgp_asnum(src)
            if self.network_graph.is_bgp_enabled(dst):
                dst_asnum = self.network_graph.get_bgp_asnum(dst)
            proto = None
            if src_asnum and dst_asnum:
                if dst not in self.network_graph.get_bgp_neighbors(src):
                    # No peering session is established
                    proto = 'igp'
                # Possibly BGP
                elif src_asnum != dst_asnum:
                    # this is eBGP
                    if self._check_selected(src, path[:i], propagation_dag):
                        if (dst, src, 'ebgp') not in edges:
                            proto = 'ebgp'
                            self.log.debug("  can_propagate.ebgp edge (%s, %s)", src, dst)
                        else:
                            # A eBGP wont propagate a route back
                            # it's dropped because of loops
                            self.log.debug("  can_propagate.no propagtation (%s, %s)", src, dst)
                            break
                    else:
                        # The previous eBGP router dropped the route
                        # so it wont be propagated to this router
                        proto = None
                else:
                    if len(edges) > 0:
                        # This is not first edge in the graph
                        prev_src, prev_dst, prev_protocol = edges[-1]
                        if prev_protocol =='ebgp':
                            # Previously eBGP, now iBGP
                            proto = 'ibgp'
                            self.log.debug("  can_propagate.ibgp edge (%s, %s)", src, dst)
                        elif prev_protocol == 'ibgp':
                            # Previously iBGP, but since assume the route passed via IGP
                            self.log.debug(
                                "  can_propagate.ibgp edge (%s, %s) with previous "
                                "write to igp (%s, %s, %s)", src, dst, prev_src, prev_dst, proto)
                            edges[-1] = (prev_src, prev_dst, 'igp')
                            proto = 'ibgp'
                        else:
                            self.log.debug("  can_propagate.not valid peering (%s, %s)", src, dst)
                            raise NotValidBGPPropagation(
                                "Check peering session between (%s, %s)" % (prev_dst, src))
                    else:
                        raise NotImplementedError("Route is starting from iBGP.")
            else:
                proto = 'igp'
            if proto == 'igp' and dst_asnum:
                # Check valid BGP peering sessions along the path
                for prev_src, prev_dst, prev_protocol in reversed(edges):
                    if self.network_graph.is_bgp_enabled(prev_src):
                        if dst in self.network_graph.get_bgp_neighbors(prev_src):
                            if dst_asnum == self.network_graph.get_bgp_asnum(prev_src):
                                proto = 'ibgp'
                            else:
                                proto = 'ebgp'
                            break
            if proto:
                self.log.debug("  can_propagate.last edge (%s, %s, %s)", src, dst, proto)
                edges.append((src, dst, proto))
            else:
                # No protocol can make this edge
                self.log.debug("  can_propagate.no protocol (%s, %s, %s)", src, dst, proto)
                return False, False, None
        if edges and edges[-1][-1] == 'igp':
            return False, True, edges
        return True, False, edges

    def get_forwarding_dag(self, prefix, reqs):
        """
        Given a prefix and and set of reqs
        Compute a forwarding DAG that is the union of
        all the reqs
        :return nx.DiGraph
        """
        forwarding_dag = nx.DiGraph()
        forwarding_dag.graph['prefix'] = prefix
        for req in reqs:
            self.add_req_to_dag(req, forwarding_dag)
        if not nx.is_directed_acyclic_graph(forwarding_dag):
            err = "The requirements for prefix {} do not form " \
                  "a valid forwarding DAG (has loops)".format(prefix)
            raise ForwardingLoopError(err)
        return forwarding_dag

    def compute_bfs(self, prefix, source, propagation_dag):
        g = nx.DiGraph()
        selected = set([(source,)])
        g.add_node(source, selected=selected, unselected=set(), igp_pass=set())
        visited = set([])
        # maintain a queue of paths
        queue = list()
        # push the first path into the queue
        queue.append((source,))
        while queue:
            # get the first path from the queue
            path = queue.pop(0)
            visited.add(path)
            node = path[-1]
            if self.network_graph.is_bgp_enabled(node):
                can, is_igp, prop_path = self.can_propagate(prefix, path, propagation_dag)
                if not can:
                    continue
                print "  CAN", prefix, node, prop_path
                for x, y, _ in prop_path:
                    for tmp in [x, y]:
                        if not g.has_node(tmp):
                            g.add_node(tmp, selected=set(), unselected=set(), igp_pass=set())
                    print "    ADD EDGE", x, y
                    g.add_edge(x, y)
                print "   CHECK SELECTED", prefix, node, path, propagation_dag, self._check_selected(node, path, propagation_dag)
                if self._check_selected(node, path, propagation_dag):
                    if path not in g.node[node]['selected']:
                        g.node[node]['selected'].add(path)
                else:
                    if path not in g.node[node]['unselected']:
                        g.node[node]['unselected'].add(path)
                if prop_path:
                    curr = [prop_path[0][0]]
                    for x, y, prot in prop_path:
                        curr.append(y)
                        if prot == 'igp':
                            if tuple(curr) not in g.node[y]['igp_pass']:
                                g.node[y]['igp_pass'].add(tuple(curr))

                #if not self._check_selected(node, path, propagation_dag):
                #    is_strict = g.node[node]['strict']
                #    if is_empty(is_strict):
                #        is_strict = True
                #    if is_strict is True:
                #        if path not in g.node[node]['unselected']:
                #            g.node[node]['unselected'].add(path)
                #    elif is_empty(is_strict) or is_strict is False:
                #        if path not in g.node[node]['selected']:
                #            g.node[node]['selected'].add(path)
                #    else:
                #        raise ValueError("Unknown strict value %s->%s" % (node, is_strict))

            # enumerate all adjacent nodes, construct a new path
            # and push it into the queue
            for adjacent in self.network_graph.neighbors_iter(node):
                if adjacent in path:
                    continue
                new_path = list(path)
                new_path.append(adjacent)
                new_path = tuple(new_path)
                if new_path not in visited:
                    queue.append(new_path)
        write_dag(g, "/tmp/out.dot")
        return g

    def compute_dag(self, prefix, reqs):
        """
        Given a prefix and a list of requirements, compute the
        forwarding DAG
        :param prefix: prefix or traffic class
        :param reqs: Iterable
        :return: nx.DiGraph
        """
        forwarding_dag = self.get_forwarding_dag(prefix, reqs)
        write_dag(forwarding_dag, "/tmp/%s_fwd.dot" % prefix)
        propagation_dag = forwarding_dag.reverse(copy=True)
        write_dag(propagation_dag, "/tmp/%s_rev.dot" % prefix)
        for source in self.prefix_peers[prefix]:
            if not propagation_dag.has_node(source):
                dag_add_node(propagation_dag, source, is_strict=True,
                             ordered=[set([(source,)])], is_final=True)

        # Do BFS to compute any additional propagation
        for source in self.prefix_peers[prefix]:
            print "In source", source, "for prefix", prefix
            bfs = self.compute_bfs(prefix, source, propagation_dag)
            for tmp_node in bfs.node:
                if not propagation_dag.has_node(tmp_node):
                    dag_add_node(propagation_dag, tmp_node, is_strict=False)
                for tmp_path in bfs.node[tmp_node]['unselected']:
                    if tmp_path not in propagation_dag.node[tmp_node]['unselected']:
                        propagation_dag.node[tmp_node]['unselected'].add(tmp_path)
                for tmp_path in bfs.node[tmp_node]['igp_pass']:
                    if tmp_path not in propagation_dag.node[tmp_node]['igp_pass']:
                        propagation_dag.node[tmp_node]['igp_pass'].add(tmp_path)
            for x, y in bfs.edges():
                if not propagation_dag.has_edge(x, y):
                    propagation_dag.add_edge(x, y)
        for tmp_node, attrs in propagation_dag.nodes_iter(data=True):
            final_igp_pass = set()
            for tmp_path in attrs['igp_pass']:
                selected = True
                if tmp_path in attrs['unselected']:
                    selected = True
                elif tmp_path in attrs['unordered']:
                    selected = True
                else:
                    for t2 in attrs['ordered']:
                        if tmp_path in t2:
                            selected = True
                if selected:
                    final_igp_pass.add(tmp_path)
            propagation_dag.node[tmp_node]['igp_pass'] = final_igp_pass
        write_dag(propagation_dag, "/tmp/%s_bfs.dot" % prefix)
        for node in propagation_dag.nodes_iter():
            prop_ordered = []
            for ecmp in propagation_dag.node[node]['ordered']:
                assert isinstance(ecmp, set), "Node %s" % node
                ecmp_prop = set([])
                for path in ecmp:
                    assert isinstance(path, tuple), "Node %s" % node
                    prop = self.compute_propagated_info(prefix, path, propagation_dag)
                    ecmp_prop.add(prop)
                prop_ordered.append(ecmp_prop)
            prop_unordered = set([])
            for path in propagation_dag.node[node]['unordered']:
                prop = self.compute_propagated_info(prefix, path, propagation_dag)
                prop_unordered.add(prop)
            prop_unselected = set([])
            for path in propagation_dag.node[node]['unselected']:
                prop = self.compute_propagated_info(prefix, path, propagation_dag)
                prop_unselected.add(prop)
            prop_igp_pass = set([])
            for path in propagation_dag.node[node]['igp_pass']:
                prop = self.compute_propagated_info(prefix, path, propagation_dag, prop_igp=True)
                prop_igp_pass.add(prop)
            propagation_dag.node[node]['prop_ordered'] = prop_ordered
            propagation_dag.node[node]['prop_unordered'] = prop_unordered
            propagation_dag.node[node]['prop_unselected'] = prop_unselected
            propagation_dag.node[node]['prop_igp_pass'] = prop_igp_pass
        return forwarding_dag, propagation_dag

    def compute_dags(self):
        # Collect the paths from the requirements for each prefix
        # Net-> List of Reqs
        net_reqs = {}
        for req in self.reqs:
            if req.dst_net not in net_reqs:
                net_reqs[req.dst_net] = []
            net_reqs[req.dst_net].append(req)
        # Find the leftovers (prefixes announced but not in reqs)
        for prefix, peers in self.prefix_peers.iteritems():
            if prefix not in net_reqs:
                net_reqs[prefix] = []
                for peer in peers:
                    new_req = PathReq(Protocols.BGP,
                                      dst_net=prefix, path=[peer],
                                      strict=True)
                    net_reqs[prefix].append(new_req)
        # For each prefix compute a route propagation graph
        self.forwarding_dags = {}
        self.propagation_dags = {}
        for net, reqs in net_reqs.iteritems():
            forwarding, propagation = self.compute_dag(net, reqs)
            self.forwarding_dags[net] = forwarding
            self.propagation_dags[net] = propagation

    def add_net_graph(self, prefix, union_g, propagation):
        """
        Add new route propagation graph for a specific net to the graph
        that holds all the route propagation information for all prefixes
        :param union_g:
        :param propagation:
        :return:
        """
        assert union_g.is_directed()
        assert propagation.is_directed()
        topo_nodes = set(list(self.network_graph.nodes()))
        propagation_nodes = set(list(propagation.nodes()))
        assert propagation_nodes.issubset(topo_nodes)

        for src, dst in propagation.edges_iter():
            union_g.add_edge(src, dst)
        for node in propagation_nodes:
            if not union_g.has_node(node):
                union_g.add_node(node, prefixes={})
            if 'prefixes' not in union_g.node[node]:
                union_g.node[node]['prefixes'] = {}
            set_attrs = ['unordered', 'unselected', 'igp_pass',
                         'prop_unordered', 'prop_unselected', 'prop_igp_pass']
            list_attrs = ['ordered', 'prop_ordered']
            if prefix not in union_g.node[node]['prefixes']:
                union_g.node[node]['prefixes'][prefix] = dict(strict=False)
                for attr in set_attrs:
                    union_g.node[node]['prefixes'][prefix][attr] = set([])
                for attr in list_attrs:
                    union_g.node[node]['prefixes'][prefix][attr] = []
            for attr in list_attrs:
                union_g.node[node]['prefixes'][prefix][attr].extend(
                    propagation.node[node][attr])
            for attr in set_attrs:
                old = union_g.node[node]['prefixes'][prefix][attr]
                new_val = propagation.node[node][attr]
                union_g.node[node]['prefixes'][prefix][attr] = old.union(new_val)
            if propagation.node[node]['strict'] is True:
                union_g.node[node]['prefixes'][prefix]['strict'] = True
        return union_g

    def print_union(self):
        for node in self.union_graph.nodes_iter():
            label = "%s\\n" % node
            for prefix, data in self.union_graph.node[node]['prefixes'].iteritems():
                label += "Prefix: %s\\n" % prefix
                label += "  Ordered: %s\\n" % data['prop_ordered']
                label += "  Unordered: %s\\n" % data['prop_unordered']
                label += "  Unselected: %s\\n" % data['prop_unselected']
                label += "  IGP Pass: %s\\n" % data['prop_igp_pass']
            self.union_graph.node[node]['label'] = label
        from networkx.drawing.nx_agraph import write_dot
        write_dot(self.union_graph, '/tmp/composed.dot')

    def union_graphs(self):
        """Union all the DAG per prefix to one graph"""
        union_g = nx.DiGraph()
        for prefix, propagation in self.propagation_dags.iteritems():
            union_g = self.add_net_graph(prefix, union_g, propagation)
        self.union_graph = union_g
        self.print_union()

    def add_constraints(self, solver, track=True):
        """Add constraints to the solver"""
        for box in self.boxes:
            box.add_constraints(solver, track)

    def set_model(self, model):
        """Set the Z3 model"""
        for box in self.boxes:
            box.set_model(model)

    def update_network_graph(self):
        """Update the network graph with the concrete values"""
        for box in self.boxes:
            box.update_network_graph()

    def synthesize(self):
        """Synthesize the BGP configs"""
        jobs = []
        for node in sorted(list(self.network_graph.local_routers_iter())):
            if 'syn' not in self.network_graph.node[node]:
                continue
            box = self.network_graph.node[node]['syn']['box']
            if self.parallel:
                process = multiprocessing.Process(name=node, target=box.synthesize)
                process.start()
                jobs.append(process)
            else:
                box.synthesize()
        # Wait for processes to finish
        for job in jobs:
            job.join()

    @staticmethod
    def create_context(name,
                       announcements, announcements_map, announcement_sort,
                       prefix_fun, prefix_sort, prefix_map,
                       peer_fun, peer_sort, peer_map,
                       origin_fun, origin_sort, origin_map,
                       as_path_fun, as_path_sort, as_path_map,
                       as_path_len_fun,
                       next_hop_fun, next_hop_sort, next_hop_map,
                       local_pref_fun, permitted_fun, communities_fun):
        """
        Creates SMTContext
        :return: SMTContext
        """

        ann_var_map = dict([(announcements_map[ann], announcements[str(ann)])
                            for ann in announcements_map])
        # Create wrapper
        wprefix = SMTPrefixWrapper(
            'prefixw', announcement_sort, ann_var_map,
            prefix_fun, prefix_sort, prefix_map)

        wpeer = SMTPeerWrapper(
            'wpeer', announcement_sort, ann_var_map,
            peer_fun, peer_sort, peer_map)

        worigin = SMTOriginWrapper(
            'worigin', announcement_sort, ann_var_map,
            origin_fun, origin_sort, origin_map)

        waspath = SMTASPathWrapper(
            'waspath', announcement_sort, ann_var_map,
            as_path_fun, as_path_sort, as_path_map)

        waspathlen = SMTASPathLenWrapper(
            'waspathlen', announcement_sort, ann_var_map,
            as_path_len_fun)

        wnext_hop = SMTNexthopWrapper(
            'wnext_hop', announcement_sort, ann_var_map,
            next_hop_fun, next_hop_sort, next_hop_map)

        wlocalpref = SMTLocalPrefWrapper(
            'wlocalpref', announcement_sort, ann_var_map,
            local_pref_fun)

        wpermitted = SMTPermittedWrapper(
            'wpermitted', announcement_sort, ann_var_map,
            permitted_fun)

        wcommunities = {}
        for community in communities_fun.keys():
            name = community.name
            wc1 = SMTCommunityWrapper(
                'w%s' % name, community, announcement_sort,
                ann_var_map, communities_fun[community])
            wcommunities[community] = wc1

        ctx = SMTContext(name, announcements, announcements_map,
                         announcement_sort, wprefix, wpeer, worigin, waspath,
                         waspathlen, wnext_hop, wlocalpref, wcommunities,
                         wpermitted)
        return ctx
