#!/usr/bin/env python
"""
Synthesize directly connected interfaces
"""

from collections import Iterable

from ipaddress import ip_address
from ipaddress import ip_interface
from ipaddress import ip_network

from synet.topo.graph import NetworkGraph
from synet.utils.common import PathOrderReq
from synet.utils.common import PathReq
from synet.utils.smt_context import VALUENOTSET


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class InterfaceIsDownError(Exception):
    """The interface is configured to be shutdown, while it's required to be up"""
    def __init__(self, src, src_iface):
        super(InterfaceIsDownError, self).__init__()
        self.src = src
        self.src_iface = src_iface


class NotValidSubnetsError(Exception):
    def __init__(self, src, src_iface, src_net, dst, dst_iface, dst_net):
        """The two interfaces have IP addresses with different subnets"""
        super(NotValidSubnetsError, self).__init__()
        self.src = src
        self.src_iface = src_iface
        self.src_net = src_net
        self.dst = dst
        self.dst_iface = dst_iface
        self.dst_net = dst_net


class DuplicateAddressError(Exception):
    """The two interfaces are configured with the same IP addresses"""
    def __init__(self, src, src_iface, src_addr, dst, dst_iface, dst_addr):
        super(DuplicateAddressError, self).__init__()
        self.src = src
        self.src_iface = src_iface
        self.src_addr = src_addr
        self.dst = dst
        self.dst_iface = dst_iface
        self.dst_addr = dst_addr


class ConnectedSyn(object):
    def __init__(self, reqs, network_graph, start_net=u'10.0.0.0', prefix_len=31):
        if not reqs:
            reqs = []
        assert isinstance(network_graph, NetworkGraph)
        assert isinstance(reqs, Iterable)
        for req in reqs:
            assert isinstance(req, (PathReq, PathOrderReq))
        self.reqs = reqs
        self.g = network_graph
        self.prefix_len = prefix_len
        self._next_net = int(ip_address(start_net))

    def get_next_net(self):
        """Get the next subnet to be assigned to interfaces"""
        curr_ip = ip_address(self._next_net)
        net = ip_network(u"%s/%d" % (curr_ip, self.prefix_len))
        self._next_net += ((32 - self.prefix_len) ** 2) + 1
        return net

    def reqs_connected_pairs(self):
        """Get the connected paris based on direct user reqs"""
        all_paths = []
        connected_pairs = []
        for req in self.reqs:
            if isinstance(req, PathReq):
                all_paths.append(req.path)
            elif isinstance(req, PathOrderReq):
                for sub_req in req.paths:
                    all_paths.append(sub_req.path)
            else:
                raise ValueError("Unknown Req type %s" % type(req))
        for path in all_paths:
            connected_pairs.extend(zip(path[0::1], path[1::1]))
        connected_pairs = list(set(connected_pairs))
        return connected_pairs

    def get_bgp_connected_pairs(self):
        """Get the connected pairs due to direct BGP peering sessions"""
        connected_pairs = []
        for node in self.g.routers_iter():
            for neigbor in self.g.get_bgp_neighbors(node):
                if self.g.has_edge(node, neigbor):
                    connected_pairs.append((node, neigbor))
        return connected_pairs

    def _pre_process_connected_pairs(self, connnected_paris):
        """
        Connected pairs are list of (src, dst) tuples
        In this case (src, dst) and (dst, src) can appear
        twice in the list. This methond eliminate that
        """
        ret_val = []
        for src, dst in connnected_paris:
            tmp = set([src, dst])
            if tmp not in ret_val:
                ret_val.append(tmp)
        return [tuple(sorted(list(val))) for val in ret_val]

    def is_connnected(self, src, dst):
        """Returns true if the two nodes are properly connected"""
        if not self.g.has_edge(src, dst):
            return False
        iface1 = self.g.get_edge_iface(src, dst)
        iface2 = self.g.get_edge_iface(dst, src)

        if self.g.is_iface_shutdown(src, iface1):
            return False
        if self.g.is_iface_shutdown(dst, iface2):
            return False

        addr1 = self.g.get_iface_addr(src, iface1)
        addr2 = self.g.get_iface_addr(dst, iface2)
        if VALUENOTSET in [addr1, addr2]:
            return False
        net1 = addr1.network
        net2 = addr2.network
        if net1 != net2:
            return False
        if addr1 == addr2:
            return False
        return True

    def synthesize_connection(self, src, dst):
        """Synthesize connection between two routers"""
        err = "Routers (%s, %s) are not directly connected" % (src, dst)
        assert self.g.has_edge(src, dst), err
        iface1 = self.g.get_edge_iface(src, dst)
        iface2 = self.g.get_edge_iface(dst, src)
        # Make sure interfaces are up
        if self.g.is_iface_shutdown(src, iface1):
            raise InterfaceIsDownError(src, iface1)
        if self.g.is_iface_shutdown(dst, iface2):
            raise InterfaceIsDownError(src, iface2)
        addr1 = self.g.get_iface_addr(src, iface1)
        addr2 = self.g.get_iface_addr(dst, iface2)
        err1 = "Address not set and not a hole for iface: %s-%s" % (src, iface1)
        err2 = "Address not set and not a hole for iface: %s-%s" % (dst, iface2)
        assert addr1, err1
        assert addr2, err2

        # Get the subnet for both ends of the line
        if addr1 == addr2 and addr1 == VALUENOTSET:
            # No initial config is given
            # Then synthesize completely new subnet
            net1 = self.get_next_net()
            net2 = net1
        elif VALUENOTSET in [addr1, addr2]:
            # Only one side is concrete
            net = addr1.network if addr1 != VALUENOTSET else addr2.network
            net1 = net
            net2 = net
        else:
            # Both sides are concrete
            net1 = addr1.network
            net2 = addr2.network

        # The two interfaces must have the same network
        if net1 != net2:
            raise NotValidSubnetsError(src, iface1, net1, dst, iface2, net2)

        # Assign IP addresses to the first interface (if needed)
        if addr1 == VALUENOTSET:
            for host in net1.hosts():
                addr = ip_interface(u"%s/%d" % (host, net1.prefixlen))
                if addr == addr2:
                    continue
                addr1 = addr
                self.g.set_iface_addr(src, iface1, addr)
                break
        # Assign IP addresses to the second interface (if needed)
        if addr2 == VALUENOTSET:
            for host in net2.hosts():
                addr = ip_interface(u"%s/%d" % (host, net2.prefixlen))
                if addr != addr1:
                    addr2 = addr
                    self.g.set_iface_addr(dst, iface2, addr)
                    break
        # The interfaces must have unique IP addresses
        if addr1 == addr2:
            raise DuplicateAddressError(src, iface1, addr1, dst, iface2, addr2)
        assert iface1

    def synthesize(self):
        bgp_connected = self.get_bgp_connected_pairs()
        reqs_connecetd = self.reqs_connected_pairs()
        connected_pairs = bgp_connected + reqs_connecetd
        connected_pairs = list(set(connected_pairs))
        connected_pairs = self._pre_process_connected_pairs(connected_pairs)
        # Assign iface names between edges (if needed)
        self.g.set_iface_names()
        for src, dst in sorted(connected_pairs):
            self.synthesize_connection(src, dst)
        edges_to_remove = []
        for src, dst in self.g.edges_iter():
            if (src, dst) not in connected_pairs:
                if self.is_connnected(src, dst):
                    continue
                # The links are not connected and not needed for any req
                edges_to_remove.append((src, dst))
                edges_to_remove.append((dst, src))
        edges_to_remove = list(set(edges_to_remove))
        for src, dst in edges_to_remove:
            self.g.remove_edge(src, dst)
