#!/usr/bin/env python
"""
Synthesize Static Routes
"""

import copy
from synet.utils.smt_context import is_empty
from synet.topo.graph import NetworkGraph


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class CannotSynthesizeStaticRoute(Exception):
    """
    Raised when a static route cannot be synthesized
    i.e. no available holes
    """
    def __init__(self, prefix, src, dst):
        super(CannotSynthesizeStaticRoute, self).__init__()
        self.prefix = prefix
        self.src = src
        self.dst = dst


class StaticSyn(object):
    """Synthesize Static Routes"""
    def __init__(self, reqs, network_graph):
        """
        :param reqs: List of Path reqs
        :param network_graph: NetworkGraph
        """
        assert isinstance(network_graph, NetworkGraph)
        self.g = network_graph
        self.reqs = reqs
        self.node_old_static = {}
        self.concrete_static = {}
        for node in self.g.routers_iter():
            curr = copy.copy(self.g.get_static_routes(node))
            self.node_old_static[node] = curr

        for node, value in self.node_old_static.iteritems():
            if node not in self.concrete_static:
                self.concrete_static[node] = {}
            if is_empty(value):
                continue
            if not value:
                continue
            for prefix, next_hop in value.iteritems():
                if is_empty(prefix):
                    continue
                if is_empty(next_hop):
                    continue
                self.concrete_static[node][prefix] = next_hop

    def has_route(self, prefix, node, next_hop):
        """Return True if the static route is already configured"""
        # TODO: consider longest prefix matching
        # TODO: consider that next_hop is an IP address
        current_next_hope = self.concrete_static[node].get(prefix, None)
        return current_next_hope == next_hop

    def synthesize_static_route(self, prefix, node, next_hop):
        """Synthesize new static route"""
        if is_empty(self.node_old_static[node]):
            self.concrete_static[node][prefix] = next_hop
            return
        raise CannotSynthesizeStaticRoute(prefix, node, next_hop)

    def synthesize_req(self, req):
        """Synthesize for one path requirement"""
        path = req.path
        pairs = zip(path[0::1], path[1::1])
        for src, dst in pairs:
            if self.has_route(req.dst_net, src, dst):
                # Static Route already exists
                continue
            self.synthesize_static_route(req.dst_net, src, dst)

    def synthesize(self):
        """Synthesize static routes"""
        for req in self.reqs:
            self.synthesize_req(req)
        for node, static_routes in self.concrete_static.iteritems():
            for prefix, next_hop in static_routes.iteritems():
                self.g.add_static_route(node, prefix, next_hop)
