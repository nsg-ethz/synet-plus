# !/usr/bin/env python
"""
Check an eBGP peering graph assigned with path preferences
"""

import networkx as nx

from synet.utils.common import flatten

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class EBGPVerify(object):
    """Verify the stability of the eBGP requirements"""

    def __init__(self, network_graph, reqs):
        """
        :param network_graph: synet.topo.graph.NetworkGraph
        :param reqs: list of BGP paths preferences
        """
        self.network_graph = network_graph
        self.reqs = reqs
        self.peering_graph = self._extract_peering_graph()

    def _extract_peering_graph(self):
        """
        Extract only the eBGP peering graph.
        Each node is an AS num, if the AS has multiple routers, then
        they are grouped into only one node.
        :return: networkx.Graph
        """
        graph = nx.Graph()
        ases = {}
        for node in self.network_graph:
            if self.network_graph.is_bgp_enabled(node):
                asnum = self.network_graph.get_bgp_asnum(node)
                if asnum not in ases:
                    ases[asnum] = []
                ases[asnum].append(node)
        for asnum, routers in ases.iteritems():
            graph.add_node(asnum)
            for router in routers:
                for neighbor in self.network_graph.get_bgp_neighbors(router):
                    if not self.network_graph.is_bgp_enabled(neighbor):
                        # Not BGP router
                        continue
                    n_asnum = self.network_graph.get_bgp_asnum(neighbor)
                    if asnum == n_asnum:
                        # BGP router is the in the same AS
                        continue
                    graph.add_edge(asnum, n_asnum)
        return graph

    def _get_segment(self, order, split, node):
        """
        Return the ordered segment at a node
        """
        segment = []
        for paths in order:
            current = set()
            for path in paths:
                if split in path:
                    current.add(path[:path.index(split) + 1])
                else:
                    if path[-1] == node and split not in path:
                        current.add(tuple(list(path) + [split]))
                    else:
                        pass
            if current:
                if not segment or (segment and current != segment[-1]):
                    segment.append(current)
        return segment

    def check_order(self, graph):
        """Check that the path preferences are implementable by BGP"""
        unmatching_orders = []
        for node in graph.nodes():
            graph.node[node]['order'] = [x for x in graph.node[node]['order'] if x]
        for node in graph.nodes():
            preds = set(flatten(flatten(graph.node[node]['order'])))
            for pred in preds:
                if pred == node:
                    continue
                # print "\t\tIn pred", pred
                if node in flatten(flatten(graph.node[pred]['order'])):
                    segment = self._get_segment(graph.node[node]['order'], pred, node)
                else:
                    segment = self._get_segment(graph.node[node]['order'], pred, None)
                first_match = graph.node[pred]['order'].index(segment[0])
                comp = graph.node[pred]['order'][first_match:len(segment) + 1]
                err = "node %s, pred %s: expected %s but found %s" % (node, pred, segment, comp)
                if segment != comp:
                    unmatching_orders.append((segment, comp, err))
        return unmatching_orders
