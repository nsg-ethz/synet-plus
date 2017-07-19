#!/usr/bin/env python

"""
Simple Test cases for OSPF synthesis
"""

import networkx as nx
import unittest

from synet.common import NODE_TYPE
from synet.common import INTERNAL_EDGE
from synet.ospf_synthesizer_noint import OSPFSyn
from synet.ospf_synthesizer_noint import PathReq
from synet.ospf_synthesizer_noint import PathProtocols


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class TestOSPFNoHeuristic(unittest.TestCase):

    @staticmethod
    def get_g():
        """
        Get a simple graph of 4 mesh connected graph
        :return: Networkx Digraph
        """
        # Start with some initial inputs
        # This input only define routers, interfaces, and networks
        g_phy = nx.DiGraph()
        g_phy.add_node('R1', vertex_type=NODE_TYPE)
        g_phy.add_node('R2', vertex_type=NODE_TYPE)
        g_phy.add_node('R3', vertex_type=NODE_TYPE)
        g_phy.add_node('R4', vertex_type=NODE_TYPE)

        g_phy.add_edge('R1', 'R2', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R1', 'R3', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R1', 'R4', edge_type=INTERNAL_EDGE)

        g_phy.add_edge('R2', 'R1', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R2', 'R3', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R2', 'R4', edge_type=INTERNAL_EDGE)

        g_phy.add_edge('R3', 'R1', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R3', 'R2', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R3', 'R4', edge_type=INTERNAL_EDGE)

        g_phy.add_edge('R4', 'R1', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R4', 'R2', edge_type=INTERNAL_EDGE)
        g_phy.add_edge('R4', 'R3', edge_type=INTERNAL_EDGE)

        return g_phy

    def setUp(self):
        self.g = TestOSPFNoHeuristic.get_g()

    def test_4nodes_1paths(self):
        p1 = ['R1', 'R2', 'R3', 'R4']
        paths = [p1]
        ospf = OSPFSyn([], self.g)
        for path in paths:
            req = PathReq(PathProtocols.OSPF, path[-1], path, 10)
            ospf.add_path_req(req)
        assert ospf.solve()

    def test_4nodes_3paths_unstatified(self):
        p1 = ['R1', 'R4']
        p2 = ['R1', 'R2', 'R3', 'R4']
        p3 = ['R1', 'R3', 'R4']
        paths = [p1, p2, p3]
        ospf = OSPFSyn([], self.g)
        for path in paths:
            req = PathReq(PathProtocols.OSPF, path[-1], path, 10)
            ospf.add_path_req(req)
        assert not ospf.solve()



