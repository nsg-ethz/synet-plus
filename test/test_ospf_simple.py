#!/usr/bin/env python

"""
Simple Test cases for OSPF synthesis
"""

import random
import unittest

import networkx as nx

import synet.synthesis.ospf
import synet.synthesis.ospf_heuristic

from synet.utils.common import INTERNAL_EDGE
from synet.utils.common import NODE_TYPE
from synet.utils.common import Protocols
from synet.utils.common import PathReq

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class TestOSPF(unittest.TestCase):

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
        self.g = TestOSPF.get_g()
        self.random = random.Random(3010720575261890242)

    @staticmethod
    def get_1path_req():
        p1 = ['R1', 'R2', 'R3', 'R4']
        req = PathReq(Protocols.OSPF, p1[-1], p1, False)
        return [req]

    @staticmethod
    def get_3path_req():
        p1 = ['R1', 'R4']
        p2 = ['R1', 'R2', 'R3', 'R4']
        p3 = ['R1', 'R3', 'R4']
        paths = [p1, p2, p3]
        reqs = []
        for path in paths:
            req = PathReq(Protocols.OSPF, path[-1], path, False)
            reqs.append(req)
        return reqs

    def test_4nodes_1paths(self):
        reqs = TestOSPF.get_1path_req()
        ospf = synet.synthesis.ospf.OSPFSyn([], self.g)
        for req in reqs:
            ospf.add_path_req(req)
        self.assertTrue(ospf.solve())

    def test_4nodes_3paths_unstatified(self):
        reqs = TestOSPF.get_3path_req()
        ospf = synet.synthesis.ospf.OSPFSyn([], self.g)
        for req in reqs:
            ospf.add_path_req(req)
        self.assertFalse(ospf.solve())

    def test_4nodes_1paths_heuristic(self):
        reqs = TestOSPF.get_1path_req()
        ospf = synet.synthesis.ospf_heuristic.OSPFSyn([], self.g)
        for req in reqs:
            ospf.add_path_req(req)
        self.assertTrue(ospf.synthesize())
        self.assertEqual(len(ospf.reqs), 1)
        self.assertEqual(len(ospf.removed_reqs), 0)

    def test_4nodes_3paths_unstatified_heuristic(self):
        reqs = TestOSPF.get_3path_req()
        ospf = synet.synthesis.ospf_heuristic.OSPFSyn([], self.g)
        for req in reqs:
            ospf.add_path_req(req)
        self.assertTrue(ospf.synthesize())
        self.assertEqual(len(ospf.reqs), 1)
        self.assertEqual(len(ospf.removed_reqs), 2)
