#!/usr/bin/env python

"""
Simple Test cases for OSPF synthesis
"""

import random
import networkx as nx
import unittest

from nose.plugins.attrib import attr

from synet.synthesis.connected import ConnectedSyn
import synet.synthesis.ospf
import synet.synthesis.ospf_heuristic

from synet.utils.common import Protocols
from synet.utils.common import PathReq
from synet.utils.common import ECMPPathsReq
from synet.utils.common import PathOrderReq
from synet.utils.topo_gen import get_fanout_topology

from synet.topo.graph import NetworkGraph


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


@attr(speed='fast')
class TestOSPF(unittest.TestCase):

    @staticmethod
    def get_g():
        """
        Get a simple graph of 4 mesh connected graph
        :return: NetworkGraph
        """
        # Start with some initial inputs
        # This input only define routers, interfaces, and networks
        g_phy = NetworkGraph()
        g_phy.add_router('R1')
        g_phy.add_router('R2')
        g_phy.add_router('R3')
        g_phy.add_router('R4')
        g_phy.enable_ospf('R1', 100)
        g_phy.enable_ospf('R2', 100)
        g_phy.enable_ospf('R3', 100)
        g_phy.enable_ospf('R4', 100)

        g_phy.add_router_edge('R1', 'R2')
        g_phy.add_router_edge('R1', 'R3')
        g_phy.add_router_edge('R1', 'R4')
        g_phy.add_router_edge('R2', 'R1')
        g_phy.add_router_edge('R2', 'R3')
        g_phy.add_router_edge('R2', 'R4')
        g_phy.add_router_edge('R3', 'R1')
        g_phy.add_router_edge('R3', 'R2')
        g_phy.add_router_edge('R3', 'R4')
        g_phy.add_router_edge('R4', 'R1')
        g_phy.add_router_edge('R4', 'R2')
        g_phy.add_router_edge('R4', 'R3')
        conn_syn = ConnectedSyn([], g_phy, full=True)
        conn_syn.synthesize()
        return g_phy

    def get_triangles(self, fanout):
        topo = get_fanout_topology(fanout)
        for node in topo.local_routers_iter():
            topo.enable_ospf(node, 100)
        conn_syn = ConnectedSyn([], topo, full=True)
        conn_syn.synthesize()
        return topo

    def setUp(self):
        self.network_graph = TestOSPF.get_g()
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
        ospf = synet.synthesis.ospf.OSPFSyn(self.network_graph)
        for req in reqs:
            ospf.add_req(req)
        self.assertTrue(ospf.solve())

    def test_4nodes_3paths_unstatified(self):
        reqs = TestOSPF.get_3path_req()
        ospf = synet.synthesis.ospf.OSPFSyn(self.network_graph)
        for req in reqs:
            ospf.add_req(req)
        self.assertFalse(ospf.solve())

    def test_4nodes_1paths_heuristic(self):
        reqs = TestOSPF.get_1path_req()
        ospf = synet.synthesis.ospf_heuristic.OSPFSyn(self.network_graph, gen_paths=10)
        for req in reqs:
            ospf.add_req(req)
        ret = ospf.synthesize()
        self.assertTrue(ret)
        ospf.update_network_graph()
        self.assertEqual(len(ospf.reqs), 1)
        self.assertEqual(len(ospf.removed_reqs), 0)

    @attr(speed='slow')
    def test_4nodes_3paths_unstatified_heuristic(self):
        reqs = TestOSPF.get_3path_req()
        ospf = synet.synthesis.ospf_heuristic.OSPFSyn(self.network_graph, gen_paths=10)
        for req in reqs:
            ospf.add_req(req)
        ret = ospf.synthesize()
        self.assertTrue(ret)
        ospf.update_network_graph()
        self.assertEqual(len(ospf.reqs), 1)
        self.assertEqual(len(ospf.removed_reqs), 2)

    @attr(speed='fast')
    def test_ecmp_full(self):
        fan_out = 4
        network_graph = self.get_triangles(fan_out)
        source = 'source'
        sink = 'sink'
        p1 = [source, 'R1', sink]
        p2 = [source, 'R2', sink]
        path1 = PathReq(Protocols.OSPF, 'Google', p1, False)
        path2 = PathReq(Protocols.OSPF, 'Google', p2, False)
        ecmp_req = ECMPPathsReq(Protocols.OSPF, 'Google', [path1, path2], False)
        ospf = synet.synthesis.ospf.OSPFSyn(network_graph)
        ospf.add_req(ecmp_req)
        ret = ospf.solve()
        self.assertTrue(ret)
        ospf.update_network_graph()
        ecmp = [
            tuple(p) for p in
            nx.all_shortest_paths(network_graph, source, sink, 'ospf_cost')]
        ecmp = set(ecmp)
        self.assertEquals(ecmp, set([tuple(p1), tuple(p2)]))

    @attr(speed='fast')
    def test_ecmp_correct(self):
        fan_out = 4
        network_graph = self.get_triangles(fan_out)
        source = 'source'
        sink = 'sink'
        p1 = [source, 'R1', sink]
        p2 = [source, 'R2', sink]
        path1 = PathReq(Protocols.OSPF, 'Google', p1, False)
        path2 = PathReq(Protocols.OSPF, 'Google', p2, False)
        ecmp_req = ECMPPathsReq(Protocols.OSPF, 'Google', [path1, path2], False)
        ospf = synet.synthesis.ospf_heuristic.OSPFSyn(network_graph, gen_paths=10)
        ospf.add_req(ecmp_req)
        ret = ospf.synthesize()
        self.assertTrue(ret)
        ospf.update_network_graph()
        ecmp = [
            tuple(p) for p in
            nx.all_shortest_paths(network_graph, source, sink, 'ospf_cost')]
        ecmp = set(ecmp)
        self.assertEquals(ecmp, set([tuple(p1), tuple(p2)]))

    @attr(speed='fast')
    def test_ordered_full(self):
        fan_out = 4
        network_graph = self.get_triangles(fan_out)
        source = 'source'
        sink = 'sink'
        p1 = [source, 'R1', sink]
        p2 = [source, 'R2', sink]
        p3 = [source, 'R3', sink]
        p4 = [source, 'R4', sink]
        path1 = PathReq(Protocols.OSPF, 'Google', p1, False)
        path2 = PathReq(Protocols.OSPF, 'Google', p2, False)
        path3 = PathReq(Protocols.OSPF, 'Google', p3, False)
        paths = [path1, path2, path3]
        order_req = PathOrderReq(Protocols.OSPF, 'Google', paths, False)
        ospf = synet.synthesis.ospf.OSPFSyn(network_graph)
        ospf.add_req(order_req)
        ret = ospf.solve()
        self.assertTrue(ret)
        ospf.update_network_graph()
        p1_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p1[0::1], p1[1::1])]
        p2_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p2[0::1], p2[1::1])]
        p3_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p3[0::1], p3[1::1])]
        p4_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p4[0::1], p4[1::1])]
        p1_cost = sum(p1_cost)
        p2_cost = sum(p2_cost)
        p3_cost = sum(p3_cost)
        p4_cost = sum(p4_cost)
        self.assertLessEqual(p1_cost, p2_cost)
        self.assertLessEqual(p2_cost, p3_cost)
        self.assertLessEqual(p3_cost, p4_cost)

    @attr(speed='fast')
    def test_ordered_correct(self):
        fan_out = 4
        network_graph = self.get_triangles(fan_out)
        source = 'source'
        sink = 'sink'
        p1 = [source, 'R1', sink]
        p2 = [source, 'R2', sink]
        p3 = [source, 'R3', sink]
        p4 = [source, 'R4', sink]
        path1 = PathReq(Protocols.OSPF, 'Google', p1, False)
        path2 = PathReq(Protocols.OSPF, 'Google', p2, False)
        path3 = PathReq(Protocols.OSPF, 'Google', p3, False)
        paths = [path1, path2, path3]
        order_req = PathOrderReq(Protocols.OSPF, 'Google', paths, False)
        ospf = synet.synthesis.ospf_heuristic.OSPFSyn(network_graph, gen_paths=10)
        ospf.add_req(order_req)
        ret = ospf.synthesize()
        self.assertTrue(ret)
        ospf.update_network_graph()
        p1_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p1[0::1], p1[1::1])]
        p2_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p2[0::1], p2[1::1])]
        p3_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p3[0::1], p3[1::1])]
        p4_cost = [
            network_graph.get_edge_ospf_cost(src, dst)
            for src, dst in zip(p4[0::1], p4[1::1])]
        p1_cost = sum(p1_cost)
        p2_cost = sum(p2_cost)
        p3_cost = sum(p3_cost)
        p4_cost = sum(p4_cost)
        self.assertLessEqual(p1_cost, p2_cost)
        self.assertLessEqual(p2_cost, p3_cost)
        self.assertLessEqual(p3_cost, p4_cost)

    @attr(speed='fast')
    def test_ordered_notvalid(self):
        fan_out = 4
        network_graph = self.get_triangles(fan_out)
        source = 'source'
        sink = 'sink'
        p1 = [source, 'R1', sink]
        p2 = [source, 'R2', sink]
        p3 = [source, 'R3', sink]
        path1 = PathReq(Protocols.OSPF, 'Google', p1, False)
        path2 = PathReq(Protocols.OSPF, 'Google', p2, False)
        path3 = PathReq(Protocols.OSPF, 'Google', p3, False)
        paths = [path1, path2, path3]
        order_req1 = PathOrderReq(Protocols.OSPF, 'Google', paths, False)
        order_req2 = PathOrderReq(Protocols.OSPF, 'Google', [path3, path2, path1], False)
        ospf = synet.synthesis.ospf_heuristic.OSPFSyn(network_graph, gen_paths=10)
        ospf.add_req(order_req1)
        ospf.add_req(order_req2)
        ret = ospf.synthesize()
        self.assertFalse(ret)
