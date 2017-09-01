#!/usr/bin/env python

import tempfile
import unittest

from synet.topo.graph import EDGETYPE
from synet.topo.graph import EDGE_TYPE
from synet.topo.graph import VERTEX_TYPE
from synet.topo.graph import VERTEXTYPE
from synet.topo.graph import NetworkGraph


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class TestNetworkGraph(unittest.TestCase):

    def get_mesh(self, g_size):
        # Start with some initial inputs
        # This input only define routers
        g_phy = NetworkGraph()
        for num in range(g_size):
            node = 'R%d' % (num + 1)
            g_phy.add_router(node)
            g_phy.set_bgp_asnum(node, 100)

        for src in g_phy.nodes():
            for dst in g_phy.nodes():
                if src == dst:
                    continue
                g_phy.add_router_edge(src, dst)
                g_phy.add_bgp_neighbor(src, dst)
        return g_phy

    def get_add_one_peer(self, g, nodes, announcements):
        g.add_peer('ATT')
        g.set_bgp_asnum('ATT', 2000)
        for node in nodes:
            g.add_peer_edge(node, 'ATT')
            g.add_peer_edge('ATT', node)
            g.add_bgp_neighbor(node, 'ATT')
        for ann in announcements:
            g.add_bgp_advertise(ann.peer, ann)
        return g

    def test_add_node(self):
        g = NetworkGraph()
        with self.assertRaises(ValueError):
            g.add_node('R1')

    def test_add_router(self):
        # init
        g = NetworkGraph()
        router = 'R1'
        # Action
        g.add_router(router)
        # Asserts
        self.assertTrue(g.has_node(router))
        self.assertTrue(g.is_router(router))
        self.assertTrue(g.is_local_router(router))
        self.assertEqual(g.node[router][VERTEX_TYPE], VERTEXTYPE.ROUTER)
        self.assertEqual(list(g.routers_iter()), [router])
        self.assertEqual(list(g.local_routers_iter()), [router])
        self.assertFalse(g.is_network(router))
        self.assertFalse(g.is_peer(router))

    def test_add_network(self):
        # init
        g = NetworkGraph()
        network = 'NET1'
        # Action
        g.add_network(network)
        # Asserts
        self.assertTrue(g.has_node(network))
        self.assertTrue(g.is_network(network))
        self.assertEqual(g.node[network][VERTEX_TYPE], VERTEXTYPE.NETWORK)
        self.assertFalse(g.is_router(network))
        self.assertFalse(g.is_local_router(network))
        self.assertFalse(g.is_peer(network))
        self.assertEqual(list(g.networks_iter()), [network])

    def test_add_peer(self):
        # init
        g = NetworkGraph()
        peer = 'PEER1'
        # Action
        g.add_peer(peer)
        # Asserts
        self.assertTrue(g.has_node(peer))
        self.assertTrue(g.is_peer(peer))
        self.assertTrue(g.is_router(peer))
        self.assertEqual(g.node[peer][VERTEX_TYPE], VERTEXTYPE.PEER)
        self.assertEqual(list(g.peers_iter()), [peer])
        self.assertFalse(g.is_local_router(peer))
        self.assertFalse(g.is_network(peer))

    def test_add_edge(self):
        # init
        g = NetworkGraph()
        router1 = 'R1'
        router2 = 'R2'
        g.add_router(router1)
        g.add_router(router2)
        # Action
        g.add_edge('R1', 'R2', **{EDGE_TYPE: EDGETYPE.ROUTER})
        with self.assertRaises(ValueError):
            g.add_edge('R1', 'R2')

    def test_add_router_link(self):
        # init
        g = NetworkGraph()
        router1 = 'R1'
        router2 = 'R2'
        g.add_router(router1)
        g.add_router(router2)
        # Action
        g.add_router_edge(router1, router2)
        # Assert
        self.assertEqual(list(g.edges()), [(router1, router2)])
        self.assertEqual(g[router1][router2][EDGE_TYPE], EDGETYPE.ROUTER)

    def test_add_peer_link(self):
        # init
        g = NetworkGraph()
        router1 = 'R1'
        router2 = 'R2'
        g.add_router(router1)
        g.add_peer(router2)
        # Action
        g.add_peer_edge(router1, router2)
        # Assert
        self.assertEqual(list(g.edges()), [(router1, router2)])
        self.assertEqual(g[router1][router2][EDGE_TYPE], EDGETYPE.PEER)

    def test_write_graphml(self):
        g = self.get_mesh(4)
        self.get_add_one_peer(g, ['R2', 'R3'], [])
        graphml_file = tempfile.NamedTemporaryFile(prefix='synet_test')
        g.write_graphml(graphml_file)
