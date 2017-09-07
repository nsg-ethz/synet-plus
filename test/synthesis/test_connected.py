#!/usr/bin/env python
import unittest

from ipaddress import ip_interface

from synet.synthesis.connected import InterfaceIsDownError
from synet.synthesis.connected import DuplicateAddressError
from synet.synthesis.connected import NotValidSubnetsError
from synet.synthesis.connected import ConnectedSyn

from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.topo.graph import NetworkGraph

from synet.utils.common import Protocols
from synet.utils.common import PathReq
from synet.utils.smt_context import VALUENOTSET
from synet.utils.topo_gen import gen_mesh


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class ConnectedTest(unittest.TestCase):
    def get_two_nodes(self):
        g = NetworkGraph()
        g.add_router('R1')
        g.add_router('R2')
        g.add_router_edge('R1', 'R2')
        g.add_router_edge('R2', 'R1')
        return g

    def get_announcements(self, num_anns, num_communities):
        # Communities
        all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        cs = dict([(c, False) for c in all_communities])
        anns = {}
        for i in range(num_anns):
            ann = Announcement(
                prefix='P_%s' % i,
                peer='ATT',
                origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5, 7, 6], as_path_len=5,
                next_hop='ATTHop', local_pref=100,
                communities=cs, permitted=True)
            anns["%s_%s" % (ann.peer, ann.prefix)] = ann
        return anns

    def get_add_one_peer(self, g, nodes, announcements):
        g.add_peer('ATT')
        g.set_bgp_asnum('ATT', 2000)
        for node in nodes:
            g.add_peer_edge(node, 'ATT')
            g.add_peer_edge('ATT', node)
            g.add_bgp_neighbor(node, 'ATT', VALUENOTSET, VALUENOTSET)
        for ann in announcements:
            g.add_bgp_advertise(ann.peer, ann)
        return g

    def test_correct_concrete(self):
        g = self.get_two_nodes()
        reqs = [PathReq(Protocols.BGP, 'Prefix', ['R1', 'R2'], False)]

        addr1 = ip_interface(u"192.168.0.1/24")
        addr2 = ip_interface(u"192.168.0.2/24")

        # Set Iface for R1 to R2
        iface = 'Fa0/0'
        g.add_iface('R1', iface, is_shutdown=False)
        g.set_iface_addr('R1', iface, addr1)
        g.set_edge_iface('R1', 'R2', iface)
        g.set_iface_description('R1', iface, ''"To {}"''.format('R2'))

        # Set Iface for R2 to R1
        iface = 'Fa0/0'
        g.add_iface('R2', iface, is_shutdown=False)
        g.set_iface_addr('R2', iface, addr2)
        g.set_edge_iface('R2', 'R1', iface)
        g.set_iface_description('R2', iface, ''"To {}"''.format('R1'))

        p = ConnectedSyn(reqs, g)
        p.synthesize()

    def test_wrong_subnets(self):
        g = self.get_two_nodes()
        reqs = [PathReq(Protocols.BGP, 'Prefix', ['R1', 'R2'], False)]

        addr1 = ip_interface(u"192.168.0.1/24")
        addr2 = ip_interface(u"192.168.0.2/25")

        # Set Iface for R1 to R2
        iface = 'Fa0/0'
        g.add_iface('R1', iface, is_shutdown=False)
        g.set_iface_addr('R1', iface, addr1)
        g.set_edge_iface('R1', 'R2', iface)
        g.set_iface_description('R1', iface, ''"To {}"''.format('R2'))

        # Set Iface for R2 to R1
        iface = 'Fa0/0'
        g.add_iface('R2', iface, is_shutdown=False)
        g.set_iface_addr('R2', iface, addr2)
        g.set_edge_iface('R2', 'R1', iface)
        g.set_iface_description('R2', iface, ''"To {}"''.format('R1'))

        p = ConnectedSyn(reqs, g)
        with self.assertRaises(NotValidSubnetsError):
            p.synthesize()

    def test_duplicate_address(self):
        g = self.get_two_nodes()
        reqs = [PathReq(Protocols.BGP, 'Prefix', ['R1', 'R2'], False)]

        addr1 = ip_interface(u"192.168.0.1/24")
        addr2 = ip_interface(u"192.168.0.1/24")

        # Set Iface for R1 to R2
        iface = 'Fa0/0'
        g.add_iface('R1', iface, is_shutdown=False)
        g.set_iface_addr('R1', iface, addr1)
        g.set_edge_iface('R1', 'R2', iface)
        g.set_iface_description('R1', iface, ''"To {}"''.format('R2'))

        # Set Iface for R2 to R1
        iface = 'Fa0/0'
        g.add_iface('R2', iface, is_shutdown=False)
        g.set_iface_addr('R2', iface, addr2)
        g.set_edge_iface('R2', 'R1', iface)
        g.set_iface_description('R2', iface, ''"To {}"''.format('R1'))

        p = ConnectedSyn(reqs, g)
        with self.assertRaises(DuplicateAddressError):
            p.synthesize()

    def test_shutdown(self):
        g = self.get_two_nodes()
        reqs = [PathReq(Protocols.BGP, 'Prefix', ['R1', 'R2'], False)]

        addr1 = ip_interface(u"192.168.0.1/24")
        addr2 = ip_interface(u"192.168.0.1/24")

        # Set Iface for R1 to R2
        iface = 'Fa0/0'
        g.add_iface('R1', iface, is_shutdown=True)
        g.set_iface_addr('R1', iface, addr1)
        g.set_edge_iface('R1', 'R2', iface)
        g.set_iface_description('R1', iface, ''"To {}"''.format('R2'))

        # Set Iface for R2 to R1
        iface = 'Fa0/0'
        g.add_iface('R2', iface, is_shutdown=False)
        g.set_iface_addr('R2', iface, addr2)
        g.set_edge_iface('R2', 'R1', iface)
        g.set_iface_description('R2', iface, ''"To {}"''.format('R1'))

        p = ConnectedSyn(reqs, g)
        with self.assertRaises(InterfaceIsDownError):
            p.synthesize()

    def test_one_side_concrete(self):
        g = self.get_two_nodes()
        reqs = [PathReq(Protocols.BGP, 'Prefix', ['R1', 'R2'], False)]

        addr1 = ip_interface(u"192.168.0.1/24")
        # Set Iface for R1 to R2
        iface = 'Fa0/0'
        g.add_iface('R1', iface, is_shutdown=False)
        g.set_iface_addr('R1', iface, addr1)
        g.set_edge_iface('R1', 'R2', iface)
        g.set_iface_description('R1', iface, ''"To {}"''.format('R2'))

        # Set Iface for R2 to R1
        iface = 'Fa0/0'
        g.add_iface('R2', iface, is_shutdown=False)
        g.set_iface_addr('R2', iface, VALUENOTSET)
        g.set_edge_iface('R2', 'R1', iface)
        g.set_iface_description('R2', iface, ''"To {}"''.format('R1'))

        p = ConnectedSyn(reqs, g)
        p.synthesize()
        self.assertNotEqual(g.get_iface_addr('R2', iface), VALUENOTSET)

    def test_one_extra(self):
        g = self.get_two_nodes()
        g.add_router('R3')
        g.add_router_edge('R1', 'R3')
        g.add_router_edge('R2', 'R3')
        g.add_router_edge('R3', 'R1')
        g.add_router_edge('R3', 'R2')

        reqs = [PathReq(Protocols.BGP, 'Prefix', ['R1', 'R2'], False)]

        # Set Iface for R1 to R3
        iface1 = 'Fa0/0'
        addr1 = ip_interface(u"192.168.0.1/24")
        g.add_iface('R1', iface1, is_shutdown=False)
        g.set_iface_addr('R1', iface1, addr1)
        g.set_edge_iface('R1', 'R3', iface1)
        g.set_iface_description('R1', iface1, ''"To {}"''.format('R3'))

        # Set Iface for R3 to R1
        iface2 = 'Fa0/0'
        addr2 = ip_interface(u"192.168.0.2/24")
        g.add_iface('R3', iface2, is_shutdown=False)
        g.set_iface_addr('R3', iface2, addr2)
        g.set_edge_iface('R3', 'R1', iface2)
        g.set_iface_description('R3', iface2, ''"To {}"''.format('R1'))

        # Set Iface for R2 to R3
        iface3 = 'Fa0/0'
        addr3 = ip_interface(u"192.168.1.1/24")
        g.add_iface('R2', iface3, is_shutdown=True)
        g.set_iface_addr('R2', iface3, addr3)
        g.set_edge_iface('R2', 'R3', iface3)
        g.set_iface_description('R2', iface3, ''"To {}"''.format('R3'))

        # Set Iface for R3 to R2
        iface4 = 'Fa0/1'
        addr4 = ip_interface(u"192.168.2.2/24")
        g.add_iface('R3', iface4, is_shutdown=True)
        g.set_iface_addr('R3', iface4, addr4)
        g.set_edge_iface('R3', 'R2', iface4)
        g.set_iface_description('R3', iface4, ''"To {}"''.format('R1'))

        p = ConnectedSyn(reqs, g)
        p.synthesize()
        self.assertTrue(g.has_edge('R1', 'R2'))
        self.assertTrue(g.has_edge('R1', 'R3'))
        self.assertTrue(g.has_edge('R2', 'R1'))
        self.assertFalse(g.has_edge('R2', 'R3'))
        self.assertTrue(g.has_edge('R3', 'R1'))
        self.assertFalse(g.has_edge('R3', 'R2'))

    def test_grid_one_peer(self):
        anns = self.get_announcements(1, 1)
        g = gen_mesh(4, 100)
        self.get_add_one_peer(g, ['R2'], anns.values())

        ann = anns.values()[0]
        reqs = [
            PathReq(Protocols.BGP, ann.prefix, ['ATT', 'R2'], False),
            PathReq(Protocols.BGP, ann.prefix, ['ATT', 'R2', 'R1'], False),
            PathReq(Protocols.BGP, ann.prefix, ['ATT', 'R2', 'R3'], False),
            PathReq(Protocols.BGP, ann.prefix, ['ATT', 'R2', 'R4'], False),
        ]

        # Set Iface for R2 to ATT
        iface = 'Fa0/0'
        g.add_iface('R2', iface, is_shutdown=False)
        g.set_iface_addr('R2', iface, VALUENOTSET)
        g.set_edge_iface('R2', 'ATT', iface)
        g.set_iface_description('R2', iface, ''"To {}"''.format('ATT'))

        p = ConnectedSyn(reqs, g)
        p.synthesize()
