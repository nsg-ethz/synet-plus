#!/usr/bin/env python
import unittest

import z3

from synet.synthesis.connected import ConnectedSyn
from synet.synthesis.propagation import EBGPPropagation

from synet.topo.bgp import Access
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine
from synet.topo.graph import NetworkGraph

from synet.utils.common import PathProtocols
from synet.utils.common import PathReq
from synet.utils.smt_context import VALUENOTSET
from synet.utils.topo_gen import gen_mesh


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class iBGPTest(unittest.TestCase):
    def get_diamond(self, asnum):
        g = NetworkGraph()
        for num in range(4):
            node = 'R%d' % (num + 1)
            g.add_router(node)

        g.set_bgp_asnum('R1', asnum)
        g.set_bgp_asnum('R4', asnum)

        g.add_router_edge('R1', 'R2')
        g.add_router_edge('R1', 'R3')
        g.add_router_edge('R2', 'R1')
        g.add_router_edge('R2', 'R4')
        g.add_router_edge('R3', 'R1')
        g.add_router_edge('R3', 'R4')
        g.add_router_edge('R4', 'R2')
        g.add_router_edge('R4', 'R3')

        g.add_bgp_neighbor(router_a='R1',
                           router_b='R4',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
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

    def test_grid_one_peer(self):
        anns = self.get_announcements(1, 1)
        g = gen_mesh(4, 100)
        self.get_add_one_peer(g, ['R2'], anns.values())

        ann = anns.values()[0]
        reqs = [
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2', 'R1'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2', 'R3'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2', 'R4'], 10),
        ]
        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)
        p.synthesize()
        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        p.set_model(model)
        for node in g.routers_iter():
            box = g.node[node]['syn']['box']
            print box.get_config()

    def test_grid_one_peer2(self):
        anns = self.get_announcements(1, 1)
        g = gen_mesh(4, 100)
        self.get_add_one_peer(g, ['R2', 'R3'], anns.values())

        ann = anns.values()[0]
        reqs = [
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2', 'R4'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R3'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R3', 'R1'], 10),
        ]

        # R1 Import from R3
        set_pref = ActionSetLocalPref(VALUENOTSET)
        line1 = RouteMapLine(matches=None, actions=[set_pref],
                             access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=None,
                             access=Access.deny, lineno=20)
        name = "Import_R1_from_R3"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R1', rmap)
        g.add_bgp_import_route_map('R1', 'R3', rmap.name)

        # R4 Import from R2
        set_pref = ActionSetLocalPref(VALUENOTSET)
        line1 = RouteMapLine(matches=None, actions=[set_pref],
                             access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=None,
                             access=Access.deny, lineno=20)
        name = "Import_R4_from_R2"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R4', rmap)
        g.add_bgp_import_route_map('R4', 'R2', rmap.name)

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)
        p.synthesize()
        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        p.set_model(model)
        for node in g.routers_iter():
            box = g.node[node]['syn']['box']
            print box.get_config()

    def test_igp_fail(self):
        g = self.get_diamond(100)
        anns = self.get_announcements(1, 1)
        ann = anns.values()[0]
        self.get_add_one_peer(g, ['R1'], anns.values())

        # Just to force synthesizing interfaces
        syn1 = ConnectedSyn(
            [
                PathReq(PathProtocols.Static, ann.prefix, ['R1', 'R2'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R1', 'R3'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R2', 'R1'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R2', 'R4'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R3', 'R1'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R3', 'R4'], 10),
            ], g)
        syn1.synthesize()
        reqs = [
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R1', 'R2', 'R4'], 10),
        ]
        # Actual iBGP
        p = EBGPPropagation(reqs, g, allow_igp=False)
        p.synthesize()
        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        self.assertEquals(ret, z3.unsat)

    def test_igp_correct(self):
        g = self.get_diamond(100)
        anns = self.get_announcements(1, 1)
        ann = anns.values()[0]
        self.get_add_one_peer(g, ['R1'], anns.values())

        # Just to force synthesizing interfaces
        syn1 = ConnectedSyn(
            [
                PathReq(PathProtocols.Static, ann.prefix, ['R1', 'R2'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R1', 'R3'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R2', 'R1'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R2', 'R4'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R3', 'R1'], 10),
                PathReq(PathProtocols.Static, ann.prefix, ['R3', 'R4'], 10),
            ], g)
        syn1.synthesize()
        reqs = [
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R1', 'R2', 'R4'], 10),
        ]
        # Actual iBGP
        p = EBGPPropagation(reqs, g, allow_igp=True)
        p.synthesize()
        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        self.assertEquals(ret, z3.sat)