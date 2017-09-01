#!/usr/bin/env python
import time
import unittest

import z3
from synet.utils.common import PathReq
from synet.utils.common import PathProtocols
from synet.topo.graph import NetworkGraph
from synet.topo.bgp import Access
from synet.topo.bgp import ActionSetCommunity
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList
from synet.topo.bgp import MatchCommunitiesList
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine

from synet.utils.smt_context import SMTASPathWrapper
from synet.utils.smt_context import SMTASPathLenWrapper
from synet.utils.smt_context import SMTContext
from synet.utils.smt_context import SMTCommunityWrapper
from synet.utils.smt_context import SMTLocalPrefWrapper
from synet.utils.smt_context import SMTNexthopWrapper
from synet.utils.smt_context import SMTOriginWrapper
from synet.utils.smt_context import SMTPeerWrapper
from synet.utils.smt_context import SMTPrefixWrapper
from synet.utils.smt_context import SMTPermittedWrapper
from synet.utils.smt_context import get_as_path_key
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import VALUENOTSET

from synet.synthesis.propagation import EBGPPropagation


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class iBGPTest(unittest.TestCase):
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

    def get_grid(self):
        # Start with some initial inputs
        # This input only define routers
        g_phy = NetworkGraph()
        g_phy.add_router('R1')
        g_phy.add_router('R2')
        g_phy.add_router('R3')
        g_phy.add_router('R4')

        g_phy.set_bgp_asnum('R1', 100)
        g_phy.set_bgp_asnum('R2', 100)
        g_phy.set_bgp_asnum('R3', 100)
        g_phy.set_bgp_asnum('R4', 100)

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
        g_phy.add_router_edge('R4', 'R4')

        g_phy.add_bgp_neighbor('R1', 'R2')
        g_phy.add_bgp_neighbor('R1', 'R3')
        g_phy.add_bgp_neighbor('R1', 'R4')
        g_phy.add_bgp_neighbor('R2', 'R1')
        g_phy.add_bgp_neighbor('R2', 'R3')
        g_phy.add_bgp_neighbor('R2', 'R4')
        g_phy.add_bgp_neighbor('R3', 'R1')
        g_phy.add_bgp_neighbor('R3', 'R2')
        g_phy.add_bgp_neighbor('R3', 'R4')
        g_phy.add_bgp_neighbor('R4', 'R1')
        g_phy.add_bgp_neighbor('R4', 'R2')
        g_phy.add_bgp_neighbor('R4', 'R3')
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

    def test_grid_one_peer(self):
        anns = self.get_announcements(1, 1)
        g = self.get_grid()
        self.get_add_one_peer(g, ['R2'], anns.values())

        ann = anns.values()[0]
        reqs = [
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2', 'R1'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2', 'R3'], 10),
            PathReq(PathProtocols.BGP, ann.prefix, ['ATT', 'R2', 'R4'], 10),
        ]
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
        g = self.get_grid()
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
