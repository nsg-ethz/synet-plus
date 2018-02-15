
import time
import unittest

from nose.plugins.attrib import attr

import z3

from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.topo.graph import NetworkGraph
from synet.topo.bgp import Access
from synet.topo.bgp import ActionSetCommunity
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import Announcement as FullAnnouncement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList
from synet.topo.bgp import MatchCommunitiesList
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine

from synet.utils.smt_context import VALUENOTSET

from synet.synthesis.connected import ConnectedSyn
from synet.synthesis.propagation import EBGPPropagation


# Hack for interface change
from functools import partial
Announcement = partial(FullAnnouncement, med=100)


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


@attr(speed='fast')
class PropagationTest(unittest.TestCase):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='ATTHop', local_pref=100,
            communities={c1: False, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='YouTube', peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 8], as_path_len=5,
            next_hop='ATTHop', local_pref=100,
            communities={c1: True, c2: False, c3: True}, permitted=True)

        self.anns = {
            'ATT_Google': ann1,
            'ATT_YouTube': ann2,
        }

    def setUp(self):
        self._pre_load()

    def get_g_two_routers_one_peer(self):
        # Start with some initial inputs
        # This input only define routers
        g_phy = NetworkGraph()
        g_phy.add_router('R1')
        g_phy.add_router('R2')
        g_phy.add_peer('ATT')
        g_phy.set_bgp_asnum('R1', 100)
        g_phy.set_bgp_asnum('R2', 200)
        g_phy.set_bgp_asnum('ATT', 2000)

        g_phy.add_peer_edge('R1', 'ATT')
        g_phy.add_peer_edge('ATT', 'R1')
        g_phy.add_router_edge('R1', 'R2')
        g_phy.add_router_edge('R2', 'R1')
        g_phy.add_bgp_neighbor('R1', 'ATT',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        g_phy.add_bgp_neighbor('R1', 'R2',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        for ann in self.anns.values():
            g_phy.add_bgp_advertise(ann.peer, ann)
        return g_phy

    def get_g_two_routers_two_peers(self):
        # Start with some initial inputs
        # This input only define routers
        g_phy = NetworkGraph()
        g_phy.add_router('R1')
        g_phy.add_router('R2')
        g_phy.add_peer('ATT')
        g_phy.add_peer('DT')
        g_phy.set_bgp_asnum('R1', 100)
        g_phy.set_bgp_asnum('R2', 200)
        g_phy.set_bgp_asnum('ATT', 2000)
        g_phy.set_bgp_asnum('DT', 3000)

        g_phy.add_peer_edge('R1', 'ATT')
        g_phy.add_peer_edge('ATT', 'R1')
        g_phy.add_peer_edge('R2', 'DT')
        g_phy.add_peer_edge('DT', 'R2')

        g_phy.add_router_edge('R1', 'R2')
        g_phy.add_router_edge('R2', 'R1')

        g_phy.add_bgp_neighbor('R1', 'ATT',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        g_phy.add_bgp_neighbor('R1', 'R2',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        g_phy.add_bgp_neighbor('R2', 'DT',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        for ann in self.anns.values():
            g_phy.add_bgp_advertise(ann.peer, ann)
        return g_phy

    def load_import_route_maps(self, g, node, neighbor, value):
        set_localpref = ActionSetLocalPref(value)
        line = RouteMapLine(matches=None, actions=[set_localpref],
                            access=Access.permit, lineno=10)
        name = "From_%s_%s" % (node, neighbor)
        rmap = RouteMap(name=name, lines=[line])
        g.add_route_map(node, rmap)
        g.add_bgp_import_route_map(node, neighbor, rmap.name)

    def test_small(self):
        g = self.get_g_two_routers_one_peer()
        youtube_req1 = PathReq(Protocols.BGP, 'YouTube', ['R2', 'R1', 'ATT'], False)
        google_req1 = PathReq(Protocols.BGP, 'Google', ['R2', 'R1', 'ATT'], False)
        reqs = [
            youtube_req1,
            google_req1,
        ]

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)
        r1 = p.network_graph.node['R1']['syn']['box']
        p.synthesize()
        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        print solver.unsat_core()
        self.assertEquals(ret, z3.sat)
        p.set_model(solver.model())
        print r1.get_config()

    def test_two_peers(self):
        # Communities
        num_comms = 5
        num_prefixs = 1
        all_communities = []
        self.anns = {}
        prefixs = []
        for n in range(num_comms):
            all_communities.append(Community("100:%d" % n))
        for n in range(num_prefixs):
            comms = dict([(c, False) for c in all_communities])
            prefix = "Prefix_%d" % n
            prefixs.append(prefix)
            ann_name1 = "ATT_%s" % prefix
            ann1 = Announcement(
                prefix=prefix, peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[5000], as_path_len=1,
                next_hop='ATTHop', local_pref=100,
                communities=comms, permitted=True)
            self.anns[ann_name1] = ann1
            ann_name2 = "DT_%s" % prefix
            ann2 = Announcement(
                prefix=prefix, peer='DT', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[5000], as_path_len=1,
                next_hop='DTHop', local_pref=100,
                communities=comms, permitted=True)
            self.anns[ann_name2] = ann2
        self.all_communities = set(all_communities)

        g = self.get_g_two_routers_two_peers()

        # Export route map
        action = ActionSetCommunity([all_communities[0]])
        line = RouteMapLine(matches=None, actions=[action],
                            access=Access.permit, lineno=10)
        name = "Export_R1_to_R2"
        rmap = RouteMap(name=name, lines=[line])
        g.add_route_map('R1', rmap)
        g.add_bgp_export_route_map('R1', 'R2', rmap.name)

        # Import Route Map at R2
        clist = CommunityList(list_id=1, access=Access.permit, communities=[VALUENOTSET])
        match = MatchCommunitiesList(clist)
        set_pref = ActionSetLocalPref(VALUENOTSET)
        line1 = RouteMapLine(matches=[match], actions=[set_pref],
                            access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=None,
                             access=Access.deny, lineno=20)
        name = "Import_R2_from_R1"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R2', rmap)
        g.add_bgp_import_route_map('R2', 'R1', rmap.name)

        reqs = []
        for prefix in prefixs:
            req1 = PathReq(Protocols.BGP, prefix, ['R2', 'R1', 'ATT'], False)
            reqs.append(req1)

        connected_syn = ConnectedSyn([], g, full=True)
        connected_syn.synthesize()
        start = time.time()
        p = EBGPPropagation(reqs, g)
        p.synthesize()
        end = time.time()
        init_time = end - start
        solver = z3.Solver()
        start = time.time()
        p.add_constraints(solver, track=False)
        end = time.time()
        load_time = end - start
        start = time.time()
        ret = solver.check()
        end = time.time()
        smt_time = end - start
        print "Init Time", init_time, "Seconds"
        print "SMT Load Time", load_time, "Seconds"
        print "SMT Solve Time", smt_time, "Seconds"
        # print solver.to_smt2()
        # print solver.unsat_core()
        self.assertEquals(ret, z3.sat)
        p.set_model(solver.model())
        r1 = p.network_graph.node['R1']['syn']['box']
        r2 = p.network_graph.node['R2']['syn']['box']
        print "R1 Configs"
        print r1.get_config()
        print "R2 Configs"
        print r2.get_config()
        print r1.general_ctx.communities_ctx.keys()
