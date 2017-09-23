import unittest
from nose.plugins.attrib import attr
import time

import z3
from synet.utils.common import PathOrderReq
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.topo.graph import NetworkGraph
from synet.topo.bgp import Access
from synet.topo.bgp import ActionSetCommunity
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine
from synet.topo.bgp import IpPrefixList
from synet.topo.bgp import MatchIpPrefixListList
from synet.topo.bgp import MatchCommunitiesList

from synet.utils.smt_context import VALUENOTSET
from synet.utils.bgp_utils import ConflictingPreferences

from synet.synthesis.connected import ConnectedSyn
from synet.synthesis.propagation import EBGPPropagation


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


@attr(speed='fast')
class SMTSetup(unittest.TestCase):
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
            prefix='Google', peer='DT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[3, 2, 5, 7, 6], as_path_len=5,
            next_hop='DTHop', local_pref=100,
            communities={c1: False, c2: False, c3: False}, permitted=True)

        ann3 = Announcement(
            prefix='YouTube', peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 8], as_path_len=5,
            next_hop='ATTHop', local_pref=100,
            communities={c1: True, c2: False, c3: True}, permitted=True)

        self.anns = {
            'ATT_Google': ann1,
            'DT_Google': ann2,
            'ATT_YouTube': ann3,
        }

    def setUp(self):
        self._pre_load()

    def get_solver(self):
        return z3.Solver()


@attr(speed='fast')
class EBGPTest(SMTSetup):
    def get_g_one_router_two_peers(self):
        """
        Get a simple graph of 1 local router and two peers ATT, DT
        :return: Networkx Digraph
        """
        # Start with some initial inputs
        # This input only define routers
        g_phy = NetworkGraph()
        g_phy.add_router('R1')
        g_phy.add_peer('ATT')
        g_phy.add_peer('DT')
        g_phy.set_bgp_asnum('R1', 100)
        g_phy.set_bgp_asnum('ATT', 2000)
        g_phy.set_bgp_asnum('DT', 3000)

        g_phy.add_peer_edge('ATT', 'R1')
        g_phy.add_peer_edge('R1', 'ATT')
        g_phy.add_peer_edge('DT', 'R1')
        g_phy.add_peer_edge('R1', 'DT')

        g_phy.add_bgp_neighbor('R1', 'ATT',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        g_phy.add_bgp_neighbor('R1', 'DT',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        for ann in self.anns.values():
            g_phy.add_bgp_advertise(ann.peer, ann)
        return g_phy

    def get_g_two_routers_one_peer(self):
        """
        Get a simple graph of 1 local router and two peers ATT, DT
        :return: Networkx Digraph
        """
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
        g_phy.add_router_edge('R1', 'R2')
        g_phy.add_peer_edge('R2', 'ATT')
        g_phy.add_router_edge('R2', 'R1')
        g_phy.add_peer_edge('ATT', 'R1')
        g_phy.add_peer_edge('ATT', 'R2')

        g_phy.add_bgp_neighbor('R1', 'ATT',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        g_phy.add_bgp_neighbor('R1', 'R2',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        g_phy.add_bgp_neighbor('R2', 'ATT',
                               router_a_iface=VALUENOTSET,
                               router_b_iface=VALUENOTSET)
        for ann in self.anns.values():
            g_phy.add_bgp_advertise(ann.peer, ann)
        return g_phy

    def get_diamond_plus_one(self):
        g = NetworkGraph()
        asnum = 100
        for num in range(5):
            node = 'R%d' % (num + 1)
            g.add_router(node)
            g.set_bgp_asnum(node, asnum)
            asnum += 100

        g.add_router_edge('R1', 'R2')
        g.add_router_edge('R1', 'R3')
        g.add_router_edge('R2', 'R1')
        g.add_router_edge('R2', 'R4')
        g.add_router_edge('R3', 'R1')
        g.add_router_edge('R3', 'R4')
        g.add_router_edge('R4', 'R2')
        g.add_router_edge('R4', 'R3')
        g.add_router_edge('R4', 'R5')
        g.add_router_edge('R5', 'R4')

        g.add_peer('ATT')
        g.set_bgp_asnum('ATT', 2000)
        g.add_peer_edge('R1', 'ATT')
        g.add_peer_edge('ATT', 'R1')

        g.add_bgp_neighbor(router_a='R1',
                           router_b='ATT',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R1',
                           router_b='R2',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R1',
                           router_b='R3',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R2',
                           router_b='R4',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R3',
                           router_b='R4',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R4',
                           router_b='R5',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        for ann in self.anns.values():
            if g.has_node(ann.peer):
                g.add_bgp_advertise(ann.peer, ann)
        return g

    def load_import_route_maps(self, g, node, neighbor, value):
        set_localpref = ActionSetLocalPref(value)
        line = RouteMapLine(matches=None, actions=[set_localpref],
                            access=Access.permit, lineno=10)
        name = "From_%s_%s" % (node, neighbor)
        rmap = RouteMap(name=name, lines=[line])
        g.add_route_map(node, rmap)
        g.add_bgp_import_route_map(node, neighbor, rmap.name)

    def test_small(self):
        g = self.get_g_one_router_two_peers()
        youtube_req1 = PathReq(Protocols.BGP, 'YouTube', ['R1', 'ATT'], False)
        google_req1 = PathReq(Protocols.BGP, 'Google', ['R1', 'DT'], False)

        reqs = [
            youtube_req1,
            google_req1,
        ]
        self.load_import_route_maps(g, 'R1', 'ATT', VALUENOTSET)
        self.load_import_route_maps(g, 'R1', 'DT', VALUENOTSET)

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)
        r1 = p.network_graph.node['R1']['syn']['box']
        p.synthesize()

        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        self.assertEquals(ret, z3.sat, solver.unsat_core())
        p.set_model(solver.model())
        print r1.get_config()

    def test_small_order(self):
        g = self.get_g_one_router_two_peers()
        youtube_req1 = PathReq(Protocols.BGP, 'YouTube', ['R1', 'ATT'], False)
        google_p1 = PathReq(Protocols.BGP, 'Google', ['R1', 'DT'], False)
        google_p2 = PathReq(Protocols.BGP, 'Google', ['R1', 'ATT'], False)
        google_req = PathOrderReq(Protocols.BGP, 'Google', [google_p1, google_p2], False)
        reqs = [
            youtube_req1,
            google_req,
        ]
        self.load_import_route_maps(g, 'R1', 'ATT', VALUENOTSET)
        self.load_import_route_maps(g, 'R1', 'DT', VALUENOTSET)

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)
        r1 = p.network_graph.node['R1']['syn']['box']
        p.synthesize()

        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        print solver.to_smt2()
        self.assertEquals(ret, z3.sat, solver.unsat_core())
        p.set_model(solver.model())
        print r1.get_config()

    @attr(speed='slow')
    def test_triangle(self):
        # Communities
        num_comms = 5
        num_prefixs = 2
        all_communities = []
        anns = {}
        prefixs = []
        for n in range(num_comms):
            c1 = Community("100:%d" % n)
            all_communities.append(c1)
        for n in range(num_prefixs):
            comms = dict([(c, False) for c in all_communities])
            prefix = "Prefix_%d" % n
            prefixs.append(prefix)
            ann_name = "ATT_%s" % prefix
            ann1 = Announcement(
                prefix=prefix, peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[5000], as_path_len=1,
                next_hop='ATTHop', local_pref=100,
                communities=comms, permitted=True)
            anns[ann_name] = ann1
        self.all_communities = set(all_communities)
        self.anns = anns

        g = self.get_g_two_routers_one_peer()

        reqs = []
        for prefix in prefixs:
            req1 = PathReq(Protocols.BGP, prefix, ['R1', 'ATT'], False)
            req2 = PathReq(Protocols.BGP, prefix, ['R2', 'ATT'], False)
            reqs.append(req1)
            reqs.append(req2)

        connected_syn = ConnectedSyn(reqs, g)
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
        #print solver.to_smt2()
        #print solver.unsat_core()
        self.assertEquals(ret, z3.sat)
        p.set_model(solver.model())
        r1 = p.network_graph.node['R1']['syn']['box']
        r2 = p.network_graph.node['R2']['syn']['box']
        print r1.get_config()
        print r2.get_config()

    def test_triangle_comm(self):
        # Communities
        num_comms = 5
        num_prefixs = 2
        all_communities = []
        anns = {}
        prefixs = []
        for n in range(num_comms):
            c1 = Community("100:%d" % n)
            all_communities.append(c1)
        for n in range(num_prefixs):
            comms = dict([(c, False) for c in all_communities])
            prefix = "Prefix_%d" % n
            prefixs.append(prefix)
            ann_name = "ATT_%s" % prefix
            ann1 = Announcement(
                prefix=prefix, peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[5000, 5100], as_path_len=2,
                next_hop='ATTHop', local_pref=100,
                communities=comms, permitted=True)
            anns[ann_name] = ann1
        self.all_communities = set(all_communities)
        self.anns = anns

        g = self.get_g_two_routers_one_peer()

        # R1 import route map
        set_c1 = ActionSetCommunity([all_communities[0]])
        iplist = IpPrefixList(name='L1', access=Access.permit,
                              networks=[VALUENOTSET])
        match = MatchIpPrefixListList(iplist)
        line1 = RouteMapLine(matches=[match], actions=[set_c1],
                            access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=None,
                             access=Access.permit, lineno=500)
        name = "R1_import_ATT"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R1', rmap)
        g.add_bgp_import_route_map('R1', 'ATT', rmap.name)

        # R2 import from R1 route map
        set_pref = ActionSetLocalPref(VALUENOTSET)
        clist = CommunityList(list_id='A', access=Access.permit, communities=[VALUENOTSET])
        match = MatchCommunitiesList(clist)
        line1 = RouteMapLine(matches=[match], actions=[set_pref],
                            access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=[],
                             access=Access.permit, lineno=500)
        name = "R2_import_R1"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R2', rmap)
        g.add_bgp_import_route_map('R2', 'R1', rmap.name)

        # R2 Import from ATT
        iplist = IpPrefixList(name='L1', access=Access.permit,
                              networks=[VALUENOTSET])
        match = MatchIpPrefixListList(iplist)
        line1 = RouteMapLine(matches=[match], actions=None,
                             access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=[],
                             access=Access.permit, lineno=500)
        name = "R2_import_ATT"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R2', rmap)
        g.add_bgp_import_route_map('R2', 'ATT', rmap.name)

        reqs = []
        req1 = PathReq(Protocols.BGP, prefixs[0], ['R2', 'R1', 'ATT'], False)
        reqs.append(req1)

        for prefix in prefixs[1:]:
            req1 = PathReq(Protocols.BGP, prefix, ['R1', 'ATT'], False)
            req2 = PathReq(Protocols.BGP, prefix, ['R2', 'ATT'], False)
            reqs.append(req1)
            reqs.append(req2)

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        start = time.time()
        p = EBGPPropagation(reqs, g)
        p.synthesize()
        end = time.time()
        init_time = end - start
        solver = z3.Solver()
        start = time.time()
        p.add_constraints(solver, track=True)
        end = time.time()
        load_time = end - start
        start = time.time()
        ret = solver.check()
        print solver.unsat_core()
        end = time.time()
        smt_time = end - start
        print "Init Time", init_time, "Seconds"
        print "SMT Load Time", load_time, "Seconds"
        print "SMT Solve Time", smt_time, "Seconds"
        #print solver.to_smt2()
        #print solver.unsat_core()
        self.assertEquals(ret, z3.sat, solver.unsat_core())
        p.set_model(solver.model())
        r1 = p.network_graph.node['R1']['syn']['box']
        r2 = p.network_graph.node['R2']['syn']['box']
        print r1.get_config()
        print r2.get_config()

    def test_triangle_deny(self):
        # Communities
        num_comms = 5
        num_prefixs = 2
        all_communities = []
        anns = {}
        prefixs = []
        for n in range(num_comms):
            c1 = Community("100:%d" % n)
            all_communities.append(c1)
        for n in range(num_prefixs):
            comms = dict([(c, False) for c in all_communities])
            prefix = "Prefix_%d" % n
            prefixs.append(prefix)
            ann_name = "ATT_%s" % prefix
            ann1 = Announcement(
                prefix=prefix, peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[5000, 5100], as_path_len=2,
                next_hop='ATTHop', local_pref=100,
                communities=comms, permitted=True)
            anns[ann_name] = ann1
        self.all_communities = set(all_communities)
        self.anns = anns

        g = self.get_g_two_routers_one_peer()

        # R1 export to R2
        iplist = IpPrefixList(name='L1', access=Access.permit,
                              networks=[VALUENOTSET])
        match = MatchIpPrefixListList(iplist)
        line1 = RouteMapLine(matches=[match], actions=None,
                             access=Access.deny, lineno=10)
        line2 = RouteMapLine(matches=None, actions=[],
                             access=Access.permit, lineno=20)
        name = "R1_export_R2"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R1', rmap)
        g.add_bgp_export_route_map('R1', 'R2', rmap.name)

        # R2 export to R1
        iplist = IpPrefixList(name='L2', access=Access.permit,
                              networks=[VALUENOTSET])
        match = MatchIpPrefixListList(iplist)
        line1 = RouteMapLine(matches=[match], actions=None,
                             access=Access.deny, lineno=10)
        line2 = RouteMapLine(matches=None, actions=[],
                             access=Access.permit, lineno=20)
        name = "R2_export_R1"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R2', rmap)
        g.add_bgp_export_route_map('R2', 'R1', rmap.name)

        # R2 Import from R1
        set_pref = ActionSetLocalPref(VALUENOTSET)
        line1 = RouteMapLine(matches=None, actions=[set_pref],
                             access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=[],
                             access=Access.deny, lineno=500)
        name = "R2_import_from_R1"
        rmap = RouteMap(name=name, lines=[line1, line2])
        g.add_route_map('R2', rmap)
        g.add_bgp_import_route_map('R2', 'R1', rmap.name)

        reqs = []
        req1 = PathReq(Protocols.BGP, prefixs[0], ['R1', 'ATT'], False)
        reqs.append(req1)
        req1 = PathReq(Protocols.BGP, prefixs[0], ['R2', 'ATT'], False)
        reqs.append(req1)

        for prefix in prefixs[1:]:
            req1 = PathReq(Protocols.BGP, prefix, ['R2', 'R1', 'ATT'], False)
            reqs.append(req1)

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        start = time.time()
        p = EBGPPropagation(reqs, g)
        p.synthesize()
        end = time.time()
        init_time = end - start
        solver = z3.Solver()
        start = time.time()
        p.add_constraints(solver, track=True)
        end = time.time()
        load_time = end - start
        start = time.time()
        ret = solver.check()
        print "Unsat core", solver.unsat_core()
        end = time.time()
        smt_time = end - start
        print "Init Time", init_time, "Seconds"
        print "SMT Load Time", load_time, "Seconds"
        print "SMT Solve Time", smt_time, "Seconds"
        #print solver.to_smt2()
        #print solver.model()
        print "Unsat core", solver.unsat_core()
        self.assertEquals(ret, z3.sat)
        p.set_model(solver.model())
        r1 = p.network_graph.node['R1']['syn']['box']
        r2 = p.network_graph.node['R2']['syn']['box']
        print r1.get_config()
        print r2.get_config()

    def test_diamond_fail(self):
        self.anns = {'ATT_Google': self.anns['ATT_Google']}
        g = self.get_diamond_plus_one()

        google_req1 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R2', 'R1', 'ATT'], False)
        google_req2 = PathReq(Protocols.BGP, 'Google', ['R4', 'R3', 'R1', 'ATT'], False)
        reqs = [
            google_req1,
            google_req2,
        ]

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        with self.assertRaises(ConflictingPreferences):
            p = EBGPPropagation(reqs, g)
            p.synthesize()

            solver = z3.Solver()
            p.add_constraints(solver)
            ret = solver.check()
            self.assertEquals(ret, z3.unsat)

    def test_diamond_correct(self):
        self.anns = {'ATT_Google': self.anns['ATT_Google']}
        g = self.get_diamond_plus_one()

        google_req1 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R2', 'R1', 'ATT'], False)
        google_req2 = PathReq(Protocols.BGP, 'Google', ['R3', 'R1', 'ATT'], False)
        reqs = [
            google_req1,
            google_req2,
        ]
        self.load_import_route_maps(g, 'R4', 'R2', 200)
        self.load_import_route_maps(g, 'R3', 'R1', 200)
        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)
        p.synthesize()

        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        self.assertEquals(ret, z3.sat)
