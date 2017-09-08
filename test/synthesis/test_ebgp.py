import unittest
from nose.plugins.attrib import attr
import time

import z3
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

    def _define_types(self, prefix_list=None, next_hope_list=None,
                      peer_list=None, as_path_list=None):
        # Ann Type
        (self.ann_sort, self.announcements) = \
            z3.EnumSort('AnnouncementSort', self.anns.keys())

        ann_map = dict([(str(ann), ann) for ann in self.announcements])
        self.ann_map = ann_map
        self.ann_var_map = dict([(self.ann_map[ann], self.anns[str(ann)]) for ann in self.ann_map])

        self.local_pref_fun = z3.Function('LocalPref', self.ann_sort, z3.IntSort())
        self.permitted_fun = z3.Function('PermittedFun', self.ann_sort, z3.BoolSort())

        if not prefix_list:
            l = [ann.prefix for ann in self.anns.values() if not is_empty(ann.prefix)]
            prefix_list = list(set(l))
        (self.prefix_sort, self.prefixes) = z3.EnumSort('PrefixSort', prefix_list)

        prefix_map = dict([(str(prefix), prefix) for prefix in self.prefixes])
        self.prefix_map = prefix_map
        self.prefix_fun = z3.Function('PrefixFunc', self.ann_sort, self.prefix_sort)

        if not peer_list:
            l = [x.peer for x in self.anns.values() if not is_empty(x.peer)]
            peer_list = list(set(l))
        (self.peer_sort, self.peers) = z3.EnumSort('PeerSort', peer_list)
        peer_map = dict([(str(p), p) for p in self.peers])
        self.peer_map = peer_map
        self.peer_fun = z3.Function('PeerFun', self.ann_sort, self.peer_sort)

        origin_list = BGP_ATTRS_ORIGIN.__members__.keys()
        (self.origin_sort, self.origins) = z3.EnumSort('OriginSort', origin_list)
        origin_map = dict([(str(p), p) for p in self.origins])
        for k, v in BGP_ATTRS_ORIGIN.__members__.iteritems():
            origin_map[v] = origin_map[k]
        self.origin_map = origin_map
        self.origin_fun = z3.Function('OriginFun', self.ann_sort, self.origin_sort)

        if not as_path_list:
            l = [get_as_path_key(x.as_path) for x in self.anns.values()
                 if not is_empty(x.as_path)]
            as_path_list = list(set(l))
        (self.as_path_sort, self.as_paths) = z3.EnumSort('PrefixSort', as_path_list)

        as_path_map = dict([(str(p), p) for p in self.as_paths])
        self.as_path_map = as_path_map
        self.as_path_fun = z3.Function('AsPathFunc', self.ann_sort, self.as_path_sort)
        self.as_path_len_fun = z3.Function('AsPathLenFunc', self.ann_sort, z3.IntSort())

        if not next_hope_list:
            l = [x.next_hop for x in self.anns.values() if not is_empty(x.next_hop)]
            next_hope_list = list(set(l))
        (self.next_hop_sort, self.next_hops) = z3.EnumSort('NexthopSort', next_hope_list)

        next_hop_map = dict([(str(p), p) for p in self.next_hops])
        self.next_hop_map = next_hop_map
        self.next_hop_fun = z3.Function('NexthopFunc', self.ann_sort, self.next_hop_sort)

        # Create functions for communities
        self.communities_fun = {}
        self.reverse_communities = {}
        for c in self.all_communities:
            name = 'Has_%s' % c.name
            self.communities_fun[c] = z3.Function(name, self.ann_sort, z3.BoolSort())
            self.reverse_communities[name] = c

        self.route_denied_fun = z3.Function('route_denied', self.ann_sort, z3.BoolSort())

    def setUp(self):
        self._pre_load()
        self._define_types()

    def get_solver(self):
        return z3.Solver()

    def get_context(self):
        # Create wrapper
        wprefix = SMTPrefixWrapper(
            'prefixw', self.ann_sort, self.ann_var_map,
            self.prefix_fun, self.prefix_sort, self.prefix_map)

        wpeer = SMTPeerWrapper(
            'wpeer', self.ann_sort, self.ann_var_map,
            self.peer_fun, self.peer_sort, self.peer_map)

        worigin = SMTOriginWrapper(
            'worigin', self.ann_sort, self.ann_var_map,
            self.origin_fun, self.origin_sort, self.origin_map)

        waspath = SMTASPathWrapper(
            'waspath', self.ann_sort, self.ann_var_map,
            self.as_path_fun, self.as_path_sort, self.as_path_map)

        waspathlen = SMTASPathLenWrapper(
            'waspathlen', self.ann_sort, self.ann_var_map,
            self.as_path_len_fun)

        wnext_hop = SMTNexthopWrapper(
            'wnext_hop', self.ann_sort, self.ann_var_map,
            self.next_hop_fun, self.next_hop_sort, self.next_hop_map)

        wlocalpref = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)

        wpermitted = SMTPermittedWrapper(
            'wpermitted', self.ann_sort, self.ann_var_map,
            self.permitted_fun)

        wcommunities = {}
        for community in self.all_communities:
            name = community.name
            wc1 = SMTCommunityWrapper(
                'w%s' % name, community, self.ann_sort,
                self.ann_var_map, self.communities_fun[community])
            wcommunities[community] = wc1

        ctx = SMTContext('ctx1', self.anns, self.ann_map, self.ann_sort,
                         wprefix, wpeer, worigin, waspath, waspathlen,
                         wnext_hop, wlocalpref, wcommunities, wpermitted)
        return ctx


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
        youtube_req1 = PathReq(Protocols.BGP, 'YouTube', ['ATT', 'R1'], False)
        google_req1 = PathReq(Protocols.BGP, 'Google', ['DT', 'R1'], False)

        reqs = [
            youtube_req1,
            google_req1,
        ]
        self.load_import_route_maps(g, 'R1', 'ATT', 100)
        self.load_import_route_maps(g, 'R1', 'DT', VALUENOTSET)

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

    @attr(speed='slow')
    def test_triangle(self):
        # Communities
        num_comms = 5
        num_prefixs = 100
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
        self._define_types()

        g = self.get_g_two_routers_one_peer()

        reqs = []
        for prefix in prefixs:
            req1 = PathReq(Protocols.BGP, prefix, ['ATT', 'R1'], False)
            req2 = PathReq(Protocols.BGP, prefix, ['ATT', 'R2'], False)
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
        self._define_types()

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
        req1 = PathReq(Protocols.BGP, prefixs[0], ['ATT', 'R1', 'R2'], False)
        reqs.append(req1)

        for prefix in prefixs[1:]:
            req1 = PathReq(Protocols.BGP, prefix, ['ATT', 'R1'], False)
            req2 = PathReq(Protocols.BGP, prefix, ['ATT', 'R2'], False)
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
        self.assertEquals(ret, z3.sat)
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
        self._define_types()

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
        req1 = PathReq(Protocols.BGP, prefixs[0], ['ATT', 'R1'], False)
        reqs.append(req1)
        req1 = PathReq(Protocols.BGP, prefixs[0], ['ATT', 'R2'], False)
        reqs.append(req1)

        for prefix in prefixs[1:]:
            req1 = PathReq(Protocols.BGP, prefix, ['ATT', 'R1', 'R2'], False)
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

        google_req1 = PathReq(Protocols.BGP, 'Google', ['ATT', 'R1', 'R2', 'R4', 'R5'], False)
        google_req2 = PathReq(Protocols.BGP, 'Google', ['ATT', 'R1', 'R3', 'R4'], False)
        reqs = [
            google_req1,
            google_req2,
        ]

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)
        p.synthesize()

        solver = z3.Solver()
        p.add_constraints(solver)
        ret = solver.check()
        self.assertEquals(ret, z3.unsat)

    def test_diamond_correct(self):
        self.anns = {'ATT_Google': self.anns['ATT_Google']}
        g = self.get_diamond_plus_one()

        google_req1 = PathReq(Protocols.BGP, 'Google', ['ATT', 'R1', 'R2', 'R4', 'R5'], False)
        google_req2 = PathReq(Protocols.BGP, 'Google', ['ATT', 'R1', 'R3'], False)
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
