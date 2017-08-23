import unittest

import z3

from synet.synthesis.ebgp import Announcement
from synet.synthesis.ebgp import BGP_ATTRS_ORIGIN

from synet.topo.bgp import Access
from synet.topo.bgp import ActionSetCommunity
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList
from synet.topo.bgp import IpPrefixList
from synet.topo.bgp import MatchCommunitiesList
from synet.topo.bgp import MatchIpPrefixListList
from synet.topo.bgp import MatchNextHop
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine
from synet.topo.bgp import VALUENOTSET

from synet.utils.policy import OrOp
from synet.utils.policy import SMTActions
from synet.utils.policy import SMTCommunity
from synet.utils.policy import SMTCommunityList
from synet.utils.policy import SMTLocalPref
from synet.utils.policy import SMTIpPrefix
from synet.utils.policy import SMTIpPrefixList
from synet.utils.policy import SMTMatch
from synet.utils.policy import SMTMatches
from synet.utils.policy import SMTNextHop
from synet.utils.policy import SMTRouteMap
from synet.utils.policy import SMTRouteMapLine
from synet.utils.policy import SMTSetCommunity
from synet.utils.policy import SMTSetLocalPref

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
from synet.utils.smt_context import is_symbolic


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


def is_symbolic(var):
    return hasattr(var, 'sort')


class SMTSetup(unittest.TestCase):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='SwissCom', local_pref=100,
            communities={c1: True, c2: False, c3: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
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


class SMTCommunityTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='SwissCom', local_pref=100,
            communities={c1: True, c2: False, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='SwissCom', local_pref=100,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_match_concrete(self):
        c1, c2, c3 = self.all_communities
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        ctx = self.get_context()

        # Create wrapper
        c1_match = SMTCommunity(name='rm1', community=c1, context=ctx)
        c2_match = SMTCommunity(name='rm2', community=c2, context=ctx)
        c3_match = SMTCommunity(name='rm3', community=c3, context=ctx)
        s1 = self.get_solver()
        s2 = self.get_solver()
        s3 = self.get_solver()
        s4 = self.get_solver()
        # Assumptions
        s1.add(c1_match.match_fun(ann1) == True)
        s2.add(c2_match.match_fun(ann1) == False)
        s3.add(c3_match.match_fun(ann1) == True)
        # SMT Solving
        c1_match.add_constraints(s1)
        c2_match.add_constraints(s2)
        c3_match.add_constraints(s3)
        ctx.add_constraints(s1)
        ctx.add_constraints(s2)
        ctx.add_constraints(s3)
        ctx.add_constraints(s4)
        # Assertions
        self.assertEquals(s1.check(), z3.sat)
        self.assertEquals(s2.check(), z3.sat)
        self.assertEquals(s3.check(), z3.sat)
        self.assertEquals(s4.check(), z3.sat)
        m1 = s1.model()
        m2 = s2.model()
        m3 = s3.model()
        c1_match.set_model(m1)
        c2_match.set_model(m2)
        c3_match.set_model(m3)
        c1_val = c1_match.get_value()
        c2_val = c2_match.get_value()
        c3_val = c3_match.get_value()
        self.assertEquals(c1_val, c1)
        self.assertEquals(c2_val, c2)
        self.assertEquals(c3_val, c3)
        self.assertEquals(c1_match.get_config(), c1)
        self.assertEquals(c2_match.get_config(), c2)
        self.assertEquals(c3_match.get_config(), c3)

    def test_match_notconcrete(self):
        c1, c2, c3 = self.all_communities
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        ctx = self.get_context()

        # Create wrapper
        c1_match = SMTCommunity(name='rm1', community=VALUENOTSET, context=ctx)
        s1 = self.get_solver()
        # Assumptions
        s1.add(c1_match.match_fun(ann1) == True)
        s1.add(c1_match.match_fun(ann2) == True)
        # SMT Solving
        c1_match.add_constraints(s1)
        ctx.add_constraints(s1)
        # Assertions
        self.assertEquals(s1.check(), z3.sat)
        m1 = s1.model()
        c1_match.set_model(m1)
        c1_val = c1_match.get_value()
        self.assertEquals(c1_val, c3)
        self.assertEquals(c1_match.get_config(), c3)


class SMTCommunityListTest(SMTSetup):
    def test_communities_list(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        c1_list = CommunityList(1, Access.permit, [c1, c3])
        l1_match = SMTCommunityList(
            name='rm1', community_list=c1_list, context=ctx)
        c2_list = CommunityList(1, Access.permit,
                                [VALUENOTSET, VALUENOTSET])
        l2_match = SMTCommunityList(
            name='rm2', community_list=c2_list, context=ctx)

        s1 = self.get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        s1.add(match1 == True)
        ctx.add_constraints(s1)
        l1_match.add_constraints(s1)


        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        l1_match.set_model(m)
        self.assertEquals(l1_match.get_value(), [c1, c3])

        self.assertEquals(l1_match.get_config(), c1_list)

        s2 = self.get_solver()
        match2 = l2_match.match_fun(self.ann_map['Ann1_Google'])
        s2.add(match2 == True)
        ctx.add_constraints(s2)
        l2_match.add_constraints(s2)
        self.assertEquals(s2.check(), z3.sat)
        m = s2.model()
        l2_match.set_model(m)
        self.assertEquals(set(l2_match.get_value()), set([c1, c3]))
        self.assertEquals(l2_match.get_config(), c1_list)

    def test_stress_partial_comp(self):
        num_communities = 100
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            if i == 0:
                cs = [(self.all_communities[0], True)]
                cs += [(c, False) for c in self.all_communities[1:]]
            else:
                cs = [(c, False) for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                prefix=name, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='N',
                local_pref=100, communities=cs, permitted=True)
            self.anns[name] = ann
        self._define_types()

        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [c1])
        l1_m = SMTCommunityList(name='rm1', community_list=c1_l, context=ctx)

        s1 = self.get_solver()
        match1 = l1_m.match_fun(self.ann_map['Prefix_0'])
        s1.add(match1 == True)
        ctx.add_constraints(s1)
        l1_m.add_constraints(s1)

        self.assertTrue(l1_m.is_concrete())
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        l1_m.set_model(m)
        self.assertEquals(l1_m.get_value(), [c1])

    def test_stress_no_partial_eval(self):
        num_communities = 100
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            if i == 0:
                cs = [(self.all_communities[0], True)]
                cs += [(c, False) for c in self.all_communities[1:]]
            else:
                cs = [(c, False) for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                prefix=name, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='N',
                local_pref=100, communities=cs, permitted=True)
            self.anns[name] = ann

        self._define_types()
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [VALUENOTSET])
        l1_m = SMTCommunityList(name='rm1', community_list=c1_l, context=ctx)

        s1 = self.get_solver()
        match1 = l1_m.match_fun(self.ann_map['Prefix_0'])
        s1.add(match1 == True)
        ctx.add_constraints(s1)
        l1_m.add_constraints(s1)
        self.assertFalse(l1_m.is_concrete())
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        l1_m.set_model(m)
        self.assertEquals(l1_m.get_value(), [c1])


class SMTIpPrefixTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix=VALUENOTSET, peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_match_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        self._define_types(prefix_list=['Google', 'Yahoo'])
        ctx = self.get_context()
        google = self.prefix_map['Google']
        yahoo = self.prefix_map['Yahoo']

        p1_match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)
        p2_match = SMTIpPrefix(name='p2', prefix=yahoo, context=ctx)
        s1 = self.get_solver()
        # Assumptions
        s1.add(p1_match.match_fun(ann1) == True)
        s1.add(p2_match.match_fun(ann1) == False)
        s1.add(p1_match.match_fun(ann2) == False)
        s1.add(p2_match.match_fun(ann2) == True)
        # Solve SMT
        p1_match.add_constraints(s1)
        p2_match.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        p1_match.set_model(m)
        p2_match.set_model(m)
        self.assertEquals(p1_match.get_var(), google)
        self.assertEquals(p1_match.get_value(), 'Google')
        self.assertEquals(p2_match.get_var(), yahoo)
        self.assertEquals(p2_match.get_value(), 'Yahoo')

    def test_match_notconcrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        self._define_types(prefix_list=['Google', 'Yahoo'])
        ctx = self.get_context()
        google = self.prefix_map['Google']
        yahoo = self.prefix_map['Yahoo']

        p3_match = SMTIpPrefix(name='p3', prefix=VALUENOTSET, context=ctx)
        p4_match = SMTIpPrefix(name='p4', prefix=VALUENOTSET, context=ctx)
        s1 = self.get_solver()
        # Assumptions
        s1.add(p3_match.match_fun(ann1) == True)
        s1.add(p3_match.match_fun(ann2) == False)
        s1.add(p4_match.match_fun(ann1) == False)
        s1.add(p4_match.match_fun(ann2) == True)
        # Solve SMT
        ctx.add_constraints(s1)
        p3_match.add_constraints(s1)
        p4_match.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        p3_match.set_model(m)
        p4_match.set_model(m)
        self.assertEquals(p3_match.get_var(), google)
        self.assertEquals(p3_match.get_value(), 'Google')
        self.assertEquals(p4_match.get_var(), yahoo)
        self.assertEquals(p4_match.get_value(), 'Yahoo')


class SMTIpPrefixListTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_ip_prefix_list(self):
        google = self.prefix_map['Google']
        yahoo = self.prefix_map['Yahoo']
        ctx = self.get_context()
        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        p2_list = IpPrefixList(2, access=Access.permit, networks=['Yahoo'])
        p3_list = IpPrefixList(1, access=Access.permit, networks=[VALUENOTSET])
        p4_list = IpPrefixList(2, access=Access.permit, networks=[VALUENOTSET])

        l1_match = SMTIpPrefixList(name='pl1', prefix_list=p1_list, context=ctx)
        l2_match = SMTIpPrefixList(name='pl2', prefix_list=p2_list, context=ctx)
        l3_match = SMTIpPrefixList(name='pl3', prefix_list=p3_list, context=ctx)
        l4_match = SMTIpPrefixList(name='pl4', prefix_list=p4_list, context=ctx)

        s1 = self.get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = l2_match.match_fun(self.ann_map['Ann2_Yahoo'])
        match3 = l3_match.match_fun(self.ann_map['Ann1_Google'])
        match4 = l4_match.match_fun(self.ann_map['Ann2_Yahoo'])
        s1.add(match1 == True)
        s1.add(match2 == True)
        s1.add(match3 == True)
        s1.add(match4 == True)
        l1_match.add_constraints(s1)
        l2_match.add_constraints(s1)
        l3_match.add_constraints(s1)
        l4_match.add_constraints(s1)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()

        l1_match.set_model(m)
        l2_match.set_model(m)
        l3_match.set_model(m)
        l4_match.set_model(m)

        self.assertEquals(l1_match.get_var(), [google])
        self.assertEquals(l2_match.get_var(), [yahoo])
        self.assertEquals(l3_match.get_var(), [google])
        self.assertEquals(l4_match.get_var(), [yahoo])
        self.assertEquals(l3_match.get_config(), p1_list)
        self.assertEquals(l4_match.get_config(), p2_list)


class SMTNextHopTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='ATT',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[7, 2, 5, 7, 8], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_match_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        att = self.next_hop_map['ATT']
        dt = self.next_hop_map['DT']
        ctx = self.get_context()
        # Subject
        p1_match = SMTNextHop(name='p1', next_hop='ATT', context=ctx)
        p2_match = SMTNextHop(name='p2', next_hop='DT', context=ctx)
        # Assumptions
        s1 = self.get_solver()
        s1.add(p1_match.match_fun(ann1) == True)
        s1.add(p2_match.match_fun(ann1) == False)
        s1.add(p1_match.match_fun(ann2) == False)
        s1.add(p2_match.match_fun(ann2) == True)
        # SMT Sove
        p1_match.add_constraints(s1)
        p2_match.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        p1_match.set_model(m)
        p2_match.set_model(m)
        self.assertEquals(p1_match.get_var(), att)
        self.assertEquals(p1_match.get_value(), 'ATT')
        self.assertEquals(p2_match.get_var(), dt)
        self.assertEquals(p2_match.get_value(), 'DT')

    def test_prefix_match_notconcrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        att = self.next_hop_map['ATT']
        dt = self.next_hop_map['DT']
        ctx = self.get_context()
        # Subject
        p1_match = SMTNextHop(name='p1', next_hop=VALUENOTSET, context=ctx)
        p2_match = SMTNextHop(name='p2', next_hop=VALUENOTSET, context=ctx)
        # Assumptions
        s1 = self.get_solver()
        s1.add(p1_match.match_fun(ann1) == True)
        s1.add(p1_match.match_fun(ann2) == False)
        s1.add(p2_match.match_fun(ann1) == False)
        s1.add(p2_match.match_fun(ann2) == True)
        # Load SMT
        p1_match.add_constraints(s1)
        p2_match.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        p1_match.set_model(m)
        p2_match.set_model(m)
        self.assertEquals(p1_match.get_var(), att)
        self.assertEquals(p1_match.get_value(), 'ATT')
        self.assertEquals(p2_match.get_var(), dt)
        self.assertEquals(p2_match.get_value(), 'DT')


class SMTLocalPrefTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=200, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_match_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        self._define_types(prefix_list=['Google', 'Yahoo'])
        ctx = self.get_context()

        p1_match = SMTLocalPref(name='p1', local_pref=100, context=ctx)
        p2_match = SMTLocalPref(name='p2', local_pref=200, context=ctx)
        s1 = self.get_solver()
        # Assumptions
        s1.add(p1_match.match_fun(ann1) == True)
        s1.add(p2_match.match_fun(ann1) == False)
        s1.add(p1_match.match_fun(ann2) == False)
        s1.add(p2_match.match_fun(ann2) == True)
        # Solve SMT
        p1_match.add_constraints(s1)
        p2_match.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertTrue(p1_match.is_concrete_match())
        self.assertTrue(p2_match.is_concrete_match())
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        p1_match.set_model(m)
        p2_match.set_model(m)
        self.assertEquals(p1_match.get_var(), 100)
        self.assertEquals(p1_match.get_value(), 100)
        self.assertEquals(p2_match.get_var(), 200)
        self.assertEquals(p2_match.get_value(), 200)

    def test_match_notconcrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        self._define_types(prefix_list=['Google', 'Yahoo'])
        ctx = self.get_context()

        p3_match = SMTLocalPref(name='p3', local_pref=VALUENOTSET, context=ctx)
        p4_match = SMTLocalPref(name='p4', local_pref=VALUENOTSET, context=ctx)
        s1 = self.get_solver()
        # Assumptions
        s1.add(p3_match.match_fun(ann1) == True)
        s1.add(p3_match.match_fun(ann2) == False)
        s1.add(p4_match.match_fun(ann1) == False)
        s1.add(p4_match.match_fun(ann2) == True)
        # Solve SMT
        ctx.add_constraints(s1)
        p3_match.add_constraints(s1)
        p4_match.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertFalse(p3_match.is_concrete_match())
        self.assertFalse(p4_match.is_concrete_match())
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        p3_match.set_model(m)
        p4_match.set_model(m)
        self.assertEquals(p3_match.get_var(), 100)
        self.assertEquals(p3_match.get_value(), 100)
        self.assertEquals(p4_match.get_var(), 200)
        self.assertEquals(p4_match.get_value(), 200)


class SMTMatchTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True, c2: False, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True, c2: False, c3: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_ip_prefix_list(self):
        ctx = self.get_context()
        google = self.ann_map['Ann1_Google']
        yahoo = self.ann_map['Ann2_Yahoo']

        # Matches
        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        p2_list = IpPrefixList(2, access=Access.permit, networks=['Yahoo'])
        p3_list = IpPrefixList(1, access=Access.permit, networks=[VALUENOTSET])
        p4_list = IpPrefixList(2, access=Access.permit, networks=[VALUENOTSET])

        l1_m = MatchIpPrefixListList(prefix_list=p1_list)
        l2_m = MatchIpPrefixListList(prefix_list=p2_list)
        l3_m = MatchIpPrefixListList(prefix_list=p3_list)
        l4_m = MatchIpPrefixListList(prefix_list=p4_list)

        l1_match = SMTMatch(name='m1', match=l1_m, context=ctx)
        l2_match = SMTMatch(name='m2', match=l2_m, context=ctx)
        l3_match = SMTMatch(name='m3', match=l3_m, context=ctx)
        l4_match = SMTMatch(name='m4', match=l4_m, context=ctx)

        # Assertions
        s1 = self.get_solver()
        match1 = l1_match.match_fun(google)
        match2 = l2_match.match_fun(yahoo)
        match3 = l3_match.match_fun(google)
        match4 = l4_match.match_fun(yahoo)
        s1.add(match1 == True)
        s1.add(match2 == True)
        s1.add(match3 == True)
        s1.add(match4 == True)
        ctx.add_constraints(s1)
        l1_match.add_constraints(s1)
        l2_match.add_constraints(s1)
        l3_match.add_constraints(s1)
        l4_match.add_constraints(s1)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        l1_match.set_model(m)
        l2_match.set_model(m)
        l3_match.set_model(m)
        l4_match.set_model(m)
        self.assertEquals(l1_match.get_value(), ['Google'])
        self.assertEquals(l2_match.get_value(), ['Yahoo'])
        self.assertEquals(l3_match.get_value(), ['Google'])
        self.assertEquals(l4_match.get_value(), ['Yahoo'])
        self.assertEquals(l1_match.get_config(), l1_m)
        self.assertEquals(l2_match.get_config(), l2_m)
        self.assertEquals(l3_match.get_config(), l1_m)
        self.assertEquals(l4_match.get_config(), l2_m)

    def test_communities_list(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]
        google = self.ann_map['Ann1_Google']
        # Matches
        c1_l = CommunityList(1, Access.permit, [c1, c3])
        c2_l = CommunityList(1, Access.permit, [VALUENOTSET, VALUENOTSET])
        l1_m = MatchCommunitiesList(communities_list=c1_l)
        l2_m = MatchCommunitiesList(communities_list=c2_l)

        l1_match = SMTMatch(name='m1', match=l1_m, context=ctx)
        l2_match = SMTMatch(name='m2', match=l2_m, context=ctx)
        # Assumptions
        s1 = self.get_solver()
        match1 = l1_match.match_fun(google)
        s1.add(match1 == True)
        l1_match.add_constraints(s1)
        ctx.add_constraints(s1)
        match2 = l2_match.match_fun(google)
        s1.add(match2 == True)
        l2_match.add_constraints(s1)
        # Assertions
        ret = s1.check()
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        l1_match.set_model(m)
        l2_match.set_model(m)
        self.assertEquals(l1_match.get_value(), [c1, c3])
        self.assertEquals(l1_match.get_config(), l1_m)
        self.assertEquals(set(l2_match.get_value()), set([c1, c3]))
        self.assertEquals(l2_match.get_config(), l1_m)

    def test_or(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Matches
        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        p2_list = IpPrefixList(2, access=Access.permit, networks=['Yahoo'])
        p3_list = IpPrefixList(1, access=Access.permit, networks=[VALUENOTSET])
        p4_list = IpPrefixList(2, access=Access.permit, networks=[VALUENOTSET])

        l1_m = MatchIpPrefixListList(prefix_list=p1_list)
        l2_m = MatchIpPrefixListList(prefix_list=p2_list)
        l3_m = MatchIpPrefixListList(prefix_list=p3_list)
        l4_m = MatchIpPrefixListList(prefix_list=p4_list)

        or1 = OrOp(values=[l1_m, l2_m])
        or2 = OrOp(values=[l1_m, l3_m])
        or3 = OrOp(values=[l3_m, l4_m])

        l1_match = SMTMatch(name='m1', match=or1, context=ctx)
        l2_match = SMTMatch(name='m2', match=or2, context=ctx)
        l3_match = SMTMatch(name='m3', match=or3, context=ctx)
        # Assumptions
        s1 = self.get_solver()
        match1 = l1_match.match_fun(ann1)
        match2 = l2_match.match_fun(ann2)
        match3 = l3_match.match_fun(ann1)

        s1.add(match1 == True)
        s1.add(match2 == True)
        s1.add(match3 == True)
        ctx.add_constraints(s1)
        l1_match.add_constraints(s1)
        l2_match.add_constraints(s1)
        l3_match.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        l1_match.set_model(m)
        l2_match.set_model(m)
        l3_match.set_model(m)
        self.assertEquals(len(l1_match.get_value()), 2)
        self.assertEquals(len(l2_match.get_value()), 2)
        self.assertEquals(len(l3_match.get_value()), 2)
        self.assertEquals(l1_match.get_value(), [['Google'], ['Yahoo']])
        self.assertEquals(l2_match.get_value(), [['Google'], ['Yahoo']])
        self.assertEquals(l1_match.get_config(), [l1_m, l2_m])


class SMTMatchesTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True, c2: False, c3: True},
            permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True, c2: False, c3: False},
            permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        ctx = self.get_context()
        c1, c2, c3 = self.all_communities

        # Matches
        c1_l = CommunityList(1, Access.permit, [c1, c3])
        l1_m = MatchCommunitiesList(communities_list=c1_l)
        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        l2_m = MatchIpPrefixListList(prefix_list=p1_list)
        # Group AND match
        l1_match = SMTMatches(name='m1', matches=[l1_m, l2_m], context=ctx)
        # Assumptions
        s1 = self.get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        s1.add(match1 == True)
        l1_match.add_constraints(s1)
        ctx.add_constraints(s1)
        ret = s1.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        l1_match.set_model(m)
        self.assertEquals(l1_match.get_value(), [[c1, c3], ['Google']])

    def test_empty_matches(self):
        ctx = self.get_context()
        # Matches
        l1_match = SMTMatches(name='m1', matches=[], context=ctx)
        s1 = self.get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = l1_match.match_fun(self.ann_map['Ann2_Yahoo'])
        # Load Constraints
        l1_match.add_constraints(s1)
        ctx.add_constraints(s1)
        ret = s1.check()
        self.assertEquals(ret, z3.sat)
        m = s1.model()
        self.assertTrue(z3.is_true(m.eval(match1)))
        self.assertTrue(z3.is_true(m.eval(match2)))


class SMTSetLocalPrefTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_set_concrete(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        # Match
        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)
        # Set
        set1 = SMTSetLocalPref(name='s1', localpref=200, match=match, context=ctx)
        # Load SMT
        s1 = self.get_solver()
        set1.add_constraints(s1)
        ctx2 = set1.get_new_context()
        ctx2.add_constraints(s1)
        # Assertions
        self.assertEquals(s1.check(), z3.sat)
        self.assertTrue(set1.is_concrete())
        model1 = s1.model()
        set1.set_model(model1)
        ctx2.set_model(model1)
        self.assertEquals(set1.get_var(), 200)
        #self.assertEquals(model1.eval(set1.action_fun(ann1)).as_long(), 200)
        #self.assertEquals(model1.eval(set1.action_fun(ann2)).as_long(), 100)
        self.assertEquals(ctx.local_pref_ctx.get_value(ann1), 100)
        self.assertEquals(ctx.local_pref_ctx.get_value(ann2), 100)
        self.assertEquals(ctx2.local_pref_ctx.get_value(ann1), 200)
        self.assertEquals(ctx2.local_pref_ctx.get_value(ann2), 100)
        self.assertEquals(set1.get_config(), ActionSetLocalPref(200))

    def test_set_notconcrete(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)

        set2 = SMTSetLocalPref(name='s2', localpref=VALUENOTSET,
                               match=match, context=ctx)

        s2 = self.get_solver()
        self.assertFalse(set2.is_concrete())
        s2.add(set2.action_fun(ann1) == 200)
        ctx2 = set2.get_new_context()
        ctx2.add_constraints(s2)
        set2.add_constraints(s2)
        match.add_constraints(s2)
        ctx2 = set2.get_new_context()
        self.assertEquals(s2.check(), z3.sat)
        model2 = s2.model()
        set2.set_model(model2)
        ctx2.set_model(model2)
        self.assertFalse(set2.is_concrete())
        self.assertEquals(set2.get_value(), 200)
        self.assertEquals(model2.eval(set2.action_fun(ann1)).as_long(), 200)
        self.assertEquals(model2.eval(set2.action_fun(ann2)).as_long(), 100)
        self.assertEquals(ctx2.local_pref_ctx.get_value(ann1), 200)
        self.assertEquals(ctx2.local_pref_ctx.get_value(ann2), 100)
        self.assertEquals(set2.get_config(), ActionSetLocalPref(200))


class SMTSetCommunityTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: False, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: True, c3: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_set_concrete_additive(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)

        self.assertTrue(match.is_match(ann1))
        set1 = SMTSetCommunity(name='s1', communities=[c1, c2],
                               additive=True, match=match, context=ctx)

        # Concrete, Additive = True
        s = self.get_solver()
        self.assertTrue(match.is_concrete())
        set1.add_constraints(s)
        match.add_constraints(s)
        ctx.add_constraints(s)

        self.assertEquals(s.check(), z3.sat)
        self.assertTrue(set1.is_concrete())
        ctx2 = set1.get_new_context()
        model = s.model()
        set1.set_model(model)
        self.assertEquals(set1.get_value(), [c1, c2])
        self.assertTrue(ctx2.communities_ctx[c1].get_var(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_var(ann1))
        self.assertTrue(ctx2.communities_ctx[c3].get_var(ann1))

        self.assertFalse(ctx2.communities_ctx[c1].get_var(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_var(ann2))
        self.assertTrue(ctx2.communities_ctx[c3].get_var(ann2))
        self.assertEquals(set1.get_config(), ActionSetCommunity([c1, c2]))

    def test_set_concrete_notadditive(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)
        set1 = SMTSetCommunity(name='s1', communities=[c1, c2],
                               additive=False, match=match, context=ctx)

        s = self.get_solver()
        # Concrete, Additive = False

        self.assertTrue(set1.is_concrete())
        set1.add_constraints(s)
        match.add_constraints(s)
        ctx.add_constraints(s)

        self.assertEquals(s.check(), z3.sat)
        ctx2 = set1.get_new_context()
        model = s.model()
        set1.set_model(model)
        match.set_model(model)
        self.assertEquals(set1.get_value(), [c1, c2])
        self.assertTrue(ctx2.communities_ctx[c1].get_var(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_var(ann1))
        self.assertFalse(ctx2.communities_ctx[c3].get_var(ann1))

        self.assertFalse(ctx2.communities_ctx[c1].get_var(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_var(ann2))
        self.assertTrue(ctx2.communities_ctx[c3].get_var(ann2))
        self.assertEquals(set1.get_config(), ActionSetCommunity([c1, c2]))


    def test_set_concrete_syn_notadditive(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)
        set1 = SMTSetCommunity(name='s1', communities=[c1, c2],
                               additive=VALUENOTSET, match=match, context=ctx)

        s = self.get_solver()
        # Concrete, Additive = False
        set1.add_constraints(s)
        match.add_constraints(s)

        ctx2 = set1.get_new_context()
        ctx2.add_constraints(s)
        self.assertTrue(set1.is_concrete())


        self.assertEquals(s.check(), z3.sat)

        model = s.model()
        set1.set_model(model)
        match.set_model(model)
        ctx2.set_model(model)
        self.assertEquals(set1.get_value(), [c1, c2])
        self.assertTrue(ctx2.communities_ctx[c1].get_value(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann1))
        self.assertFalse(ctx2.communities_ctx[c3].get_value(ann1))

        self.assertFalse(ctx2.communities_ctx[c1].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c3].get_value(ann2))
        self.assertEquals(set1.get_config(), ActionSetCommunity([c1, c2]))


    @unittest.skip
    def test_set_notconcrete_additive(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)
        set1 = SMTSetCommunity(name='s2', communities=[c1, VALUENOTSET],
                               additive=True, match=match, context=ctx)

        # Not Concrete, Additive = True
        s = self.get_solver()
        self.assertFalse(set1.is_concrete())
        s.add(set1.constraints)
        s.add(match.constraints)

        self.assertEquals(s.check(), z3.sat)

        ctx = set1.get_new_context()
        model = s.model()
        self.assertEquals(set1.get_val(model), [c1, c2])
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c1](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertEquals(set1.get_config(model), ActionSetCommunity([c1, c2]))

    @unittest.skip
    def test_set_notconcrete_notadditive(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)
        set1 = SMTSetCommunity(name='s1', communities=[c1, VALUENOTSET, VALUENOTSET],
                               additive=False, match=match, context=ctx)

        s = self.get_solver()
        # Concrete, Additive = False

        self.assertFalse(set1.is_concrete())
        s.add(set1.constraints)
        s.add(match.constraints)

        self.assertEquals(s.check(), z3.sat)
        ctx = set1.get_new_context()
        model = s.model()
        self.assertEquals(set1.get_val(model), [c1, c2])
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c1](ann2))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann2))))
        self.assertEquals(set1.get_config(model), ActionSetCommunity([c1, c2]))


class SMTActionsTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: False, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: True, c3: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_set_actions(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)

        set_c = ActionSetCommunity(communities=[c1, c2], additive=False)
        set_pref = ActionSetLocalPref(200)
        actions = SMTActions(name='s1', match=match,
                             actions=[set_c, set_pref], context=ctx)

        # Concrete, Additive = True
        s = self.get_solver()
        actions.add_constraints(s)
        match.add_constraints(s)
        ctx2 = actions.get_new_context()
        ctx2.add_constraints(s)
        s.add(ctx2.local_pref_ctx.fun(ann1) == 200)

        self.assertEquals(s.check(), z3.sat)
        self.assertTrue(actions.is_concrete())

        model = s.model()
        ctx2.set_model(model)
        actions.set_model(model)
        self.assertTrue(ctx2.communities_ctx[c1].get_value(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann1))
        self.assertFalse(ctx2.communities_ctx[c3].get_value(ann1))
        self.assertFalse(ctx2.communities_ctx[c1].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c3].get_value(ann2))
        self.assertEquals(actions.get_config(), [set_c, set_pref])


class SMTRouteMapLineTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: False, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: True, c3: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_matches_actions(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        match = MatchIpPrefixListList(prefix_list=p1_list)
        matches = [match]

        set_c = ActionSetCommunity(communities=[c1, c2], additive=False)
        set_pref = ActionSetLocalPref(200)
        actions = [set_c, set_pref]
        line = RouteMapLine(matches=matches, actions=actions,
                            access=Access.permit, lineno=10)

        l = SMTRouteMapLine(name='l', line=line, context=ctx)
        # Load SMT
        s = self.get_solver()
        l.add_constraints(s)
        ctx2 = l.get_new_context()
        ctx2.add_constraints(s)
        ret = s.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = s.model()
        l.set_model(model)
        self.assertTrue(ctx2.communities_ctx[c1].get_value(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann1))
        self.assertFalse(ctx2.communities_ctx[c3].get_value(ann1))

        self.assertFalse(ctx2.communities_ctx[c1].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c3].get_value(ann2))

        self.assertEquals(l.get_value(), (True, [['Google']], [[c1, c2], 200]))
        self.assertEquals(l.get_config(), line)

    def test_none_actions(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        matches = []

        set_c = ActionSetCommunity(communities=[c1, c2], additive=False)
        set_pref = ActionSetLocalPref(200)
        actions = [set_c, set_pref]
        line = RouteMapLine(matches=matches, actions=actions,
                            access=Access.permit, lineno=10)

        l = SMTRouteMapLine(name='l', line=line, context=ctx)

        # Load SMT
        s = self.get_solver()
        l.add_constraints(s)
        ctx2 = l.get_new_context()
        ctx2.add_constraints(s)
        s.add(l.matches.match_fun(ann1) == True)
        ret = s.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = s.model()
        ctx2.set_model(model)
        l.set_model(model)
        self.assertTrue(ctx2.communities_ctx[c1].get_value(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann1))
        self.assertFalse(ctx2.communities_ctx[c3].get_value(ann1))

        self.assertTrue(ctx2.communities_ctx[c1].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann2))
        self.assertFalse(ctx2.communities_ctx[c3].get_value(ann2))

        self.assertEquals(l.get_value(), (True, [True], [[c1, c2], 200]))
        self.assertEquals(l.get_config(), line)

    def test_syn_access(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        match = MatchIpPrefixListList(prefix_list=p1_list)
        matches = [match]

        set_c = ActionSetCommunity(communities=[c1, c2], additive=False)
        set_pref = ActionSetLocalPref(200)
        actions = [set_c, set_pref]
        line = RouteMapLine(matches=matches, actions=actions,
                            access=VALUENOTSET, lineno=10)

        l = SMTRouteMapLine(name='l', line=line, context=ctx)
        # Load SMT
        s = self.get_solver()
        l.add_constraints(s)
        ctx2 = l.get_new_context()
        s.add(l.permitted_action.get_var() == True)
        ctx2.add_constraints(s)
        ret = s.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = s.model()
        l.set_model(model)
        ctx2.set_model(model)

        self.assertTrue(ctx2.communities_ctx[c1].get_value(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann1))
        self.assertFalse(ctx2.communities_ctx[c3].get_value(ann1))

        self.assertFalse(ctx2.communities_ctx[c1].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c3].get_value(ann2))
        self.assertEquals(l.get_value(), (True, [['Google']], [[c1, c2], 200]))
        line.access = Access.permit
        self.assertEquals(l.get_config(), line)

    def test_stress(self):
        num_communities = 2
        num_anns = 2
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns / 2):
            prefix = 'Prefix_%d' % i
            name1 = "Ann_%s_1" % prefix
            name2 = "Ann_%s_2" % prefix
            cs1 = [(self.all_communities[0], True)]
            cs1 += [(c, False) for c in self.all_communities[1:]]
            cs2 = [(c, False) for c in self.all_communities]
            cs1 = dict(cs1)
            cs2 = dict(cs2)

            ann1 = Announcement(
                prefix=name1, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='N',
                local_pref=100, communities=cs1, permitted=True)
            self.anns[name1] = ann1

            ann2 = Announcement(
                prefix=name1, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='N',
                local_pref=100, communities=cs2, permitted=True)
            self.anns[name2] = ann2

        self._define_types()

        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [c1])
        matches = [MatchCommunitiesList(c1_l)]
        actions = [ActionSetLocalPref(VALUENOTSET)]
        line = RouteMapLine(matches=matches, actions=actions,
                            access=VALUENOTSET, lineno=10)

        rline = SMTRouteMapLine(name='l', line=line, context=ctx)

        s1 = self.get_solver()
        ctx2 = rline.get_new_context()
        for name, ann in self.ann_map.iteritems():
            s1.add(ctx2.permitted_ctx.get_value(ann) == True)
            if name.endswith('_1'):
                s1.add(ctx2.local_pref_ctx.fun(ann) == 200)

        rline.add_constraints(s1)
        ctx2.add_constraints(s1)
        ret = s1.check()
        self.assertEquals(ret, z3.sat)
        model = s1.model()
        ctx2.set_model(model)
        rline.set_model(model)
        for name, ann in self.ann_map.iteritems():
            if name.endswith('_1'):
                self.assertEquals(ctx2.local_pref_ctx.get_value(ann), 200)
            else:
                self.assertEquals(ctx2.local_pref_ctx.get_value(ann), 100)

        new_line = RouteMapLine(
            matches=[MatchCommunitiesList(CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(200)],
            access=Access.permit,
            lineno=10
        )
        self.assertEquals(rline.get_config(), new_line)


class SMTRouteMapTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: False, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: False, c2: True, c3: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_matches_actions(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        p2_list = IpPrefixList(1, access=Access.permit, networks=['Yahoo'])
        match_google = MatchIpPrefixListList(prefix_list=p1_list)
        match_yahoo = MatchIpPrefixListList(prefix_list=p2_list)

        set_c1_c2 = ActionSetCommunity(communities=[c1, c2], additive=False)
        set_c2_c3 = ActionSetCommunity(communities=[c2, c3], additive=False)
        set_pref200 = ActionSetLocalPref(200)
        set_pref400 = ActionSetLocalPref(VALUENOTSET)

        l1 = RouteMapLine(matches=[match_google],
                          actions=[set_c1_c2, set_pref200],
                          access=Access.permit,
                          lineno=10)

        l2 = RouteMapLine(matches=[match_yahoo],
                          actions=[set_c2_c3, set_pref400],
                          access=Access.permit, lineno=20)

        route_map = RouteMap(name='rm1', lines=[l1, l2])
        r = SMTRouteMap(name='l', route_map=route_map, context=ctx)

        s = self.get_solver()
        r.add_constraints(s)
        ctx2 = r.get_new_context()
        s.add(ctx2.local_pref_ctx.fun(ann2) == 400)

        ctx2.add_constraints(s)
        self.assertEquals(s.check(), z3.sat)
        model = s.model()
        r.set_model(model)
        ctx.set_model(model)
        ctx2.set_model(model)

        self.assertTrue(ctx2.communities_ctx[c1].get_value(ann1))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann1))
        self.assertFalse(ctx2.communities_ctx[c3].get_value(ann1))

        self.assertFalse(ctx2.communities_ctx[c1].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c2].get_value(ann2))
        self.assertTrue(ctx2.communities_ctx[c3].get_value(ann2))

        self.assertEquals(ctx2.local_pref_ctx.get_value(ann1), 200)
        self.assertEquals(ctx2.local_pref_ctx.get_value(ann2), 400)
        self.assertEquals(r.get_value(),
                          [(True, [['Google']], [[c1, c2], 200]),
                           (True, [['Yahoo']], [[c2, c3], 400])
                           ])
        l1 = RouteMapLine(matches=[match_google],
                          actions=[set_c1_c2, set_pref200],
                          access=Access.permit, lineno=10)
        l2 = RouteMapLine(matches=[match_yahoo],
                          actions=[set_c2_c3, ActionSetLocalPref(400)],
                          access=Access.permit, lineno=20)

        route_map = RouteMap(name='rm1', lines=[l1, l2])
        self.assertEquals(r.get_config(), route_map)

    def test_stress(self):
        num_communities = 2
        num_anns = 2
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns / 2):
            prefix = 'Prefix_%d' % i
            name1 = "Ann_%s_1" % prefix
            name2 = "Ann_%s_2" % prefix
            cs1 = [(self.all_communities[0], True)]
            cs1 += [(c, False) for c in self.all_communities[1:]]
            cs2 = [(c, False) for c in self.all_communities]
            cs1 = dict(cs1)
            cs2 = dict(cs2)

            ann1 = Announcement(
                prefix=name1, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='N',
                local_pref=100, communities=cs1, permitted=True)
            self.anns[name1] = ann1

            ann2 = Announcement(
                prefix=name1, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='N',
                local_pref=100, communities=cs2, permitted=True)
            self.anns[name2] = ann2

        self._define_types()

        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [VALUENOTSET])
        matches = [MatchCommunitiesList(c1_l)]
        actions = [ActionSetLocalPref(200)]
        line = RouteMapLine(matches=matches,
                            actions=actions,
                            access=VALUENOTSET,
                            lineno=10)
        default_line = RouteMapLine(matches=None,
                                    actions=None,
                                    access=Access.permit,
                                    lineno=20)
        route_map = RouteMap(name='rm1', lines=[line, default_line])
        smap = SMTRouteMap(name=route_map.name, route_map=route_map, context=ctx)

        s1 = self.get_solver()
        s1.add(smap.constraints)
        ctx2 = smap.get_new_context()
        for name, ann in self.ann_map.iteritems():
            s1.add(ctx2.permitted_ctx.fun(ann) == True)
            if name.endswith('_1'):
                s1.add(ctx2.local_pref_ctx.get_var(ann) == 200)

        ctx2.add_constraints(s1)
        smap.add_constraints(s1)
        self.assertEquals(s1.check(), z3.sat)
        model = s1.model()
        ctx2.set_model(model)
        smap.set_model(model)
        for name, ann in self.ann_map.iteritems():
            if name.endswith('_1'):
                self.assertEquals(ctx2.local_pref_ctx.get_value(ann), 200)
            else:
                self.assertEquals(ctx2.local_pref_ctx.get_value(ann), 100)

        new_line = RouteMapLine(
            matches=[MatchCommunitiesList(CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(200)],
            access=Access.permit,
            lineno=10
        )
        new_route_map = RouteMap(name=route_map.name, lines=[new_line, default_line])
        self.assertEquals(smap.get_config(), new_route_map)

    def test_double_stress(self):
        """Test Two route maps back to back"""
        num_communities = 2
        num_anns = 2
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns / 2):
            prefix = 'Prefix_%d' % i
            name1 = "Ann_%s_1" % prefix
            name2 = "Ann_%s_2" % prefix
            cs1 = [(self.all_communities[0], True)]
            cs1 += [(c, False) for c in self.all_communities[1:]]
            cs2 = [(c, False) for c in self.all_communities]
            cs1 = dict(cs1)
            cs2 = dict(cs2)

            ann1 = Announcement(
                prefix=name1, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='M', local_pref=100,
                communities=cs1, permitted=True)
            self.anns[name1] = ann1

            ann2 = Announcement(
                prefix=name1, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop='N', local_pref=100,
                communities=cs2, permitted=True)
            self.anns[name2] = ann2

        self._define_types()

        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [VALUENOTSET])
        matches1 = [MatchCommunitiesList(c1_l)]
        actions1 = [ActionSetLocalPref(VALUENOTSET)]
        matches2 = [MatchNextHop('M')]
        actions2 = [ActionSetLocalPref(VALUENOTSET)]
        line1 = RouteMapLine(matches=matches1,
                             actions=actions1,
                             access=VALUENOTSET,
                             lineno=10)
        line2 = RouteMapLine(matches=matches2,
                             actions=actions2,
                             access=VALUENOTSET,
                             lineno=10)
        default_line = RouteMapLine(matches=None,
                                    actions=None,
                                    access=Access.permit,
                                    lineno=20)

        route_map1 = RouteMap(name='rm1', lines=[line1, default_line])
        route_map2 = RouteMap(name='rm2', lines=[line2, default_line])
        smap1 = SMTRouteMap(name=route_map1.name,
                            route_map=route_map1,
                            context=ctx)
        ctx1 = smap1.get_new_context()

        smap2 = SMTRouteMap(name=route_map2.name,
                            route_map=route_map2,
                            context=ctx1)
        ctx2 = smap2.get_new_context()

        s1 = self.get_solver()

        for name, ann in self.ann_map.iteritems():
            s1.add(ctx1.permitted_ctx.fun(ann) == True)
            s1.add(ctx2.permitted_ctx.fun(ann) == True)
            if name.endswith('_1'):
                s1.add(ctx1.local_pref_ctx.get_var(ann) == 200)
                s1.add(ctx2.local_pref_ctx.get_var(ann) == 50)

        ctx1.add_constraints(s1)
        ctx2.add_constraints(s1)
        smap1.add_constraints(s1)
        smap2.add_constraints(s1)
        import time
        start = time.time()
        self.assertEquals(s1.check(), z3.sat)
        end = time.time()
        print "Syn", (end- start)
        model = s1.model()
        smap1.set_model(model)
        smap2.set_model(model)
        ctx1.set_model(model)
        ctx2.set_model(model)
        for name, ann in self.ann_map.iteritems():
            if name.endswith('_1'):
                self.assertEquals(ctx1.local_pref_ctx.get_value(ann), 200)
                self.assertEquals(ctx2.local_pref_ctx.get_value(ann), 50)
            else:
                self.assertEquals(ctx1.local_pref_ctx.get_value(ann), 100)
                self.assertEquals(ctx2.local_pref_ctx.get_value(ann), 100)

        new_line1 = RouteMapLine(
            matches=[MatchCommunitiesList(CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(200)],
            access=Access.permit,
            lineno=10
        )
        new_route_map1 = RouteMap(name=route_map1.name, lines=[new_line1, default_line])
        new_line2 = RouteMapLine(
            matches=[MatchNextHop('M')],
            actions=[ActionSetLocalPref(50)],
            access=Access.permit,
            lineno=10
        )
        new_route_map2 = RouteMap(name=route_map2.name, lines=[new_line2, default_line])
        self.assertEquals(smap1.get_config(), new_route_map1)
        self.assertEquals(smap2.get_config(), new_route_map2)
