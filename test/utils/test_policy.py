
import unittest
import networkx as nx
import z3

from synet.synthesis.ebgp import Announcement
from synet.synthesis.ebgp import BGP_ATTRS_ORIGIN
from synet.synthesis.ebgp import EBGP

from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import CommunityList
from synet.topo.bgp import ActionSetCommunity
from synet.topo.bgp import MatchCommunitiesList
from synet.topo.bgp import MatchPeer
from synet.topo.bgp import MatchIpPrefixListList
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine
from synet.topo.bgp import VALUENOTSET
from synet.topo.bgp import Access
from synet.topo.bgp import Community
from synet.topo.bgp import MatchLocalPref
from synet.topo.bgp import IpPrefixList


from synet.utils.policy import SMTCommunity
from synet.utils.policy import SMTCommunityList
from synet.utils.policy import SMTIpPrefix
from synet.utils.policy import SMTIpPrefixList
from synet.utils.policy import SMTContext
from synet.utils.policy import SMTMatch
from synet.utils.policy import SMTMatches
from synet.utils.policy import OrOp


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class SMTSetup(unittest.TestCase):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
        }

    def setUp(self):
        self._pre_load()
        # Ann Type
        (self.ann_sort, self.announcements) = \
            z3.EnumSort('AnnouncementSort',self.anns.keys())

        ann_map = dict([(str(ann), ann) for ann in self.announcements])
        self.ann_map = ann_map

        anns_list = list(set([ann.PREFIX for ann in self.anns.values()]))
        (self.prefix_sort, self.prefixes) = z3.EnumSort('PrefixSort', anns_list)

        prefix_map = dict([(str(prefix), prefix) for prefix in self.prefixes])
        self.prefix_map = prefix_map
        self.prefix_func = z3.Function('PrefixFunc', self.ann_sort, self.prefix_sort)

        # Create functions for communities
        self.communities_func = {}
        self.reverse_communities = {}
        for c in self.all_communities:
            name = 'Has_%s' % c
            self.communities_func[c] = z3.Function(name, self.ann_sort, z3.BoolSort())
            self.reverse_communities[name] = c

    def _load_communities_smt(self, solver):
        for name in sorted(self.anns.keys()):
            var = self.ann_map[name]
            ann = self.anns[name]
            # Assign communities
            for community, val in ann.COMMUNITIES.iteritems():
                c_name = str(community)
                c_fun = self.communities_func[community]
                assert_name = 'init_comm_%s_%s' % (str(var), c_name)
                if val == 'T':
                    solver.assert_and_track(c_fun(var) == True, assert_name)
                elif val == 'F':
                    solver.assert_and_track(c_fun(var) == False, assert_name)

    def _load_prefixes_smt(self, solver):
        for name, ann in self.anns.iteritems():
            ann = self.anns[name]
            ann_var = self.ann_map[name]
            prefix = ann.PREFIX
            prefix_var = self.prefix_map[prefix]
            solver.add(self.prefix_func(ann_var) == prefix_var)

    def get_context(self):
        ctx = SMTContext(
            announcements=self.anns,
            announcements_vars=self.announcements,
            announcement_sort=self.ann_sort,
            communities_fun=self.communities_func,
            prefixes_vars=self.prefix_map,
            prefix_sort=self.prefix_sort,
            prefix_fun=self.prefix_func
        )
        return ctx


class SMTCommunityTest(SMTSetup):
    def get_solver(self):
        solver = z3.Solver()
        self._load_communities_smt(solver)
        return solver

    def test_community_match(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        c1_match = SMTCommunity(name='rm1', community=c1, context=ctx)
        c2_match = SMTCommunity(name='rm2', community=c2, context=ctx)
        c3_match = SMTCommunity(name='rm3', community=c3, context=ctx)
        wild1_match = SMTCommunity(community=VALUENOTSET, name='rm4', context=ctx)

        s1 = self.get_solver()
        s2 = self.get_solver()
        s3 = self.get_solver()
        s4 = self.get_solver()
        s1.add(c1_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s1.add(wild1_match.constraints)
        s2.add(c2_match.match_fun(self.ann_map['Ann1_Google']) == False)
        s2.add(wild1_match.constraints)
        s3.add(c3_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s3.add(wild1_match.constraints)
        s4.add(wild1_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s4.add(wild1_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        self.assertEquals(s2.check(), z3.sat)
        self.assertEquals(s3.check(), z3.sat)
        self.assertEquals(s4.check(), z3.sat)
        m1 = s1.model()
        m2 = s2.model()
        m3 = s3.model()
        m4 = s4.model()
        c1_val = c1_match.get_val(m1)
        c2_val = c2_match.get_val(m2)
        c3_val = c3_match.get_val(m3)
        wild1_val = wild1_match.get_val(m4)
        self.assertEquals(c1_val, c1)
        self.assertEquals(c2_val, c2)
        self.assertEquals(c3_val, c3)
        self.assertEquals(c1_match.get_config(m1), c1)
        self.assertEquals(c2_match.get_config(m2), c2)
        self.assertEquals(c3_match.get_config(m3), c3)
        self.assertIn(wild1_val, [c1, c3])

    def test_communities_and_match(self):
        ctx = self.get_context()

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        c1_match = SMTCommunity(name='rm1', community=c1, context=ctx)
        c2_match = SMTCommunity(name='rm2', community=c2, context=ctx)
        c3_match = SMTCommunity(name='rm3', community=c3, context=ctx)
        wild1_match = SMTCommunity('rm4', community=VALUENOTSET, context=ctx)
        wild2_match = SMTCommunity('rm5', community=VALUENOTSET, context=ctx)

        s1 = self.get_solver()
        s2 = self.get_solver()
        match1 = c1_match.match_fun(self.ann_map['Ann1_Google'])
        match3 = c3_match.match_fun(self.ann_map['Ann1_Google'])
        s1.add(c1_match.constraints)
        s1.add(c2_match.constraints)
        s1.add(c3_match.constraints)
        s1.add(z3.And(match1 == True, match3 == True))
        self.assertEquals(s1.check(), z3.sat)

        match1 = wild1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = wild2_match.match_fun(self.ann_map['Ann1_Google'])
        s2.add(wild1_match.constraints)
        s2.add(wild2_match.constraints)
        s2.add(z3.And(match1 == True, match2 == True,))
        # To guarantee synthesizing two different values
        s2.add(wild2_match.match_synthesized != wild1_match.match_synthesized)
        self.assertEquals(s2.check(), z3.sat)
        m = s2.model()
        self.assertIn(wild1_match.get_val(m), [c1, c3])
        self.assertIn(wild2_match.get_val(m), [c1, c3])
        self.assertNotEqual(wild1_match.get_val(m), wild2_match.get_val(m))


class SMTCommunityListTest(SMTSetup):
    def test_communities_list(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        c1_list = CommunityList(1, Access.permit,
                                [self.all_communities[0],
                                 self.all_communities[2]])
        l1_match = SMTCommunityList(
            name='rm1', community_list= c1_list, context=ctx)
        c2_list = CommunityList(1, Access.permit,
                                [VALUENOTSET, VALUENOTSET])
        l2_match = SMTCommunityList(
            name='rm2', community_list=c2_list, context=ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_communities_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        s1.add(match1 == True)
        s1.add(l1_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(l1_match.get_val(m), [c1, c3])

        self.assertEquals(l1_match.get_config(m), c1_list)

        s2 = get_solver()
        match2 = l2_match.match_fun(self.ann_map['Ann1_Google'])
        s2.add(match2 == True)
        s2.add(l2_match.constraints)
        self.assertEquals(s2.check(), z3.sat)
        m = s2.model()
        self.assertEquals(set(l2_match.get_val(m)), set([c1, c3]))
        self.assertEquals(l2_match.get_config(m), c1_list)


class SMTPrefixTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_prefix_match(self):
        ctx = self.get_context()

        p1_match = SMTIpPrefix(
            name='p1',
            prefix='Google', context=ctx)

        p2_match = SMTIpPrefix(
            name='p2',
            prefix='Yahoo', context=ctx)

        p3_match = SMTIpPrefix(
            name='p3',
            prefix=VALUENOTSET, context=ctx)

        p4_match = SMTIpPrefix(
            name='p4',
            prefix=VALUENOTSET, context=ctx)

        def get_solver():
            s = z3.Solver()
            self._load_prefixes_smt(s)
            return s

        s1 = get_solver()
        s1.add(p1_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s1.add(p2_match.match_fun(self.ann_map['Ann1_Google']) == False)
        s1.add(p1_match.match_fun(self.ann_map['Ann2_Yahoo']) == False)
        s1.add(p2_match.match_fun(self.ann_map['Ann2_Yahoo']) == True)
        s1.add(p3_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s1.add(p3_match.match_fun(self.ann_map['Ann2_Yahoo']) == False)
        s1.add(p3_match.constraints)
        s1.add(p4_match.match_fun(self.ann_map['Ann1_Google']) == False)
        s1.add(p4_match.match_fun(self.ann_map['Ann2_Yahoo']) == True)
        s1.add(p4_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        print m
        self.assertEquals(p3_match.get_val(m), 'Google')
        self.assertEquals(p4_match.get_val(m), 'Yahoo')


class SMTIpPrefixListTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_ip_prefix_list(self):
        ctx = self.get_context()
        p1_list = IpPrefixList(1, access=Access.permit,
                               networks=['Google'])
        p2_list = IpPrefixList(2, access=Access.permit,
                               networks=['Yahoo'])
        p3_list = IpPrefixList(1, access=Access.permit,
                               networks=[VALUENOTSET])
        p4_list = IpPrefixList(2, access=Access.permit,
                               networks=[VALUENOTSET])

        l1_match = SMTIpPrefixList(name='pl1', prefix_list=p1_list, context=ctx)
        l2_match = SMTIpPrefixList(name='pl2', prefix_list=p2_list, context=ctx)
        l3_match = SMTIpPrefixList(name='pl3', prefix_list=p3_list, context=ctx)
        l4_match = SMTIpPrefixList(name='pl4', prefix_list=p4_list, context=ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_prefixes_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = l2_match.match_fun(self.ann_map['Ann2_Yahoo'])
        match3 = l3_match.match_fun(self.ann_map['Ann1_Google'])
        match4 = l4_match.match_fun(self.ann_map['Ann2_Yahoo'])
        s1.add(match1 == True)
        s1.add(match2 == True)
        s1.add(match3 == True)
        s1.add(match4 == True)
        s1.add(l1_match.constraints)
        s1.add(l2_match.constraints)
        s1.add(l3_match.constraints)
        s1.add(l4_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(l1_match.get_val(m), ['Google'])
        self.assertEquals(l2_match.get_val(m), ['Yahoo'])
        self.assertEquals(l3_match.get_val(m), ['Google'])
        self.assertEquals(l4_match.get_val(m), ['Yahoo'])
        self.assertEquals(l3_match.get_config(m), p1_list)
        self.assertEquals(l4_match.get_config(m), p2_list)


class SMTMatchTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_ip_prefix_list(self):
        ctx = self.get_context()
        p1_list = IpPrefixList(1, access=Access.permit,
                               networks=['Google'])
        p2_list = IpPrefixList(2, access=Access.permit,
                               networks=['Yahoo'])
        p3_list = IpPrefixList(1, access=Access.permit,
                               networks=[VALUENOTSET])
        p4_list = IpPrefixList(2, access=Access.permit,
                               networks=[VALUENOTSET])

        l1_m = MatchIpPrefixListList(prefix_list=p1_list)
        l2_m = MatchIpPrefixListList(prefix_list=p2_list)
        l3_m = MatchIpPrefixListList(prefix_list=p3_list)
        l4_m = MatchIpPrefixListList(prefix_list=p4_list)

        l1_match = SMTMatch(name='m1', match=l1_m, context=ctx)
        l2_match = SMTMatch(name='m2', match=l2_m, context=ctx)
        l3_match = SMTMatch(name='m3', match=l3_m, context=ctx)
        l4_match = SMTMatch(name='m4', match=l4_m, context=ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_prefixes_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = l2_match.match_fun(self.ann_map['Ann2_Yahoo'])
        match3 = l3_match.match_fun(self.ann_map['Ann1_Google'])
        match4 = l4_match.match_fun(self.ann_map['Ann2_Yahoo'])
        s1.add(match1 == True)
        s1.add(match2 == True)
        s1.add(match3 == True)
        s1.add(match4 == True)
        s1.add(l1_match.constraints)
        s1.add(l2_match.constraints)
        s1.add(l3_match.constraints)
        s1.add(l4_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(l1_match.get_val(m), ['Google'])
        self.assertEquals(l2_match.get_val(m), ['Yahoo'])
        self.assertEquals(l3_match.get_val(m), ['Google'])
        self.assertEquals(l4_match.get_val(m), ['Yahoo'])
        self.assertEquals(l1_match.get_config(m), l1_m)
        self.assertEquals(l2_match.get_config(m), l2_m)
        self.assertEquals(l3_match.get_config(m), l1_m)
        self.assertEquals(l4_match.get_config(m), l2_m)

    def test_communities_list(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        c1_l = CommunityList(1, Access.permit, [c1, c3])
        l1_m = MatchCommunitiesList(communities_list=c1_l)
        c2_l = CommunityList(1, Access.permit, [VALUENOTSET, VALUENOTSET])
        l2_m = MatchCommunitiesList(communities_list=c2_l)

        l1_match = SMTMatch(name='m1', match=l1_m, context=ctx)
        l2_match = SMTMatch(name='m2', match=l2_m, context=ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_communities_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        s1.add(match1 == True)
        s1.add(l1_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(l1_match.get_val(m), [c1, c3])

        self.assertEquals(l1_match.get_config(m), l1_m)

        s2 = get_solver()
        match2 = l2_match.match_fun(self.ann_map['Ann1_Google'])
        s2.add(match2 == True)
        s2.add(l2_match.constraints)
        self.assertEquals(s2.check(), z3.sat)
        m = s2.model()
        self.assertEquals(set(l2_match.get_val(m)), set([c1, c3]))
        self.assertEquals(l2_match.get_config(m), l1_m)

    def test_or(self):
        ctx = self.get_context()
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


        def get_solver():
            solver = z3.Solver()
            self._load_prefixes_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = l2_match.match_fun(self.ann_map['Ann2_Yahoo'])
        match3 = l3_match.match_fun(self.ann_map['Ann1_Google'])

        s1.add(match1 == True)
        s1.add(match2 == True)
        s1.add(match3 == True)
        s1.add(l1_match.constraints)
        s1.add(l2_match.constraints)
        s1.add(l3_match.constraints)

        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(len(l1_match.get_val(m)), 2)
        self.assertEquals(len(l2_match.get_val(m)), 2)
        self.assertEquals(len(l3_match.get_val(m)), 2)
        self.assertEquals(l1_match.get_val(m), [['Google'], ['Yahoo']])
        self.assertEquals(l2_match.get_val(m), [['Google'], ['Yahoo']])
        self.assertEquals(l1_match.get_config(m), [l1_m, l2_m])


class SMTMatchesTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'T', c2: 'F', c3: 'F'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_matches(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c3 = self.all_communities[2]

        c1_l = CommunityList(1, Access.permit, [c1, c3])
        l1_m = MatchCommunitiesList(communities_list=c1_l)

        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        l2_m = MatchIpPrefixListList(prefix_list=p1_list)

        l1_match = SMTMatches(name='m1', matches=[l1_m, l2_m], context=ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_prefixes_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        s1.add(match1 == True)
        s1.add(l1_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertIn(['Google'], l1_match.get_val(m))
        self.assertIn(c1_l.communities, l1_match.get_val(m))
        self.assertIn(l1_m, l1_match.get_config(m))
        self.assertIn(l2_m, l1_match.get_config(m))

