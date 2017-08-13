
import unittest
import networkx as nx
import z3

from synet.synthesis.ebgp import Announcement
from synet.synthesis.ebgp import BGP_ATTRS_ORIGIN
from synet.synthesis.ebgp import EBGP

from synet.topo.bgp import Access
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


from synet.utils.policy import SMTActions
from synet.utils.policy import SMTCommunity
from synet.utils.policy import SMTCommunityList
from synet.utils.policy import SMTIpPrefix
from synet.utils.policy import SMTIpPrefixList
from synet.utils.policy import SMTContext
from synet.utils.policy import SMTMatch
from synet.utils.policy import SMTMatches
from synet.utils.policy import OrOp
from synet.utils.policy import SMTSetLocalPref
from synet.utils.policy import SMTSetCommunity
from synet.utils.policy import SMTRouteMap
from synet.utils.policy import SMTRouteMapLine


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

    def _define_types(self):
        # Ann Type
        (self.ann_sort, self.announcements) = \
            z3.EnumSort('AnnouncementSort', self.anns.keys())

        ann_map = dict([(str(ann), ann) for ann in self.announcements])
        self.ann_map = ann_map

        anns_list = list(set([ann.PREFIX for ann in self.anns.values()]))
        (self.prefix_sort, self.prefixes) = z3.EnumSort('PrefixSort', anns_list)

        prefix_map = dict([(str(prefix), prefix) for prefix in self.prefixes])
        self.prefix_map = prefix_map
        self.prefix_fun = z3.Function('PrefixFunc', self.ann_sort, self.prefix_sort)
        self.local_pref_fun = z3.Function('LocalPref', self.ann_sort, z3.IntSort())

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

    def _load_communities_smt(self, solver):
        vars = []
        for name in sorted(self.anns.keys()):
            var = self.ann_map[name]
            ann = self.anns[name]
            # Assign communities
            for community, val in ann.COMMUNITIES.iteritems():
                c_name = str(community)
                c_fun = self.communities_fun[community]
                if val == 'T':
                    vars.append(c_fun(var) == True)
                elif val == 'F':
                    vars.append(c_fun(var) == False)
                else:
                    print "SKIPPED", var, community
        solver.append(vars)

    def _load_prefixes_smt(self, solver):
        for name, ann in self.anns.iteritems():
            ann = self.anns[name]
            ann_var = self.ann_map[name]
            prefix = ann.PREFIX
            if prefix != VALUENOTSET:
                prefix_var = self.prefix_map[prefix]
                solver.add(self.prefix_fun(ann_var) == prefix_var)

    def _load_local_prefs(self, solver):
        for name, ann in self.anns.iteritems():
            ann_var = self.ann_map[name]
            localpref = ann.LOCAL_PREF
            if localpref != VALUENOTSET:
                solver.add(self.local_pref_fun(ann_var) == localpref)

    def _load_route_denied(self, solver):
        tmp = z3.Const('deny_tmp', self.ann_sort)
        solver.add(
            z3.ForAll(
                [tmp],
                self.route_denied_fun(tmp) == False))

    def get_context(self):
        ctx = SMTContext(
            announcements=self.anns,
            announcements_map=self.ann_map,
            announcement_sort=self.ann_sort,
            communities_fun=self.communities_fun,
            prefixes_vars=self.prefix_map,
            prefix_sort=self.prefix_sort,
            prefix_fun=self.prefix_fun,
            local_pref_fun=self.local_pref_fun,
            route_denied_fun=self.route_denied_fun
        )
        return ctx


class SMTContextTest(SMTSetup):
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
            PREFIX=VALUENOTSET, PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=VALUENOTSET,
            COMMUNITIES={c1: VALUENOTSET, c2: 'F', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_NotSet': ann2,
        }

    def get_solver(self):
        solver = z3.Solver()
        self._load_communities_smt(solver)
        self._load_prefixes_smt(solver)
        self._load_local_prefs(solver)
        self._load_route_denied(solver)
        return solver

    def test_context(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]
        name1 = 'Ann1_Google'
        name2 = 'Ann2_NotSet'
        ann1_var = self.ann_map[name1]
        ann2_var = self.ann_map[name2]
        s = self.get_solver()

        s.add(ctx.has_community(ann1_var, c1) == True)
        s.add(ctx.has_community(ann2_var, c1) == True)
        s.add(ctx.get_prefix_var(ann2_var) == self.prefix_map['Google'])

        ret = s.check()

        self.assertEquals(ret, z3.sat)
        self.assertEquals(ctx.get_ann_by_name(name1), ann1_var)
        self.assertEquals(ctx.get_ann_by_name(name2), ann2_var)
        self.assertTrue(ctx.has_community(ann1_var, c1))
        self.assertFalse(ctx.has_community(ann1_var, c2))
        self.assertTrue(ctx.has_community(ann1_var, c3))
        self.assertFalse(ctx.has_community(ann2_var, c2))
        self.assertTrue(ctx.has_community(ann2_var, c3))
        self.assertEquals(ctx.get_prefix_var(ann1_var), self.prefix_map['Google'])


class SMTCommunityTest(SMTSetup):
    def get_solver(self):
        solver = z3.Solver()
        self._load_communities_smt(solver)
        return solver

    def test_community_match_concerte(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        c1_match = SMTCommunity(name='rm1', community=c1, context=ctx)
        c2_match = SMTCommunity(name='rm2', community=c2, context=ctx)
        c3_match = SMTCommunity(name='rm3', community=c3, context=ctx)


        s1 = self.get_solver()
        s2 = self.get_solver()
        s3 = self.get_solver()
        s4 = self.get_solver()
        s1.add(c1_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s1.add(c1_match.constraints)
        s2.add(c2_match.match_fun(self.ann_map['Ann1_Google']) == False)
        s2.add(c2_match.constraints)
        s3.add(c3_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s3.add(c3_match.constraints)

        self.assertEquals(s1.check(), z3.sat)
        self.assertEquals(s2.check(), z3.sat)
        self.assertEquals(s3.check(), z3.sat)
        self.assertEquals(s4.check(), z3.sat)
        m1 = s1.model()
        m2 = s2.model()
        m3 = s3.model()

        c1_val = c1_match.get_val(m1)
        c2_val = c2_match.get_val(m2)
        c3_val = c3_match.get_val(m3)

        self.assertEquals(c1_val, c1)
        self.assertEquals(c2_val, c2)
        self.assertEquals(c3_val, c3)
        self.assertEquals(c1_match.get_config(m1), c1)
        self.assertEquals(c2_match.get_config(m2), c2)
        self.assertEquals(c3_match.get_config(m3), c3)

    def test_community_match_notconcrete(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        w1_match = SMTCommunity(community=VALUENOTSET, name='rm4', context=ctx)

        s4 = self.get_solver()
        s4.add(w1_match.match_fun(self.ann_map['Ann1_Google']) == True)
        s4.add(w1_match.constraints)
        self.assertEquals(s4.check(), z3.sat)
        m4 = s4.model()
        wild1_val = w1_match.get_val(m4)
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

        c1_list = CommunityList(1, Access.permit, [c1, c3])
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

    def test_stress_partial_comp(self):
        num_communities = 100
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            if i == 0:
                cs = [(self.all_communities[0], 'T')]
                cs += [(c, 'F') for c in self.all_communities[1:]]
            else:
                cs = [(c, 'F') for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                PREFIX=name, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs)
            self.anns[name] = ann

        self._define_types()
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [c1])
        l1_m = SMTCommunityList(name='rm1', community_list= c1_l, context=ctx)

        def get_solver():
            solver = z3.Solver()
            #self._load_communities_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_m.match_fun(self.ann_map['Prefix_0'])
        s1.add(match1 == True)
        s1.add(l1_m.constraints)
        self.assertTrue(l1_m.is_concrete())
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(l1_m.get_val(m), [c1])

    def test_stress_no_partial_eval(self):
        num_communities = 100
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            if i == 0:
                cs = [(self.all_communities[0], 'T')]
                cs += [(c, 'F') for c in self.all_communities[1:]]
            else:
                cs = [(c, 'F') for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                PREFIX=name, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs)
            self.anns[name] = ann

        self._define_types()
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [VALUENOTSET])
        l1_m = SMTCommunityList(name='rm1', community_list= c1_l, context=ctx)

        def get_solver():
            import time
            start = time.time()
            solver = z3.Solver()
            self._load_communities_smt(solver)
            end = time.time()
            print "Loading communties too", (end - start)
            return solver

        s1 = get_solver()
        match1 = l1_m.match_fun(self.ann_map['Prefix_0'])
        s1.add(match1 == True)
        s1.add(l1_m.constraints)
        self.assertFalse(l1_m.is_concrete())
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(l1_m.get_val(m), [c1])


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

    def test_prefix_match_concrete(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        p1_match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)
        p2_match = SMTIpPrefix(name='p2', prefix='Yahoo', context=ctx)

        def get_solver():
            s = z3.Solver()
            self._load_prefixes_smt(s)
            return s

        s1 = get_solver()

        s1.add(p1_match.match_fun(ann1) == True)
        s1.add(p2_match.match_fun(ann1) == False)
        s1.add(p1_match.match_fun(ann2) == False)
        s1.add(p2_match.match_fun(ann2) == True)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertEquals(p1_match.get_val(m), 'Google')
        self.assertEquals(p2_match.get_val(m), 'Yahoo')

    def test_prefix_match_notconcrete(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        p3_match = SMTIpPrefix(name='p3', prefix=VALUENOTSET, context=ctx)
        p4_match = SMTIpPrefix(name='p4', prefix=VALUENOTSET, context=ctx)

        def get_solver():
            s = z3.Solver()
            self._load_prefixes_smt(s)
            return s

        s1 = get_solver()
        s1.add(p3_match.match_fun(ann1) == True)
        s1.add(p3_match.match_fun(ann2) == False)
        s1.add(p3_match.constraints)
        s1.add(p4_match.match_fun(ann1) == False)
        s1.add(p4_match.match_fun(ann2) == True)
        s1.add(p4_match.constraints)
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
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
        p1_list = IpPrefixList(1, access=Access.permit, networks=['Google'])
        p2_list = IpPrefixList(2, access=Access.permit, networks=['Yahoo'])
        p3_list = IpPrefixList(1, access=Access.permit, networks=[VALUENOTSET])
        p4_list = IpPrefixList(2, access=Access.permit, networks=[VALUENOTSET])

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

    def test_empty_matches(self):
        ctx = self.get_context()
        c1 = self.all_communities[0]
        c3 = self.all_communities[2]

        l1_match = SMTMatches(name='m1', matches=[], context=ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_prefixes_smt(solver)
            return solver

        s1 = get_solver()
        match1 = l1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = l1_match.match_fun(self.ann_map['Ann2_Yahoo'])
        self.assertEquals(s1.check(), z3.sat)
        m = s1.model()
        self.assertTrue(z3.is_true(m.eval(match1)))
        self.assertTrue(z3.is_true(m.eval(match2)))


class SMTSetLocalPrefTest(SMTSetup):
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

    def test_set(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)

        set1 = SMTSetLocalPref(name='s1', localpref=200,
                               match=match, context=ctx)
        set2 = SMTSetLocalPref(name='s2', localpref=VALUENOTSET,
                               match=match, context=ctx)

        def get_solver():
            s = z3.Solver()
            self._load_prefixes_smt(s)
            self._load_local_prefs(s)
            return s

        s1 = get_solver()
        s2 = get_solver()

        s1.add(set1.action_fun(ann1) == 200)
        self.assertFalse(set1.is_concrete())
        s1.add(set1.constraints)

        self.assertEquals(s1.check(), z3.sat)
        ctx1 = set1.get_new_context()
        model1 = s1.model()
        self.assertEquals(set1.get_val(model1), 200)
        self.assertEquals(model1.eval(set1.action_fun(ann1)).as_long(), 200)
        self.assertEquals(model1.eval(set1.action_fun(ann2)).as_long(), 100)
        self.assertEquals(model1.eval(ctx1.local_pref_fun(ann1)).as_long(), 200)
        self.assertEquals(model1.eval(ctx1.local_pref_fun(ann2)).as_long(), 100)
        self.assertEquals(set1.get_config(model1), ActionSetLocalPref(200))

        s2.add(set2.action_val == 200)
        s2.add(set2.constraints)
        self.assertEquals(s2.check(), z3.sat)
        ctx2 = set2.get_new_context()
        model2 =s2.model()
        self.assertFalse(set2.is_concrete())
        self.assertEquals(set2.get_val(model2), 200)
        self.assertEquals(model2.eval(set2.action_fun(ann1)).as_long(), 200)
        self.assertEquals(model2.eval(set2.action_fun(ann2)).as_long(), 100)
        self.assertEquals(model2.eval(ctx2.local_pref_fun(ann1)).as_long(), 200)
        self.assertEquals(model2.eval(ctx2.local_pref_fun(ann2)).as_long(), 100)
        self.assertEquals(set2.get_config(model2), ActionSetLocalPref(200))


class SMTSetCommunityTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'T', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def get_solver(self):
        s = z3.Solver()
        self._load_prefixes_smt(s)
        self._load_communities_smt(s)
        return s

    def test_set_concrete_additive(self):
        ctx = self.get_context()
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]

        match = SMTIpPrefix(name='p1', prefix='Google', context=ctx)

        set1 = SMTSetCommunity(name='s1', communities=[c1, c2],
                               additive=True, match=match, context=ctx)

        # Concrete, Additive = True
        s = self.get_solver()
        s.add(set1.constraints)
        s.add(match.constraints)

        self.assertEquals(s.check(), z3.sat)
        self.assertFalse(set1.is_concrete())
        ctx = set1.get_new_context()
        model = s.model()
        self.assertEquals(set1.get_val(model), [c1, c2])
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c3](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c1](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c3](ann2))))
        self.assertEquals(set1.get_config(model), ActionSetCommunity([c1, c2]))

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
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c3](ann2))))
        self.assertEquals(set1.get_config(model), ActionSetCommunity([c1, c2]))

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
        print s.to_smt2()
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
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'T', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def get_solver(self):
        s = z3.Solver()
        self._load_prefixes_smt(s)
        self._load_communities_smt(s)
        return s

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
        s.add(actions.constraints)
        s.add(match.constraints)
        ctx = actions.get_new_context()
        s.add(ctx.local_pref_fun(ann1) == 200)

        self.assertEquals(s.check(), z3.sat)
        self.assertFalse(actions.is_concrete())

        model = s.model()
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c1](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c3](ann2))))
        self.assertEquals(actions.get_config(model), [set_c, set_pref])


class SMTRouteMapLineTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'T', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def get_solver(self):
        s = z3.Solver()
        self._load_prefixes_smt(s)
        self._load_communities_smt(s)
        self._load_route_denied(s)
        return s

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

        s = self.get_solver()
        s.add(l.match_constraints)
        s.add(l.action_constraints)
        s.add(l.matches.match_fun(ann1) == True)

        self.assertEquals(s.check(), z3.sat)
        ctx = l.get_new_context()
        model = s.model()
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c1](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c3](ann2))))
        self.assertEquals(l.get_val(model), (Access.permit, [['Google']], [[c1, c2], 200]))
        self.assertEquals(l.get_config(model), line)

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

        s = self.get_solver()
        s.add(l.match_constraints)
        s.add(l.action_constraints)
        s.add(l.matches.match_fun(ann1) == True)

        self.assertEquals(s.check(), z3.sat)
        ctx = l.get_new_context()
        model = s.model()
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann1))))

        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann2))))

        self.assertEquals(l.get_val(model), (Access.permit, [True], [[c1, c2], 200]))
        self.assertEquals(l.get_config(model), line)

    def test_stress(self):
        num_communities = 2
        num_anns = 2
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns / 2):
            prefix = 'Prefix_%d' % i
            name1= "Ann_%s_1" % prefix
            name2= "Ann_%s_2" % prefix
            cs1 = [(self.all_communities[0], 'T')]
            cs1 += [(c, 'F') for c in self.all_communities[1:]]
            cs2 = [(c, 'F') for c in self.all_communities]
            cs1 = dict(cs1)
            cs2 = dict(cs2)

            ann1 = Announcement(
                PREFIX=name1, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs1)
            self.anns[name1] = ann1

            ann2 = Announcement(
                PREFIX=name1, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs2)
            self.anns[name2] = ann2

        self._define_types()

        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [VALUENOTSET])
        matches = [MatchCommunitiesList(c1_l)]
        actions = [ActionSetLocalPref(VALUENOTSET)]
        line = RouteMapLine(matches=matches, actions=actions, access=VALUENOTSET, lineno=10)

        rline = SMTRouteMapLine(name='l', line=line, context=ctx)
        def get_solver():
            solver = z3.Solver()
            self._load_communities_smt(solver)
            self._load_prefixes_smt(solver)
            self._load_local_prefs(solver)
            return solver

        s1 = get_solver()
        s1.add(rline.match_constraints)
        s1.add(rline.action_constraints)
        ctx = rline.get_new_context()
        for name, ann in self.ann_map.iteritems():
            s1.add(rline.route_denied_fun(ann) == False)
            if name.endswith('_1'):
                s1.add(ctx.local_pref_fun(ann) == 200)

        self.assertEquals(s1.check(), z3.sat)
        model = s1.model()
        for name, ann in self.ann_map.iteritems():
            if name.endswith('_1'):
                self.assertEquals(model.eval(ctx.local_pref_fun(ann)).as_long(), 200)
            else:
                self.assertEquals(model.eval(ctx.local_pref_fun(ann)).as_long(), 100)


        new_line = RouteMapLine(
            matches=[MatchCommunitiesList(CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(200)],
            access=Access.permit,
            lineno=10
        )
        self.assertEquals(rline.get_config(model), new_line)


class SMTRouteMapTest(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'F', c3: 'T'})

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES={c1: 'F', c2: 'T', c3: 'T'})

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def get_solver(self):
        s = z3.Solver()
        self._load_prefixes_smt(s)
        self._load_communities_smt(s)
        self._load_route_denied(s)
        self._load_local_prefs(s)
        return s

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

        set_c = ActionSetCommunity(communities=[c1, c2], additive=False)
        set_pref200 = ActionSetLocalPref(200)
        set_pref400 = ActionSetLocalPref(VALUENOTSET)
        l1 = RouteMapLine(matches=[match_google], actions=[set_c, set_pref200],
                            access=Access.permit, lineno=10)
        l2 = RouteMapLine(matches=[match_yahoo], actions=[set_c, set_pref400],
                          access=Access.permit, lineno=10)

        route_map = RouteMap(name='rm1', lines=[l1, l2])
        r = SMTRouteMap(name='l', route_map=route_map, context=ctx)

        s = self.get_solver()
        s.add(r.constraints)
        ctx = r.get_new_context()
        s.add(ctx.local_pref_fun(ann2) == 400)

        self.assertEquals(s.check(), z3.sat)

        model = s.model()


        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann1))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann1))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann1))))

        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c1](ann2))))
        self.assertTrue(z3.is_true(model.eval(ctx.communities_fun[c2](ann2))))
        self.assertTrue(z3.is_false(model.eval(ctx.communities_fun[c3](ann2))))

        self.assertEquals(model.eval(ctx.local_pref_fun(ann1)), 200)
        self.assertEquals(model.eval(ctx.local_pref_fun(ann2)), 400)
        self.assertEquals(r.get_val(model),
                          [(Access.permit, [['Google']], [[c1, c2], 200]),
                           (Access.permit, [['Yahoo']], [[c1, c2], 400])
                           ])
        l1 = RouteMapLine(matches=[match_google], actions=[set_c, set_pref200],
                          access=Access.permit, lineno=10)
        l2 = RouteMapLine(matches=[match_yahoo], actions=[set_c, ActionSetLocalPref(400)],
                          access=Access.permit, lineno=10)

        route_map = RouteMap(name='rm1', lines=[l1, l2])
        self.assertEquals(r.get_config(model), route_map)


    def test_stress(self):
        num_communities = 10
        num_anns = 1000
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns / 2):
            prefix = 'Prefix_%d' % i
            name1= "Ann_%s_1" % prefix
            name2= "Ann_%s_2" % prefix
            cs1 = [(self.all_communities[0], 'T')]
            cs1 += [(c, 'F') for c in self.all_communities[1:]]
            cs2 = [(c, 'F') for c in self.all_communities]
            cs1 = dict(cs1)
            cs2 = dict(cs2)

            ann1 = Announcement(
                PREFIX=name1, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs1)
            self.anns[name1] = ann1

            ann2 = Announcement(
                PREFIX=name1, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs2)
            self.anns[name2] = ann2

        self._define_types()

        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [VALUENOTSET])
        matches = [MatchCommunitiesList(c1_l)]
        actions = [ActionSetLocalPref(VALUENOTSET)]
        line = RouteMapLine(matches=matches, actions=actions, access=VALUENOTSET, lineno=10)

        route_map = RouteMap(name='rm1', lines=[line])
        smap = SMTRouteMap(name=route_map.name, route_map=route_map, context=ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_communities_smt(solver)
            self._load_prefixes_smt(solver)
            self._load_local_prefs(solver)
            return solver

        s1 = get_solver()
        s1.add(smap.constraints)
        ctx = smap.get_new_context()
        for name, ann in self.ann_map.iteritems():
            s1.add(smap.boxes[0].route_denied_fun(ann) == False)
            if name.endswith('_1'):
                s1.add(ctx.local_pref_fun(ann) == 200)

        self.assertEquals(s1.check(), z3.sat)
        model = s1.model()
        for name, ann in self.ann_map.iteritems():
            if name.endswith('_1'):
                self.assertEquals(model.eval(ctx.local_pref_fun(ann)).as_long(), 200)
            else:
                self.assertEquals(model.eval(ctx.local_pref_fun(ann)).as_long(), 100)


        new_line = RouteMapLine(
            matches=[MatchCommunitiesList(CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(200)],
            access=Access.permit,
            lineno=10
        )
        new_route_map = RouteMap(name=route_map.name, lines=[new_line])
        self.assertEquals(smap.get_config(model), new_route_map)

    def test_double_stress(self):
        """Test Two route maps back to back"""
        num_communities = 10
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns / 2):
            prefix = 'Prefix_%d' % i
            name1= "Ann_%s_1" % prefix
            name2= "Ann_%s_2" % prefix
            cs1 = [(self.all_communities[0], 'T')]
            cs1 += [(c, 'F') for c in self.all_communities[1:]]
            cs2 = [(c, 'F') for c in self.all_communities]
            cs1 = dict(cs1)
            cs2 = dict(cs2)

            ann1 = Announcement(
                PREFIX=name1, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs1)
            self.anns[name1] = ann1

            ann2 = Announcement(
                PREFIX=name1, PEER='N', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                AS_PATH=[1, 2, 5], NEXT_HOP='N', LOCAL_PREF=100,
                COMMUNITIES=cs2)
            self.anns[name2] = ann2

        self._define_types()

        ctx = self.get_context()
        c1 = self.all_communities[0]
        c1_l = CommunityList(1, Access.permit, [VALUENOTSET])
        matches1 = [MatchCommunitiesList(c1_l)]
        actions1 = [ActionSetLocalPref(VALUENOTSET)]
        matches2 = [MatchCommunitiesList(c1_l)]
        actions2 = [ActionSetLocalPref(VALUENOTSET)]
        line1 = RouteMapLine(matches=matches1, actions=actions1, access=VALUENOTSET, lineno=10)
        line2 = RouteMapLine(matches=matches2, actions=actions2, access=VALUENOTSET, lineno=10)

        route_map1 = RouteMap(name='rm1', lines=[line1])
        route_map2 = RouteMap(name='rm2', lines=[line2])
        smap1 = SMTRouteMap(name=route_map1.name, route_map=route_map1, context=ctx)
        smap2 = SMTRouteMap(name=route_map2.name, route_map=route_map2, context=smap1.ctx)

        def get_solver():
            solver = z3.Solver()
            self._load_communities_smt(solver)
            self._load_prefixes_smt(solver)
            self._load_local_prefs(solver)
            return solver

        s1 = get_solver()
        s1.add(smap1.constraints)
        s1.add(smap2.constraints)
        ctx1 = smap1.get_new_context()
        ctx2 = smap2.get_new_context()
        for name, ann in self.ann_map.iteritems():
            s1.add(smap1.boxes[0].route_denied_fun(ann) == False)
            s1.add(smap2.boxes[0].route_denied_fun(ann) == False)
            if name.endswith('_1'):
                s1.add(ctx1.local_pref_fun(ann) == 200)
                s1.add(ctx2.local_pref_fun(ann) == 50)

        self.assertEquals(s1.check(), z3.sat)
        model = s1.model()
        for name, ann in self.ann_map.iteritems():
            if name.endswith('_1'):
                self.assertEquals(model.eval(ctx1.local_pref_fun(ann)).as_long(), 200)
                self.assertEquals(model.eval(ctx2.local_pref_fun(ann)).as_long(), 50)
            else:
                self.assertEquals(model.eval(ctx1.local_pref_fun(ann)).as_long(), 100)
                self.assertEquals(model.eval(ctx2.local_pref_fun(ann)).as_long(), 100)


        new_line1 = RouteMapLine(
            matches=[MatchCommunitiesList(CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(200)],
            access=Access.permit,
            lineno=10
        )
        new_route_map1 = RouteMap(name=route_map1.name, lines=[new_line1])
        new_line2 = RouteMapLine(
            matches=[MatchCommunitiesList(CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(50)],
            access=Access.permit,
            lineno=10
        )
        new_route_map2 = RouteMap(name=route_map2.name, lines=[new_line2])
        self.assertEquals(smap1.get_config(model), new_route_map1)
        self.assertEquals(smap2.get_config(model), new_route_map2)
