
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
from synet.topo.bgp import MatchIpPrefixListList
from synet.topo.bgp import IpPrefixList


from synet.utils.policy import SMTCommunity
from synet.utils.policy import SMTCommunityList


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
            ann = self.anns[name]#
            # Assign communities
            for community, val in ann.COMMUNITIES.iteritems():
                c_name = str(community)
                c_fun = self.communities_func[community]
                assert_name = 'init_comm_%s_%s' % (str(var), c_name)
                if val == 'T':
                    solver.assert_and_track(c_fun(var) == True, assert_name)
                elif val == 'F':
                    solver.assert_and_track(c_fun(var) == False, assert_name)


class SMTCommunityTest(SMTSetup):
    def test_community_match(self):
        c1_match = SMTCommunity(
            community=self.all_communities[0],
            name='rm1',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        c2_match = SMTCommunity(
            community=self.all_communities[1],
            name='rm2',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        c3_match = SMTCommunity(
            community=self.all_communities[2],
            name='rm3',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        wild1_match = SMTCommunity(
            community=VALUENOTSET,
            name='rm4',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        def get_solver():
            solver = z3.Solver()
            self._load_communities_smt(solver)
            return solver

        s1 = get_solver()
        s2 = get_solver()
        s3 = get_solver()
        s4 = get_solver()
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
        self.assertEquals(c1_val, self.all_communities[0])
        self.assertEquals(c2_val, self.all_communities[1])
        self.assertEquals(c3_val, self.all_communities[2])
        self.assertEquals(c1_match.get_config(m1), self.all_communities[0])
        self.assertEquals(c2_match.get_config(m2), self.all_communities[1])
        self.assertEquals(c3_match.get_config(m3), self.all_communities[2])
        self.assertIn(wild1_val,
                      [self.all_communities[0], self.all_communities[2]])

    def test_communities_and_match(self):
        c1_match = SMTCommunity(
            community=self.all_communities[0],
            name='rm1',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        c2_match = SMTCommunity(
            community=self.all_communities[1],
            name='rm2',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        c3_match = SMTCommunity(
            community=self.all_communities[2],
            name='rm3',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        wild1_match = SMTCommunity(
            community=VALUENOTSET,
            name='rm4',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        wild2_match = SMTCommunity(
            community=VALUENOTSET,
            name='rm5',
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        def get_solver():
            solver = z3.Solver()
            self._load_communities_smt(solver)
            return solver

        s1 = get_solver()
        match1 = c1_match.match_fun(self.ann_map['Ann1_Google'])
        match3 = c3_match.match_fun(self.ann_map['Ann1_Google'])
        s1.add(c1_match.constraints)
        s1.add(c2_match.constraints)
        s1.add(c3_match.constraints)
        s1.add(z3.And(match1 == True, match3 == True))
        self.assertEquals(s1.check(), z3.sat)

        s2 = get_solver()
        match1 = wild1_match.match_fun(self.ann_map['Ann1_Google'])
        match2 = wild2_match.match_fun(self.ann_map['Ann1_Google'])
        s2.add(wild1_match.constraints)
        s2.add(wild2_match.constraints)
        print match1
        s2.add(z3.And(match1 == True, match2 == True,))
        # To guarantee synthesizing two different values
        s2.add(wild2_match.match_synthesized != wild1_match.match_synthesized)
        self.assertEquals(s2.check(), z3.sat)
        m = s2.model()
        self.assertIn(wild1_match.get_val(m),
                      [self.all_communities[0], self.all_communities[2]])
        self.assertIn(wild2_match.get_val(m),
                      [self.all_communities[0], self.all_communities[2]])
        self.assertNotEqual(wild1_match.get_val(m), wild2_match.get_val(m))


class SMTCommunityListMatchTest(SMTSetup):
    def test_communities_list(self):
        c1_list = CommunityList(1, Access.permit,
                                [self.all_communities[0],
                                 self.all_communities[2]])
        l1_match = SMTCommunityList(
            name='rm1',
            community_list= c1_list,
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

        c2_list = CommunityList(1, Access.permit,
                                [VALUENOTSET, VALUENOTSET])
        l2_match = SMTCommunityList(
            name='rm2',
            community_list=c2_list,
            announcement_sort=self.ann_sort,
            announcements=self.anns,
            communities_fun=self.communities_func)

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
        self.assertEquals(l1_match.get_val(m),
                          [self.all_communities[0], self.all_communities[2]])

        self.assertEquals(l1_match.get_config(m), c1_list)

        s2 = get_solver()
        match2 = l2_match.match_fun(self.ann_map['Ann1_Google'])
        s2.add(match2 == True)
        s2.add(l2_match.constraints)
        self.assertEquals(s2.check(), z3.sat)
        m = s2.model()
        self.assertEquals(set(l2_match.get_val(m)),
                          set([self.all_communities[0],
                               self.all_communities[2]]))
        self.assertEquals(l2_match.get_config(m), c1_list)

