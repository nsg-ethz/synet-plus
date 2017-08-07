
import unittest
import networkx as nx

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


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class TestEBGP(unittest.TestCase):
    def test_no_inputs(self):
        c1 = Community("4:16")
        c = (c1,)
        anns = {}
        route_map = RouteMap('RM1', [])
        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        self.assertTrue(ebgp1.solve(route_map, []))

    def test_match_community_set_localpref(self):
        # Received announcements
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann2 = Announcement(
            PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann3 = Announcement(
            PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 10, 30, 40], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('T', 'F', 'T'))

        ann4 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 3], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann5 = Announcement(
            PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann6 = Announcement(
            PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('T', 'F', 'T'))

        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
            'Ann3': ann3,
            'Ann4': ann4,
            'Ann5': ann5,
            'Ann6': ann6
        }
        # Required Routes to be choosen by BGP
        reqs = ['Ann3', 'Ann6']

        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        c = (c1, c2, c3)

        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)

        # Synthesize with the community value known
        l1 = RouteMapLine(
            matches=[MatchCommunitiesList(
                CommunityList(1, Access.permit, [c1]))],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map1 = RouteMap('RM1', [l1])
        result = ebgp1.solve(route_map1, reqs)
        l = ebgp1.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match.communities, [c1])
        self.assertLess(100, l.actions[0].value)

        # Synthesize with the community value unknown
        # Synthesize with the community as a hole
        l2 = RouteMapLine(
            matches=[MatchCommunitiesList(
                CommunityList(1, Access.permit, [VALUENOTSET]))],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map2 = RouteMap('RM2', [l2])

        ebgp2 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)

        result = ebgp2.solve(route_map2, reqs)
        l = ebgp2.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp2.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match.communities, [c1])
        self.assertLess(100, l.actions[0].value)

    def test_match_peer_set_localpref(self):
        print "#" * 10, "Test Match=Peer, Action=LocalPref", "#" * 20
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann2 = Announcement(
            PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann3 = Announcement(
            PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 10, 30, 40], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann4 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 3], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann5 = Announcement(
            PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann6 = Announcement(
            PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
            'Ann3': ann3,
            'Ann4': ann4,
            'Ann5': ann5,
            'Ann6': ann6
        }
        reqs = ['Ann1', 'Ann4']

        # Communities
        c1 = Community("4:16")
        c2 = Community("4:17")
        c3 = Community("4:18")
        c = (c1, c2, c3)

        # First, try fix the peer match
        # Synthesize with the peer value known
        l1 = RouteMapLine(
            matches=[MatchPeer('SwissCom')],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map1 = RouteMap('RM1', [l1])

        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        result = ebgp1.solve(route_map1, reqs)
        l = ebgp1.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match, 'SwissCom')
        self.assertLess(100, l.actions[0].value)

        # Second, peer match is EMPY
        l1 = RouteMapLine(
            matches=[MatchPeer(VALUENOTSET)],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map2 = RouteMap('RM2', [l1])
        ebgp2 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                    announcements=anns, all_communities=c)
        result = ebgp2.solve(route_map2, reqs)
        l = ebgp2.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match, 'SwissCom')
        self.assertLess(100, l.actions[0].value)

    def test_match_localpref_set_localpref(self):
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=101,
            COMMUNITIES=('F', 'F', 'T'))

        ann2 = Announcement(
            PREFIX='Google', PEER='ATT',  ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4, 7], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann3 = Announcement(
            PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 9], NEXT_HOP='DT', LOCAL_PREF=50,
            COMMUNITIES=('T', 'F', 'T'))

        ann4 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 3, 4, 3], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann5 = Announcement(
            PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4, 1], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann6 = Announcement(
            PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 8], NEXT_HOP='DT', LOCAL_PREF=50,
            COMMUNITIES=('T', 'F', 'T'))

        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
            'Ann3': ann3,
            'Ann4': ann4,
            'Ann5': ann5,
            'Ann6': ann6
        }
        reqs = ['Ann3', 'Ann6']

        # Communities
        c1 = Community("4:16")
        c2 = Community("4:17")
        c3 = Community("4:18")
        c = (c1, c2, c3)

        l1 = RouteMapLine(
            matches=[MatchLocalPref(50)],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map1 = RouteMap('RM1', [l1])
        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                    announcements=anns, all_communities=c)
        result = ebgp1.solve(route_map1, reqs)
        l = ebgp1.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match, 50)
        self.assertLess(101, l.actions[0].value)

        l2 = RouteMapLine(
            matches=[MatchLocalPref(VALUENOTSET)],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map2 = RouteMap('RM2', [l2])
        ebgp2 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        result = ebgp2.solve(route_map2, reqs)
        l = ebgp2.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match, 50)
        self.assertLess(101, l.actions[0].value)

    def test_drop_all(self):
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, ], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('T',))

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, ], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('T',))

        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
        }

        c1 = Community("4:16")
        c = (c1,)
        l1 = RouteMapLine(
            matches=[MatchCommunitiesList(
                CommunityList(1, Access.permit, [c1]))],
            actions=[],
            access=VALUENOTSET,
            lineno=10
        )
        route_map = RouteMap('RM1', [l1])
        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        result = ebgp1.solve(route_map, [])
        self.assertTrue(result)
        self.assertEquals(ebgp1.exported.keys(), [])

    def test_match_prefix_set_drop(self):
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann2 = Announcement(
            PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4, 7], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann3 = Announcement(
            PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 9], NEXT_HOP='DT', LOCAL_PREF=500,
            COMMUNITIES=('T', 'F', 'T'))

        ann4 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom',  ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 3, 4, 3], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann5 = Announcement(
            PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4, 1], NEXT_HOP='ATT', LOCAL_PREF=50,
            COMMUNITIES=('F', 'F', 'T'))

        ann6 = Announcement(
            PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 8], NEXT_HOP='DT', LOCAL_PREF=50,
            COMMUNITIES=('T', 'F', 'T'))

        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
            'Ann3': ann3,
            'Ann4': ann4,
            'Ann5': ann5,
            'Ann6': ann6
        }
        reqs = ['Ann3']

        # Communities
        c1 = Community("4:16")
        c2 = Community("4:17")
        c3 = Community("4:18")
        c = (c1, c2, c3)

        l1 = RouteMapLine(
            matches=[MatchIpPrefixListList(
                IpPrefixList(1, Access.permit, ['Yahoo']))],
            actions=[],
            access=Access.deny,
            lineno=10
        )
        route_map1 = RouteMap('RM1', [l1])
        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        result = ebgp1.solve(route_map1, reqs)
        l = ebgp1.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match.networks, ['Yahoo'])
        self.assertEquals(l.actions, [])

        l2 = RouteMapLine(
            matches=[MatchIpPrefixListList(
                IpPrefixList(1, Access.permit, [VALUENOTSET]))],
            actions=[],
            access=Access.deny,
            lineno=10
        )
        route_map2 = RouteMap('RM2', [l2])
        ebgp2 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        result = ebgp2.solve(route_map2, reqs)
        l = ebgp2.synthesized_route_map.lines[0]
        self.assertTrue(result)
        self.assertEquals(set(ebgp2.exported.keys()), set(reqs))
        self.assertEquals(l.matches[0].match.networks, ['Yahoo'])
        self.assertEquals(l.actions, [])

    @unittest.skip
    def test_match_prefix_set_drop_simple(self):
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1,], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('T',))

        ann2 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4,], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('T',))

        ann3 = Announcement(
            PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, ], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('F',))

        ann4 = Announcement(
            PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, ], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('F',))

        # Communities
        c1 = Community("4:16")
        c = (c1,)
        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
            'Ann3': ann3,
            'Ann4': ann4,
        }
        reqs = ['Ann3', 'Ann4']

        l1 = RouteMapLine(
            matches=[MatchCommunitiesList(
                CommunityList(1, Access.permit, [VALUENOTSET]))],
            actions=[],
            access=VALUENOTSET,
            lineno=10
        )

        l2 = RouteMapLine(
            matches=[MatchLocalPref(100)],
            actions=[ActionSetLocalPref(120)],
            access=Access.permit,
            lineno=20
        )
        route_map1 = RouteMap('RM1', lines=[l1, l2])
        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        self.assertTrue(ebgp1.solve(route_map1, reqs))
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        l1 = ebgp1.synthesized_route_map.lines[0]
        self.assertEquals(l1.access, Access.deny)
        l2 = ebgp1.synthesized_route_map.lines[1]
        self.assertEquals(l2.access, Access.permit)


        return
        # Second, match is EMPY
        route_maps = [RouteMap(name='RM1', match=MatchCommunity(EMPTY), action=SetDrop(True), permit=True)]
        ebgp = EBGP(asnum=100, peer_name='R1', nexthop='R1', announcements=anns, all_communities=('C1',))
        assert ebgp.solve(route_maps, reqs)

    def test_match_localpref_set_drop(self):
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=30,
            COMMUNITIES=('F', 'F', 'T'))

        ann2 = Announcement(
            PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4, 7], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann3 = Announcement(
            PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 9],  NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('T', 'F', 'T'))

        ann4 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom',  ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 3, 4, 3], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann5 = Announcement(PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                            AS_PATH=[4, 5, 6, 4, 1], NEXT_HOP='ATT', LOCAL_PREF=100,
                            COMMUNITIES=('F', 'F', 'T'))

        ann6 = Announcement(PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
                            AS_PATH=[4, 5, 6, 7, 8], NEXT_HOP='DT', LOCAL_PREF=100,
                            COMMUNITIES=('T', 'F', 'T'))
        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
            'Ann3': ann3,
            'Ann4': ann4,
            'Ann5': ann5,
            'Ann6': ann6
        }
        reqs = ['Ann1']

        c1 = Community("4:16")
        c2 = Community("4:17")
        c3 = Community("4:18")
        c = (c1, c2, c3)

        l1 = RouteMapLine(
            matches=[MatchLocalPref(100)],
            actions=[],
            access=Access.deny,
            lineno=10
        )
        route_map1 = RouteMap('RM1', [l1])
        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                    announcements=anns, all_communities=c)
        assert ebgp1.solve(route_map1, reqs)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        l = ebgp1.synthesized_route_map.lines[0]
        self.assertEquals(l.matches[0].match, 100)
        self.assertEquals(l.actions, [])
        self.assertEquals(l.access, Access.deny)

        l2 = RouteMapLine(
            matches=[MatchLocalPref(VALUENOTSET)],
            actions=[],
            access=Access.deny,
            lineno=10
        )
        route_map2 = RouteMap('RM2', [l2])
        ebgp2 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        assert ebgp2.solve(route_map2, reqs)
        self.assertEquals(set(ebgp1.exported.keys()), set(reqs))
        l = ebgp2.synthesized_route_map.lines[0]
        self.assertEquals(l.matches[0].match, 100)
        self.assertEquals(l.actions, [])
        self.assertEquals(l.access, Access.deny)

    @unittest.skip
    def test_match_community_list_set_localpref(self):
        # Received announcements
        ann1 = Announcement(
            PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 5, 7, 6], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'T', 'T'))

        ann2 = Announcement(
            PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 4], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann3 = Announcement(
            PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7, 10, 30, 40], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('T', 'T', 'F'))

        ann4 = Announcement(
            PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[1, 2, 3], NEXT_HOP='SwissCom', LOCAL_PREF=100,
            COMMUNITIES=('F', 'F', 'T'))

        ann5 = Announcement(
            PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6], NEXT_HOP='ATT', LOCAL_PREF=100,
            COMMUNITIES=('F', 'T', 'T'))

        ann6 = Announcement(
            PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
            AS_PATH=[4, 5, 6, 7], NEXT_HOP='DT', LOCAL_PREF=100,
            COMMUNITIES=('T', 'T', 'T'))

        anns = {
            'Ann1': ann1,
            'Ann2': ann2,
            'Ann3': ann3,
            'Ann4': ann4,
            'Ann5': ann5,
            'Ann6': ann6
        }
        # Required Routes to be choosen by BGP
        reqs = ['Ann3', 'Ann6']

        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        c = (c1, c2, c3)

        ebgp1 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)

        # Synthesize with the community value known
        l1 = RouteMapLine(
            matches=[MatchCommunitiesList(
                CommunityList(1, Access.permit, [c1, c2]))],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map1 = RouteMap('RM1', [l1])
        assert ebgp1.solve(route_map1, reqs)
        l = ebgp1.synthesized_route_map.lines[0]
        assert l.matches[0].match.communities == [c1, c2]
        assert l.actions[0].value > 100

        # Synthesize with the community value unknown
        # Synthesize with the community as a hole
        l2 = RouteMapLine(
            matches=[MatchCommunitiesList(
                CommunityList(1, Access.permit, [VALUENOTSET, VALUENOTSET]))],
            actions=[ActionSetLocalPref(VALUENOTSET)],
            access=Access.permit,
            lineno=10
        )
        route_map2 = RouteMap('RM2', [l2])

        ebgp2 = EBGP(asnum=100, peer_name='R1', nexthop='R1',
                     announcements=anns, all_communities=c)
        assert ebgp2.solve(route_map2, reqs)
        l = ebgp2.synthesized_route_map.lines[0]
        assert l.matches[0].match.communities == [c1]
        assert l.actions[0].value > 100


def get_random_announcements(num_prefixes, num_peers, num_communities, min_as_path=2, max_as_path=10,
                min_localpref=100, max_localpref=100, random_gen=None):
    prefixes = ["Prefix%05d" % i for i in range(num_prefixes)]
    peers = ["Peer%04d" % i for i in range(num_peers)]
    communities = ["Community%04d" % i for i in range(num_communities)]
    # Distribute prefixes among peers
    peers_prefixes = dict([(peer, []) for peer in peers])
    for prefix in prefixes:
        selected_peers = random_gen.sample(peers, random_gen.choice(range(1, len(peers) + 1)))
        for peer in selected_peers:
            peers_prefixes[peer].append(prefix)
    annoucements = []
    for peer in peers_prefixes:
        for prefix in peers_prefixes[peer]:
            as_path_length = random_gen.choice(list(range(min_as_path, max_as_path + 1)))
            as_path = random_gen.sample(list(range(100, 1000)), as_path_length)
            localpref = random_gen.choice(list(range(min_localpref, max_localpref + 1)))
            num_select_comm = random_gen.choice(list(range(0, num_communities + 1)))
            select_communities = random_gen.sample(communities, num_select_comm)
            selected_comm = tuple(['T' if c in select_communities else 'F' for c in communities])
            ann = Announcement(PREFIX=prefix, PEER=peer, ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=as_path,
                               NEXT_HOP=peer, LOCAL_PREF=localpref, COMMUNITIES=selected_comm)
            annoucements.append(ann)
    return annoucements, communities


def manual_stress(announcements, communities, random_gen):
    print "#" * 10, "Test Stress", "#" * 20
    prefix_announcement = {}
    peer_announcement = {}
    for ann in announcements:
        prefix = ann.PREFIX
        if prefix not in prefix_announcement: prefix_announcement[prefix] = []
        prefix_announcement[prefix].append(ann)
    reqs = []
    for prefix in prefix_announcement:
        anns = prefix_announcement[prefix]
        #ann = random_gen.choice(anns)
        selected = False
        for ann in anns:
            if ann.PEER == 'Peer0001':
                reqs.append(ann)
                selected = True
                break
        if not selected:
            ann = random_gen.choice(anns)
            reqs.append(ann)

    reqs_names = []
    for i, ann in enumerate(announcements):
        if ann in reqs:
            reqs_names.append('Ann%d' % (i+1))

    RM1 = RouteMap(name='RM1', match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True)
    RM2 = RouteMap(name='RM2', match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True)
    RM3 = RouteMap(name='RM3', match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True)
    RM4 = RouteMap(name='RM4', match=MatchPeer(EMPTY), action=SetLocalPref(EMPTY), permit=True)
    route_maps = [RM1, RM2, RM3, RM4]
    route_maps = [RouteMap(name='RM%d' % i , match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True) for i in range(len(communities))]
    #route_maps += [RouteMap(name='RM2%d' % i, match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True) for i
    #              in range(len(communities))]
    ebgp = EBGP(asnum=100, peer_name='R1', nexthop='R1', announcements=announcements, all_communities=communities)
    assert ebgp.solve(route_maps, reqs_names)


def update_peer(announcements, peer):
    c_anns = {}
    for name, ann in announcements.iteritems():
        new_ann = {}
        for f in ann._fields:
            if f == 'PEER':
                new_ann[f] = peer
            else:
                new_ann[f] = getattr(ann, f)
        new_ann = Announcement(**new_ann)
        c_anns[name] = new_ann
    return c_anns


def apply_syn(anns, reqs):
    routemap1 = RouteMap(
        name='RM1', match=MatchPeer(EMPTY),
        action=SetCommunity('C1', EMPTY), permit=True)
    routemap2 = RouteMap(
        name='RM2', match=MatchCommunity(EMPTY),
        action=SetLocalPref(EMPTY), permit=True)
    route_maps = [routemap1, routemap2]
    bgp = EBGP(asnum=100, peer_name='R1', nexthop='R1', announcements=anns)
    assert bgp.solve(route_maps, reqs)
    return bgp.exported


def get_reqs(announcements, reqs):
    req_names = []

    def match(ann, req):
        return (ann.PREFIX, ann.PEER, ann.NEXT_HOP) == req

    for i, name in enumerate(announcements.keys()):
        ann = announcements[name]
        for req in reqs:
            if match(ann, req):
                req_names.append(name)
    return req_names


def test_graph():
    g = nx.DiGraph()
    g.add_nodes_from(['A', 'B', 'C', 'D'])
    for src in g.nodes():
        for dst in g.nodes():
            if src == dst: continue
            g.add_edge(src, dst)

    ann1 = Announcement(
        PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[2, 5, 8], NEXT_HOP='SwissCom', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    ann2 = Announcement(
        PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[6, 7], NEXT_HOP='DT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    anns = {
        'Ann1': ann1,
        'Ann2': ann2,
    }

    req_map = {}
    req_map['D'] = [('Google', 'SwissCom', 'SwissCom')]
    req_map['A'] = [('Google', 'B', 'SwissCom')]
    req_map['B'] = [('Google', 'C', 'SwissCom')]
    req_map['C'] = [('Google', 'D', 'SwissCom')]

    exported = {}
    exported['A'] = []
    exported['B'] = []
    exported['C'] = []
    exported['D'] = []


    source = 'D'
    print "In", source
    exported[source] = apply_syn(anns, get_reqs(anns, req_map[source]))
    successors = nx.bfs_successors(g, source)
    print ''
    for succ in successors[source]:
        print "In", succ
        tmp_anns = update_peer(exported[source], source)
        exported[succ] += apply_syn(tmp_anns, get_reqs(tmp_anns, req_map[succ]))
        print ""

    print "*" * 50
    print "Second Iteration"
    source = 'C'
    print "In", source
    exported[source] = apply_syn(anns, get_reqs(anns, req_map[source]))
    successors = nx.bfs_successors(g, source)
    for succ in successors[source]:
        if succ == 'D': continue
        print "In", succ
        tmp_anns = update_peer(exported[source], source)
        exported[succ] = apply_syn(tmp_anns, get_reqs(tmp_anns, req_map[succ]))
        print ""


def main():

    test_graph()
    return


    import random
    import sys
    seed = random.randint(0, sys.maxint)
    random_gen = random.Random()
    seed = 8348970342609031081
    random_gen.seed(seed)
    print "Seed is", seed
    anns, communities = get_random_announcements(num_prefixes=10, num_peers=10, num_communities=10, random_gen=random_gen)
    manual_stress(anns, communities, random_gen)
    return


    test_match_peer_set_localpref()
    test_match_community_set_localpref()
    test_match_localpref_set_localpref()
    #test_match_prefix_set_drop()
    test_match_prefix_set_drop_simple()
    test_match_localpref_set_drop()
    routemap2 = RouteMap(name='RM2', match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True)


if __name__ == '__main__':
    main()
