from synet.ebgp import Announcement
from synet.ebgp import RouteMap
from synet.ebgp import MatchLocalPref
from synet.ebgp import MatchCommunity
from synet.ebgp import MatchPrefix
from synet.ebgp import SetLocalPref
from synet.ebgp import SetCommunity
from synet.ebgp import SetDrop
from synet.ebgp import BGP_ATTRS_ORIGIN
from synet.ebgp import EBGP
from synet.ebgp import EMPTY


def test_match_peer_set_localpref():
    ann1 = Announcement(PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 5, 7, 6],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann2 = Announcement(PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann3 = Announcement(PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 10, 30, 40],
                        NEXT_HOP='DT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann4 = Announcement(PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 3],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann5 = Announcement(PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann6 = Announcement(PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7],
                        NEXT_HOP='DT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    announcements = [ann1, ann2, ann3, ann4, ann5, ann6]
    reqs = ['Ann1', 'Ann4']
    ebgp = EBGP(announcements)

    # First, try fix the peer match
    routemap1 = RouteMap(name='RM1', match=MatchPeer('SwissCom'), action=SetLocalPref(EMPTY), permit=True)
    route_maps = [routemap1]
    assert ebgp.solve(route_maps, reqs)

    # Second, peer match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchPeer(EMPTY), action=SetLocalPref(EMPTY), permit=True)]
    ebgp = EBGP(announcements)
    assert ebgp.solve(route_maps, reqs)


def test_match_community_set_localpref():
    ann1 = Announcement(PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 5, 7, 6],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann2 = Announcement(PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann3 = Announcement(PREFIX='Google', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 10, 30, 40],
                        NEXT_HOP='DT', LOCAL_PREF=100, COMMUNITIES=('T', 'F', 'T'))

    ann4 = Announcement(PREFIX='Yahoo', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 3],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann5 = Announcement(PREFIX='Yahoo', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann6 = Announcement(PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7],
                        NEXT_HOP='DT', LOCAL_PREF=100, COMMUNITIES=('T', 'F', 'T'))

    announcements = [ann1, ann2, ann3, ann4, ann5, ann6]
    reqs = ['Ann3', 'Ann6']
    ebgp = EBGP(announcements)

    # First, try fix the peer match
    routemap1 = RouteMap(name='RM1', match=MatchCommunity('C1'), action=SetLocalPref(EMPTY), permit=True)
    route_maps = [routemap1]
    assert ebgp.solve(route_maps, reqs)

    # Second, peer match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True)]
    ebgp = EBGP(announcements)
    assert ebgp.solve(route_maps, reqs)


def test_match_localpref_set_localpref():
    ann1 = Announcement(PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 5, 7, 6],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann2 = Announcement(PREFIX='Google', PEER='ATT',      ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4, 7],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann3 = Announcement(PREFIX='Google', PEER='DT',       ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 9],
                        NEXT_HOP='DT', LOCAL_PREF=50, COMMUNITIES=('T', 'F', 'T'))

    ann4 = Announcement(PREFIX='Yahoo', PEER='SwissCom',   ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 3, 4, 3],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann5 = Announcement(PREFIX='Yahoo', PEER='ATT',        ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4, 1],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann6 = Announcement(PREFIX='Yahoo', PEER='DT',         ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 8],
                        NEXT_HOP='DT', LOCAL_PREF=50, COMMUNITIES=('T', 'F', 'T'))

    announcements = [ann1, ann2, ann3, ann4, ann5, ann6]
    reqs = ['Ann3', 'Ann6']
    ebgp = EBGP(announcements)

    # First, try fix the peer match
    routemap1 = RouteMap(name='RM1', match=MatchLocalPref(50), action=SetLocalPref(EMPTY), permit=True)
    route_maps = [routemap1]
    assert ebgp.solve(route_maps, reqs)

    # Second, peer match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchLocalPref(EMPTY), action=SetLocalPref(EMPTY), permit=True)]
    ebgp = EBGP(announcements)
    assert ebgp.solve(route_maps, reqs)


def test_match_prefix_set_drop():
    ann1 = Announcement(PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 5, 7, 6],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann2 = Announcement(PREFIX='Google', PEER='ATT',      ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4, 7],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann3 = Announcement(PREFIX='Google', PEER='DT',       ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 9],
                        NEXT_HOP='DT', LOCAL_PREF=500, COMMUNITIES=('T', 'F', 'T'))

    ann4 = Announcement(PREFIX='Yahoo', PEER='SwissCom',  ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 3, 4, 3],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann5 = Announcement(PREFIX='Yahoo', PEER='ATT',       ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4, 1],
                        NEXT_HOP='ATT', LOCAL_PREF=50, COMMUNITIES=('F', 'F', 'T'))

    ann6 = Announcement(PREFIX='Yahoo', PEER='DT',        ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 8],
                        NEXT_HOP='DT', LOCAL_PREF=50, COMMUNITIES=('T', 'F', 'T'))

    announcements = [ann1, ann2, ann3, ann4, ann5, ann6]
    reqs = ['Ann3']
    ebgp = EBGP(announcements)

    # First, try fix the match
    routemap1 = RouteMap(name='RM1', match=MatchPrefix('Yahoo'), action=SetDrop(True), permit=True)
    #route_maps = [routemap1]
    #assert ebgp.solve(route_maps, reqs)

    # Second, match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchPrefix(EMPTY), action=SetDrop(True), permit=True)]
    ebgp = EBGP(announcements)
    assert ebgp.solve(route_maps, reqs)


def test_match_prefix_set_drop_simple():
    ann1 = Announcement(PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1,],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F',))

    ann2 = Announcement(PREFIX='Yahoo', PEER='SwissCom',   ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4,],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('T',))

    announcements = [ann1, ann2]
    reqs = ['Ann1']

    # Second, match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchPrefix(EMPTY), action=SetDrop(True), permit=True)]
    ebgp = EBGP(announcements, all_communities=('C1',))
    assert ebgp.solve(route_maps, reqs)

def main():
    #test_match_peer_set_localpref()
    #test_match_community_set_localpref()
    #test_match_localpref_set_localpref()
    #test_match_prefix_set_drop()
    test_match_prefix_set_drop_simple()
    routemap2 = RouteMap(name='RM2', match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True)


if __name__ == '__main__':
    main()
