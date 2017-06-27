from synet.ebgp import Announcement
from synet.ebgp import RouteMap
from synet.ebgp import MatchLocalPref
from synet.ebgp import MatchCommunity
from synet.ebgp import MatchPeer
from synet.ebgp import MatchPrefix
from synet.ebgp import SetLocalPref
from synet.ebgp import SetCommunity
from synet.ebgp import SetDrop
from synet.ebgp import BGP_ATTRS_ORIGIN
from synet.ebgp import EBGP
from synet.ebgp import EMPTY


def test_match_peer_set_localpref():
    print "#" * 10, "Test Match=Peer, Action=LocalPref", "#" * 20
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
    print "#" * 10, "Test Match=Community, Action=LocalPref", "#" * 20
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
    print "#" * 10, "Test Match=LocalPref, Action=LocalPref", "#" * 20
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
    print "#" * 10, "Test Match=Prefix, Action=Drop", "#" * 20
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
    route_maps = [routemap1]
    assert ebgp.solve(route_maps, reqs)

    # Second, match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchPrefix(EMPTY), action=SetDrop(True), permit=True)]
    ebgp = EBGP(announcements)
    assert ebgp.solve(route_maps, reqs)


def test_match_prefix_set_drop_simple():
    print "#" * 10, "Test (Simple) Match=Prefix, Action=Drop", "#" * 20
    ann1 = Announcement(PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1,],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F',))

    ann2 = Announcement(PREFIX='Yahoo', PEER='SwissCom',   ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4,],
                        NEXT_HOP='SwissCom', LOCAL_PREF=50, COMMUNITIES=('T',))

    announcements = [ann1, ann2]
    reqs = ['Ann1']

    # Second, match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchCommunity(EMPTY), action=SetDrop(True), permit=True)]
    ebgp = EBGP(announcements, all_communities=('C1',))
    assert ebgp.solve(route_maps, reqs)


def test_match_localpref_set_drop():
    print "#" * 10, "Test Match=LocalPref, Action=Drop", "#" * 20
    ann1 = Announcement(PREFIX='Google', PEER='SwissCom', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 5, 7, 6],
                        NEXT_HOP='SwissCom', LOCAL_PREF=30, COMMUNITIES=('F', 'F', 'T'))

    ann2 = Announcement(PREFIX='Google', PEER='ATT',      ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4, 7],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann3 = Announcement(PREFIX='Google', PEER='DT',       ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 9],
                        NEXT_HOP='DT', LOCAL_PREF=100, COMMUNITIES=('T', 'F', 'T'))

    ann4 = Announcement(PREFIX='Yahoo', PEER='SwissCom',  ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 3, 4, 3],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann5 = Announcement(PREFIX='Yahoo', PEER='ATT',       ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4, 1],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann6 = Announcement(PREFIX='Yahoo', PEER='DT',        ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 8],
                        NEXT_HOP='DT', LOCAL_PREF=100, COMMUNITIES=('T', 'F', 'T'))

    announcements = [ann1, ann2, ann3, ann4, ann5, ann6]
    reqs = ['Ann1']
    ebgp = EBGP(announcements)

    print "First"
    # First, try fix the match
    routemap1 = RouteMap(name='RM1', match=MatchLocalPref(100), action=SetDrop(True), permit=True)
    route_maps = [routemap1]
    assert ebgp.solve(route_maps, reqs)
    print "Second"
    # Second, match is EMPY
    route_maps = [RouteMap(name='RM1', match=MatchLocalPref(EMPTY), action=SetDrop(EMPTY), permit=True)]
    ebgp = EBGP(announcements)
    assert ebgp.solve(route_maps, reqs)
    print "#" * 70


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


def test_stress(announcements, communities, random_gen):
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
    ebgp = EBGP(announcements, all_communities=communities)
    assert ebgp.solve(route_maps, reqs_names)


def main():
    import random
    import sys
    seed = random.randint(0, sys.maxint)
    random_gen = random.Random()
    seed = 8348970342609031081
    random_gen.seed(seed)
    print "Seed is", seed
    anns, communities = get_random_announcements(num_prefixes=10, num_peers=10, num_communities=10, random_gen=random_gen)
    test_stress(anns, communities, random_gen)
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
