#!/usr/bin/env python

import z3
from collections import namedtuple
from enum import Enum

z3.set_option('unsat-core', True)

from mins import get_max
from mins import get_min_eval_select
from mins import get_max_eval_select

EMPTY = '?'

class BGP_ATTRS_ORIGIN(Enum):
    IGP = 1
    EBGP = 2
    INCOMPLETE = 3


"""
PREFIX: the prefix that's being announced
PEER: the peer from whom that prefix has been received (this is not technically in the BGP attributes set)
ORIGIN: See BGP_ATTRS_ORIGIN
ASPATH: List of AS numbers
NEXT_HOP:
        1. If the BGP Peers are in different Autonomous Systems then the NEXT_HOP IP address that
          will be sent in the update message will be the IP address of the advertising router.
        2. If the BGP peers are in the same AS (IBGP Peers), and the destination network being
            advertised in the update message is also in the same AS, then the NEXT_HOP IP address
            that will be sent in the update message will be the IP address of the advertising router.
        3. If the BGP peers are in the same AS (IBGP Peers), and the destination network being advertised
            in the update message is in an external AS, then the NEXT_HOP IP address that will be sent in
            the update message will be the IP address of the external peer router which sent
            the advertisement to this AS.
LOCAL_PREF: is only used in updates sent to the IBGP Peers,
            It is not passed on to the BGP peers in other autonomous systems.
COMMUNITIES: List of Community values
"""
Announcement = namedtuple('Announcement', ['PREFIX', 'PEER', 'ORIGIN', 'AS_PATH', 'NEXT_HOP', 'LOCAL_PREF', 'COMMUNITIES'])
Imported = namedtuple('Imported', ['PREFIX', 'PEER', 'ORIGIN', 'AS_PATH', 'NEXT_HOP', 'LOCAL_PREF', 'COMMUNITIES'])
Selected = namedtuple('Selected', ['PREFIX', 'PEER', 'ORIGIN', 'AS_PATH', 'NEXT_HOP', 'LOCAL_PREF', 'COMMUNITIES'])
Exported = namedtuple('Exported', ['PREFIX', 'PEER', 'ORIGIN', 'AS_PATH', 'NEXT_HOP', 'LOCAL_PREF', 'COMMUNITIES'])

RouteMap = namedtuple('RouteMap', ['name', 'match', 'action', 'permit'])

MatchPrefix = namedtuple('MatchPrefix', ['prefix'])
MatchPeer = namedtuple('MatchPeer', ['peer'])
MatchLocalPref = namedtuple('MatchLocalPref', ['localpref'])
MatchCommunity = namedtuple('MatchCommunity', ['community'])

SetCommunity = namedtuple('SetCommunity', ['community', 'value'])
SetLocalPref = namedtuple('SetLocalPref', ['localpref'])
SetDrop = namedtuple('DropRoute', ['value'])

RouteMapResult = namedtuple('RouteMapResult', ['name', 'match', 'match_synthesized', 'match_syn_map', 'action', 'action_val', 'localpref', 'communities', 'drop', 'smt', 'prev_result'])


class EBGP(object):
    def __init__(self, announcements, network_graph = None, solver = None):
        self.network_graph = network_graph
        self.solver = solver or z3.Solver()
        self._announcements_map = None
        self.load_announcements(announcements)

    def get_announcement(self, announcement_name):
        """Given a string name of the announcement return it's Z3 value"""
        return self._announcements_map[announcement_name]

    def get_peer(self, peer_name):
        """Given a string name of a peer return it's Z3 value"""
        return self._peers_map[peer_name]

    def get_prefix(self, prefix_name):
        """Given a string name of a prefix return it's Z3 value"""
        return self._prefixes_map[prefix_name]

    def load_announcements(self, announcements):
        all_communities = ('C1', 'C2', 'C3')
        # Special none valid route to help with Z3 tricks!
        self.notvalid = Announcement(PREFIX='NOTVALID', PEER='NOTVALID', ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[i for i in range(100)], NEXT_HOP='NOTVALID', LOCAL_PREF=0, COMMUNITIES=('F', 'F', 'F'))
        announcements = [self.notvalid] + announcements

        # Give a name for each announcement
        self.announcement_names = {}
        for i, ann in enumerate(announcements):
            self.announcement_names['Ann%d' % i] = ann

        # Create Z3 Enum type for the announcements
        (self.AnnouncementSort, AllAnnouncements) = z3.EnumSort('AnnouncementSort', self.announcement_names.keys())
        # Create Z3 Enum type for peers
        (self.PeerSort, AllPeers) = z3.EnumSort('PeerSort', list(set([ann.PEER for ann in announcements])))
        # Create Z3 Enum type for Prefixes
        (self.PrefixSort, AllPrefixes) = z3.EnumSort('PrefixSort', list(set([ann.PREFIX for ann in announcements])))
        self.AllAnnouncements = sorted(AllAnnouncements)
        self.AllPeers = sorted(AllPeers)
        self.AllPrefixes = sorted(AllPrefixes)
        # For convenience
        self._announcements_map = dict([(str(ann), ann) for ann in self.AllAnnouncements])
        self._peers_map = dict([(str(peer), peer) for peer in self.AllPeers])
        self._prefixes_map = dict([(str(prefix), prefix) for prefix in self.AllPrefixes])
        self.naAnnouncement = self.get_announcement('Ann0')
        # Announcement Prefix
        self.prefix = z3.Function('Prefix', self.AnnouncementSort, self.PrefixSort)
        # Announcement Peer
        self.peer = z3.Function('Peer', self.AnnouncementSort, self.PeerSort)
        # LocalPref Function
        self.localpref = z3.Function('LocalPref', self.AnnouncementSort, z3.IntSort())
        # AsPath Length
        self.aspathlength = z3.Function('ASPathLength', self.AnnouncementSort, z3.IntSort())
        # Denied Routes
        self.route_denied = z3.Function('DeniedRoutes', self.AnnouncementSort, z3.BoolSort())
        # Create functions for communities
        self.communities = {}
        for c in all_communities:
            self.communities[c] = z3.Function('Has%s' % c, self.AnnouncementSort, z3.BoolSort())

        for i, name in enumerate(sorted(self.announcement_names)):
            ann = self.announcement_names[name]
            var = self.get_announcement(name)
            # Set Prefix
            self.solver.assert_and_track(self.prefix(var) == self.get_prefix(ann.PREFIX), 'init_prefix_%s' % str(var))
            # Set Peer
            self.solver.assert_and_track(self.peer(var) == self.get_peer(ann.PEER), 'init_peer_%s' % str(var))
            # Set AS PATH LENGTH, TODO: Set AS PATH it self!
            self.solver.assert_and_track(self.aspathlength(var) == len(ann.AS_PATH), 'init_as_path_length_%s' % str(var))
            # Set LOCAL PREF
            if ann.LOCAL_PREF == '?':
                self.solver.add(self.localpref(var) > 0)
            else:
                self.solver.assert_and_track(self.localpref(var) == ann.LOCAL_PREF, 'init_local_pref_%s' % str(var))
            # Nothing denied, only route maps can do that
            self.solver.add(self.route_denied(var) == False)

            # Assign communities
            for i, c in enumerate(ann.COMMUNITIES):
                c_name = all_communities[i]
                c_fun = self.communities[c_name]
                assert_name = 'init_comm_%s_%s' % (str(var), c_name)
                if c == 'T':
                    self.solver.assert_and_track(c_fun(var) == True, assert_name)
                elif c == 'F':
                    self.solver.assert_and_track(c_fun(var) == False, assert_name)

    def process_route_map(self, route_map, prev_localpref, prev_communities, prev_drop, prev_result=None):
        name = route_map.name
        match = route_map.match
        action = route_map.action
        # Temp variables for the quantifiers
        t1, t2 = z3.Consts('%s_Tmp1 %s_Tmp2' % (name, name), self.AnnouncementSort)

        match_synthesized = None
        match_syn_map = None
        # Capture the match function, should be a boolean function
        if isinstance(match, MatchCommunity):
            if match.community != EMPTY:
                match_fun = prev_communities[match.community]
            else:
                # This is a bit tricky to handle
                # In case the community match is EMPTY, the the synthesizer is free to choose any community
                # We create a dummy function such that it ranges and values maps exactly to one or more assigned communities
                # Then we enumerate the communities, and the variable _Selected_Community tells us which one that successfuly
                # mapped to our dummy match
                dummy_match = z3.Function('%s_Synthesize_Community_Match' % (name), self.AnnouncementSort, z3.BoolSort())
                match_synthesized = z3.Const('%s_Selected_Community_Match' % (name), z3.IntSort())
                match_syn_map = {}
                constrains = []
                for i, community in enumerate(sorted(prev_communities.keys())):
                    match_syn_map[i] = prev_communities[community]
                    constrains.append(
                        z3.And(match_synthesized == i, z3.ForAll([t1], dummy_match(t1) == prev_communities[community](t1)))
                    )
                constrains = z3.Or(*constrains)
                self.solver.append(constrains)
                match_fun = dummy_match
        elif isinstance(match, MatchLocalPref):
            if match.localpref != EMPTY:
                match_fun = lambda x: prev_localpref(x) == match.localpref
            else:
                dummy_match = z3.Function('%s_Synthesize_LocalPref_Match' % (name), self.AnnouncementSort, z3.IntSort())
                match_synthesized = z3.Const('%s_Selected_LocalPref_Match' % (name), z3.IntSort())
                match_syn_map = None
                self.solver.append(z3.ForAll([t1], dummy_match(t1) == z3.If(prev_localpref(t1) == match_synthesized, True, False)))
                match_fun = dummy_match
        elif isinstance(match, MatchPeer):
            if match.peer != EMPTY:
                match_fun = lambda x: self.peer(x) == self.get_peer(match.peer)
            else:
                dummy_match = z3.Function('%s_Synthesize_Peer_Match' % (name), self.AnnouncementSort, z3.BoolSort())
                match_synthesized = z3.Const('%s_Selected_Peer_Match' % (name), self.PeerSort)
                match_syn_map = None
                self.solver.append( z3.ForAll([t1], dummy_match(t1) == z3.If(self.peer(t1) == match_synthesized, True, False)))
                match_fun = dummy_match
        elif isinstance(match, MatchPrefix):
            if match.prefix != EMPTY:
                match_fun = lambda x: self.prefix(x) == self.get_prefix(match.prefix)
            else:
                dummy_match = z3.Function('%s_Synthesize_Prefix_Match' % (name), self.AnnouncementSort, z3.BoolSort())
                match_synthesized = z3.Const('%s_Selected_Prefix_Match' % (name), self.PrefixSort)
                match_syn_map = None
                self.solver.append( z3.ForAll([t1], dummy_match(t1) == z3.If(self.prefix(t1) == match_synthesized, True, False)))
                match_fun = dummy_match

        else:
            raise ValueError("Unknown match type %s" % type(match))

        # Handle actions
        if route_map.permit == False:
            # Function for denied routes
            route_denied = z3.Function('%s_DeniedRoutes' % (name,), self.AnnouncementSort, z3.BoolSort())
            action_fun = route_denied
            action_val = z3.Const('%s_action_val' % name, z3.BoolSort())
            # If match then drop route, no further eval is needed
            c = z3.ForAll([t1], z3.If(match_fun(t1) == True, route_denied(t1) == action_val, route_denied(t1) == prev_drop(t1)))
            c = z3.And(c, action_val == True)
            result_communities = prev_communities
            result_localpref = prev_localpref
            result_drop = route_denied
            result_smt = c
        elif isinstance(action, SetLocalPref):
            newlocalpref = z3.Function('%s_localPref' % name, self.AnnouncementSort, z3.IntSort())
            action_fun = newlocalpref
            action_val = z3.Const('%s_action_val' % name, z3.IntSort())
            # If local pref is not fixed, then leave it empty for the SMT to assign
            c = z3.ForAll([t1], newlocalpref(t1) == z3.If(match_fun(t1) == True, action_val, prev_localpref(t1)))
            if action.localpref != EMPTY:
                c = z3.And(c, action_val == action.localpref)
            else:
                c = z3.And(c, action_val > 0)
            # If the route already dropped, then don't bother
            with_drop = z3.ForAll([t1], z3.Implies(prev_drop(t1) == False, c))
            result_communities = prev_communities
            result_localpref = newlocalpref
            result_drop = prev_drop
            result_smt = with_drop
        elif isinstance(action, SetCommunity):
            newcommunity = z3.Function('%s_Has%s' % (name, action.community), self.AnnouncementSort, z3.BoolSort())
            action_fun = newcommunity
            action_val = z3.Const('%s_action_val' % name, z3.BoolSort())
            c = z3.ForAll([t1], newcommunity(t1) == z3.If(match_fun(t1), action_val, prev_communities[action.community](t1)))
            if action.value != EMPTY:
                c = z3.And(c, action_val == action.value)
            result_communities = prev_communities.copy()
            result_communities[action.community] = newcommunity
            result_localpref = prev_localpref
            result_drop = prev_drop
            result_smt = c
        elif isinstance(action, SetDrop):
            # Function for denied routes
            route_denied = z3.Function('%s_DeniedRoutes' % (name,), self.AnnouncementSort, z3.BoolSort())
            action_fun = route_denied
            action_val = z3.Const('%s_action_val', z3.BoolSort())
            c = z3.ForAll([t1], route_denied(t1) == z3.If(match_fun(t1), action_val, prev_drop(t1)))
            if action.value != EMPTY:
                c = z3.And(c, action_val == action.value)
            result_communities = prev_communities
            result_localpref = prev_localpref
            result_drop = route_denied
            result_smt = c
        # Prepare our results
        result = RouteMapResult(name, match=match_fun, match_synthesized=match_synthesized, match_syn_map=match_syn_map,
                                action=action_fun, action_val=action_val, communities=result_communities,
                                localpref=result_localpref, drop=result_drop, smt=result_smt, prev_result=prev_result)
        return result

    def process_route_maps(self, route_maps):
        if len(route_maps) == 0:
            result = RouteMapResult('InitialResult', communities=self.communities, localpref=self.localpref,
                                    drop=self.route_denied, smt=None, prev_result=None)
            return result

        first = route_maps[0]
        result = self.process_route_map(route_map=first, prev_communities=self.communities,
                                        prev_localpref=self.localpref, prev_drop=self.route_denied, prev_result=None)
        self.solver.assert_and_track(result.smt, 'route_map_%s' % first.name)
        prev_result = result
        for route_map in route_maps[1:]:
            result = self.process_route_map(route_map=route_map, prev_communities=prev_result.communities,
                                            prev_localpref=prev_result.localpref, prev_drop=prev_result.drop,
                                            prev_result=prev_result)
            self.solver.assert_and_track(result.smt, 'route_map_%s' % route_map.name)
            prev_result = result

        return prev_result

    def eval_route_map(self, model, result, summary=True):
        if result.prev_result is not None:
            self.eval_route_map(model, result.prev_result, summary)
        name = result.name
        print "Route Map", name
        if summary:
            print "\t", "Match", result.match
            print "\t", "Action", result.action, model.eval(result.action_val)
            if result.match_synthesized is not None:
                if result.match_syn_map:
                    print "\tSelected", result.match_syn_map[model.eval(result.match_synthesized).as_long()]
                else:
                    print "\tSelected", model.eval(result.match_synthesized)
        else:
            for route in self._announcements_map.values():
                if str(route) == 'Ann0': continue
                print "\t", result.match, route, model.eval(result.match(route))
                print "\t", result.action, route, model.eval(result.action(route))

    def solve(self, route_maps, required_names=[]):
        na = self._announcements_map['Ann0']
        result = self.process_route_maps(route_maps)

        localpref = result.localpref
        communities_fun = result.communities
        route_denied = result.drop
        select_route_vars = []
        for prefix in set([ann.PREFIX for ann in self.announcement_names.values()]):
            if prefix == self.notvalid.PREFIX:
                continue
            Selected = z3.Const('SelectedRoute%s' % prefix, self.AnnouncementSort)
            prefixAnn = [self.get_announcement(ann) for ann in self._announcements_map if self.announcement_names[ann].PREFIX == prefix]
            if len(prefixAnn) == 1:
                self.solver.add(Selected == z3.If(route_denied(prefixAnn[0]), na, prefixAnn[0]))
                continue

            MaxLP = z3.Const('MaxLP%s' % prefix, z3.IntSort())
            MinAS = z3.Const('MinAS%s' % prefix, z3.IntSort())
            # Find the maximum local pref
            self.solver.add(MaxLP == localpref(get_max_eval_select(route_denied, False, localpref, na,  *prefixAnn)))

            select_route_vars.append(Selected)
            self.solver.add(Selected == get_min_eval_select(localpref, MaxLP, self.aspathlength, na, *prefixAnn))

            for name in required_names:
                if prefix == self.announcement_names[name].PREFIX:
                    self.solver.assert_and_track(Selected == self.get_announcement(name), 'select_%s_%s' % (prefix, name))

        if self.solver.check() == z3.sat:
            #print self.solver.model()
            model = self.solver.model()
            selected_routes = []
            for route in select_route_vars:
                route = str(model.eval(route))
                # Skip the non valid route
                if route == 'Ann0': continue
                selected_routes.append(route)

            self.eval_route_map(model, result)
            for name in sorted(self._announcements_map.keys()):
                ann = self.get_announcement(name)
                print "Drop", name, model.eval(route_denied(ann))
            #assert selected_routes == required_names, selected_routes
            return True
        else:
            print self.solver.unsat_core()
            return False


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

    ann4 = Announcement(PREFIX='Yahoo', PEER='SwissCom',   ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[1, 2, 3, 4, 3],
                        NEXT_HOP='SwissCom', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann5 = Announcement(PREFIX='Yahoo', PEER='ATT',        ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 4, 1],
                        NEXT_HOP='ATT', LOCAL_PREF=100, COMMUNITIES=('F', 'F', 'T'))

    ann6 = Announcement(PREFIX='Yahoo', PEER='DT',         ORIGIN=BGP_ATTRS_ORIGIN.EBGP, AS_PATH=[4, 5, 6, 7, 8],
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


def main():
    #test_match_peer_set_localpref()
    #test_match_community_set_localpref()
    #test_match_localpref_set_localpref()
    test_match_prefix_set_drop()
    routemap2 = RouteMap(name='RM2', match=MatchCommunity(EMPTY), action=SetLocalPref(EMPTY), permit=True)


if __name__ == '__main__':
    main()