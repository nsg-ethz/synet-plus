#!/usr/bin/env python

import z3
from collections import namedtuple


from mins import get_max
from mins import get_min_eval_select

EMPTY = '?'

class EBGP(object):
    Announcement = namedtuple('Announcement', ['prefix', 'aspath', 'localpref', 'communities'])
    Imported = namedtuple('Imported', ['prefix', 'aspath', 'localpref', 'communities'])
    Selected = namedtuple('Selected', ['prefix', 'aspath', 'localpref', 'communities'])
    Exported = namedtuple('Exported', ['prefix', 'aspath', 'localpref', 'communities'])
    RouteMap = namedtuple('RouteMap', ['name', 'match', 'action'])
    CommunityMatch = namedtuple('CommunityMatch', ['community'])
    LocalPrefMatch = namedtuple('LocalPrefMatch', ['localpref'])
    SetCommunity = namedtuple('SetCommunity', ['community', 'value'])
    SetLocalPref = namedtuple('SetLocalPref', ['localpref'])
    RouteMapResult = namedtuple('RouteMapResult', ['name', 'communities', 'localpref', 'smt'])

    def __init__(self, network_graph = None, solver = None):
        self.network_graph = network_graph
        self.solver = solver or z3.Solver()

    def load_announcements(self):
        all_communities = ('C1', 'C2', 'C3')
        ann1 = EBGP.Announcement('Google', [1, 2, 3, 45, 6], 199, ('T', EMPTY, 'T'))
        ann2 = EBGP.Announcement('Google', [4, 5, 6, 4, 4], 199, ('F', 'T', 'T'))
        ann3 = EBGP.Announcement('Google', [4, 5, 6, 7], EMPTY, ('F', 'T', 'T'))
        ann4 = EBGP.Announcement('Yahoo', [1, 2, 3, 45, 6], 199, ('T', EMPTY, 'T'))
        ann5 = EBGP.Announcement('Yahoo', [4, 5, 6, 4, 4], 199, ('F', 'T', 'T'))
        ann6 = EBGP.Announcement('Yahoo', [4, 5, 6, 7], EMPTY, ('F', 'T', 'T'))

        # Special none valid route to help with Z3 tricks!
        notvalid = EBGP.Announcement('NOTVALID', [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 0, ('F', 'F', 'F'))
        announcements = [notvalid, ann1, ann2, ann3, ann3, ann4, ann5, ann6]

        self.ann_names = {}
        # Give a name for each announcement
        for i, ann in enumerate(announcements):
            self.ann_names['Ann%d' % i] = ann

        # Create Z3 Enum type for the announcements
        (self.Route, self.AllRoutes) = z3.EnumSort('Routes', self.ann_names.keys())
        self.AllRoutes = sorted(self.AllRoutes)
        # For convenience
        self.routes_map = dict([(str(ann), ann) for ann in self.AllRoutes])
        self.naAnnouncement = self.routes_map.get('Ann0')
        # LocalPref Function
        self.localpref = z3.Function('LocalPref', self.Route, z3.IntSort())
        # AsPath Length
        self.aspathlength = z3.Function('ASPathLength', self.Route, z3.IntSort())
        # Create functions for communities
        self.comm_functions = {}
        for c in all_communities:
            self.comm_functions[c] = z3.Function('Has%s' % c, self.Route, z3.BoolSort())

        for i, ann in enumerate(announcements):
            name = 'Ann%d' % (i)
            var = self.routes_map[name]
            self.solver.add(self.aspathlength(var) == len(ann.aspath))
            if ann.localpref == '?':
                self.solver.add(self.localpref(var) > 0)
            else:
                self.solver.add(self.localpref(var) == ann.localpref)
            for i, c in enumerate(ann.communities):
                c_name = all_communities[i]
                c_fun = self.comm_functions[c_name]
                if c == 'T':
                    self.solver.add(c_fun(var) == True)
                elif c == 'F':
                    self.solver.add(c_fun(var) == False)


    def process_route_map(self, routemap, prev_communities, prev_localpref):
        name = routemap.name
        match = routemap.match
        action = routemap.action
        if isinstance(match, EBGP.CommunityMatch):
            match_fun = prev_communities[match.community]
        elif isinstance(match, EBGP.LocalPrefMatch):
            match_fun = lambda x: prev_localpref(x) == match.localpref
        else:
            raise ValueError("Unknown match")
        t = z3.Const('%s_Tmp' % name, self.Route)
        result = EBGP.RouteMapResult
        if isinstance(action, EBGP.SetLocalPref):
            newlocalpref = z3.Function('%s_localPref' % name, self.Route, z3.IntSort())
            if action.localpref != EMPTY:
                c = z3.ForAll([t], newlocalpref(t) == z3.If(match_fun(t) == True, action.localpref, prev_localpref(t)))
            else:
                c = z3.ForAll([t], z3.Implies(match_fun(t) == False, newlocalpref(t) == prev_localpref(t)))
            result.communities = prev_communities
            result.localpref = newlocalpref
            result.smt = c
        elif isinstance(action, EBGP.SetCommunity):
            newcommunity = z3.Function('%s_Has%s' % (name, action.community), self.Route, z3.BoolSort())
            if action.value != EMPTY:
                c = z3.ForAll([t], newcommunity(t) == z3.If(match_fun(t), action.value, prev_communities[action.community](t)))
            else:
                c = z3.ForAll([t], z3.Implies(match_fun(t) == False, newcommunity(t) == prev_communities[action.community](t)))
            result.communities = prev_communities.copy()
            result.communities[action.community] = newcommunity
            result.localpref = prev_localpref
            result.smt = c
        return result

    def solve(self):
        self.load_announcements()
        na = self.routes_map['Ann0']
        a1 = self.routes_map['Ann1']
        a2 = self.routes_map['Ann2']
        a3 = self.routes_map['Ann3']

        routemap1 = EBGP.RouteMap(name='RM1', match=EBGP.CommunityMatch('C3'), action=EBGP.SetLocalPref(100))
        routemap2 = EBGP.RouteMap(name='RM1', match=EBGP.CommunityMatch('C3'), action=EBGP.SetCommunity('C2', True))
        result1 = self.process_route_map(routemap1, self.comm_functions, self.localpref)
        self.solver.add(result1.smt)
        result2 = self.process_route_map(routemap2, result1.communities, result1.localpref)
        self.solver.add(result2.smt)

        localpref = result2.localpref
        communities_fun = result2.communities
        for prefix in set([ann.prefix for ann in self.ann_names.values()]):
            prefixAnn = [self.routes_map[ann] for ann in self.routes_map if self.ann_names[ann].prefix == prefix]
            if len(prefixAnn) == 1:
                continue

            MaxLP = z3.Const('MaxLP%s' % prefix, z3.IntSort())
            MinAS = z3.Const('MinAS%s' % prefix, z3.IntSort())
            # Find the maximum local pref
            self.solver.add(MaxLP == get_max(*[localpref(a) for a in prefixAnn]))

            Selected = z3.Const('SelectedRoute%s' % prefix, self.Route)
            self.solver.add(Selected == get_min_eval_select(localpref, MaxLP, self.aspathlength, na, *prefixAnn))
            #self.solver.add(Selected == a3)

        self.solver.check()
        print self.solver.model()





def main():
    ebgp = EBGP()
    ebgp.solve()

if __name__ == '__main__':
    main()