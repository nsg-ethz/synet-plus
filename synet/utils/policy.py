#!/usr/bin/env python
"""
Synthesize policies .. aka route maps for the moment

Match Semantics from
https://www.cisco.com/c/en/us/support/docs/ip/border-gateway-protocol-bgp/49111-route-map-bestp.html

A match or set command in each clause can be missed or repeated several times,
    if one of these conditions exist:

If several match commands are present in a clause, all must succeed for
    a given route in order for that route to match the clause
    (in other words, the logical AND algorithm is applied for multiple
    match commands).

If a match command refers to several objects in one command, either of
    them should match (the logical OR algorithm is applied).
    For example, in the match ip address 101 121 command,
    a route is permitted if it is permitted by access list 101 or access list 121.

If a match command is not present, all routes match the clause.
    In the previous example, all routes that reach clause 30 match;
    therefore, the end of the route-map is never reached.

If a set command is not present in a route-map permit clause then
    the route is redistributed without modification of its current attributes.
"""


from collections import namedtuple
import z3

from synet.topo.bgp import VALUENOTSET
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


AndOp = namedtuple('AndOp', ['values'])
OrOp = namedtuple('OrOp', ['values'])


class SMTCommunity(object):
    """
    Synthesis one Community match
    """

    def __init__(self, name, community, announcements, announcement_sort,
                 communities_fun):
        """
        :param community: Community object or VALUENOTSET
        :param name: unique name to make the SMT variables more readable
        :param announcement_sort: Z3 sort for announcement types
        :param announcements: dict of Announcements
        :param communities_fun: dict [Community -> z3 match function]
        """
        assert community == VALUENOTSET or isinstance(community, Community)
        self.ann_sort = announcement_sort
        self.name = name
        self._community = community
        self._prev_communities_fun = communities_fun
        self.announcements = announcements
        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}
        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized community for this match
        :param model: Z3 model
        :return: Community
        """
        if self.match_synthesized is None:
            return self._community
        index = model.eval(self.match_synthesized).as_long()
        ret = self.match_syn_map[index]
        return ret

    def is_concrete(self):
        """
        Return true if concrete Community object defined for all
        known announcements in self.announcements
        :return:
        """
        if self._community == VALUENOTSET:
            return False
        concrete = True
        for _, ann in self.announcements.iteritems():
            if ann.COMMUNITIES[self._community] not in ['T', 'F']:
                return False
        return concrete

    def _gen_match_func(self):
        if self._community != VALUENOTSET:
            if self.is_concrete():
                func = lambda x: self.announcements[str(x)].COMMUNITIES[self._community] == 'T'
                return func
            return self._prev_communities_fun[self._community]
        else:
            # This is a bit tricky to handle
            # In case the community match is EMPTY,
            #     the the synthesizer is free to choose any community
            # We create a dummy function such that it ranges and values maps exactly to
            # one or more assigned communities.
            # Then we enumerate the communities,
            # and the variable _Selected_Community tells us which one that successfully
            # mapped to our dummy match
            f_name = '%s_Synthesize_Comm_Match' % self.name
            dummy_match = z3.Function(f_name, self.ann_sort, z3.BoolSort())
            c_name = '%s_Selected_Comm_Match' % self.name
            self.match_synthesized = z3.Const(c_name, z3.IntSort())
            self.match_syn_map = {}
            constrains = []
            for i, community in enumerate(sorted(self._prev_communities_fun.keys())):
                # TODO: there are some room for partial eval
                tmp = z3.Const('%s_Tmp%d' % (self.name, i), self.ann_sort)
                self.match_syn_map[i] = community
                constrains.append(
                    z3.And(self.match_synthesized == i,
                           z3.ForAll(
                               [tmp],
                               dummy_match(tmp) == self._prev_communities_fun[community](tmp)
                           ))
                )
            self.constraints = [z3.Or(*constrains)]
            # self.solver.append(constrains)
            match_fun = dummy_match
        return match_fun

    def get_config(self, model):
        """
        Get the synthesized Community
        :param model: Z3 model
        :return: Community
       """
        return self.get_val(model)


class SMTCommunityList(object):
    """
    Synthesis list of Communities (AND)
    """
    def __init__(self, name,
                 community_list,
                 announcement_sort,
                 announcements,
                 communities_fun):
        """
        :param communities: list of Community object or VALUENOTSET
        :param name: unique name to make the SMT variables more readable
        :param announcement_sort: Z3 sort for announcement types
        :param announcements: dict of Announcements
        :param communities_fun: dict [Community -> z3 match function]
        """
        assert isinstance(community_list, CommunityList)
        self.ann_sort = announcement_sort
        self.name = name
        self._prev_communities_fun = communities_fun
        self.announcements = announcements
        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}
        self._community_list = community_list
        self._smt_matches = []
        for i, community in enumerate(self._community_list.communities):
            smt = SMTCommunity(community=community,
                               name='%s_%d' % (name, i),
                               announcement_sort=announcement_sort,
                               announcements=announcements,
                               communities_fun=communities_fun)
            self._smt_matches.append(smt)
        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized list of Communities for this match
        :param model: Z3 model
        :return: list of Community
        """
        return [smt.get_val(model) for smt in self._smt_matches]

    def is_concrete(self):
        """
        Return true if concrete Community object defined for all
        known announcements in self.announcements
        :return:
        """
        for smt in self._smt_matches:
            if not smt.is_concrete():
                return False
        return True

    def _gen_match_func(self):
        # Add constraints
        for smt in self._smt_matches:
            self.constraints.extend(smt.constraints)
        dist = [smt.match_synthesized for smt in
                self._smt_matches if smt.match_synthesized is not None]
        if len(dist) > 1:
            unique_c = z3.Distinct(dist)
            self.constraints.append(unique_c)
        fun = lambda x: z3.And(*[smt.match_fun(x) for smt in self._smt_matches])
        return fun

    def get_config(self, model):
        """
        Get the synthesized CommunityList
        :param model: Z3 model
        :return: CommunityList
        """
        communities = self.get_val(model)
        return CommunityList(list_id=self._community_list.list_id,
                             access=self._community_list.access,
                             communities=communities)
