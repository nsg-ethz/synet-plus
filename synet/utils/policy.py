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


List of route maps
https://www.cisco.com/c/en/us/support/docs/ip/border-gateway-protocol-bgp/26634-bgp-toc.html#routemaps
"""

from collections import Iterable
from collections import namedtuple
import z3

from synet.topo.bgp import Access
from synet.topo.bgp import VALUENOTSET
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList
from synet.topo.bgp import IpPrefixList
from synet.topo.bgp import MatchIpPrefixListList
from synet.topo.bgp import MatchCommunitiesList
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import ActionSetCommunity
from synet.topo.bgp import RouteMapLine
from synet.topo.bgp import RouteMap

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"

AndOp = namedtuple('AndOp', ['values'])
OrOp = namedtuple('OrOp', ['values'])


class SMTContext(object):
    """
    Hold SMT Context needed for the policy synthesis
    """

    def __init__(self, announcements, announcements_vars, announcement_sort,
                 communities_fun, prefixes_vars, prefix_sort, prefix_fun,
                 local_pref_fun, route_denied_fun):
        """
        :param announcements: dict of name -> Announcement
        :param announcements_vars: dict of name -> Z3 Announcement
        :param announcement_sort: Z3 announcement type
        :param communities_fun: Community -> (z3.function (Announcement->True or False))
        :param prefixes_vars: dict of name -> Z3 Prefix var
        :param prefix_sort: Z3 prefix type
        :param prefix_fun: prefix -> (z3.function (Announcement->True or False))
        :param local_pref_fun: Announcement Sort -> Int local pref
        :param route_denied_fun: Announcement Sort -> Boolean (true if route is dropped
        """
        self.announcements = announcements
        self.announcements_vars = announcements_vars
        self.announcement_sort = announcement_sort
        self.communities_fun = communities_fun
        self.prefixes_vars = prefixes_vars
        self.prefix_sort = prefix_sort
        self.prefix_fun = prefix_fun
        self.local_pref_fun = local_pref_fun
        self.route_denied_fun = route_denied_fun


class SMTObject(object):
    """
    Parent object for SMT helper classes
    """

    def get_val(self, model):
        """
        Return the concrete or synthesized value
        :param model: Z3 model
        :return: dependent on the subclass
        """
        raise NotImplementedError()

    def get_config(self, model):
        """
        Return the concrete or synthesized configuration instance
        :param model: Z3 model
        :return: dependent on the subclass
        """
        raise NotImplementedError()

    def is_concrete(self):
        """
        Return true if this can be solved with out Z3
        """
        raise NotImplementedError()


class SMTCommunity(SMTObject):
    """
    Synthesis one Community match
    """

    def __init__(self, name, community, context):
        """
        :param community: Community object or VALUENOTSET
        :param name: unique name to make the SMT variables more readable
        :param context: SMTContext
        """
        assert community == VALUENOTSET or isinstance(community, Community)
        self.name = name
        self._community = community
        self.ctx = context
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
        """
        if self._community == VALUENOTSET:
            return False
        concrete = True
        for _, ann in self.ctx.announcements.iteritems():
            if ann.COMMUNITIES[self._community] not in ['T', 'F']:
                return False
        return concrete

    def _gen_match_func(self):
        if self._community != VALUENOTSET:
            if self.is_concrete():
                func = lambda x: self.ctx.announcements[str(x)].COMMUNITIES[self._community] == 'T'
                return func
            return self.ctx.communities_fun[self._community]
        else:
            # This is a bit tricky to handle
            # In case the community match is EMPTY,
            #     the the synthesizer is free to choose any community
            # We create a dummy function such that it ranges and values maps exactly to
            # one or more assigned communities.
            # Then we enumerate the communities,
            # and the variable _Selected_Community tells us which one that successfully
            # mapped to our dummy match
            f_name = '%s_SynComm_Match' % self.name
            dummy_match = z3.Function(f_name, self.ctx.announcement_sort, z3.BoolSort())
            c_name = '%s_SelComm_Match' % self.name
            self.match_synthesized = z3.Const(c_name, z3.IntSort())
            self.match_syn_map = {}
            constrains = []
            for i, community in enumerate(sorted(self.ctx.communities_fun.keys())):
                # TODO: there are some room for partial eval
                tmp = z3.Const('%s_Tmp%d' % (self.name, i), self.ctx.announcement_sort)
                self.match_syn_map[i] = community
                constrains.append(
                    z3.And(self.match_synthesized == i,
                           z3.ForAll(
                               [tmp],
                               dummy_match(tmp) == self.ctx.communities_fun[community](tmp)
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


class SMTCommunityList(SMTObject):
    """
    Synthesis list of Communities (AND)
    """

    def __init__(self, name, community_list, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param communities: CommunityList object
        :param context: SMTContext
        """
        assert isinstance(community_list, CommunityList)
        self.name = name
        self._community_list = community_list
        self.ctx = context
        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}
        self._smt_matches = []
        for i, comm in enumerate(self._community_list.communities):
            name = '%s_%d' % (self.name, i)
            smt = SMTCommunity(name=name, community=comm, context=self.ctx)
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


class SMTIpPrefix(SMTObject):
    """
    Synthesis one IPPrefix
    TODO: Support longest prefix matching
    """

    def __init__(self, name, prefix, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param prefix: Prefix or VALUENOTSET
        :param context: SMTContext
        """
        assert prefix == VALUENOTSET or isinstance(prefix, basestring)
        self.name = name
        self._prefix = prefix
        self.ctx = context

        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}

        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized prefix for this match
        :param model: Z3 model
        :return: prefix
        """
        if self.match_synthesized is None:
            return self._prefix
        index = model.eval(self.match_synthesized)
        index = index.as_long()
        ret = self.match_syn_map[index]
        return ret

    def is_concrete(self):
        """
        Return true if concrete Prefix object
        :return: boolean
        """
        return self._prefix != VALUENOTSET

    def _gen_match_func(self):
        if self._prefix != VALUENOTSET:
            match_fun = lambda x: self.ctx.prefix_fun(x) == self.ctx.prefixes_vars[self._prefix]
        else:
            dummy_match = z3.Function(
                '%s_Synthesize_Prefix_Match' % self.name,
                self.ctx.announcement_sort, z3.BoolSort())
            self.match_synthesized = z3.Const(
                '%s_Selected_Prefix_Match' % self.name, z3.IntSort())
            self.match_syn_map = {}
            constraints = []
            for i, prefix in enumerate(sorted(self.ctx.prefixes_vars.keys())):
                prefix_var = self.ctx.prefixes_vars[prefix]
                tmp = z3.Const('%s_Tmp%d' % (self.name, i), self.ctx.announcement_sort)
                self.match_syn_map[i] = prefix
                constraints.append(
                    z3.And(self.match_synthesized == i,
                           z3.ForAll(
                               [tmp],
                               dummy_match(tmp) == z3.If(
                                   self.ctx.prefix_fun(tmp) == prefix_var,
                                   True,
                                   False))))
            self.constraints = [z3.Or(*constraints)]
            match_fun = dummy_match
        return match_fun

    def get_config(self, model):
        """
        Get the synthesized Prefix
        :param model: Z3 model
        :return: Prefix
       """
        return self.get_val(model)


class SMTIpPrefixList(SMTObject):
    """
    Synthesis list of IP Prefixes (AND)
    """

    def __init__(self, name, prefix_list, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param prefix_list: IpPrefixlist object
        :param context: SMTContext
        """
        assert isinstance(prefix_list, IpPrefixList)
        self.name = name
        self.prefix_list = prefix_list
        self.ctx = context

        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}

        self._smt_matches = []
        for i, prefix in enumerate(self.prefix_list.networks):
            name = '%s_%d' % (self.name, i)
            smt = SMTIpPrefix(name=name, prefix=prefix, context=self.ctx)
            self._smt_matches.append(smt)
        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized list of Prefixes for this match
        :param model: Z3 model
        :return: list of Community
        """
        return [smt.get_val(model) for smt in self._smt_matches]

    def is_concrete(self):
        """
        Return true if concrete Prefix object defined
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
        prefixes = self.get_val(model)
        return IpPrefixList(name=self.prefix_list.name,
                            access=self.prefix_list.access,
                            networks=prefixes)


class SMTTrueMatch(SMTObject):
    """
    Special Match, that is True for all
    """
    def __init__(self):
        self.match_fun = lambda x: True

    def is_concrete(self):
        return True

    def get_val(self, model):
        return True

    def get_config(self, model):
        return None


class SMTMatch(SMTObject):
    """
    A single match is OR between a list of the same object type
    """

    def __init__(self, name, match, context):
        self.name = name
        self.match = match
        self.ctx = context
        self.constraints = []
        self.smts = []
        self._is_concrete = False
        self.match_dispatch = {
            MatchCommunitiesList: self._match_comm,
            MatchIpPrefixListList: self._match_ip,
            OrOp: self._match_or,
            type(None): self._none_match,
        }
        self.match_fun = self.match_dispatch[type(match)](match)

    def is_concrete(self):
        return self._is_concrete

    def _none_match(self, match):
        self.match_fun = lambda x: True

    def _match_comm(self, match):
        name = "%s_comm_list" % self.name
        self.smts = [SMTCommunityList(name, match.match, self.ctx)]
        self.constraints.extend(self.smts[0].constraints)
        self._is_concrete = self.smts[0].is_concrete()
        return self.smts[0].match_fun

    def _match_ip(self, match):
        name = "%s_ip_list" % self.name
        self.smts = [SMTIpPrefixList(name, match.match, self.ctx)]
        self.constraints.extend(self.smts[0].constraints)
        self._is_concrete = self.smts[0].is_concrete()
        return self.smts[0].match_fun

    def _match_or(self, match):
        matches = []
        is_concrete = True
        for i, value in enumerate(match.values):
            name = "%s_or_%d_" % (self.name, i)
            new_match = SMTMatch(name, value, self.ctx)
            match_func = new_match.match_fun
            constraints = new_match.constraints
            matches.append(match_func)
            self.constraints.extend(constraints)
            self.smts.append(new_match)
            if not new_match.is_concrete():
                is_concrete = False
        self._is_concrete = is_concrete
        match_func = lambda x: z3.Or(*[m(x) for m in matches])
        return match_func

    def get_val(self, model):
        if len(self.smts) == 1:
            return self.smts[0].get_val(model)
        return [smt.get_val(model) for smt in self.smts]

    def _get_single_config(self, smt, model):
        config = smt.get_config(model)
        if isinstance(self.match, MatchCommunitiesList):
            return MatchCommunitiesList(config)
        elif isinstance(self.match, MatchIpPrefixListList):
            return MatchIpPrefixListList(config)
        return config

    def get_config(self, model):
        if isinstance(self.match, OrOp):
            return [smt.get_config(model) for smt in self.smts]
        return self._get_single_config(self.smts[0], model)


class SMTMatches(SMTObject):
    """
    A multiple matches with AND operator
    """

    def __init__(self, name, matches, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param matches: List of Match objects
        :param context: SMTContext
        """
        self.name = name
        self.matches = matches
        self.ctx = context
        self.constraints = []
        self.boxes = []
        self.match_fun = self._load_matches()

    def _load_matches(self):
        if len(self.matches) == 0:
            box = SMTTrueMatch()
            self.boxes.append(box)
        for i, match in enumerate(self.matches):
            name = "%s_and_%d_" % (self.name, i)
            box = SMTMatch(name=name, match=match, context=self.ctx)
            self.constraints.extend(box.constraints)
            self.boxes.append(box)
        return lambda x: z3.And([box.match_fun(x) for box in self.boxes])

    def is_concrete(self):
        return [] == [box.is_concrete() for box in self.boxes if not box.is_concrete()]

    def get_val(self, model):
        return [m.get_val(model) for m in self.boxes]

    def get_config(self, model):
        ret = [m.get_config(model) for m in self.boxes]
        if ret == [None]:
            return []
        return ret


class SMTAction(SMTObject):
    """A parent class for Action that changes route attributes"""

    def get_new_context(self):
        """
        Return a new contex with the new function that
        changed the route attributes based on the action.
        """
        raise NotImplementedError()


class SMTSetLocalPref(SMTAction):
    """
    Set the Local Pref for a route
    """

    def __init__(self, name, localpref, match, context):
        """
        :param name: a unique name to generate the SMT vars and fun
        :param localpref: int or VALUENOTSET
        :param match: and SMTObject with a match_fun
        :param context: SMTContext
        """
        assert localpref == VALUENOTSET or isinstance(localpref, int)
        assert isinstance(match, SMTObject)
        self.name = name
        self._localpref = localpref
        self.match = match
        self.constraints = []
        self.ctx = context
        self.action_val = None
        self.action_fun = None
        self.prev_action_fun = self.ctx.local_pref_fun
        self._load_action()

    def _load_action(self):
        self.action_fun = z3.Function("%s_set_localpref_fun" % self.name,
                                      self.ctx.announcement_sort,
                                      z3.IntSort())
        self.action_val = z3.Const('%s_localpref_val' % self.name, z3.IntSort())
        if self._localpref != VALUENOTSET:
            self.constraints.append(self.action_val == self._localpref)
        else:
            self.constraints.append(self.action_val > 0)

        for val in self.ctx.announcements_vars:
            c = self.action_fun(val) == z3.If(self.match.match_fun(val) == True,
                                              self.action_val,
                                              self.prev_action_fun(val))
            self.constraints.append(c)

        return self.action_fun

    def is_concrete(self):
        # TODO: concerte values for Actions
        return False

    def get_val(self, model):
        if self._localpref != VALUENOTSET:
            return self._localpref
        localpref = model.eval(self.action_val)
        localpref = localpref.as_long()
        return localpref

    def get_config(self, model):
        val = self.get_val(model)
        return ActionSetLocalPref(val)

    def get_new_context(self):
        ctx = SMTContext(
            announcements=self.ctx.announcements,
            announcements_vars=self.ctx.announcements_vars,
            announcement_sort=self.ctx.announcement_sort,
            communities_fun=self.ctx.communities_fun,
            prefixes_vars=self.ctx.prefixes_vars,
            prefix_sort=self.ctx.prefix_sort,
            prefix_fun=self.ctx.prefix_fun,
            local_pref_fun=self.action_fun,
            route_denied_fun=self.ctx.route_denied_fun
        )
        return ctx


class SMTSetCommunity(SMTAction):
    """
    Set a community value of a route
    """

    def __init__(self, name, communities, additive, match, context):
        """
        :param name: z3 var name
        :param communities: list of Community
        :param additive: if False, all the other communities will be overriden
        :param match: SMTObject with match_fun
        :param context: SMTContext
        """
        assert isinstance(communities, Iterable)
        for comm in communities:
            assert isinstance(comm, Community)
        assert isinstance(match, SMTObject)
        self.name = name
        self._communities = communities
        self.match = match
        self.additive = additive
        self.constraints = []
        self.ctx = context
        self.prev_action_fun = self.ctx.communities_fun
        self.new_comm_fun = {}
        self._load_action()

    def _load_action(self):
        ann_sort = self.ctx.announcement_sort
        match_fun = self.match.match_fun

        def get_prev(comm):
            """Get the community function from the previous context"""
            if self.additive:
                return self.prev_action_fun[comm]
            else:
                # Only override communities that matches
                return lambda x: z3.If(match_fun(x) == True,
                                       False,
                                       self.prev_action_fun[comm](x))

        def get_new_community(comm):
            """Synthesize new community"""
            name = "%s_set_comm_%s_fun" % (self.name, comm.name)
            fun = z3.Function(name, ann_sort, z3.BoolSort())
            name = '%s_%s_Tmp' % (self.name, comm.name)
            tmp = z3.Const(name, ann_sort)
            prev = get_prev(comm)
            if comm not in self._communities:
                return prev
            c = z3.ForAll(
                [tmp],
                fun(tmp) == z3.If(match_fun(tmp) == True, True, prev(tmp))
            )
            self.constraints.append(c)
            return fun

        #def syn_new_community(n, not_set_vals):
        #    f_name = '%s_%s_Synthesize_Comm_Match' % (self.name, n)
        #    fun = z3.Function(f_name, ann_sort, z3.BoolSort())
        #    c_name = '%s_%s_Selected_Comm_Match' % (self.name, n)
        #    syn_index = z3.Const(c_name, z3.IntSort())
        #    syn_map = {}
        #    constrains = []
        #    for i, community in enumerate(sorted(not_set_vals)):
        #        # TODO: there are some room for partial eval
        #        tmp = z3.Const('%s_%s_Tmp%d' % (self.name, n, i), ann_sort)
        #        syn_map[i] = community
        #        prev = get_prev(community)
        #        constrains.append(
        #            z3.And(
        #                z3.If(
        #                    syn_index == i,
        #                    z3.ForAll(
        #                        [tmp],
        #                        fun(tmp) == z3.If(match_fun(tmp), True, prev(tmp))),
        #                    z3.ForAll(
        #                        [tmp],
        #                        fun(tmp) == prev(tmp)
        #                    ))))
        #        self.new_comm_fun[community] = lambda x: z3.If(syn_index == i, fun(x), prev(x))
        #    self.constraints.append(z3.Or(*constrains))
        #    return (fun, syn_index, syn_map)
        #
        #not_set_vals = [comm for comm in self.prev_action_fun
        #                if comm not in self._communities]

        self.synthesized_communities = []
        for n, community in enumerate(self._communities):
            if community != VALUENOTSET:
                self.new_comm_fun[community] = get_new_community(community)
                self.synthesized_communities.append(community)
            #else:
            #new_fun, syn_index, syn_map = syn_new_community(n, not_set_vals)
            #self.synthesized_communities.append((syn_index, syn_map))
        # Fill remaining communities
        for community in self.prev_action_fun:
            if community not in self.new_comm_fun:
                self.new_comm_fun[community] = get_prev(community)

    def is_concrete(self):
        return False

    def get_val(self, model):

        if VALUENOTSET not in self._communities:
            return self._communities
        vals = []
        for val in self.synthesized_communities:
            if isinstance(val, tuple):
                syn_index, syn_map = val
                index = model.eval(syn_index).as_long()
                print syn_map
                val = syn_map[index]
                vals.append(val)
            else:
                vals.append(val)
        return vals

    def get_config(self, model):
        val = self.get_val(model)
        return ActionSetCommunity(val)

    def get_new_context(self):
        ctx = SMTContext(
            announcements=self.ctx.announcements,
            announcements_vars=self.ctx.announcements_vars,
            announcement_sort=self.ctx.announcement_sort,
            communities_fun=self.new_comm_fun,
            prefixes_vars=self.ctx.prefixes_vars,
            prefix_sort=self.ctx.prefix_sort,
            prefix_fun=self.ctx.prefix_fun,
            local_pref_fun=self.ctx.local_pref_fun,
            route_denied_fun=self.ctx.route_denied_fun
        )
        return ctx


class SMTActions(SMTAction):
    """Synthesize list of actions"""

    def __init__(self, name, match, actions, context):
        self.name = name
        self.match = match
        self.actions = actions
        self.ctx = context
        self.action_dispatch = {
            ActionSetLocalPref: self._set_localpref,
            ActionSetCommunity: self._set_community,
        }
        self.boxes = []
        self.constraints = []
        prev_ctx = self.ctx
        for i, action in enumerate(self.actions):
            new_name = "%s_%d" % (self.name, i)
            fun = self.action_dispatch[type(action)]
            box = fun(name=new_name, action=action, context=prev_ctx)
            prev_ctx = box.get_new_context()
            self.boxes.append(box)
            self.constraints.extend(box.constraints)
        self._new_context = prev_ctx

    def is_concrete(self):
        return [] == [b for b in self.boxes if b.is_concrete() is False]

    def get_val(self, model):
        return [b.get_val(model) for b in self.boxes]

    def get_config(self, model):
        return [b.get_config(model) for b in self.boxes]

    def get_new_context(self):
        return  self._new_context

    def _set_localpref(self, name, action, context):
        return SMTSetLocalPref(name=name, localpref=action.value,
                               match=self.match, context=context)

    def _set_community(self, name, action, context):
        return SMTSetCommunity(name=name, communities=action.communities,
                               match=self.match, additive=action.additive,
                               context=context)


class SMTRouteMapLine(SMTAction):
    """Synthesize one RouteMapLine"""

    def __init__(self, name, line, context):
        """
        :param name: name for z3 vars
        :param line: RouteMapLine
        :param context: SMTContext
        """
        self.name = name
        self.ctx = context
        self.line = line
        self.match_constraints = []
        self.action_constraints = []
        self.matches = SMTMatches(name="m_%s" % name,
                                  matches=line.matches, context=context)
        self.match_constraints.extend(self.matches.constraints)
        # No need to apply the actions if the route is dropped
        if line.access != Access.deny:
            self.actions = SMTActions(name="a_%s" % name, match=self.matches,
                                      actions=line.actions, context=context)
            self.action_constraints.extend(self.actions.constraints)
        self._load()

    def _load(self):
        access = self.line.access
        tmp = z3.Const('%s_tmp' % self.name, self.ctx.announcement_sort)
        prev = self.ctx.route_denied_fun
        fun = z3.Function('%s_deny' % self.name, self.ctx.announcement_sort, z3.BoolSort())
        self.route_denied_fun = fun
        if access in [Access.permit, Access.deny]:
            val = True if access == Access.deny else False
        else:
            val = z3.Const('%s_route_denied' % self.name, z3.BoolSort())
        self.access_val = val
        self.match_constraints.append(
            z3.ForAll(
                [tmp],
                fun(tmp) == z3.If(self.matches.match_fun(tmp) == True,
                                  val, prev(tmp))))

    def get_access(self, model):
        """Get the synthesized Access (permit or deny"""
        if isinstance(self.access_val, bool):
            denied = self.access_val
        else:
            denied = z3.is_true(model.eval(self.access_val))
        access = Access.deny if denied else Access.permit
        return access

    def get_val(self, model):
        access = self.get_access(model)
        return (access, self.matches.get_val(model), self.actions.get_val(model))

    def is_concrete(self):
        return self.matches.is_concrete() and self.actions.is_concrete()

    def get_config(self, model):
        return RouteMapLine(
            matches=self.matches.get_config(model),
            actions=self.actions.get_config(model),
            access=self.get_access(model),
            lineno=self.line.lineno)

    def get_new_context(self):
        ctx = self.actions.get_new_context()
        ctx.route_denied_fun = self.route_denied_fun
        return ctx


class SMTRouteMap(SMTAction):
    """Synthesize RouteMap"""

    def __init__(self, name, route_map, context):
        self.name = name
        self.route_map = route_map
        self.ctx = context
        self.boxes = []
        self.constraints = []
        for i, line in enumerate(self.route_map.lines):
            name = "%s_line_%s" % (self.name, i)
            box = SMTRouteMapLine(name, line=line, context=self.ctx)
            self.boxes.append(box)
        self._load()
        self.get_new_context()

    def _get_match_i(self, i, var):
        """
        Get the match in order
        For a match to be checked, all the previous lines should be false
        """
        if i == 0:
            return self.boxes[i].matches.match_fun(var) == True
        else:
            matches = []
            for box in self.boxes[:i]:
                matches.append(box.matches.match_fun(var) == False)
            matches.append(self.boxes[i].matches.match_fun(var) == True)
            return z3.And(*matches)

    def _load(self):
        tmp = z3.Const('%s_tmp' % self.name, self.ctx.announcement_sort)
        for i, box in enumerate(self.boxes):
            self.constraints.extend(box.match_constraints)
            match_fun = self._get_match_i(i, tmp)
            constraint = z3.ForAll(
                [tmp],
                z3.Implies(
                    match_fun,
                    z3.And(*box.action_constraints)
                ))
            self.constraints.append(constraint)

    def is_concrete(self):
        return False

    def _get_fun_ctx_i(self, ctx_name, key_name, var, index):
        if index >= len(self.boxes):
            match_fun = lambda x: True
            ctx = self.ctx
        else:
            match_fun = self._get_match_i(index, var)
            ctx = self.boxes[index].get_new_context()

        if key_name is None:
            prev = getattr(ctx, ctx_name)
        else:
            prev = getattr(ctx, ctx_name)[key_name]

        if index < len(self.boxes):
            else_ctx = self._get_fun_ctx_i(ctx_name, key_name, var, index + 1)
        else:
            else_ctx = None

        if else_ctx is None:
            return prev(var)
        return z3.If(match_fun == True,
                     prev(var),
                     else_ctx)

    def _get_new_fun(self, ctx_name):
        fun = getattr(self.ctx, ctx_name)
        # If the function is a dict (like communities)
        # Then load each key separately
        if isinstance(fun, dict):
            new_dict = {}
            for key in fun.keys():
                key_name = getattr(key, 'name', key)
                fun_name = 'new_%s_%s' % (self.name, key_name)
                tmp_name = '%s_%s_tmp' % (self.name, key_name)
                new_fun = z3.Function(fun_name, fun[key].domain(0), fun[key].range())
                tmp = z3.Const(tmp_name, self.ctx.announcement_sort)
                constraint = z3.ForAll(
                    [tmp],
                    new_fun(tmp) == self._get_fun_ctx_i(ctx_name, key, tmp, 0)
                )
                self.constraints.append(constraint)
                new_dict[key] = new_fun
            return new_dict
        # Create new function
        fun_name = 'new_%s_%s' % (self.name, str(fun))
        tmp_name = '%s_%s_tmp' % (self.name, str(fun))
        tmp = z3.Const(tmp_name, self.ctx.announcement_sort)
        new_fun = z3.Function(fun_name, fun.domain(0), fun.range())
        constraint = z3.ForAll(
            [tmp],
            new_fun(tmp) == self._get_fun_ctx_i(ctx_name, None, tmp, 0)
        )
        self.constraints.append(constraint)
        return new_fun

    def get_new_context(self):
        announcements = self.ctx.announcements
        announcements_vars = self.ctx.announcements_vars
        announcement_sort = self.ctx.announcement_sort
        communities_fun = self._get_new_fun('communities_fun')
        prefixes_vars = self.ctx.prefixes_vars
        prefix_sort = self.ctx.prefix_sort
        prefix_fun = self._get_new_fun('prefix_fun')
        local_pref_fun = self._get_new_fun('local_pref_fun')
        route_denied_fun = self._get_new_fun('route_denied_fun')

        ctx = SMTContext(
            announcements=announcements,
            announcements_vars=announcements_vars,
            announcement_sort=announcement_sort,
            communities_fun=communities_fun,
            prefixes_vars=prefixes_vars,
            prefix_sort=prefix_sort,
            prefix_fun=prefix_fun,
            local_pref_fun=local_pref_fun,
            route_denied_fun=route_denied_fun,
        )
        return ctx

    def get_config(self, model):
        lines = [b.get_config(model) for b in self.boxes]
        new_map = RouteMap(name=self.route_map.name,
                           lines=lines)
        return new_map

    def get_val(self, model):
        return [b.get_val(model) for b in self.boxes]
