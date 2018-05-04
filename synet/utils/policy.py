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

from tekton.bgp import Access
from tekton.bgp import Announcement
from tekton.bgp import ActionSetCommunity
from tekton.bgp import ActionSetLocalPref
from tekton.bgp import ActionSetNextHop
from tekton.bgp import Community
from tekton.bgp import CommunityList
from tekton.bgp import IpPrefixList
from tekton.bgp import MatchCommunitiesList
from tekton.bgp import MatchIpPrefixListList
from tekton.bgp import MatchNextHop
from tekton.bgp import RouteMap
from tekton.bgp import RouteMapLine

from synet.utils.smt_context import SMTASPathLenWrapper
from synet.utils.smt_context import SMTASPathWrapper
from synet.utils.smt_context import SMTCommunityWrapper
from synet.utils.smt_context import SMTContext
from synet.utils.smt_context import SMTLocalPrefWrapper
from synet.utils.smt_context import SMTNexthopWrapper
from synet.utils.smt_context import SMTOriginWrapper
from synet.utils.smt_context import SMTPeerWrapper
from synet.utils.smt_context import SMTPermittedWrapper
from synet.utils.smt_context import SMTPrefixWrapper
from synet.utils.smt_context import SMTSymbolicObject
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import is_symbolic
from synet.utils.smt_context import VALUENOTSET

# Hack for interface change
from tekton.bgp import Announcement as FullAnnouncement
from functools import partial
Announcement = partial(FullAnnouncement, med=100)


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"

AndOp = namedtuple('AndOp', ['values'])
OrOp = namedtuple('OrOp', ['values'])


class SMTObject(SMTSymbolicObject):
    """SMT Object Abstraction"""

    def get_var(self):
        """
        Get the value for the given ann_var
        (applies partial eval whenever possible
        """
        raise NotImplementedError()

    def get_value(self):
        """Return a concrete variable"""
        raise NotImplementedError()

    def get_config(self):
        """Return the synthesized configurations"""
        raise NotImplementedError()


class SMTSynMatchVal(SMTObject):
    """
    Synthesis Match on one value in the Announcement
    """

    def __init__(self, name, match_value, value_ctx, model_eval_fun,
                 config_class, custom_match_gen=None):
        """
        :param name: name to be used with z3 variables
        :param match_value: the value to match on (Concrete or VALUENOTSET)
        :param value_ctx: SMTValueWrapper
        :param model_eval_fun: (model, value) -> value
        :param config_class: value-> config
        :param custom_match_gen: generate custom match function (often not needed)
        """
        self.name = name
        self._match_value = match_value
        self.value_ctx = value_ctx
        self.constraints = {}
        self.match_synthesized = None
        self.match_syn_map = {}
        self.model_eval_fun = model_eval_fun
        self.config_class = config_class
        self._model = None
        self.var_constraints = {}
        if is_empty(self._match_value):
            self._match_value = None
        elif not is_symbolic(self._match_value) and self.value_ctx.range_map:
            self._match_value = self.value_ctx.range_map[self._match_value]
        if custom_match_gen:
            self.match_fun = custom_match_gen()
        else:
            self.match_fun = self._gen_match_func()

    def _gen_match_func(self):
        """Generate a match_fun(ann_var) -> true or false"""
        if self.is_concrete_match():
            match_fun = lambda x: self.value_ctx.get_var(x) == self._match_value
        else:
            f_name = '%s_syn_match' % self.name
            match_fun = z3.Function(f_name,
                                    self.value_ctx.announcement_sort,
                                    z3.BoolSort())
            syn_constraints = None
            if self.value_ctx.range_map is None:
                var_name = '%s_syn_value' % self.name
                var = z3.Const(var_name, self.value_ctx.fun_range_sort)
                constrain = [match_fun(tmp) == (self.value_ctx.get_var(tmp) == var)
                             for tmp in self.value_ctx.ann_var_iter()]
                self._match_value = var
                syn_constraints = z3.And(*constrain)
            else:
                # This is a bit tricky to handle
                # In case the self._match_value match is EMPTY,
                # the the synthesizer is free to choose any value
                # in range such that it's true for all Anns in the context
                c_name = '%s_sel_match' % self.name
                self.match_synthesized = z3.Const(c_name, z3.IntSort())
                self.match_syn_map = {}
                constrains = []
                for index, key in enumerate(sorted(self.value_ctx.range_map.values())):
                    # TODO: there are some room for partial eval
                    self.match_syn_map[index] = key
                    constrain = [match_fun(tmp) == (self.value_ctx.get_var(tmp) == key)
                                 for tmp in self.value_ctx.ann_var_iter()]
                    first = [self.match_synthesized == index]
                    constrain = first + constrain
                    constrains.append(z3.And(*[constrain]))
                syn_constraints = z3.Or(*constrains)
            const_name = "%s_match_constraints" % self.name
            self.constraints[const_name] = syn_constraints
        return match_fun

    def is_match(self, ann_var):
        """
        Evaluate ann_var and return True if it matches match_value
        This works only with concrete matches or when model is provided
        """
        if self.is_concrete():
            return self.value_ctx.get_var(ann_var) == self._match_value
        elif self._model:
            return z3.is_true(
                self.value_ctx.get_var(ann_var) == self._match_value)
        else:
            raise RuntimeError("Cannot used is_match without a Z3 model")

    def get_var(self):
        if self.match_synthesized is None:
            ret = self._match_value
        else:
            assert self._model is not None
            index = self._model.eval(self.match_synthesized).as_long()
            ret = self.match_syn_map[index]
        if is_symbolic(ret) and self._model is not None:
            return self.model_eval_fun(self._model, ret)
        return ret

    def get_value(self):
        var = self.get_var()
        return self.value_ctx.get_value_of_var(var)

    def is_concrete_match(self):
        """Return true if the value matched on is concrete"""
        if self._match_value is None:
            return False
        if self.value_ctx.range_map:
            return self._match_value in self.value_ctx.range_map.values()
        return not is_symbolic(self._match_value)

    def is_concrete(self):
        """
        Return if both the match value and the values in the Ann
        are both concrete
        """
        if not self.is_concrete_match():
            return False
        return self.value_ctx.is_range_concrete()

    def get_config(self):
        """Return the synthesized configurations"""
        if not self.is_concrete():
            assert self._model is not None
        return self.config_class(self.get_value())

    def get_var_constraints(self, ann_var, get_prev):
        return []

    def get_general_constraints(self, get_prev):
        return self.constraints

    def add_constraints(self, solver, track):
        for name, const in self.get_general_constraints(True).iteritems():
            solver.assert_and_track(const, name)
        return self.constraints

    def set_model(self, model):
        self._model = model

    def __str__(self):
        return "<%s(%s)>" % (self.__class__.__name__, self.name)

    def __repr__(self):
        return self.__str__()


class SMTCommunity(SMTSynMatchVal):
    """
    Match on a community value in the Announcement.
    """

    def __init__(self, name, community, context):
        """
        :param name: name to be used with z3 var names
        :param community: Community or VALUENOTSET
        :param context: SMTContext
        """
        # This is a tricky one!!!
        # If community value is concrete then it's easy normal value
        # If community value is not known then we're trying to find a community
        #  s.t it's true for all announcements in the context
        if community in context.communities_ctx:
            val_ctx = context.communities_ctx[community]
            self.community = community
            self._custom = False

            def model_eval(model, val):
                """Evaluate community"""
                return community if z3.is_true(model.eval(val)) else None

            super(SMTCommunity, self).__init__(
                name=name,
                match_value=True,
                value_ctx=val_ctx,
                model_eval_fun=model_eval,
                config_class=lambda x: community)
        else:
            assert is_empty(community) or is_symbolic(community)
            model_eval = lambda model, val: z3.is_true(model.eval(val))
            self.context = context
            val_ctx = context.communities_ctx.values()[0]
            self.community = community
            self._custom = False
            super(SMTCommunity, self).__init__(
                name=name,
                match_value=True,
                value_ctx=val_ctx,
                model_eval_fun=model_eval,
                config_class=lambda x: community,
                custom_match_gen=self._gen_match_func_com
            )
            self._custom = True

    def is_concrete_match(self):
        return False if self._custom else \
            super(SMTCommunity, self).is_concrete_match()

    def _gen_match_func_com(self):
        # This is a bit tricky to handle
        # In case the community match is EMPTY,
        #     the the synthesizer is free to choose any community
        # We create a dummy function such that it ranges and values maps exactly to
        # one or more assigned communities.
        # Then we enumerate the communities,
        # and the variable self.match_synthesized tells us which one that successfully
        # mapped to our dummy match
        f_name = '%s_syn_match' % self.name
        match_fun = z3.Function(f_name, self.context.announcement_sort, z3.BoolSort())
        c_name = '%s_sel_match' % self.name
        self.match_synthesized = z3.Const(c_name, z3.IntSort())
        self.match_syn_map = {}
        constrains = []
        for index, community in enumerate(sorted(self.context.communities_ctx)):
            ctx = self.context.communities_ctx[community]
            self.match_syn_map[index] = community
            constrain = [match_fun(tmp) == (ctx.get_var(tmp) == True)
                         for tmp in ctx.ann_var_iter()]
            first = [self.match_synthesized == index]
            constrain = first + constrain
            constrains.append(z3.And(*[constrain]))
        syn_constraints = z3.Or(*constrains)

        const_name = "%s_match_constraints" % self.name
        self.constraints[const_name] = syn_constraints
        return match_fun

    def get_var(self):
        val = super(SMTCommunity, self).get_var()
        if self._custom is True:
            return val
        return val

    def get_value(self):
        val = super(SMTCommunity, self).get_var()
        if self._custom is True:
            return val
        return self.community if val else None

    def get_config(self):
        return self.get_value()


class SMTIpPrefix(SMTSynMatchVal):
    """
    Synthesis one IPPrefix
    TODO: Support longest prefix matching
    """

    def __init__(self, name, prefix, context):
        """
        :param name: name for z3 variables
        :param prefix: IPPrefix or VALUENOTSET
        :param context: SMTContext
        """
        self.ctx = context
        super(SMTIpPrefix, self).__init__(
            name=name,
            match_value=prefix,
            value_ctx=context.prefix_ctx,
            model_eval_fun=lambda model, val: model.eval(val),
            config_class=lambda x: x)


class SMTNextHop(SMTSynMatchVal):
    """
    Synthesis one NextHop match
    """

    def __init__(self, name, next_hop, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param next_hop: NextHop or VALUENOTSET
        :param context: SMTContext
        """
        self.ctx = context
        super(SMTNextHop, self).__init__(
            name=name,
            match_value=next_hop,
            value_ctx=context.next_hop_ctx,
            model_eval_fun=lambda model, val: model.eval(val),
            config_class=lambda x: MatchNextHop(x)
        )


class SMTLocalPref(SMTSynMatchVal):
    """
    Synthesis one Local Pref
    """

    def __init__(self, name, local_pref, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param local_pref: Int or VALUENOTSET
        :param context: SMTContext
        """
        self.ctx = context
        super(SMTLocalPref, self).__init__(
            name=name,
            match_value=local_pref,
            value_ctx=context.local_pref_ctx,
            model_eval_fun=lambda model, val: model.eval(val).as_long(),
            config_class=lambda x: x
        )


class SMTCommunityList(SMTSynMatchVal):
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
        self.constraints = {}
        self.match_synthesized = None
        self.match_syn_map = {}
        self._smt_matches = []
        self._model = None
        for i, comm in enumerate(self._community_list.communities):
            name = '%s_%d' % (self.name, i)
            smt = SMTCommunity(name=name, community=comm, context=self.ctx)
            self._smt_matches.append(smt)
        self.match_fun = self._gen_match_func()

    def _gen_match_func(self):
        # Add constraints
        dist = [smt.match_synthesized for smt in
                self._smt_matches if smt.match_synthesized is not None]
        if len(dist) > 1:
            unique_c = z3.Distinct(dist)
            name = "%s_unique" % self.name
            self.constraints[name] = unique_c
        fun = lambda x: z3.And(*[smt.match_fun(x) for smt in self._smt_matches])
        return fun

    def is_match(self, ann_var):
        if self.is_concrete():
            return [] == [s for s in self._smt_matches if s.is_match(ann_var) == False]
        else:
            raise RuntimeError("Cannot used is_match without a Z3 model")

    def get_var(self):
        """
        Return the synthesized list of Communities for this match
        :param model: Z3 model
        :return: list of Community
        """
        return [smt.get_var() for smt in self._smt_matches]

    def get_value(self):
        """
        Return the synthesized list of Communities for this match
        :param model: Z3 model
        :return: list of Community
        """
        return [smt.get_value() for smt in self._smt_matches]

    def is_concrete(self):
        for smt in self._smt_matches:
            if not smt.is_concrete():
                return False
        return True

    def get_config(self):
        """
        Get the synthesized CommunityList
        :param model: Z3 model
        :return: CommunityList
        """
        communities = self.get_value()
        return CommunityList(list_id=self._community_list.list_id,
                             access=self._community_list.access,
                             communities=communities)

    def set_model(self, model):
        for smt in self._smt_matches:
            smt.set_model(model)
        self._model = model

    def add_constraints(self, solver, track):
        constraints = {}
        for smt in self._smt_matches:
            constraints.update(smt.add_constraints(solver, track))
        for name, constraint in self.constraints.iteritems():
            solver.assert_and_track(constraint, name)
        return constraints


class SMTIpPrefixList(SMTSynMatchVal):
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

        self.constraints = {}
        self.match_synthesized = None
        self.match_syn_map = {}
        self._model = None
        self._smt_matches = []
        for i, prefix in enumerate(self.prefix_list.networks):
            name = '%s_%d' % (self.name, i)
            smt = SMTIpPrefix(name=name, prefix=prefix, context=self.ctx)
            self._smt_matches.append(smt)
        self.match_fun = self._gen_match_func()

    def is_match(self, ann_var):
        for s in self._smt_matches:
            if s.is_match(ann_var):
                return True
        return False

    def set_model(self, model):
        self._model = model
        for smt in self._smt_matches:
            smt.set_model(model)

    def get_var(self):
        return [smt.get_var() for smt in self._smt_matches]

    def get_value(self):
        return [smt.get_value() for smt in self._smt_matches]

    def is_concrete(self):
        for smt in self._smt_matches:
            if not smt.is_concrete():
                return False
        return True

    def _gen_match_func(self):

        dist = [smt.match_synthesized for smt in
                self._smt_matches if smt.match_synthesized is not None]
        if len(dist) > 1:
            unique_c = z3.Distinct(dist)
            name = '%s_unique' % self.name
            self.constraints[name] = unique_c
        fun = lambda x: z3.And(*[smt.match_fun(x) for smt in self._smt_matches])
        return fun

    def get_config(self):
        prefixes = self.get_value()
        return IpPrefixList(name=self.prefix_list.name,
                            access=self.prefix_list.access,
                            networks=prefixes)

    def add_constraints(self, solver, track):
        constraints = {}
        for smt in self._smt_matches:
            constraints.update(smt.add_constraints(solver, track))
        for name, constraint in self.constraints.iteritems():
            solver.assert_and_track(constraint, name)
            constraints[name] = constraint
        return constraints


class SMTTrueMatch(SMTSynMatchVal):
    """
    Special Match, that is True for all
    """

    def __init__(self):
        self.match_fun = lambda x: True
        self._model = None
        self.name = 'TrueMatch'

    def is_match(self, ann_var):
        return True

    def is_concrete(self):
        return True

    def get_value(self):
        return True

    def get_var(self):
        return True

    def get_config(self):
        return None

    def add_constraints(self, solver, track):
        return {}

    def set_model(self, model):
        self._model = model

    def get_general_constraints(self, get_prev):
        return {}

    def get_var_constraints(self, ann_var, get_prev):
        return []


class SMTMatch(SMTSynMatchVal):
    """
    A single match is OR between a list of the same object type
    """

    def __init__(self, name, match, context):
        self.name = name
        self.match = match
        self.ctx = context
        self.constraints = {}
        self.smts = []
        self._is_concrete = False
        self.match_dispatch = {
            MatchCommunitiesList: self._match_comm,
            MatchIpPrefixListList: self._match_ip,
            MatchNextHop: self._match_next_hop,
            OrOp: self._match_or,
            type(None): self._none_match,
        }
        self._model = None
        self.match_fun = self.match_dispatch[type(match)](match)

    def is_concrete(self):
        for smt in self.smts:
            if not smt.is_concrete():
                return False
        return True

    def is_match(self, ann_var):
        if self.is_concrete():
            return [] == [s for s in self.smts if s.is_match(ann_var) == False]
        elif self._model:
            return z3.is_true(z3.And(*[s.match_fun(ann_var) == True for s in self.smts]))
        else:
            raise RuntimeError("Cannot used is_match without a Z3 model")

    def _none_match(self, match):
        self.match_fun = lambda x: True

    def _match_comm(self, match):
        name = "%s_comm_list" % self.name
        self.smts = [SMTCommunityList(name, match.match, self.ctx)]
        self._is_concrete = self.smts[0].is_concrete()
        return self.smts[0].match_fun

    def _match_ip(self, match):
        name = "%s_ip_list" % self.name
        self.smts = [SMTIpPrefixList(name, match.match, self.ctx)]
        self._is_concrete = self.smts[0].is_concrete()
        return self.smts[0].match_fun

    def _match_next_hop(self, match):
        name = "%s_next_hop" % self.name
        self.smts = [SMTNextHop(name, match.match, self.ctx)]
        self._is_concrete = self.smts[0].is_concrete()
        return self.smts[0].match_fun

    def _match_or(self, match):
        matches = []
        is_concrete = True
        for i, value in enumerate(match.values):
            name = "%s_or_%d_" % (self.name, i)
            new_match = SMTMatch(name, value, self.ctx)
            match_func = new_match.match_fun
            matches.append(match_func)
            self.smts.append(new_match)
            if not new_match.is_concrete():
                is_concrete = False
        self._is_concrete = is_concrete
        match_func = lambda x: z3.Or(*[m(x) for m in matches])
        return match_func

    def get_value(self):
        ret = [smt.get_value() for smt in self.smts]
        if len(self.smts) == 1:
            return ret[0]
        return ret

    def get_var(self):
        if len(self.smts) == 1:
            return self.smts[0].get_var()
        return [smt.get_var() for smt in self.smts]

    def _get_single_config(self, smt):
        config = smt.get_config()
        if isinstance(self.match, MatchCommunitiesList):
            return MatchCommunitiesList(config)
        elif isinstance(self.match, MatchIpPrefixListList):
            return MatchIpPrefixListList(config)
        return config

    def get_config(self):
        if isinstance(self.match, OrOp):
            return [smt.get_config() for smt in self.smts]
        return self._get_single_config(self.smts[0])

    def set_model(self, model):
        for smt in self.smts:
            smt.set_model(model)

    def add_constraints(self, solver, track):
        constraints = {}
        for smt in self.smts:
            constraints.update(smt.add_constraints(solver, track))
        for name, constraint in self.constraints.iteritems():
            solver.assert_and_track(constraint, name)
            constraints[name] = constraint
        return constraints


class SMTMatches(SMTSynMatchVal):
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
        self.boxes = []
        self._model = None
        self.match_fun = self._load_matches()

    def _load_matches(self):
        if not self.matches:
            box = SMTTrueMatch()
            self.boxes.append(box)
        for i, match in enumerate(self.matches):
            name = "%s_and_%d_" % (self.name, i)
            box = SMTMatch(name=name, match=match, context=self.ctx)
            self.boxes.append(box)
        return lambda x: z3.And([box.match_fun(x) for box in self.boxes])

    def is_concrete(self):
        for box in self.boxes:
            if not box.is_concrete():
                return False
        return True

    def is_match(self, ann_var):
        if self.is_concrete():
            return [] == [s for s in self.boxes if not s.is_match(ann_var)]
        elif self._model:
            return z3.is_true(z3.And(*[s.match_fun(ann_var) == True for s in self.boxes]))
        else:
            raise RuntimeError("Cannot used is_match without a Z3 model")

    def get_var(self):
        return [m.get_var() for m in self.boxes]

    def get_value(self):
        return [m.get_value() for m in self.boxes]

    def get_config(self):
        ret = [m.get_config() for m in self.boxes if not isinstance(m, SMTTrueMatch)]
        if ret == [None]:
            return []
        return ret

    def set_model(self, model):
        for box in self.boxes:
            box.set_model(model)

    def add_constraints(self, solver, track):
        constraints = {}
        for box in self.boxes:
            constraints.update(box.add_constraints(solver, track))
        return constraints


class SMTAction(SMTObject):
    """A parent class for Action that changes route attributes"""

    def get_new_context(self):
        """
        Return a new contex with the new function that
        changed the route attributes based on the action.
        """
        raise NotImplementedError()


class SMTSetVal(SMTAction):
    """
    Set a value in the Announcement
    """

    def __init__(self, name, value, match, value_ctx, config_class,
                 model_val, context):
        assert isinstance(match, SMTObject)
        self.name = name
        self._value = value
        self.match = match
        self.value_ctx = value_ctx
        self.config_class = config_class
        self.model_val = model_val
        self.ctx = context

        self.constraints = {}
        self._action_val = None
        self._action_fun = None
        self._action_fun_used = False
        self._model = None
        self._load_action()

    @property
    def action_fun(self):
        """
        Return the actions z3 function
        This will trigger adding more constraints
        """
        self._action_fun_used = True
        return self._action_fun

    def _load_action(self):
        domain = self.value_ctx.announcement_sort
        f_range = self.value_ctx.fun_range_sort
        val_name = '%s_val' % self.name
        new_var = z3.Const(val_name, f_range)
        f_name = "%s_fun" % self.name
        self._action_fun = z3.Function(f_name, domain, f_range)

        # If value is empty, convert it to z3 variable
        if is_empty(self._value):
            self._action_val = new_var
        else:
            if is_symbolic(self._value):
                self._action_val = self._value
            else:
                # The variable is a string and there is a z3 object for it
                if self.value_ctx.range_map is not None:
                    self._action_val = self.value_ctx.range_map[self._value]
                else:
                    # The variable is not mapped to z3 objects
                    # (for example local prefs)
                    self._action_val = self._value

    def is_concrete(self):
        return self.match.is_concrete() and not is_empty(self._value)

    def get_var(self):
        return self._action_val

    def get_value(self):
        var = self.get_var()
        if self._model and is_symbolic(var):
            return self.model_val(self._model, var)
        return self.value_ctx.get_value_of_var(var)

    def set_model(self, model):
        self._model = model

    def add_constraints(self, solver, track):
        if not self._action_fun_used:
            return {}
        if self.match.is_concrete():
            for ann_var in self.value_ctx.ann_var_iter():
                name = "%s_set_action_val_%s" % (self.name, str(ann_var))
                if self.match.is_match(ann_var):
                    val = self.get_var()
                else:
                    val = self.value_ctx.get_var(ann_var)
                constraint = self._action_fun(ann_var) == val
                self.constraints[name] = constraint
        else:
            #tmp = z3.Const("%s_tmp" % self.name, self.value_ctx.announcement_sort)
            #constraint = z3.ForAll(
            #    [tmp],
            #    self._action_fun(tmp) == z3.If(
            #        self.match.match_fun(tmp) == True,
            #        self._action_val,
            #        self.value_ctx.get_var(tmp)
            #    ))

            check = z3.And([self.match.match_fun(tmp) == True for tmp in self.value_ctx.announcements_var_map])
            constraint = [
                self._action_fun(tmp) == z3.If(
                    check == True,
                    self._action_val,
                    self.value_ctx.get_var(tmp)) for tmp in self.value_ctx.announcements_var_map]

            name = "%s_set_action_val_all" % self.name
            self.constraints[name] = z3.And(constraint)
        for name, constraint in self.constraints.iteritems():
            solver.assert_and_track(constraint, name)
        return self.constraints

    def get_config(self):
        val = self.get_value()
        return self.config_class(val)

    def __str__(self):
        return "<%s(%s)>" % (self.__class__.__name__, self.name)

    def __repr__(self):
        return self.__str__()


class SMTSetLocalPref(SMTSetVal):
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
        assert is_empty(localpref) or isinstance(localpref, int)

        def eval_model(model, var):
            try:
                return model.eval(var).as_long()
            except Exception as err:
                return 100
                #raise RuntimeError("Couldn't eval %s: %s" % (var, err.message))

        super(SMTSetLocalPref, self).__init__(
            name=name,
            value=localpref,
            match=match,
            value_ctx=context.local_pref_ctx,
            config_class=ActionSetLocalPref,
            model_val=eval_model,
            context=context
        )

    def get_new_context(self):
        name = '%s_ctx' % self.name
        announcements = {}
        announcements_map = {}
        ann_var_map = {}
        if self.match.is_concrete():
            for ann_name, ann_var in self.ctx.announcements_map.iteritems():
                ann = self.ctx.announcements[ann_name]
                if self.match.is_match(ann_var):
                    new_ann = ann.copy()
                    new_ann.local_pref = self.get_var()
                else:
                    new_ann = ann
                announcements[ann_name] = new_ann
                announcements_map[ann_name] = ann_var
                ann_var_map[ann_var] = new_ann
        else:
            for ann_name, ann_var in self.ctx.announcements_map.iteritems():
                ann = self.ctx.announcements[ann_name]
                new_ann = ann.copy()
                new_ann.local_pref = z3.If(
                    self.match.match_fun(ann_var) == True,
                    self.get_value(),
                    self.value_ctx.get_value(ann_var)
                )
                announcements[ann_name] = new_ann
                announcements_map[ann_name] = ann_var
                ann_var_map[ann_var] = new_ann

        def transformer(ann_var, ann):
            """Transformer for the new context"""
            return ann_var_map[ann_var]

        new_local_pref_fun = z3.Function(
            "%s_local_pref" % name, self.ctx.announcement_sort, z3.IntSort())

        prefix_ctx = self.ctx.prefix_ctx.get_new_context(
            name='%s_subset_prefix' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.prefix_ctx._fun,
            transformer=transformer)
        peer_ctx = self.ctx.peer_ctx.get_new_context(
            '%s_subset_peer' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.peer_ctx._fun,
            transformer=transformer)
        origin_ctx = self.ctx.origin_ctx.get_new_context(
            '%s_subset_origin' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.origin_ctx._fun,
            transformer=transformer)
        as_path_ctx = self.ctx.as_path_ctx.get_new_context(
            '%s_subset_as_path' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        as_path_len_ctx = self.ctx.as_path_len_ctx.get_new_context(
            '%s_subset_as_path_len' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        next_hop_ctx = self.ctx.next_hop_ctx.get_new_context(
            '%s_subset_next_hop' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.next_hop_ctx._fun,
            transformer=transformer)
        local_pref_ctx = self.ctx.local_pref_ctx.get_new_context(
            '%s_subset_local_pref' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=new_local_pref_fun,
            transformer=transformer)
        permitted_ctx = self.ctx.permitted_ctx.get_new_context(
            '%s_subset_permitted' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.permitted_ctx._fun,
            transformer=transformer)
        communities_ctx = {}
        for community, community_ctx in self.ctx.communities_ctx.iteritems():
            communities_ctx[community] = community_ctx.get_new_context(
                '%s_subset_community_%s' % (name, community.name),
                ann_vars=ann_var_map.keys(),
                new_fun=community_ctx._fun,
                transformer=transformer)

        ctx = self.ctx.get_new_context(
            name=name,
            announcements=announcements,
            announcements_map=announcements_map,
            prefix_ctx=prefix_ctx,
            peer_ctx=peer_ctx,
            origin_ctx=origin_ctx,
            as_path_ctx=as_path_ctx,
            as_path_len_ctx=as_path_len_ctx,
            next_hop_ctx=next_hop_ctx,
            local_pref_ctx=local_pref_ctx,
            communities_ctx=communities_ctx,
            permitted_ctx=permitted_ctx,
            prev_ctxs=[self.ctx] + self.ctx.prev_ctxs)
        return ctx


class SMTSetNextHop(SMTSetVal):
    """
    Set the next hop
    """

    def __init__(self, name, next_hop, match, context):
        """
        :param name: a unique name to generate the SMT vars and fun
        :param next_hop: NextHop VALUENOTSET
        :param match: and SMTObject with a match_fun
        :param context: SMTContext
        """
        super(SMTSetNextHop, self).__init__(
            name=name,
            value=next_hop,
            match=match,
            value_ctx=context.next_hop_ctx,
            config_class=ActionSetNextHop,
            model_val=lambda model, var: model.eval(var),
            context=context
        )

    def get_new_context(self):
        name = '%s_ctx' % self.name
        announcements = {}
        announcements_map = {}
        ann_var_map = {}
        if self.match.is_concrete():
            for ann_name, ann_var in self.ctx.announcements_map.iteritems():
                ann = self.ctx.announcements[ann_name]
                if self.match.is_match(ann_var):
                    new_ann = ann.copy()
                    new_ann.next_hop = self.get_var()
                else:
                    new_ann = ann
                announcements[ann_name] = new_ann
                announcements_map[ann_name] = ann_var
                ann_var_map[ann_var] = new_ann
        else:
            for ann_name, ann_var in self.ctx.announcements_map.iteritems():
                ann = self.ctx.announcements[ann_name]
                new_ann = ann.copy()
                new_ann.next_hop = z3.If(
                    self.match.match_fun(ann_var) == True,
                    self.get_value(),
                    self.value_ctx.get_value(ann_var)
                )
                announcements[ann_name] = new_ann
                announcements_map[ann_name] = ann_var
                ann_var_map[ann_var] = new_ann

        def transformer(ann_var, ann):
            """Transformer for the new context"""
            return ann_var_map[ann_var]

        new_next_hop_fun = z3.Function(
            "%s_next_hop_fun" % name, self.ctx.announcement_sort, z3.IntSort())

        prefix_ctx = self.ctx.prefix_ctx.get_new_context(
            name='%s_subset_prefix' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.prefix_ctx._fun,
            transformer=transformer)
        peer_ctx = self.ctx.peer_ctx.get_new_context(
            '%s_subset_peer' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.peer_ctx._fun,
            transformer=transformer)
        origin_ctx = self.ctx.origin_ctx.get_new_context(
            '%s_subset_origin' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.origin_ctx._fun,
            transformer=transformer)
        as_path_ctx = self.ctx.as_path_ctx.get_new_context(
            '%s_subset_as_path' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        as_path_len_ctx = self.ctx.as_path_len_ctx.get_new_context(
            '%s_subset_as_path_len' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        next_hop_ctx = self.ctx.next_hop_ctx.get_new_context(
            '%s_subset_next_hop' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=new_next_hop_fun,
            transformer=transformer)
        local_pref_ctx = self.ctx.local_pref_ctx.get_new_context(
            '%s_subset_local_pref' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.local_pref_ctx,
            transformer=transformer)
        permitted_ctx = self.ctx.permitted_ctx.get_new_context(
            '%s_subset_permitted' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.permitted_ctx._fun,
            transformer=transformer)
        communities_ctx = {}
        for community, community_ctx in self.ctx.communities_ctx.iteritems():
            communities_ctx[community] = community_ctx.get_new_context(
                '%s_subset_community_%s' % (name, community.name),
                ann_vars=ann_var_map.keys(),
                new_fun=community_ctx._fun,
                transformer=transformer)

        ctx = self.ctx.get_new_context(
            name=name,
            announcements=announcements,
            announcements_map=announcements_map,
            prefix_ctx=prefix_ctx,
            peer_ctx=peer_ctx,
            origin_ctx=origin_ctx,
            as_path_ctx=as_path_ctx,
            as_path_len_ctx=as_path_len_ctx,
            next_hop_ctx=next_hop_ctx,
            local_pref_ctx=local_pref_ctx,
            communities_ctx=communities_ctx,
            permitted_ctx=permitted_ctx,
            prev_ctxs=[self.ctx] + self.ctx.prev_ctxs)
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
        if is_empty(additive):
            additive = z3.Const("%s_additive" % name, z3.BoolSort())
        assert isinstance(match, SMTObject)
        self.name = name
        self._communities = communities
        self.match = match
        self.additive = additive
        self.constraints = {}
        self.ctx = context
        self.prev_comm_ctx = self.ctx.communities_ctx
        self._new_comm_vars = dict([(comm, {}) for comm in self.prev_comm_ctx.keys()])
        self._load_action()

    def is_concrete_value(self):
        if is_empty(self.additive):
            return False
        for comm in self._communities:
            if is_empty(comm):
                return False
        return True

    def is_concrete(self):
        return self.match.is_concrete() and self.is_concrete_value()

    def _load_action(self):
        def new_var(comm, ann_var):
            name = '%s_new_var_%s_%s' % (self.name, comm.name, str(ann_var))
            return z3.Const(name, z3.BoolSort())

        def get_prev(comm, ann_var):
            ret_val = None
            if self.match.is_concrete() is True:
                if self.match.is_match(ann_var):
                    if comm in self._communities:
                        ret_val = True
                    else:
                        if is_symbolic(self.additive):
                            ret_val = new_var(comm, ann_var)
                            const = z3.If(
                                self.additive == True,
                                self.prev_comm_ctx[comm].get_var(ann_var),
                                False)
                            name = '%s_new_var_%s_%s_S' % (self.name, comm.name, str(ann_var))
                            self.constraints[name] = ret_val == const
                        else:
                            ret_val = self.prev_comm_ctx[comm].get_var(ann_var) if self.additive else False
                elif not self.match.is_match(ann_var):
                    ret_val = self.prev_comm_ctx[comm].get_var(ann_var)
            else:
                if comm in self._communities:
                    ret_val = new_var(comm, ann_var)
                    const = z3.If(
                        self.match.match_fun(ann_var) == True,
                        True,
                        self.prev_comm_ctx[comm].get_var(ann_var))
                    name = '%s_new_var_%s_%s_S' % (self.name, comm.name, str(ann_var))
                    self.constraints[name] = ret_val == const
                else:
                    ret_val = new_var(comm, ann_var)
                    const = z3.If(
                        self.match.match_fun(ann_var) == True,
                        z3.If(
                            self.additive == True,
                            self.prev_comm_ctx[comm].get_var(ann_var),
                            False),
                        self.prev_comm_ctx[comm].get_var(ann_var))
                    name = '%s_new_var_%s_%s_S' % (self.name, comm.name, str(ann_var))
                    self.constraints[name] = ret_val == const
            return ret_val

        for comm in self.prev_comm_ctx.keys():
            for ann_var in self.prev_comm_ctx[comm].announcements_var_map.keys():
                self._new_comm_vars[comm][ann_var] = get_prev(comm, ann_var)

    def get_value(self):
        if VALUENOTSET not in self._communities:
            return self._communities
        vals = []
        for val in self.synthesized_communities:
            if isinstance(val, tuple):
                syn_index, syn_map = val
                index = self._model.eval(syn_index).as_long()
                val = syn_map[index]
                vals.append(val)
            else:
                vals.append(val)
        return vals

    def get_config(self):
        val = self.get_value()
        return ActionSetCommunity(val)

    def add_constraints(self, solver, track):
        for name, c in self.constraints.iteritems():
            solver.assert_and_track(c, name)
        return self.constraints

    def set_model(self, model):
        self._model = model

    def get_new_context(self):
        name = '%s_ctx' % self.name
        announcements = {}
        announcements_map = {}
        ann_var_map = {}

        for ann_name, ann_var in self.ctx.announcements_map.iteritems():
            ann = self.ctx.announcements[ann_name]
            new_ann = ann.copy()
            for comm in self._new_comm_vars:
                new_ann.communities[comm] = self._new_comm_vars[comm][ann_var]

            announcements[ann_name] = new_ann
            announcements_map[ann_name] = ann_var
            ann_var_map[ann_var] = new_ann

        def transformer(ann_var, ann):
            """Transformer for the new context"""
            return ann_var_map[ann_var]

        prefix_ctx = self.ctx.prefix_ctx.get_new_context(
            name='%s_subset_prefix' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.prefix_ctx._fun,
            transformer=transformer)
        peer_ctx = self.ctx.peer_ctx.get_new_context(
            '%s_subset_peer' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.peer_ctx._fun,
            transformer=transformer)
        origin_ctx = self.ctx.origin_ctx.get_new_context(
            '%s_subset_origin' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.origin_ctx._fun,
            transformer=transformer)
        as_path_ctx = self.ctx.as_path_ctx.get_new_context(
            '%s_subset_as_path' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        as_path_len_ctx = self.ctx.as_path_len_ctx.get_new_context(
            '%s_subset_as_path_len' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        next_hop_ctx = self.ctx.next_hop_ctx.get_new_context(
            '%s_subset_next_hop' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.next_hop_ctx._fun,
            transformer=transformer)
        local_pref_ctx = self.ctx.local_pref_ctx.get_new_context(
            '%s_subset_local_pref' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.local_pref_ctx._fun,
            transformer=transformer)
        permitted_ctx = self.ctx.permitted_ctx.get_new_context(
            '%s_subset_permitted' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.permitted_ctx._fun,
            transformer=transformer)
        communities_ctx = {}
        for community, community_ctx in self.ctx.communities_ctx.iteritems():
            new_comm_fun = z3.Function(
                "%s_comm_%s_fun" % (name, community.name),
                self.ctx.announcement_sort, z3.IntSort())
            communities_ctx[community] = community_ctx.get_new_context(
                '%s_subset_community_%s' % (name, community.name),
                ann_vars=ann_var_map.keys(),
                new_fun=new_comm_fun,
                transformer=transformer)

        ctx = self.ctx.get_new_context(
            name=name,
            announcements=announcements,
            announcements_map=announcements_map,
            prefix_ctx=prefix_ctx,
            peer_ctx=peer_ctx,
            origin_ctx=origin_ctx,
            as_path_ctx=as_path_ctx,
            as_path_len_ctx=as_path_len_ctx,
            next_hop_ctx=next_hop_ctx,
            local_pref_ctx=local_pref_ctx,
            communities_ctx=communities_ctx,
            permitted_ctx=permitted_ctx,
            prev_ctxs=[self.ctx] + self.ctx.prev_ctxs)
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
            ActionSetNextHop: self._set_next_hop,
            SMTSetPermitted: self._set_access,
        }
        self.boxes = []
        self.constraints = {}
        prev_ctx = self.ctx
        for i, action in enumerate(self.actions):
            new_name = "%s_%s_%d" % (self.name, action.__class__.__name__, i)
            fun = self.action_dispatch[type(action)]
            box = fun(name=new_name, action=action, context=prev_ctx)
            prev_ctx = box.get_new_context()
            self.boxes.append(box)
        self._new_context = prev_ctx

    def is_concrete(self):
        return [] == [b for b in self.boxes if b.is_concrete() is False]

    def get_value(self):
        ret_values = []
        for box in self.boxes:
            val = box.get_value()
            if not isinstance(box, SMTSetPermitted):
                ret_values.append(val)
        return ret_values

    def get_var(self):
        ret_vars = []
        for box in self.boxes:
            var = box.get_var()
            if not isinstance(box, SMTSetPermitted):
                ret_vars.append(var)
        return ret_vars

    def get_config(self):
        return [b.get_config() for b in self.boxes
                if not isinstance(b, SMTSetPermitted)]

    def get_general_constraints(self, get_prev):
        constraints = {}
        constraints.update(self.constraints)
        if get_prev:
            for box in self.boxes:
                consts = box.get_general_constraints(get_prev=True)
                for name, const in consts:
                    assert name not in constraints
                constraints.update(consts)
        return constraints

    def get_var_constraints(self, ann_var, get_prev):
        return []

    def add_constraints(self, solver, track):
        constraints = {}
        constraints.update(self.constraints)
        for box in self.boxes:
            const = box.add_constraints(solver, track)
            constraints.update(const)
        return constraints

    def set_model(self, model):
        for box in self.boxes:
            box.set_model(model)

    def get_new_context(self):
        return self._new_context

    def _set_localpref(self, name, action, context):
        return SMTSetLocalPref(name=name, localpref=action.value,
                               match=self.match, context=context)

    def _set_next_hop(self, name, action, context):
        return SMTSetNextHop(name=name, next_hop=action.value,
                               match=self.match, context=context)

    def _set_access(self, name, action, context):
        return action

    def _set_community(self, name, action, context):
        return SMTSetCommunity(name=name, communities=action.communities,
                               match=self.match, additive=action.additive,
                               context=context)


class SMTSetPermitted(SMTAction):
    """
    Set the permitted field in the announcement
    Only overrides when access is set to Access.deny
    """

    def __init__(self, name, access, match, context):
        """
        :param name: a unique name to generate the SMT vars and fun
        :param localpref: int or VALUENOTSET
        :param match: and SMTObject with a match_fun
        :param context: SMTContext
        """
        assert isinstance(match, SMTObject)
        self.ctx = context
        if is_symbolic(access) or is_empty(access):
            value = access
        else:
            value = True if access == Access.permit else False

        def config_class(val):
            if isinstance(val, bool):
                comp = val
            else:
                comp = z3.is_true(val)
            if comp:
                return Access.permit
            else:
                return Access.deny

        self.name = name
        self._value = value
        self.match = match
        self.value_ctx = context.permitted_ctx
        self.config_class = config_class
        self.model_val = lambda model, var: z3.is_true(model.eval(var))
        self.ctx = context

        self.constraints = {}
        self._action_val = None
        self._action_fun = None
        self._action_fun_used = False
        self._model = None
        self._load_action()

    @property
    def action_fun(self):
        """
        Return the actions z3 function
        This will trigger adding more constraints
        """
        self._action_fun_used = True
        return self._action_fun

    def _load_action(self):
        domain = self.value_ctx.announcement_sort
        f_range = self.value_ctx.fun_range_sort
        val_name = '%s_val' % self.name
        new_var = z3.Const(val_name, f_range)
        f_name = "%s_fun" % self.name
        self._action_fun = z3.Function(f_name, domain, f_range)
        # If value is empty, convert it to z3 variable
        if is_empty(self._value):
            self._action_val = new_var
        else:
            if is_symbolic(self._value):
                self._action_val = self._value
            else:
                # The variable is a string and there is a z3 object for it
                if self.value_ctx.range_map is not None:
                    self._action_val = self.value_ctx.range_map[self._value]
                else:
                    # The variable is not mapped to z3 objects
                    # (for example local prefs)
                    self._action_val = self._value

    def is_concrete(self):
        return self.match.is_concrete() and not is_empty(self._value)

    def get_var(self):
        return self._action_val

    def get_value(self):
        var = self.get_var()
        if self._model and is_symbolic(var):
            return self.model_val(self._model, var)
        return self.value_ctx.get_value_of_var(var)

    def set_model(self, model):
        self._model = model

    def add_constraints(self, solver, track):
        if not self._action_fun_used:
            return {}
        if self.match.is_concrete():
            for ann_var in self.value_ctx.ann_var_iter():
                name = "%s_set_action_val_%s" % (self.name, str(ann_var))
                if self.match.is_match(ann_var):
                    val = self.get_var()
                else:
                    val = self.value_ctx.get_var(ann_var)
                constraint = self._action_fun(ann_var) == val
                self.constraints[name] = constraint
        else:
            #tmp = z3.Const("%s_tmp" % self.name, self.value_ctx.announcement_sort)
            #constraint = z3.ForAll(
            #    [tmp],
            #    self._action_fun(tmp) == z3.If(
            #        z3.And(self.match.match_fun(tmp) == True, self._action_val == False),
            #        False,
            #        self.value_ctx.get_var(tmp)
            #    ))

            check = z3.And([
                self.match.match_fun(tmp) == True for tmp in self.value_ctx.announcements_var_map])
            constraint = [
                self._action_fun(tmp) == z3.If(
                    check == True,
                    False,
                    self.value_ctx.get_var(tmp)) for tmp in self.value_ctx.announcements_var_map]

            name = "%s_set_action_val_all" % self.name
            self.constraints[name] = z3.And(constraint)
        for name, constraint in self.constraints.iteritems():
            solver.assert_and_track(constraint, name)
        return self.constraints

    def get_config(self):
        val = self.get_value()
        return self.config_class(val)

    def __str__(self):
        return "<%s(%s)>" % (self.__class__.__name__, self.name)

    def __repr__(self):
        return self.__str__()

    def get_new_context(self):
        name = '%s_ctx' % self.name
        announcements = {}
        announcements_map = {}
        ann_var_map = {}
        permitted_value = self.get_var()

        def get_permited(ann_var, premitted_var, original, match):
            if match.is_concrete() and not is_symbolic(premitted_var):
                if permitted_value:
                    ret = original
                else:
                    ret = False if match.is_match(ann_var) else original
            else:
                ret = z3.If(
                    z3.And(
                        match.match_fun(ann_var) == True,
                        permitted_value == False),
                    False,
                    original)
            return ret

        for ann_name, ann_var in self.ctx.announcements_map.iteritems():
            ann = self.ctx.announcements[ann_name]
            new_ann = ann.copy()
            new_ann.permitted = get_permited(ann_var, permitted_value, ann.permitted, self.match)
            announcements[ann_name] = new_ann
            announcements_map[ann_name] = ann_var
            ann_var_map[ann_var] = new_ann


        def transformer(ann_var, ann):
            """Transformer for the new context"""
            return ann_var_map[ann_var]

        new_permitted = z3.Function(
            "%s_permitted" % name, self.ctx.announcement_sort, z3.BoolSort())

        prefix_ctx = self.ctx.prefix_ctx.get_new_context(
            name='%s_subset_prefix' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.prefix_ctx._fun,
            transformer=transformer)
        peer_ctx = self.ctx.peer_ctx.get_new_context(
            '%s_subset_peer' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.peer_ctx._fun,
            transformer=transformer)
        origin_ctx = self.ctx.origin_ctx.get_new_context(
            '%s_subset_origin' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.origin_ctx._fun,
            transformer=transformer)
        as_path_ctx = self.ctx.as_path_ctx.get_new_context(
            '%s_subset_as_path' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        as_path_len_ctx = self.ctx.as_path_len_ctx.get_new_context(
            '%s_subset_as_path_len' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.as_path_len_ctx._fun,
            transformer=transformer)
        next_hop_ctx = self.ctx.next_hop_ctx.get_new_context(
            '%s_subset_next_hop' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.next_hop_ctx._fun,
            transformer=transformer)
        local_pref_ctx = self.ctx.local_pref_ctx.get_new_context(
            '%s_subset_local_pref' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=self.ctx.local_pref_ctx._fun,
            transformer=transformer)
        permitted_ctx = self.ctx.permitted_ctx.get_new_context(
            '%s_subset_permitted' % name,
            ann_vars=ann_var_map.keys(),
            new_fun=new_permitted,
            transformer=transformer)
        communities_ctx = {}
        for community, community_ctx in self.ctx.communities_ctx.iteritems():
            communities_ctx[community] = community_ctx.get_new_context(
                '%s_subset_community_%s' % (name, community.name),
                ann_vars=ann_var_map.keys(),
                new_fun=community_ctx._fun,
                transformer=transformer)

        ctx = self.ctx.get_new_context(
            name=name,
            announcements=announcements,
            announcements_map=announcements_map,
            prefix_ctx=prefix_ctx,
            peer_ctx=peer_ctx,
            origin_ctx=origin_ctx,
            as_path_ctx=as_path_ctx,
            as_path_len_ctx=as_path_len_ctx,
            next_hop_ctx=next_hop_ctx,
            local_pref_ctx=local_pref_ctx,
            communities_ctx=communities_ctx,
            permitted_ctx=permitted_ctx,
            prev_ctxs=[self.ctx] + self.ctx.prev_ctxs)
        return ctx


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
        self.constraints = {}

        self.matches = SMTMatches(name="m_%s" % name,
                                  matches=line.matches, context=context)

        self.permitted_action = SMTSetPermitted(name='%s_access' % self.name,
                                                match=self.matches,
                                                access=line.access, context=self.ctx)

        # No need to apply the actions if the route is dropped
        if line.access == Access.deny:
            self.actions = SMTActions(name="Action_%s" % name, match=self.matches,
                                      actions=[self.permitted_action],
                                      context=self.ctx)
        else:
            self.actions = SMTActions(name="Action_%s" % name, match=self.matches,
                                      actions=[self.permitted_action] + line.actions,
                                      context=self.ctx)
        self.new_ctx = self.actions.get_new_context()

    def get_value(self):
        return (self.permitted_action.get_value(),
                self.matches.get_value(),
                self.actions.get_value())

    def get_var(self):
        return (self.permitted_action.get_var(),
                self.matches.get_var(),
                self.actions.get_var())

    def set_model(self, model):
        self.permitted_action.set_model(model)
        self.matches.set_model(model)
        self.actions.set_model(model)

    def is_concrete(self):
        return self.matches.is_concrete() and self.actions.is_concrete()

    def get_config(self):
        return RouteMapLine(
            matches=self.matches.get_config(),
            actions=self.actions.get_config(),
            access=self.permitted_action.get_config(),
            lineno=self.line.lineno)

    def get_new_context(self):
        return self.new_ctx

    def add_constraints(self, solver, track):
        constraints = {}
        constraints.update(self.constraints)
        constraints.update(self.permitted_action.add_constraints(solver, track))
        constraints.update(self.actions.add_constraints(solver, track))
        constraints.update(self.matches.add_constraints(solver, track))
        return constraints

    def __str__(self):
        return "<Line(%s, %s)>" % (self.name, self.line.lineno)


class SMTRouteMap(SMTAction):
    """Synthesize RouteMap"""

    def __init__(self, name, route_map, context):
        self.name = name
        self.route_map = route_map
        self.ctx = context
        self.boxes = []
        self.constraints = []
        self.var_constraints = []
        for i, line in enumerate(self.route_map.lines):
            name = "%s_line_%s" % (self.name, line.lineno)
            box = SMTRouteMapLine(name, line=line, context=self.ctx)
            self.boxes.append(box)

    def add_constraints(self, solver, track):
        for box in self.boxes:
            box.add_constraints(solver, track)

    def is_concrete(self):
        return False

    def _recursive_if(self, ann_var, box_ctxs, value_ctx_name, dict_key=None):
        box, ctx = box_ctxs[0]
        value_ctx = getattr(ctx, value_ctx_name)
        if isinstance(value_ctx, dict):
            value_ctx = value_ctx[dict_key]
        if len(box_ctxs) == 1:
            var_name = "%s_%s_%s_unbonded" % (self.name, str(ann_var), value_ctx.name)
            var = z3.Const(var_name, value_ctx.fun_range_sort)
            else_var = var
        else:
            else_var = self._recursive_if(ann_var, box_ctxs[1:], value_ctx_name, dict_key)
        if ann_var not in value_ctx.announcements_var_map:
            ret_val = else_var
        elif box.matches.is_concrete():
            ret_val = value_ctx.get_var(ann_var) if box.matches.is_match(ann_var) else else_var
        else:
            ret_val = z3.If(box.matches.match_fun(ann_var), value_ctx.get_var(ann_var), else_var)
        return ret_val

    def get_new_context(self):
        ann_var_map = {}
        announcements = {}
        announcements_vars = {}

        vals = []
        all_communities = self.ctx.communities_ctx.keys()
        for box in self.boxes:
            vals.append((box, box.get_new_context()))
        for ann_name, ann_var in self.ctx.announcements_map.iteritems():
            prefix = self._recursive_if(ann_var, vals, 'prefix_ctx')
            peer = self._recursive_if(ann_var, vals, 'peer_ctx')
            origin = self._recursive_if(ann_var, vals, 'origin_ctx')
            as_path = self._recursive_if(ann_var, vals, 'as_path_ctx')
            as_path_len = self._recursive_if(ann_var, vals, 'as_path_len_ctx')
            next_hop = self._recursive_if(ann_var, vals, 'next_hop_ctx')
            local_pref = self._recursive_if(ann_var, vals, 'local_pref_ctx')
            communities = {}
            for community in all_communities:
                communities[community] = self._recursive_if(ann_var, vals, 'communities_ctx', community)
            permitted = self._recursive_if(ann_var, vals, 'permitted_ctx')
            new_ann = Announcement(
                prefix=prefix,
                peer=peer,
                origin=origin,
                as_path=as_path,
                as_path_len=as_path_len,
                next_hop=next_hop,
                local_pref=local_pref,
                communities=communities,
                permitted=permitted,
            )
            ann_var_map[ann_var] = new_ann
            announcements[ann_name] = new_ann
            announcements_vars[ann_name] = ann_var

        ann_sort = self.ctx.announcement_sort

        prefix_sort = self.ctx.prefix_ctx.fun_range_sort
        prefix_map = self.ctx.prefix_ctx.range_map
        prefix_fun = z3.Function('%s_prefix_fun' % self.name, ann_sort, prefix_sort)

        peer_sort = self.ctx.peer_ctx.fun_range_sort
        peer_map = self.ctx.peer_ctx.range_map
        peer_fun = z3.Function('%s_peer_fun' % self.name, ann_sort, peer_sort)

        origin_sort = self.ctx.origin_ctx.fun_range_sort
        origin_map = self.ctx.origin_ctx.range_map
        origin_fun = z3.Function('%s_origin_fun' % self.name, ann_sort, origin_sort)

        as_path_sort = self.ctx.as_path_ctx.fun_range_sort
        as_path_map = self.ctx.as_path_ctx.range_map
        as_path_fun = z3.Function('%s_as_path_fun' % self.name, ann_sort, as_path_sort)

        as_path_len_sort = self.ctx.as_path_len_ctx.fun_range_sort
        as_path_len_fun = z3.Function('%s_as_path_len_fun' % self.name, ann_sort, as_path_len_sort)

        next_hop_sort = self.ctx.next_hop_ctx.fun_range_sort
        next_hop_map = self.ctx.next_hop_ctx.range_map
        next_hop_fun = z3.Function('%s_next_hop_fun' % self.name, ann_sort, next_hop_sort)

        local_pref_sort = self.ctx.local_pref_ctx.fun_range_sort
        local_pref_fun = z3.Function('%s_local_pref_fun' % self.name, ann_sort, local_pref_sort)

        permitted_sort = self.ctx.permitted_ctx.fun_range_sort
        permitted_fun = z3.Function('%s_permitted_fun' % self.name, ann_sort, permitted_sort)

        wprefix = SMTPrefixWrapper(
            '%s_prefix_ctx' % self.name, ann_sort, ann_var_map,
            prefix_fun, prefix_sort, prefix_map)

        wpeer = SMTPeerWrapper(
            '%s_peer_ctx' % self.name, ann_sort, ann_var_map,
            peer_fun, peer_sort, peer_map)

        worigin = SMTOriginWrapper(
            '%s_origin_ctx' % self.name, ann_sort, ann_var_map,
            origin_fun, origin_sort, origin_map)

        waspath = SMTASPathWrapper(
            '%s_aspath_ctx' % self.name, ann_sort, ann_var_map,
            as_path_fun, as_path_sort, as_path_map)

        waspathlen = SMTASPathLenWrapper(
            '%s_aspathlen_ctx' % self.name, ann_sort, ann_var_map,
            as_path_len_fun)

        wnext_hop = SMTNexthopWrapper(
            '%s_next_hop_ctx' % self.name, ann_sort, ann_var_map,
            next_hop_fun, next_hop_sort, next_hop_map)

        wlocalpref = SMTLocalPrefWrapper(
            '%s_local_pref_ctx' % self.name, ann_sort, ann_var_map,
            local_pref_fun)

        wpermitted = SMTPermittedWrapper(
            '%s_permitted_ctx' % self.name, ann_sort, ann_var_map,
            permitted_fun)

        wcommunities = {}
        for community in all_communities:
            name = community.name
            c_sort = self.ctx.as_path_len_ctx.fun_range_sort
            c_fun = z3.Function('%s_%s_com_fun' % (self.name, community.name), ann_sort, c_sort)

            wc1 = SMTCommunityWrapper(
                '%s_%s_ctx' % (self.name, name), community, ann_sort,
                ann_var_map, c_fun)
            wcommunities[community] = wc1

        ctx = SMTContext('%s_ctx' % self.name, announcements, announcements_vars, ann_sort,
                         wprefix, wpeer, worigin, waspath, waspathlen,
                         wnext_hop, wlocalpref, wcommunities, wpermitted, prev_ctxs=[self.ctx] + self.ctx.prev_ctxs)
        return ctx

    def get_config(self):
        lines = [b.get_config() for b in self.boxes]
        new_map = RouteMap(name=self.route_map.name,
                           lines=lines)
        return new_map

    def get_value(self):
        return [b.get_value() for b in self.boxes]

    def get_var(self):
        return [b.get_var() for b in self.boxes]

    def set_model(self, model):
        for box in self.boxes:
            box.set_model(model)
