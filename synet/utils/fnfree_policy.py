"""
Synthesize policies .. aka route maps for the moment
"""

from collections import Iterable
import copy
import functools
import itertools
import logging
import z3

from tekton.bgp import Access
from tekton.bgp import ActionSetASPath
from tekton.bgp import ActionSetASPathLen
from tekton.bgp import ActionSetMED
from tekton.bgp import ActionSetCommunity
from tekton.bgp import ActionSetLocalPref
from tekton.bgp import ActionSetNextHop
from tekton.bgp import ActionSetPeer
from tekton.bgp import ActionSetOne
from tekton.bgp import ActionSetPrefix
from tekton.bgp import ActionPermitted
from tekton.bgp import Announcement
from tekton.bgp import Community
from tekton.bgp import CommunityList
from tekton.bgp import Match
from tekton.bgp import MatchAsPath
from tekton.bgp import MatchAsPathLen
from tekton.bgp import MatchPeer
from tekton.bgp import MatchLocalPref
from tekton.bgp import MatchCommunitiesList
from tekton.bgp import MatchNextHop
from tekton.bgp import MatchIpPrefixListList
from tekton.bgp import MatchPermitted
from tekton.bgp import MatchMED
from tekton.bgp import MatchSelectOne
from tekton.bgp import IpPrefixList
from tekton.bgp import RouteMap
from tekton.bgp import RouteMapLine
from synet.utils.fnfree_smt_context import ASPATH_SORT
from synet.utils.fnfree_smt_context import BGP_ORIGIN_SORT
from synet.utils.fnfree_smt_context import PEER_SORT
from synet.utils.fnfree_smt_context import PREFIX_SORT
from synet.utils.fnfree_smt_context import NEXT_HOP_SORT
from synet.utils.fnfree_smt_context import SMTVar
from synet.utils.fnfree_smt_context import SolverContext
from synet.utils.fnfree_smt_context import is_symbolic
from synet.utils.fnfree_smt_context import is_empty
from synet.utils.fnfree_smt_context import decode_as_path
from synet.utils.fnfree_smt_context import desanitize_smt_name


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"

SELECTOR = {}


class SMTAbstractMatch(object):
    """Generic Match Class"""

    def is_match(self, announcement):
        """
        Returns a Var that is evaluated when partial evaluation is possible.
        Using this method on the same announcement multiple times generates
        redundant constraints and variables
        """
        raise NotImplementedError()


class SMTMatchAll(SMTAbstractMatch):
    """Matches all announcements regardless of their contents"""

    def __init__(self, ctx):
        self.ctx = ctx
        self.match_var = ctx.create_fresh_var(
            z3.BoolSort(ctx=self.ctx.z3_ctx), name_prefix='match_all_', value=True)

    def is_match(self, announcement):
        return self.match_var

    def get_config(self):
        return None


class SMTMatchNone(SMTAbstractMatch):
    """Does NOT match any announcement regardless of its contents"""

    def __init__(self, ctx):
        self.ctx = ctx
        self.match_var = ctx.create_fresh_var(
            z3.BoolSort(ctx=self.ctx.z3_ctx), name_prefix='match_none_', value=False)

    def is_match(self, announcement):
        return self.match_var


class SMTMatchAnd(SMTAbstractMatch):
    """Combine Matches in `Or` expression"""

    def __init__(self, matches, announcements, ctx):
        self.matches = matches
        self.announcements = announcements
        self.ctx = ctx
        self.matched_announcements = {}  # Cache evaluated announcements

    def is_match(self, announcement):
        # Check cache first
        # TODO partially evaluate short cuts
        if announcement not in self.matched_announcements:
            results = [match.is_match(announcement) for match in self.matches]
            is_concrete = all([result.is_concrete for result in results])
            shortcut = [result.get_value() for result in results if result.is_concrete]
            value = None
            if is_concrete:
                value = all([result.get_value() for result in results])
            elif shortcut and not all(shortcut):
                value = False
                is_concrete = True
            match_var = self.ctx.create_fresh_var(z3.BoolSort(ctx=self.ctx.z3_ctx), name_prefix='match_and_', value=value)
            if not is_concrete:
                tmp = [result.var == True for result in results if not result.is_concrete]
                tmp += [self.ctx.z3_ctx]
                constraint = z3.And(*tmp)
                self.ctx.register_constraint(
                    match_var.var == constraint, name_prefix='const_and_')
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]

    def __str__(self):
        return "SMTMatchAnd(%s)" % [str(m) for m in self.matches]

    def get_config(self):
        configs = [match.get_config() for match in self.matches]
        return [c for c in configs if c]


class SMTMatchOr(SMTAbstractMatch):
    """Combine Matches in Or expression"""

    def __init__(self, matches, announcements, ctx):
        """
        :param matches: List of SMTMatches
        :param announcements:
        :param ctx:
        """
        self.matches = matches
        self.announcements = announcements
        self.ctx = ctx
        self.matched_announcements = {}  # Cache evaluated announcements

    def is_match(self, announcement):
        # Check cache first
        # TODO partially evaluate short cuts
        if announcement not in self.matched_announcements:
            results = [match.is_match(announcement) for match in self.matches]
            is_concrete = all([result.is_concrete for result in results])
            shortcut = [result.get_value() for result in results if result.is_concrete]
            value = None
            if is_concrete:
                value = any([result.get_value() for result in results])
            elif shortcut and any(shortcut):
                value = True
                is_concrete = True
            match_var = self.ctx.create_fresh_var(
                z3.BoolSort(ctx=self.ctx.z3_ctx), name_prefix='match_or_', value=value)
            if not is_concrete:
                tmp = [result.var == True for result in results] + [self.ctx.z3_ctx]
                constraint = z3.Or(*tmp)
                self.ctx.register_constraint(
                    match_var.var == constraint, name_prefix='const_or_')
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]

    def __str__(self):
        return "SMTMatchOr(%s)" % self.matches

    def get_config(self):
        return [match.get_config() for match in self.matches]


class SMTMatchSelectOne(SMTAbstractMatch):
    """
    Chose a SINGLE match object to meet the requirements
    """

    def __init__(self, announcements, ctx, matches=None):
        """
        :param announcements:
        :param ctx:
        :param matches: List of SMTMatch objects to use one of them
                        if None, then all attributes are going to be used.
        """
        assert isinstance(ctx, SolverContext)
        assert announcements, 'Cannot match on empty announcements'
        self.announcements = announcements
        self.ctx = ctx
        self.matched_announcements = {}  # Cache evaluated announcements

        if not matches:
            # By default all attributes are allowed
            matches = []
            for attr in Announcement.attributes:
                if attr == 'communities':
                    for community in self.announcements[0].communities:
                        # Match only when community is set
                        match = attribute_match_factory(
                            community,
                            value=None,
                            announcements=self.announcements,
                            ctx=self.ctx)
                        matches.append(match)
                else:
                    # Symbolic match value
                    match = attribute_match_factory(
                        attr,
                        value=None,
                        announcements=self.announcements,
                        ctx=self.ctx)
                    matches.append(match)

        # Create map for the different matches
        self.matches = {}
        self.index_var = self.ctx.create_fresh_var(
            z3.IntSort(ctx=self.ctx.z3_ctx), name_prefix='SelectOne_index_')
        for index, match in enumerate(matches):
            self.matches[index] = match
        # Make index in the range of number of matches
        self.ctx.register_constraint(
            z3.And(
                self.index_var.var >= 0,
                self.index_var.var < index + 1, self.ctx.z3_ctx),
            name_prefix='SelectOne_index_range_')

    def _get_match(self, announcement, current_index=0):
        """Recursively construct a match"""
        if current_index not in self.matches:
            # Base case
            return False
            return z3.And(self.index_var.var == current_index, False, self.ctx.z3_ctx)
        is_match  = self.matches[current_index].is_match(announcement)
        if is_match.is_concrete:
            match_var = is_match.get_value()
        else:
            match_var = self.matches[current_index].is_match(announcement).var
        index_check = self.index_var.var == current_index
        next_attr = self._get_match(announcement, current_index + 1)
        return z3.If(index_check, match_var, next_attr, ctx=self.ctx.z3_ctx)

    def is_match(self, announcement):
        if announcement not in self.matched_announcements:
            var = self.ctx.create_fresh_var(z3.BoolSort(ctx=self.ctx.z3_ctx))
            self.matched_announcements[announcement] = var
            constraint = var.var == self._get_match(announcement)
            self.ctx.register_constraint(
                constraint, name_prefix='SelectOne_match_')
        return self.matched_announcements[announcement]

    def get_used_match(self):
        match = self.matches[self.index_var.get_value()]
        return match

    def get_config(self):
        if self.index_var.get_value() < 0:
            return None
        return self.get_used_match().get_config()


class SMTMatchAttribute(SMTAbstractMatch):
    """Match on a single attribute of announcement"""

    def __init__(self, attribute, value, announcements, ctx):
        """
        :param attribute: Must be in Announcement.attributes
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars
        """
        super(SMTMatchAttribute, self).__init__()
        assert isinstance(ctx, SolverContext)
        assert announcements, 'Cannot match on empty announcements'
        assert attribute in Announcement.attributes
        if value is None:
            asort = getattr(announcements[0], attribute).vsort
            value = ctx.create_fresh_var(
                asort,
                name_prefix='Match_attr_%s_' % attribute)
        assert isinstance(value, SMTVar)
        attr_sort = getattr(announcements[0], attribute).vsort
        err = "Type mismatch of attribute and value %s != %s" % (
            attr_sort, value.vsort)
        assert attr_sort == value.vsort, err
        self.attribute = attribute
        self.value = value
        self.announcements = announcements
        self.ctx = ctx
        self.matched_announcements = {}  # Cache evaluated announcements

    def is_match(self, announcement):
        attr = getattr(announcement, self.attribute)
        # Check cache first
        if announcement not in self.matched_announcements:
            constraint = attr.check_eq(self.value)
            value = None
            if not is_symbolic(constraint):
                value = constraint
            match_var = self.ctx.create_fresh_var(
                z3.BoolSort(ctx=self.ctx.z3_ctx),
                name_prefix='match_%s_var_' % self.attribute,
                value=value)
            if is_symbolic(constraint):
                self.ctx.register_constraint(
                    match_var.var == constraint,
                    name_prefix='const_match_%s_' % self.attribute)
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]

    def __str__(self):
        return "SMTMatchAttribute(attribute=%s, value=%s)" % (self.attribute, self.value)


class SMTMatchCommunity(SMTAbstractMatch):
    """Match if a single community value is set to True"""

    def __init__(self, community, value, announcements, ctx):
        """

        :param community:
        :param value: Optionally can be None, then set by default to True
        :param announcements:
        :param ctx:
        """
        assert isinstance(ctx, SolverContext)
        self.ctx = ctx
        assert announcements, "Cannot match on empty announcements"
        assert community in announcements[0].communities
        if not value:
            value = ctx.create_fresh_var(
                z3.BoolSort(ctx=self.ctx.z3_ctx),
                name_prefix='Match_Community_var_',
                value=True)
        assert isinstance(value, SMTVar)
        self.value = value
        self.community = community
        self.announcements = announcements
        self.matched_announcements = {}  # Cache evaluated announcements

    def is_match(self, announcement):
        if announcement not in self.matched_announcements:
            attr = announcement.communities[self.community]
            constraint = attr.check_eq(self.value)
            value = None
            if not is_symbolic(constraint):
                value = constraint
            match_var = self.ctx.create_fresh_var(
                z3.BoolSort(ctx=self.ctx.z3_ctx),
                value=value)
            if is_symbolic(constraint):
                self.ctx.register_constraint(match_var.var == constraint)
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]

    def get_config(self):
        return self.community


class SMTMatchPrefix(SMTMatchAttribute):
    """Matches Announcement.prefix"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars
        """
        super(SMTMatchPrefix, self).__init__('prefix', value, announcements, ctx)

    def get_config(self):
        return self.value.get_value()


class SMTMatchPeer(SMTMatchAttribute):
    """Short cut to match on Announcement.peer"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars
        """
        super(SMTMatchPeer, self).__init__('peer', value, announcements, ctx)

    def get_config(self):
        return MatchPeer(self.value.get_value())


class SMTMatchOrigin(SMTMatchAttribute):
    """Short cut to match on Announcement.origin"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchOrigin, self).__init__('origin', value, announcements, ctx)


class SMTMatchNextHop(SMTMatchAttribute):
    """Short cut to match on Announcement.next_hop"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchNextHop, self).__init__(
            'next_hop', value, announcements, ctx)

    def get_config(self):
        return MatchNextHop(self.value.get_value())


class SMTMatchASPath(SMTMatchAttribute):
    """Short cut to match on Announcement.as_path"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchASPath, self).__init__('as_path', value, announcements, ctx)

    def get_config(self):
        return MatchAsPath(decode_as_path(self.value.get_value()))


class SMTMatchASPathLen(SMTMatchAttribute):
    """Short cut to match on Announcement.as_path_len"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchASPathLen, self).__init__('as_path_len', value, announcements, ctx)

    def get_config(self):
        return MatchAsPathLen(self.value.get_value())


class SMTMatchLocalPref(SMTMatchAttribute):
    """Short cut to match on Announcement.local_pref"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchLocalPref, self).__init__('local_pref', value, announcements, ctx)

    def get_config(self):
        return MatchLocalPref(self.value.get_value())


class SMTMatchMED(SMTMatchAttribute):
    """Short cut to match on Announcement.med"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchMED, self).__init__('med', value, announcements, ctx)

    def get_config(self):
        return MatchMED(self.value.get_value())


class SMTMatchPermitted(SMTMatchAttribute):
    """Short cut to match on Announcement.permitted"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchPermitted, self).__init__(
            'permitted', value, announcements, ctx)

    def get_config(self):
        return MatchLocalPref(self.value.get_value())


class SMTAbstractAction(object):
    """Parent action class"""

    @property
    def old_announcements(self):
        raise NotImplementedError()

    @property
    def announcements(self):
        raise NotImplementedError()

    @property
    def attributes(self):
        """Set of attributes affected by this action"""
        raise NotImplementedError()

    @property
    def communities(self):
        """Set of communities affected by this action"""
        raise NotImplementedError()

    def execute(self):
        """Partial evaluate the action and generate new announcements set"""
        raise NotImplementedError()


class SMTSetAttribute(SMTAbstractAction):
    """Action to change one attribute in the announcement"""

    def __init__(self, match, attribute, value, announcements, ctx):
        super(SMTSetAttribute, self).__init__()
        assert isinstance(ctx, SolverContext)
        assert attribute in Announcement.attributes
        assert hasattr(match, 'is_match')
        assert announcements
        if value is None:
            vsort = getattr(announcements[0], attribute).vsort
            prefix = 'Set_%s_val' % attribute
            value = ctx.create_fresh_var(vsort, name_prefix=prefix)
        assert isinstance(value, SMTVar)
        attr_sort = getattr(announcements[0], attribute).vsort
        err = "Type mismatch of attribute and value %s != %s" % (
            attr_sort, value.vsort)
        assert attr_sort == value.vsort, err
        self.match = match
        self.attribute = attribute
        self.value = value
        self._old_announcements = announcements
        self._announcements = None
        self.smt_ctx = ctx
        self.execute()

    @property
    def announcements(self):
        return self._announcements

    @property
    def old_announcements(self):
        return self._old_announcements

    @property
    def attributes(self):
        return set([self.attribute])

    @property
    def communities(self):
        return set([])

    def execute(self):
        if self._announcements:
            return
        constraints = []
        announcements = []
        for announcement in self._old_announcements:
            new_vals = {}
            for attr in announcement.attributes:
                attr_var = getattr(announcement, attr)
                if attr == self.attribute:
                    is_match = self.match.is_match(announcement)
                    if is_match.is_concrete and attr != 'permitted':
                        new_var = self.value if is_match.get_value() else attr_var
                    else:
                        new_var = self.smt_ctx.create_fresh_var(
                            attr_var.vsort, name_prefix='Action_set_%s_val_%s_' % (attr, self.value.name))
                        vv = self.value.var if self.value.is_concrete else self.value.get_var()
                        attv = attr_var.var if attr_var.is_concrete else attr_var.get_var()
                        if attr == 'permitted':
                            # Permitted only overwrite announcements
                            # that were not dropped before
                            constraint = z3.If(z3.And(is_match.var,
                                                      attv == True,
                                                      self.smt_ctx.z3_ctx),
                                               new_var.var == vv,
                                               new_var.var == attv,
                                               ctx=self.smt_ctx.z3_ctx)
                        else:
                            constraint = z3.If(is_match.var,
                                               new_var.var == vv,
                                               new_var.var == attv,
                                               ctx=self.smt_ctx.z3_ctx)
                        constraints.append(constraint)
                    new_vals[attr] = new_var
                else:
                    new_vals[attr] = attr_var
            new_ann = Announcement(prev_announcement=announcement, **new_vals)
            global SELECTOR
            if announcement in SELECTOR:
                SELECTOR[new_ann] = SELECTOR[announcement]
            announcements.append(new_ann)
        if constraints:
            tmp = constraints + [self.smt_ctx.z3_ctx]
            self.smt_ctx.register_constraint(z3.And(*tmp), name_prefix='Set_%s_' % attr)
        self._announcements = self._old_announcements.create_new(announcements, self)


class SMTSetCommunity(SMTAbstractAction):
    """Action to change one attribute in the announcement"""

    def __init__(self, match, community, value, announcements, ctx):
        super(SMTSetCommunity, self).__init__()
        assert isinstance(ctx, SolverContext)
        assert hasattr(match, 'is_match')
        assert community in announcements[0].communities
        assert announcements
        if value is None:
            prefix = 'Set_community_val_'
            value = ctx.create_fresh_var(
                z3.BoolSort(ctx=ctx.z3_ctx), name_prefix=prefix, value=True)
        assert isinstance(value, SMTVar)
        err = "Value is not of type BoolSort %s" % (value.vsort)
        assert z3.BoolSort(ctx=ctx.z3_ctx) == value.vsort, err
        self.match = match
        self.community = community
        self.value = value
        self._old_announcements = announcements
        self._announcements = None
        self.smt_ctx = ctx
        self.execute()

    @property
    def announcements(self):
        return self._announcements

    @property
    def old_announcements(self):
        return self._old_announcements

    @property
    def attributes(self):
        return set(['communities'])

    @property
    def communities(self):
        return set([self.community])

    def execute(self):
        if self._announcements:
            return
        constraints = []
        announcements = []
        for announcement in self._old_announcements:
            new_vals = {}
            for attr in announcement.attributes:
                attr_var = getattr(announcement, attr)
                if attr != 'communities':
                    # Other attributes stay the same
                    new_vals[attr] = attr_var
                else:
                    new_comms = {}
                    for community, old_var in announcement.communities.iteritems():
                        if community != self.community:
                            # Other communities stay the same
                            new_comms[community] = old_var
                        else:
                            is_match = self.match.is_match(announcement)
                            if is_match.is_concrete:
                                # Partial eval
                                new_var = self.value if is_match.get_value() else old_var
                            else:
                                # No partial eval
                                new_var = self.smt_ctx.create_fresh_var(
                                    z3.BoolSort(ctx=self.smt_ctx.z3_ctx),
                                    name_prefix='set_community_%s_val' % community.name)
                                constraint = z3.If(is_match.var,
                                                   new_var.var == self.value.var,
                                                   new_var.var == old_var.var,
                                                   ctx=self.smt_ctx.z3_ctx)
                                constraints.append(constraint)
                            new_comms[community] = new_var
                    new_vals[attr] = new_comms
            new_ann = Announcement(prev_announcement=announcement, **new_vals)
            global SELECTOR
            if announcement in SELECTOR:
                SELECTOR[new_ann] = SELECTOR[announcement]
            announcements.append(new_ann)
        if constraints:
            tmp = constraints + [self.smt_ctx.z3_ctx]
            self.smt_ctx.register_constraint(z3.And(*tmp), name_prefix='Set_comm_')
        self._announcements = self._old_announcements.create_new(announcements, self)

    def get_config(self):
        return self.community if self.value.get_value() else None


class SMTSetOne(SMTAbstractAction):
    """
    Chose a SINGLE match object to meet the requirements
    """

    def __init__(self, match, announcements, ctx, actions=None):
        """
        :param announcements:
        :param ctx:
        :param actions: List of SMTMatch objects to use one of them
                        if None, then all attributes are going to be used.
        """
        super(SMTSetOne, self).__init__()
        assert isinstance(ctx, SolverContext)
        assert announcements, 'Cannot match on empty announcements'
        self._old_announcements = announcements
        self._announcements = None
        self.ctx = ctx
        self.match = match

        if not actions:
            # By default all attributes are allowed
            actions = []
            for attr in Announcement.attributes:
                if attr == 'communities':
                    for community in self.old_announcements[0].communities:
                        action = attribute_set_factory(
                            community, match, None,
                            self.old_announcements, self.ctx)
                        actions.append(action)
                else:
                    # Extract he z3 type of the given attribute
                    action = attribute_set_factory(
                        attr, match, None, self.old_announcements, self.ctx)
                    actions.append(action)

        # Create map for the different actions
        self.actions = {}
        self.index_var = self.ctx.create_fresh_var(
            z3.IntSort(ctx=self.ctx.z3_ctx), name_prefix='SetOneIndex_')
        index = itertools.count(0)
        for action in actions:
            err1 = 'All actions must have the same match'
            assert action.match == self.match, err1
            err2 = 'All actions must have the same announcements'
            assert action.old_announcements == self.old_announcements, err2
            self.actions[index.next()] = action
        # Make index in the range of number of actions
        index_range = z3.And(self.index_var.var >= 0,
                             self.index_var.var < index.next(), self.ctx.z3_ctx)
        self.ctx.register_constraint(index_range,
                                     name_prefix='setone_index_max_')
        self.execute()

    @property
    def old_announcements(self):
        return self._old_announcements

    @property
    def announcements(self):
        return self._announcements

    @property
    def attributes(self):
        return reduce(
            set.union,
            [getattr(a, 'attributes', set([None])) for a in self.actions.values()])

    @property
    def communities(self):
        return reduce(
            set.union,
            [getattr(a, 'communities') for a in self.actions.values()])

    def _get_actions(self, ann_index, attribute, default, index=0):
        """
        Recursively construct a match for an attribute (other than communities
        """
        if index not in self.actions:
            # Base case
            return default
        action = self.actions[index]
        value = getattr(action.announcements[ann_index], attribute)
        index_check = self.index_var.var == index
        next_attr = self._get_actions(ann_index, attribute, default, index + 1)
        return z3.If(index_check, value.var, next_attr, ctx=self.ctx.z3_ctx)

    def _get_communities(self, ann_index, community, default, index=0):
        """Recursively construct a match for a given community"""
        if index not in self.actions:
            # Base case
            return default
        action = self.actions[index]
        value = action.announcements[ann_index].communities[community]
        index_check = self.index_var.var == index
        next_attr = self._get_communities(
            ann_index, community, default, index + 1)
        return z3.If(index_check, value.var, next_attr, ctx=self.ctx.z3_ctx)

    def execute(self):
        new_anns = []
        # Execute the previous actions
        for action in self.actions.values():
            action.execute()
        # IF all previous actions are simple Attribute setters
        # then partial eval is more possible
        attr_only = None not in self.attributes
        for index, old_ann in enumerate(self.old_announcements):
            new_values = {}
            for attr in Announcement.attributes:
                old_var = getattr(old_ann, attr)
                # Parial evaluation
                if attr_only and attr not in self.attributes:
                    # This attribute is not changed by any of the actions
                    # Thus stays the same
                    new_values[attr] = old_var
                else:
                    # This attribute can be changed by at least one action
                    if attr == 'communities':
                        # Shallow copy
                        new_comms = copy.copy(getattr(old_ann, attr))
                        for community in self.communities:
                            prefix = 'setone_community_var_'
                            new_var = self.ctx.create_fresh_var(
                                z3.BoolSort(ctx=self.ctx.z3_ctx), name_prefix=prefix)
                            value = self._get_communities(
                                index, community, new_var.var)
                            prefix = 'setone_%s_' % attr
                            self.ctx.register_constraint(
                                new_var.var == value, name_prefix=prefix)
                            new_comms[community] = new_var
                        new_values[attr] = new_comms
                    else:
                        prefix = 'setone_%s_var_' % attr
                        new_var = self.ctx.create_fresh_var(
                            old_var.vsort, name_prefix=prefix)
                        value = self._get_actions(index, attr, new_var.var)
                        prefix = 'setone_%s_' % attr
                        self.ctx.register_constraint(
                            new_var.var == value, name_prefix=prefix)
                        new_values[attr] = new_var
            new_anns.append(Announcement(prev_announcement=old_ann, **new_values))
            global SELECTOR
            if old_ann in SELECTOR:
                SELECTOR[new_anns[-1]] = SELECTOR[old_ann]
        self._announcements = self.old_announcements.create_new(new_anns, self)

    def get_used_action(self):
        """Return the used action object"""
        match = self.actions[self.index_var.get_value()]
        return match

    def get_config(self):
        return self.get_used_action().get_config()


class SMTSetLocalPref(SMTSetAttribute):
    """Short cut to set the value of Announcement.local_pref"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetLocalPref, self).__init__(
            match, 'local_pref', value, announcements, ctx)
        if not self.value.is_concrete:
            self.smt_ctx.register_constraint(self.value.var > 0, name_prefix="LocalPref_Bound")

    def get_config(self):
        return ActionSetLocalPref(self.value.get_value())


class SMTSetPrefix(SMTSetAttribute):
    """Short cut to set the value of Announcement.prefix"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetPrefix, self).__init__(
            match, 'prefix', value, announcements, ctx)

    def get_config(self):
        return ActionSetPrefix(desanitize_smt_name(self.value.get_value()))


class SMTSetPeer(SMTSetAttribute):
    """Short cut to set the value of Announcement.peer"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetPeer, self).__init__(
            match, 'peer', value, announcements, ctx)

    def get_config(self):
        return ActionSetPeer(self.value.get_value())


class SMTSetOrigin(SMTSetAttribute):
    """Short cut to set the value of Announcement.origin"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetOrigin, self).__init__(
            match, 'origin', value, announcements, ctx)


class SMTSetPermitted(SMTSetAttribute):
    """Short cut to set the value of Announcement.permitted"""

    def __init__(self, match, value, announcements, ctx):
        super(SMTSetAttribute, self).__init__()
        assert isinstance(ctx, SolverContext)
        assert hasattr(match, 'is_match')
        assert announcements
        if value is None:
            vsort = z3.BoolSort(ctx=ctx.z3_ctx)
            prefix = 'Set_%s_val' % 'permitted'
            value = ctx.create_fresh_var(vsort, name_prefix=prefix)
        assert isinstance(value, SMTVar)
        self.match = match
        self.value = value
        self._old_announcements = announcements
        self._announcements = None
        self.smt_ctx = ctx
        self.execute()

    @property
    def announcements(self):
        return self._announcements

    @property
    def old_announcements(self):
        return self._old_announcements

    @property
    def attributes(self):
        return set([self.attribute])

    @property
    def communities(self):
        return set([])

    def execute(self):
        if self._announcements:
            return
        constraints = []
        announcements = []
        for announcement in self._old_announcements:
            new_vals = {}
            for attr in announcement.attributes:
                if attr != 'permitted':
                    new_vals[attr] = getattr(announcement, attr)
                else:
                    is_match = self.match.is_match(announcement)
                    oldp = announcement.permitted
                    if is_match.is_concrete and oldp.is_concrete:
                        if is_match.get_value() and oldp.get_value() == True:
                            new_var = self.value
                        else:
                            new_var = oldp
                    else:
                        new_var = self.smt_ctx.create_fresh_var(
                            z3.BoolSort(self.smt_ctx.z3_ctx),
                            name_prefix='ActionPermittedVal')
                        vv = self.value.var if self.value.is_concrete else self.value.get_var()
                        attv = oldp.var if oldp.is_concrete else oldp.get_var()
                        # Permitted only overwrite announcements
                        # that were not dropped before
                        constraint = z3.If(z3.And(is_match.var,
                                                  attv == True,
                                                  self.smt_ctx.z3_ctx),
                                           new_var.var == vv,
                                           new_var.var == attv,
                                           ctx=self.smt_ctx.z3_ctx)

                        constraints.append(constraint)
                    new_vals[attr] = new_var

            new_ann = Announcement(prev_announcement=announcement, **new_vals)
            global SELECTOR
            if announcement in SELECTOR:
                SELECTOR[new_ann] = SELECTOR[announcement]
            announcements.append(new_ann)
        if constraints:
            tmp = constraints + [self.smt_ctx.z3_ctx]
            self.smt_ctx.register_constraint(z3.And(*tmp), name_prefix='Set_%s_' % attr)
        self._announcements = self._old_announcements.create_new(announcements, self)

    def get_config(self):
        return Access.permit if self.value.get_value() else Access.deny


class SMTSetASPath(SMTSetAttribute):
    """Short cut to set the value of Announcement.as_path"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetASPath, self).__init__(
            match, 'as_path', value, announcements, ctx)

    def get_config(self):
        return ActionSetASPath(self.value.get_value())


class SMTSetASPathLen(SMTSetAttribute):
    """Short cut to set the value of Announcement.as_path_len"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetASPathLen, self).__init__(
            match, 'as_path_len', value, announcements, ctx)

    def get_config(self):
        return ActionSetASPathLen(self.value.get_value())


class SMTSetNextHop(SMTSetAttribute):
    """Short cut to set the value of Announcement.next_hop"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetNextHop, self).__init__(
            match, 'next_hop', value, announcements, ctx)

    def get_config(self):
        return ActionSetNextHop(desanitize_smt_name(self.value.get_value()))


class SMTSetMED(SMTSetAttribute):
    """Short cut to set the value of Announcement.med"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetMED, self).__init__(
            match, 'med', value, announcements, ctx)
        if not self.value.is_concrete:
            self.smt_ctx.register_constraint(self.value.var > 0, name_prefix="MED_Bound")

    def get_config(self):
        return ActionSetMED(self.value.get_value())


def attribute_match_factory(attribute, value=None, announcements=None, ctx=None):
    """
    Given an attribute name or Community value return the right match class
    If announcements and ctx are set, then a concrete object is returned
    """
    match_map = {
        'prefix': SMTMatchPrefix,
        'peer': SMTMatchPeer,
        'origin': SMTMatchOrigin,
        'as_path': SMTMatchASPath,
        'as_path_len': SMTMatchASPathLen,
        'next_hop': SMTMatchNextHop,
        'local_pref': SMTMatchLocalPref,
        'permitted': SMTMatchPermitted,
        'med': SMTMatchMED,
    }
    if attribute in match_map:
        klass = match_map[attribute]
    elif isinstance(attribute, Community):
        klass = functools.partial(SMTMatchCommunity, community=attribute)
    else:
        raise ValueError("Unrecognized attribute or community '%s'" % attribute)

    if announcements and ctx:
        return klass(value=value, announcements=announcements, ctx=ctx)
    return klass


def attribute_set_factory(attribute, match=None, value=None, announcements=None, ctx=None):
    """
    Given an attribute name or Community value return the right match class
    If announcements and ctx are set, then a concrete object is returned
    """
    match_map = {
        'prefix': SMTSetPrefix,
        'peer': SMTSetPeer,
        'origin': SMTSetOrigin,
        'as_path': SMTSetASPath,
        'as_path_len': SMTSetASPathLen,
        'next_hop': SMTSetNextHop,
        'local_pref': SMTSetLocalPref,
        'permitted': SMTSetPermitted,
        'med': SMTSetMED,
    }
    if attribute in match_map:
        klass = match_map[attribute]
    elif isinstance(attribute, Community):
        klass = functools.partial(SMTSetCommunity, community=attribute)
    else:
        raise ValueError("Unrecognized attribute or community '%s'" % attribute)

    if match and announcements and ctx:
        return klass(match=match, value=value, announcements=announcements, ctx=ctx)
    return klass


class SMTMatchCommunityList(SMTAbstractMatch):
    def __init__(self, community_list, announcements, ctx):
        assert isinstance(community_list, CommunityList)
        self.community_list = community_list
        self.announcements = announcements
        self.ctx = ctx
        self.matches = []
        for community in self.community_list.communities:
            match = self._get_community_match(community)
            self.matches.append(match)
        self.smt_match = SMTMatchAnd(self.matches, self.announcements, self.ctx)

    def is_match(self, announcement):
        return self.smt_match.is_match(announcement)

    def _get_community_match(self, community):
        if not is_empty(community):
            var = self.ctx.create_fresh_var(vsort=z3.BoolSort(ctx=self.ctx.z3_ctx), value=True)
            match = SMTMatchCommunity(community=community, value=var,
                                      announcements=self.announcements,
                                      ctx=self.ctx)
        else:
            comms = []
            for comm in self.ctx.communities:
                var = self.ctx.create_fresh_var(z3.BoolSort(ctx=self.ctx.z3_ctx), value=True)
                smt = SMTMatchCommunity(comm, var, self.announcements, self.ctx)
                comms.append(smt)
            match = SMTMatchSelectOne(self.announcements, self.ctx, comms)
        return match

    def get_config(self):
        comm_list = CommunityList(list_id=self.community_list.list_id,
                                  access=self.community_list.access,
                                  communities=self.smt_match.get_config())
        return MatchCommunitiesList(comm_list)


class SMTMatchIpPrefixList(SMTAbstractMatch):
    def __init__(self, ip_list, announcements, ctx):
        assert isinstance(ip_list, IpPrefixList)
        self.ip_list = ip_list
        self.announcements = announcements
        self.ctx = ctx
        self.matches = []
        for community in self.ip_list.networks:
            match = self._get_ip_match(community)
            self.matches.append(match)
        self.smt_match = SMTMatchOr(self.matches, self.announcements, self.ctx)

    def _get_ip_match(self, ip):
        vsort = self.ctx.get_enum_type(PREFIX_SORT)
        if not is_empty(ip):
            val = vsort.get_symbolic_value(ip)
            var = self.ctx.create_fresh_var(vsort, value=val)
            return SMTMatchPrefix(var, self.announcements, self.ctx)

        matches = []
        for ip in vsort.symbolic_values:
            var = self.ctx.create_fresh_var(vsort, value=ip)
            m = SMTMatchPrefix(var, self.announcements, self.ctx)
            matches.append(m)
        return SMTMatchSelectOne(self.announcements, self.ctx, matches)

    def is_match(self, announcement):
        return self.smt_match.is_match(announcement)

    def get_config(self):
        networks = [desanitize_smt_name(n) for n in self.smt_match.get_config() if n]
        ip_list = IpPrefixList(name=self.ip_list.name,
                               access=self.ip_list.access,
                               networks=networks)
        return MatchIpPrefixListList(ip_list)


class SMTMatch(SMTAbstractMatch):
    def __init__(self, match, announcements, ctx):
        assert isinstance(match, Match) or match is None
        self.match = match
        self.announcements = announcements
        self.ctx = ctx
        self.smt_match = None
        self.value = None
        self.match_dispatch = {
            MatchNextHop: self._load_match_next_hop,
            MatchIpPrefixListList: self._load_match_prefix_list,
            MatchCommunitiesList: self._load_match_communities_list,
            MatchLocalPref: self._load_match_local_pref,
            MatchPeer: self._load_match_peer,
            MatchAsPath: self._load_match_as_path,
            MatchMED: self._load_match_med,
            MatchAsPathLen: self._load_match_as_path_len,
            MatchSelectOne: self._load_match_select_one,
        }
        if self.match is None:
            self.smt_match = SMTMatchAll(self.ctx)
        else:
            self.match_dispatch[type(match)]()

    def is_match(self, announcement):
        return self.smt_match.is_match(announcement)

    def _load_match_next_hop(self):
        value = self.match.match if not is_empty(self.match.match) else None
        vsort = self.ctx.get_enum_type(NEXT_HOP_SORT)
        if value:
            value = vsort.get_symbolic_value(value)
        self.value = self.ctx.create_fresh_var(vsort=vsort, value=value)
        self.smt_match = SMTMatchNextHop(self.value, self.announcements, self.ctx)

    def _load_match_local_pref(self):
        value = self.match.match if not is_empty(self.match.match) else None
        self.value = self.ctx.create_fresh_var(vsort=z3.IntSort(ctx=self.ctx.z3_ctx), value=value)
        self.smt_match = SMTMatchLocalPref(self.value, self.announcements, self.ctx)

    def _load_match_med(self):
        value = self.match.match if not is_empty(self.match.match) else None
        self.value = self.ctx.create_fresh_var(vsort=z3.IntSort(ctx=self.ctx.z3_ctx), value=value)
        self.smt_match = SMTMatchMED(self.value, self.announcements, self.ctx)

    def _load_match_as_path(self):
        value = self.match.match if not is_empty(self.match.match) else None
        vsort = self.ctx.get_enum_type(ASPATH_SORT)
        if value:
            value = vsort.get_symbolic_value(value)
        self.value = self.ctx.create_fresh_var(vsort=vsort, value=value)
        self.smt_match = SMTMatchASPath(self.value, self.announcements, self.ctx)

    def _load_match_as_path_len(self):
        value = self.match.match if not is_empty(self.match.match) else None
        self.value = self.ctx.create_fresh_var(vsort=z3.IntSort(ctx=self.ctx.z3_ctx), value=value)
        self.smt_match = SMTMatchASPathLen(self.value, self.announcements, self.ctx)

    def _load_match_peer(self):
        value = self.match.match if not is_empty(self.match.match) else None
        vsort = self.ctx.get_enum_type(PEER_SORT)
        if value:
            value = vsort.get_symbolic_value(value)
        self.value = self.ctx.create_fresh_var(vsort=vsort, value=value)
        self.smt_match = SMTMatchPeer(self.value, self.announcements, self.ctx)

    def _load_match_prefix_list(self):
        self.smt_match = SMTMatchIpPrefixList(self.match.match,
                                              self.announcements, self.ctx)

    def _load_match_communities_list(self):
        self.smt_match = SMTMatchCommunityList(
            self.match.match, self.announcements, self.ctx)

    def _load_match_select_one(self):
        matches = []
        for match in self.match.match:
            smt_match = SMTMatch(match, self.announcements, self.ctx)
            matches.append(smt_match)
        self.smt_match = SMTMatchSelectOne(self.announcements, self.ctx, matches)

    def __str__(self):
        return "SMTMatch(%s)" % self.smt_match

    def get_config(self):
        return self.smt_match.get_config()


class SMTActions(SMTAbstractAction):
    """Synthesize list of actions"""

    def __init__(self, match, actions, announcements, ctx, selector=None):
        self.actions = actions
        self.smt_actions = []
        self.match = match
        self.ctx = ctx
        self._old_announcements = announcements
        self._announcements = None
        if isinstance(match, Match) or match is None:
            self.smt_match = SMTMatch(match, self._old_announcements, self.ctx)
        else:
            assert isinstance(match, SMTAbstractMatch), match
            self.smt_match = match
        self.action_dispatch = {
            ActionSetLocalPref: self._set_local_pref,
            ActionSetCommunity: self._set_communities,
            ActionSetNextHop: self._set_next_hop,
            ActionSetPrefix: self._set_prefix,
            ActionPermitted: self._set_access,
            ActionSetOne: self._set_one,
        }
        self._selector = selector
        self.execute()

    def execute(self):
        if self._announcements:
            return
        prev_ann_ctx = self.old_announcements
        for action in self.actions:
            smt_action = self.action_dispatch[type(action)](action, prev_ann_ctx)
            if isinstance(smt_action, list):
                self.smt_actions.extend(smt_action)
                prev_ann_ctx = smt_action[-1].announcements
            else:
                self.smt_actions.append(smt_action)
                prev_ann_ctx = smt_action.announcements
            if self._selector:
                for index, ann in enumerate(self.smt_actions[-1].announcements):
                    prev = ann.prev_announcement
                    if prev in self._selector:
                        self._selector[ann] = self._selector.get(prev)
                    else:
                        global SELECTOR
                        self._selector[ann] = SELECTOR[prev]
        self._announcements = self.smt_actions[-1].announcements
        assert self._announcements != self.old_announcements

    @property
    def announcements(self):
        return self._announcements

    @property
    def old_announcements(self):
        return self._old_announcements

    def _set_access(self, action, anns):
        vsort = z3.BoolSort(ctx=self.ctx.z3_ctx)
        value = None
        if not is_empty(action.value):
            # Partial evaluate
            value = True if action.value == Access.permit else False
        var = self.ctx.create_fresh_var(vsort=vsort, value=value)
        return SMTSetPermitted(self.smt_match, var, anns, self.ctx)

    def _set_community(self, community, anns):
        assert is_empty(community) or isinstance(community, Community)
        community = community if not is_empty(community) else None
        vsort = z3.BoolSort(ctx=self.ctx.z3_ctx)
        if community:
            var = self.ctx.create_fresh_var(vsort=vsort, value=True)
            return SMTSetCommunity(self.smt_match, community, var, anns, self.ctx)
        else:
            actions = []
            for community in self.ctx.communities:
                var = self.ctx.create_fresh_var(vsort=vsort, value=True)
                tmp = SMTSetCommunity(self.smt_match, community, var, anns, self.ctx)
                actions.append(tmp)
            return SMTSetOne(self.smt_match, anns, self.ctx, actions)

    def _set_communities(self, action, anns):
        tmp = []
        prev_anns = anns
        if action.additive == False:
            for comm in self.ctx.communities:
                var = self.ctx.create_fresh_var(z3.BoolSort(ctx=self.ctx.z3_ctx), value=False)
                a = SMTSetCommunity(self.match, comm, var, prev_anns, self.ctx)
                prev_anns = a.announcements
                # Dont add these explicit resets
                #tmp.append(a)
        for comm in action.communities:
            a = self._set_community(comm, prev_anns)
            prev_anns = a.announcements
            tmp.append(a)
        return tmp

    def _set_local_pref(self, action, anns):
        value = action.value if not is_empty(action.value) else None
        vsort = z3.IntSort(ctx=self.ctx.z3_ctx)
        var = self.ctx.create_fresh_var(vsort=vsort, value=value)
        return SMTSetLocalPref(self.smt_match, var, anns, self.ctx)

    def _set_next_hop(self, action, anns):
        value = action.value if not is_empty(action.value) else None
        vsort = self.ctx.get_enum_type(NEXT_HOP_SORT)
        if value:
            value = vsort.get_symbolic_value(value)
        var = self.ctx.create_fresh_var(vsort=vsort, value=value)
        return SMTSetNextHop(self.smt_match, var, anns, self.ctx)

    def _set_one(self, action, anns):
        smt_actions = []
        for action in action.value:
            smt_action = self.action_dispatch[type(action)](action, anns)
            if isinstance(smt_action, list):
                smt_actions.extend(smt_action)
            else:
                smt_actions.append(smt_action)
        return SMTSetOne(self.smt_match, anns, self.ctx, smt_actions)

    def _set_prefix(self, action, anns):
        value = action.value if not is_empty(action.value) else None
        vsort = self.ctx.get_enum_type(PREFIX_SORT)
        if value:
            value = vsort.get_symbolic_value(value)
        var = self.ctx.create_fresh_var(vsort=vsort, value=value)
        return SMTSetPrefix(self.smt_match, var, anns, self.ctx)

    def get_config(self):
        communities = []
        configs = []

        def _gather_communities(comms, index):
            prev_action = self.actions[index]
            assert isinstance(prev_action, ActionSetCommunity), "Found: {}".format(self.actions)
            action = ActionSetCommunity(communities=comms,
                                        additive=prev_action.additive)
            return action

        for index, smt_box in enumerate(self.smt_actions):
            config = smt_box.get_config()
            if isinstance(config, Community):
                communities.append(config)
            else:
                # Close other communities
                if communities:
                    comms = _gather_communities(communities, index - 1)
                    configs.append(comms)
                    communities = []
                configs.append(config)
        # Left over communities
        if communities:
            config = _gather_communities(communities, index)
            configs.append(config)
        return configs


class SMTSelectorMatch(SMTAbstractMatch):
    def __init__(self, selectors_vars, selector_value, match, announcements, ctx):
        log_name = '%s.%s' % (self.__module__, self.__class__.__name__)
        self.log = logging.getLogger(log_name)
        self.log.debug("Selector match for vars: %s, value: %s, match: %s",
                       len(selectors_vars), selector_value, match)
        self.selectors_vars = selectors_vars
        self.selector_value = selector_value
        self.match = match
        self.announcements = announcements
        self.ctx = ctx
        self.matched_announcements = {}  # Cache evaluated announcements

    def is_match(self, announcement):
        #if not self.selectors_vars:
        #    return self.match.is_match(announcement)
        if announcement not in self.matched_announcements:
            is_match = self.match.is_match(announcement)
            global SELECTOR
            sel = SELECTOR.get(announcement, None) or self.selectors_vars.get(announcement, None)
            assert sel, "No selector variable set for announcement %s" % announcement
            value = None
            if is_match.is_concrete and is_match.get_value() == False:
                value = False
            if sel.is_concrete and sel.get_value() != self.selector_value:
                value = False
            match_var = self.ctx.create_fresh_var(
                z3.BoolSort(ctx=self.ctx.z3_ctx),
                name_prefix='match_sel_',
                value=value)
            if not value:
                self.ctx.register_constraint(
                    z3.And(is_match.var,
                           sel.var == self.selector_value, self.ctx.z3_ctx) == match_var.var,
                    name_prefix='Selector_')
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]

    def get_config(self):
        if not self.selectors_vars:
            return self.match.get_config()
        if self.selector_value.get_value() == self.selector_value:
            return self.match.get_config()


class SMTRouteMapLine(SMTAbstractAction):
    """Synthesize one RouteMapLine"""

    def __init__(self, line_no_match, line, announcements, ctx):
        """
        :param name: name for z3 vars
        :param line: RouteMapLine
        :param ctx: SMTContext
        """
        log_name = '%s.%s' % (self.__module__, self.__class__.__name__)
        self.log = logging.getLogger(log_name)
        self.log.debug("Parsing Route Map line: %d to process: %d announcements",
                       line.lineno, len(announcements))
        self.ctx = ctx
        self.line = line
        self._old_announcements = announcements
        self.line_no_match = line_no_match
        if not line.matches:
            # Empty matches all by default
            self.smt_match = SMTMatch(None, self.old_announcements, self.ctx)
        elif len(line.matches) == 1:
            # One match, no need to use And
            self.smt_match = SMTMatch(line.matches[0], self.old_announcements, self.ctx)
        else:
            # More than match, combine them with an And
            sub_matches = [SMTMatch(match, self.old_announcements, self.ctx)
                            for match in line.matches]
            self.smt_match = SMTMatchAnd(
                matches=sub_matches,
                announcements=self.old_announcements,
                ctx=self.ctx)
        # Ensure that only one route map is selected is selected
        self.selector_match = SMTSelectorMatch(
            selectors_vars=line_no_match,
            selector_value=self.line.lineno,
            match=self.smt_match,
            announcements=self.old_announcements,
            ctx=self.ctx)

        # Permitted Action to allow or drop routes
        self.permitted_action = ActionPermitted(line.access)
        actions = [self.permitted_action]
        if line.actions:
            assert isinstance(line.actions, Iterable)
            actions += line.actions
        # Call the actions
        self.smt_actions = SMTActions(
            match=self.selector_match,
            actions=actions,
            announcements=self.old_announcements,
            ctx=self.ctx,
            selector=self.line_no_match)
        self._announcements = self.smt_actions.announcements

    @property
    def announcements(self):
        return self._announcements

    @property
    def old_announcements(self):
        return self._old_announcements

    def execute(self):
        pass

    def get_config(self):
        matches = []
        match_config = self.smt_match.get_config()
        if isinstance(self.smt_match, SMTMatchAnd):
            matches.extend(match_config)
        elif match_config:
            matches.append(match_config)
        if not matches:
            matches = None
        actions = self.smt_actions.get_config()
        permittted = actions[0]
        actions = actions[1:]

        if not actions:
            actions = None

        return RouteMapLine(matches=matches, actions=actions,
                            access=permittted,
                            lineno=self.line.lineno)

    def __str__(self):
        return "SMTRouteMapLine(matches=%s, actions=%s, access=%s, lineno=%s)" % (
            self.smt_match, self.line.actions, self.line.access, self.line.lineno
        )


class SMTRouteMap(SMTAbstractAction):
    """Synthesize RouteMap"""

    def __init__(self, route_map, announcements, ctx):
        log_name = '%s.%s' % (self.__module__, self.__class__.__name__)
        self.log = logging.getLogger(log_name)
        self.log.debug("Parsing Route map %s, to process %d announcements",
                       route_map.name, len(announcements))
        self.route_map = route_map
        self.ctx = ctx
        self._old_announcements = announcements
        self.smt_lines = []
        global SELECTOR
        # Logic to ensure that the announcement is matched against only
        # one line
        name_prefix = 'SelectOneRmapLineIndex_'
        line_numbers = [line.lineno for line in route_map.lines]
        selectors = {}
        for announcement in self.old_announcements:
            index_var = self.ctx.create_fresh_var(
                z3.IntSort(ctx=self.ctx.z3_ctx), name_prefix=name_prefix)
            selectors[announcement] = index_var
            SELECTOR[announcement] = index_var
            possible_vals = [index_var.var == lineno for lineno in line_numbers]
            possible_vals += [self.ctx.z3_ctx]
            # Bound the selector variable only to the available
            # route map line numbers
            self.ctx.register_constraint(z3.Or(*possible_vals),
                                         name_prefix='RmapIndexBound_%s_' % self.route_map.name)

        prev_anns = self._old_announcements
        matched_anns = []
        for i, line in enumerate(self.route_map.lines):
            box = SMTRouteMapLine(selectors, line, prev_anns, self.ctx)
            self.smt_lines.append(box)
            # Cascade changes
            prev_anns = self.smt_lines[-1].announcements
            # Constraints to ensure the ordering is preserved when matching
            # different route map lines
            if len(self.route_map.lines) < 2:
                continue
            for ann in self.old_announcements:
                index_var = selectors[ann]
                is_match = box.smt_match.is_match(ann)
                if i == 0:
                    const = z3.If(box.smt_match.is_match(ann).var == True,
                                  index_var.var == line.lineno,
                                  index_var.var != line.lineno,
                                  ctx=self.ctx.z3_ctx)
                else:
                    prev = [z3.Not(b.smt_match.is_match(ann).var, self.ctx.z3_ctx)
                            for b in self.smt_lines[:-1]]
                    prev += [self.ctx.z3_ctx]
                    prev = z3.And(*prev)
                    const = z3.If(
                        z3.And(prev == True,
                               box.smt_match.is_match(ann).var == True,
                               self.ctx.z3_ctx),
                        index_var.var == line.lineno,
                        index_var.var != line.lineno,
                        ctx=self.ctx.z3_ctx)
                self.ctx.register_constraint(
                    const,
                    name_prefix='rmap_%s_order_' % self.route_map.name)
        self.log.debug("End parsing route map %s", self.route_map.name)
        self._announcements = self.smt_lines[-1].announcements

    @property
    def announcements(self):
        return self._announcements

    @property
    def old_announcements(self):
        return self._old_announcements

    def execute(self):
        pass

    def get_config(self):
        lines = []
        for line in self.smt_lines:
            lines.append(line.get_config())
        return RouteMap(name=self.route_map.name, lines=lines)
