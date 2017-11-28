"""
Synthesize policies .. aka route maps for the moment
"""

import z3

from synet.topo.bgp import Announcement
from synet.utils.fnfree_smt_context import SMTVar
from synet.utils.fnfree_smt_context import SolverContext
from synet.utils.fnfree_smt_context import is_symbolic


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class SMTMatch(object):
    """Generic Match Class"""

    def is_match(self, announcement):
        """
        Returns a Var that is evaluated when partial evaluation is possible.
        Using this method on the same announcement multiple times generates
        redundant constraints and variables
        """
        raise NotImplementedError()


class SMTMatchAll(SMTMatch):
    """Matches all announcements regardless of their contents"""

    def __init__(self, ctx):
        self.ctx = ctx
        self.match_var = ctx.create_fresh_var(z3.BoolSort(), value=True)

    def is_match(self, announcement):
        return self.match_var


class SMTMatchNone(SMTMatch):
    """Does NOT match any announcement regardless of its contents"""

    def __init__(self, ctx):
        self.ctx = ctx
        self.match_var = ctx.create_fresh_var(z3.BoolSort(), value=False)

    def is_match(self, announcements):
        return self.match_var


class SMTMatchAnd(SMTMatch):
    """Combine Matches in Or expression"""

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
            value = None
            if is_concrete:
                value = all([result.get_value() for result in results])
            match_var = self.ctx.create_fresh_var(z3.BoolSort(), value=value)
            if not is_concrete:
                constraint = z3.And([result.var == True for result in results])
                self.ctx.register_constraint(match_var.var == constraint)
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]


class SMTMatchOr(SMTMatch):
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
            value = None
            if is_concrete:
                value = any([result.get_value() for result in results])
            match_var = self.ctx.create_fresh_var(z3.BoolSort(), value=value)
            if not is_concrete:
                constraint = z3.Or([result.var == True for result in results])
                self.ctx.register_constraint(match_var.var == constraint)
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]


class SMTMatchSelectOne(SMTMatch):
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
                        match_val = self.ctx.create_fresh_var(
                            z3.BoolSort(), value=True)
                        match = SMTMatchCommunity(
                            community, match_val, self.announcements, self.ctx)
                else:
                    # Extract he z3 type of the given attribute
                    asort = getattr(announcements[0], attr).vsort
                    # Symbolic match value
                    match_val = self.ctx.create_fresh_var(asort, value=None)
                    match = SMTMatchAttribute(
                        attr, match_val, self.announcements, self.ctx)
                matches.append(match)

        # Create map for the different matches
        self.matches = {}
        self.index_var = self.ctx.create_fresh_var(z3.IntSort())
        for index, match in enumerate(matches):
            self.matches[index] = match
        # Make index in the range of number of matches
        self.ctx.register_constraint(self.index_var.var < index + 1)

    def _get_match(self, announcement, current_index=0):
        """Recursively construct a match"""
        if current_index not in self.matches:
            # Base case
            return z3.And(self.index_var.var == current_index, False)
        else:
            match_var = self.matches[current_index].is_match(announcement).var
            index_check = self.index_var.var == current_index
            next_attr = self._get_match(announcement, current_index + 1)
            return z3.If(index_check, match_var, next_attr)

    def is_match(self, announcement):
        if announcement not in self.matched_announcements:
            var = self.ctx.create_fresh_var(z3.BoolSort())
            self.matched_announcements[announcement] = var
            constraint = var.var == self._get_match(announcement)
            self.ctx.register_constraint(constraint)
        return self.matched_announcements[announcement]

    def get_used_match(self):
        match = self.matches[self.index_var.get_value()]
        return match


class SMTMatchAttribute(SMTMatch):
    """Match on a single attribute of announcement"""

    def __init__(self, attribute, value, announcements, ctx):
        """
        :param attribute: Must be in Announcement.attributes
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars
        """
        assert isinstance(ctx, SolverContext)
        assert announcements, 'Cannot match on empty announcements'
        assert attribute in Announcement.attributes
        if value is None:
            asort = getattr(announcements[0], attribute).vsort
            value = ctx.create_fresh_var(asort)
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
            match_var = self.ctx.create_fresh_var(z3.BoolSort(), value=value)
            if is_symbolic(constraint):
                self.ctx.register_constraint(match_var.var == constraint)
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]


class SMTMatchCommunity(SMTMatch):
    """Match if a single community value is set to True"""

    def __init__(self, community, value, announcements, ctx):
        """

        :param community:
        :param value: Optionally can be None, then set by default to True
        :param announcements:
        :param ctx:
        """
        assert isinstance(ctx, SolverContext)
        assert announcements, "Cannot match on empty announcements"
        assert community in announcements[0].communities
        if not value:
            value = ctx.create_fresh_var(z3.BoolSort(), value=True)
        assert isinstance(value, SMTVar)
        self.ctx = ctx
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
            match_var = self.ctx.create_fresh_var(z3.BoolSort(), value=value)
            if is_symbolic(constraint):
                self.ctx.register_constraint(match_var.var == constraint)
            self.matched_announcements[announcement] = match_var
        return self.matched_announcements[announcement]


class SMTMatchPrefix(SMTMatchAttribute):
    """Matches Announcement.prefix"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars
        """
        super(SMTMatchPrefix, self).__init__('prefix', value, announcements, ctx)


class SMTMatchPeer(SMTMatchAttribute):
    """Short cut to match on Announcement.peer"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars
        """
        super(SMTMatchPeer, self).__init__('peer', value, announcements, ctx)


class SMTMatchOrigin(SMTMatchAttribute):
    """Short cut to match on Announcement.origin"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchOrigin, self).__init__('origin', value, announcements, ctx)


class SMTMatchASPath(SMTMatchAttribute):
    """Short cut to match on Announcement.as_path"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchASPath, self).__init__('as_path', value, announcements, ctx)


class SMTMatchASPathLen(SMTMatchAttribute):
    """Short cut to match on Announcement.as_path_len"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchASPathLen, self).__init__('as_path_len', value, announcements, ctx)


class SMTMatchNextHop(SMTMatchAttribute):
    """Short cut to match on Announcement.next_hop"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchNextHop, self).__init__('next_hop', value, announcements, ctx)


class SMTMatchLocalPref(SMTMatchAttribute):
    """Short cut to match on Announcement.local_pref"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchLocalPref, self).__init__('local_pref', value, announcements, ctx)


class SMTMatchPermitted(SMTMatchAttribute):
    """Short cut to match on Announcement.permitted"""

    def __init__(self, value, announcements, ctx):
        """
        :param value: Symbolic Var, or None to create one by default
        :param announcements: List of announcements
        :param ctx: to register new constraints and create fresh vars"""
        super(SMTMatchPermitted, self).__init__(
            'permitted', value, announcements, ctx)


class SMTAction(object):
    """Action to change one attribute in the announcement"""

    def __init__(self, match, attribute, value, announcements, ctx):
        assert isinstance(ctx, SolverContext)
        assert attribute in Announcement.attributes
        assert hasattr(match, 'is_match')
        assert announcements
        if value is None:
            vsort = getattr(announcements[0], attribute).vsort
            value = ctx.create_fresh_var(vsort)
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
                    if is_match.is_concrete:
                        if is_match.get_value():
                            new_var = self.value
                        else:
                            new_var = getattr(announcement, attr)
                    else:
                        new_var = self.smt_ctx.create_fresh_var(
                            attr_var.vsort, value=self.value)
                        constraint = z3.If(is_match.var,
                                           new_var.var == self.value,
                                           new_var.var == attr_var.var)
                        constraints.append(constraint)
                    new_vals[attr] = new_var
                else:
                    new_vals[attr] = attr_var
            new_ann = Announcement(**new_vals)
            announcements.append(new_ann)
        if constraints:
            self.smt_ctx.register_constraint(z3.And(*constraints))
        self._announcements = self._old_announcements.create_new(announcements, self)


class SMTSetLocalPref(SMTAction):
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


class SMTSetPrefix(SMTAction):
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


class SMTSetPeer(SMTAction):
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


class SMTSetOrigin(SMTAction):
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


class SMTSetPermitted(SMTAction):
    """Short cut to set the value of Announcement.permitted"""

    def __init__(self, match, value, announcements, ctx):
        """
        :param match: SMTMatch object
        :param value: Symbolic Var, or None to create one by default
        :param announcements: AnnouncementsContext
        :param ctx: SolverContext
        """
        super(SMTSetPermitted, self).__init__(
            match, 'permitted', value, announcements, ctx)


class SMTSetASPath(SMTAction):
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


class SMTSetASPathLen(SMTAction):
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


class SMTSetNextHop(SMTAction):
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
