#!/usr/bin/env python

"""
Helper class to keep track of SMT vars and constraints
"""

import itertools
from timeit import default_timer as timer

import z3

from tekton.bgp import BGP_ATTRS_ORIGIN
from tekton.bgp import Announcement


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


# Used for the names of EnumTypes
ANNOUNCEMENT_SORT = 'AnnSort'
PREFIX_SORT = 'PrefixSort'
PEER_SORT = 'PeerSort'
BGP_ORIGIN_SORT = 'BGPOriginSort'
ASPATH_SORT = 'ASPathSort'
NEXT_HOP_SORT = 'NextHopSort'
VALUENOTSET = 'EMPTY?Value'

SMT_NAME_MAP = {
    '.': '_DOT_',
    '/': '_SLASH_',
    '-': '_DASH_',
    ':': '_SEMI_',
    '(': '_OPENP_',
    ')': '_CLOSEP_',
}


ALPHA = 'APLPHA_'


def sanitize_smt_name(name):
    """Replace special chars from a name to make more friendly to SMT solver"""
    if not name[0].isalpha():
        tmp = "{}{}".format(ALPHA, name)
    else:
        tmp = name
    for k, v in SMT_NAME_MAP.iteritems():
        tmp = tmp.replace(k, v)
    return tmp


def desanitize_smt_name(name):
    """Return the special chars to the SMT name"""
    if name.startswith(ALPHA):
        tmp = name[len(ALPHA):]
    else:
        tmp = name
    for k, v in SMT_NAME_MAP.iteritems():
        tmp = tmp.replace(v, k)
    return tmp


def is_empty(var):
    """Return true if the variable is VALUENOTSET"""
    if hasattr(var, 'get_id'):
        return False
    return str(var) == VALUENOTSET or var is None


def is_symbolic(var):
    """Return True if a given variable is symbolic (z3 var)"""
    return z3.is_const(var) or z3.is_expr(var)


def get_as_path_key(as_path):
    """Get a key for the path"""
    return 'as_path_' + '_'.join([str(n) for n in as_path])


def decode_as_path(as_path_key):
    """Inverse of get_as_path_key"""
    assert as_path_key.startswith('as_path_')
    return [int(asnum) for asnum in as_path_key.split('_')[2:]]


def read_announcements(announcements, smt_ctx):
    """
    Read announcements provided by the user and generate a list of
    the same announcements, but using symbolic variables that
    are registered in the smt context.
    """
    new_announcements = []
    for announcement in announcements:
        vals = {}
        all_attrs = [
            ('prefix', PREFIX_SORT, None),
            ('peer', PEER_SORT, None),
            ('origin', BGP_ORIGIN_SORT, lambda x: x.name),
            ('as_path', ASPATH_SORT, get_as_path_key),
            ('as_path_len', z3.IntSort(ctx=smt_ctx.z3_ctx), None),
            ('next_hop', NEXT_HOP_SORT, None),
            ('local_pref', z3.IntSort(ctx=smt_ctx.z3_ctx), None),
            ('med', z3.IntSort(ctx=smt_ctx.z3_ctx), None),
            ('permitted', z3.BoolSort(ctx=smt_ctx.z3_ctx), None),
        ]
        for attr, vsort, conv in all_attrs:
            concrete_value = getattr(announcement, attr)
            if is_empty(concrete_value):
                value = None
            else:
                if isinstance(vsort, basestring):
                    vsort = smt_ctx.get_enum_type(vsort)
                    if conv:
                        concrete_value = conv(concrete_value)
                    value = vsort.get_symbolic_value(concrete_value)
                else:
                    value = concrete_value
            vals[attr] = smt_ctx.create_fresh_var(vsort=vsort, value=value)
        # Communities are read differently
        vals['communities'] = {}
        for community in announcement.communities:
            value = announcement.communities[community]
            if is_empty(value):
                value = None
            comm_var = smt_ctx.create_fresh_var(
                vsort=z3.BoolSort(ctx=smt_ctx.z3_ctx), value=value)
            vals['communities'][community] = comm_var
        new_ann = Announcement(prev_announcement=announcement, **vals)
        new_announcements.append(new_ann)
    return AnnouncementsContext(new_announcements)


class EnumType(object):
    """Create a enum sort"""

    def __init__(self, name, values, z3_ctx):
        """
        :param name: Name of the type
        :param values: list of all possible values
        """
        assert values, "Requires at least one value for '%s'" % name
        self._name = name
        assert self._name[0].isalpha(), "Name is not valid {}".format(self.name)
        self._concrete_values = values
        self.z3_ctx = z3_ctx
        self._sort, self._symbolic_values = z3.EnumSort(name, values,
                                                        ctx=self.z3_ctx)


    @property
    def name(self):
        """The name of the type, should be unqiue"""
        return self._name

    @property
    def sort(self):
        """The type of the variable"""
        return self._sort

    @property
    def symbolic_values(self):
        """All z3 variables"""
        return self._symbolic_values

    @property
    def concrete_values(self):
        """All string values"""
        return self._concrete_values

    def get_symbolic_value(self, value):
        """Given a string value return the Z3 value"""
        value = sanitize_smt_name(value)
        if value not in self._concrete_values:
            err = "Value '%s' is not defined in %s" % (
                value, self.concrete_values)
            raise ValueError(err)
        indexof = self._concrete_values.index(value)
        return self.symbolic_values[indexof]

    def get_concrete_value(self, var):
        """Given a z3 variable, return the actual string value"""
        assert is_symbolic(var)
        if var not in self._symbolic_values:
            err = "Symbolic value '{}' of type '{}' is not defined. " \
                  "Current defined values are: {}".format(
                var, self.name, self.symbolic_values)
            raise ValueError(err)
        indexof = self.symbolic_values.index(var)
        return self.concrete_values[indexof]

    def __str__(self):
        return "EnumType(%s, %s)" % (self.name, len(self.concrete_values))

    def __repr__(self):
        return "EnumType(%s)" % self.name


class SMTVar(object):
    """Hold Symbolic variables in SyNET"""

    def __init__(self, name, vsort, value=None):
        """
        :param name: The name of z3 variable
        :param vsort: The type of the variable, support z3.IntSort & EnumType
        :param value: optional conrete value for the var
        """
        assert isinstance(name, basestring)
        self._name = name
        assert self._name[0].isalpha(), "Name is not valid {}".format(self.name)
        self._is_enum = isinstance(vsort, EnumType)
        if value is None or is_empty(value):
            is_concrete = False
            value = VALUENOTSET
        else:
            is_concrete = True
            if self._is_enum and not is_symbolic(value):
                value = vsort.get_symbolic_value(value)
        if self._is_enum:
            self._var = z3.Const(self.name, vsort.sort)
        else:
            self._var = z3.Const(self.name, vsort)
        self._vsort = vsort
        self._is_concrete = is_concrete
        self._value = value

    def __str__(self):
        return "SMTVar({}, {}, {})".format(
            self.name, self.vsort,
            self.get_value() if self.is_concrete else '?')

    def __hash__(self):
        return hash((self.name, self.get_var().get_id()))

    def __eq__(self, other):
        if self.name != getattr(other, 'name', None):
            return False
        other_var = getattr(other, 'get_var', None)
        if not other_var or other_var().get_id() != self.get_var().get_id():
            return False
        return True

    @property
    def name(self):
        """The name of variable, should be unique"""
        return self._name

    @property
    def vsort(self):
        """The type of the variable"""
        return self._vsort

    @property
    def is_concrete(self):
        """Returns True if a concrete value is already defined"""
        return self._is_concrete

    def get_var(self):
        """Return the Z3 variable"""
        return self._var

    @property
    def var(self):
        """
        Auto partially evaluate when possible
        This should be used when building constrains
        """
        if self.is_concrete:
            return self._value
        return self.get_var()

    def get_value(self):
        """Return the concrete value"""
        if self.is_concrete:
            if self._is_enum:
                return self.vsort.get_concrete_value(self._value)
            return self._value
        raise RuntimeError("Var %s is not concrete" % self.name)

    def check_eq(self, other):
        """Faster version than __eq__ for generating constraints"""
        if self.is_concrete and other.is_concrete:
            if self.get_value() == other.get_value():
                return True
        return self.var == other.var

    def eval(self, model):
        """Concertize the variable value based on the z3 model"""
        if not self.is_concrete:
            value = model.eval(self.get_var())
            if self._is_enum:
                self._value = value
            elif isinstance(value, z3.BoolRef):
                try:
                    self._value = z3.is_true(value)
                except AttributeError:
                    #raise RuntimeError("Value not assigned for %s", str(self))
                    pass
            elif value.is_int:
                try:
                    self._value = value.as_long()
                except AttributeError:
                    # raise RuntimeError("Value not assigned for %s", str(self))
                    pass
            else:
                err = "Currently only support enums and ints"
                raise NotImplementedError(err)
            self._is_concrete = True
        return self.get_value()


class SolverContext(object):
    """
    Keep track of all variables and constraints to make sure they're unique
    """

    def __init__(self, z3_ctx):
        self._vars = {}  # Map a name to a var id
        self._tracked = {}  # Map a name to constraints, additional info
        self._next_varnum = itertools.count(0)
        self._next_constnum = itertools.count(0)
        self._enum_types = {}
        self._enum_compare = {}
        self._enum_compare_sort = {}
        self.z3_ctx = z3_ctx
        self.compare_vals = ['GREATER', 'LESS', 'EQ', 'UNKNOWN']
        self.comparator = self.create_enum_type('Comparator', self.compare_vals)
        self.compare_vars = [self.comparator.get_symbolic_value(x) for x in self.compare_vals]

    def create_enum_type(self, name, values):
        """Create new Enum type"""
        if name in self._enum_types:
            raise ValueError("EnumSort %s is already defined" % name)
        assert values
        for value in values:
            if value != sanitize_smt_name(value):
                raise ValueError("Enum Value {} contains special chars".format(value))
            assert value[0].isalpha(), "Name is not valid {}".format(value)
            for ename, etype in self._enum_types.iteritems():
                if value in etype.concrete_values:
                    err = "Duplicate value '%s' already defined in %s" % (
                        value, ename)
                    raise ValueError(err)
        enum_type = EnumType(name, values, z3_ctx=self.z3_ctx)
        self._enum_types[name] = enum_type
        return self._enum_types[name]

    def get_enum_type(self, name):
        """Get the EnumType object of the given type name"""
        return self._enum_types[name]

    def fresh_var_name(self, prefix=None):
        """
        Creates a fresh name for the next variable
        :return: basestring new variable name
        """
        if not prefix:
            prefix = 'Var_'
        else:
            prefix = sanitize_smt_name(prefix)
        name = "%s%d" % (prefix, self._next_varnum.next())
        while name in self._vars:
            name = "%s%d" % (prefix, self._next_varnum.next())
        return name

    def _register_var(self, var):
        """
        Register a new SMT variable with a given name.
        Raises ValueError is the variable is duplicated
        :param name: basestring
        :param var: z3 Variable
        :return: None
        """
        assert isinstance(var, SMTVar)

        if var.name in self._vars:
            err = "Variable with name %s is already registered" % var.name
            raise ValueError(err)
        self._vars[var.name] = var

    def create_fresh_var(self, vsort, name=None, name_prefix=None, value=None):
        """
        Create new Z3 Variable
        :raise ValueError: if the variable is duplicated
        :param var_sort: The type of the variable, e.g., z3.IntSort()
        :param name: if name is not provided, a new name will be generated
        :return: z3 Variable
        """
        if not name:
            name = self.fresh_var_name(name_prefix)
        else:
            name = sanitize_smt_name(name)
        if name in self._vars:
            err = "Variable name '%s' is already registered" % name
            raise ValueError(err)
        var = SMTVar(name, vsort, value)
        self._register_var(var)
        return var

    def fresh_constraint_name(self, prefix=None):
        """
       Creates a fresh name for tracking the next constraint
       :return: basestring new variable name
       """
        if not prefix:
            prefix = 'Constrain_'
        else:
            prefix = sanitize_smt_name(prefix)
        name = "%s%d" % (prefix, self._next_constnum.next())
        while name in self._vars:
            name = "%s%d" % (prefix, self._next_constnum.next())
        return name

    def register_constraint(self, constraints, name=None, name_prefix=None, **info):
        """
        :param constraints:
        :param name:
        :param name_prefix: a prefix to make generate names easier to read
        :param info:
        :return: name
        """
        if not name:
            name = self.fresh_constraint_name(prefix=name_prefix)
        else:
            name = sanitize_smt_name(name)
        if name in self._tracked:
            err = "Constraint %s is already registered with the " \
                  "constraints: %s while the new constraints are: %s" % (
                      name, constraints, self._tracked[name])
            raise ValueError(err)
        self._tracked[name] = dict(constraints=constraints, info=info)
        return name

    def get_constraint(self, name):
        """Get the constraints tracked by the given name"""
        if name not in self._tracked:
            raise ValueError("Constraint: %s was not registered before" % name)
        return self._tracked[name]['constraints']

    def constraints_itr(self):
        """
        Iterate over all the registered constraints
        yields name, constraint
        """
        for name, value in self._tracked.iteritems():
            yield name, value['constraints']

    def get_constraints_info(self, name):
        """Get additional attributes associated with a constraint"""
        if name not in self._tracked:
            raise ValueError("Constraint: %s was not registered before" % name)
        return self._tracked[name]['info']

    def create_enum_compare(self, enum_name):
        vsort = self.get_enum_type(enum_name)
        z3sort = vsort.sort
        name = 'compare_%s' % enum_name
        err = "Compare function '{}' already created".format(name)
        assert name not in self._enum_compare, err
        func = z3.Function(name, z3sort, z3sort, self.comparator.sort)
        self._enum_compare[name] = func
        self._enum_compare_sort[name] = vsort
        return func

    def set_model(self, model):
        """Set the Z3 model, after solving it"""
        t1 = timer()
        print "Setting the Var values start at", t1
        for var in self._vars.values():
            var.eval(model)
        t2 = timer()
        print "Reading model time: %f" % (t2 - t1)

    def check(self, solver, track=True, set_model=True):
        err1 = "Z3 Solver is not attached to the same Z3 context"
        assert solver.ctx == self.z3_ctx, err1

        t1 = timer()
        partially_eval_vars = len([var for var in self._vars.values() if var.is_concrete])
        partially_eval_const = 0
        for name, const in self.constraints_itr():
            err2 = "Constraint is not attached to the same Z3 context: %s" % const
            assert isinstance(const, bool) or const.ctx == self.z3_ctx, err2
            if track:
                if isinstance(const, bool):
                    var = self.create_fresh_var(z3.BoolSort(ctx=self.z3_ctx), value=None, name_prefix='BoolHack_')
                    solver.assert_and_track(var.var == const, name)
                    solver.assert_and_track(var.var == True, "%s_hack" % name)
                    partially_eval_const += 1
                else:
                    solver.assert_and_track(const, name)
            else:
                solver.add(const)

        # Add comparator constraints:
        GREATER, LESS, EQUAL, INCOMPLETE = self.compare_vars
        tracked_eq = []
        for name, func in self._enum_compare.iteritems():
            vsort = self._enum_compare_sort[name]
            for value1 in vsort.concrete_values:
                var1 = vsort.get_symbolic_value(value1)
                for value2 in vsort.concrete_values:
                    var2 = vsort.get_symbolic_value(value2)
                    pair = set([value1, value2])
                    # Same var is equal
                    if pair not in tracked_eq:
                        equal_const1 = z3.Implies(var1 == var2,
                                                  func(var1, var2) == EQUAL,
                                                  self.z3_ctx)
                        tracked_eq.append(pair)
                    else:
                        equal_const1 = None
                    # Equal is reflexive
                    equal_const2 = z3.Implies(func(var1, var2) == EQUAL,
                                              func(var2, var1) == EQUAL,
                                              self.z3_ctx)
                    # Less is opposite of greater
                    greater_less = z3.Implies(func(var1, var2) == GREATER,
                                              func(var2, var1) == LESS,
                                              self.z3_ctx)
                    # Greater is opposite of less
                    less_greater = z3.Implies(func(var1, var2) == LESS,
                                              func(var2, var1) == GREATER,
                                              self.z3_ctx)
                    if track:
                        suffix = "{}_{}_{}".format(name, value1, value2)
                        if equal_const1 is not None:
                            solver.assert_and_track(equal_const1, "compare_equal_const_{}".format(suffix))
                        solver.assert_and_track(equal_const2, "compare_equal_reflexive_{}".format(suffix))
                        solver.assert_and_track(greater_less, "greater_implies_less_{}".format(suffix))
                        solver.assert_and_track(less_greater, "less_implies_greater_{}".format(suffix))
                    else:
                        solver.add(equal_const1)
                        solver.add(equal_const2)
                        solver.add(greater_less)
                        solver.add(less_greater)
        t2 = timer()
        print "X" * 50
        print "Total Number of variables:", len(self._vars)
        print "Total Number of Constraints:", len(self._tracked)
        print "Total Number of Partially evaluated variables:", partially_eval_vars
        if len(self._vars):
            print "Percentage Partially evaluated variables:", partially_eval_vars / (len(self._vars) * 1.0)
        print "Total Number of Partially evaluated constraints:", partially_eval_const
        if len(self._tracked) > 0:
            print "Percentage Partially evaluated constraints:", partially_eval_const / (len(self._tracked) * 1.0)
        else:
            print "No constraints"
        if (len(self._tracked) +len(self._vars)) > 0:
            print "Total Percentage Partially evaluated:", (partially_eval_vars + partially_eval_const) / ((len(self._tracked) +len(self._vars)) * 1.0)
        print "X" * 50

        print "Constraints adding time: %f" % (t2 - t1)
        print "Start Z3 check", t2
        ret = solver.check()
        t3 = timer()
        print "Z3 check time: %f" % (t3 - t2)
        if set_model and ret == z3.sat:
            self.set_model(solver.model())
        return ret

    @staticmethod
    def create_context(announcements, prefix_list=None, peer_list=None,
                       as_path_list=None, next_hop_list=None,
                       create_as_paths=True):
        """
        Creates the SMT context that contains all the known announcements
        :return: SMTContext
        """
        prefix_list = prefix_list if prefix_list else []
        peer_list = peer_list if peer_list else []
        as_path_list = as_path_list if as_path_list else []
        as_path_list = [get_as_path_key(p) for p in as_path_list]
        next_hope_list = next_hop_list if next_hop_list else []
        announcements = announcements if announcements else []
        assert announcements, "No announcements defined to extract context from"
        ctx = SolverContext(z3.Context())

        # Prefixes
        read_list = [x.prefix for x in announcements if not is_empty(x.prefix)]
        prefix_list = list(set(read_list + prefix_list))
        prefix_list = [sanitize_smt_name(prefix) for prefix in prefix_list]
        ctx.create_enum_type(PREFIX_SORT, prefix_list)

        # Peers
        read_list = [x.peer for x in announcements
                     if not is_empty(x.peer)]
        peer_list = list(set(read_list + peer_list))
        ctx.create_enum_type(PEER_SORT, peer_list)

        # BGP announcement origins
        origin_list = BGP_ATTRS_ORIGIN.__members__.keys()
        ctx.create_enum_type(BGP_ORIGIN_SORT, origin_list)

        # AS path list
        if create_as_paths:
            read_list = [get_as_path_key(x.as_path) for x in announcements
                         if not is_empty(x.as_path)]
            as_path_list = list(set(read_list + as_path_list))
            ctx.create_enum_type(ASPATH_SORT, as_path_list)

        # Next Hop
        read_list = [x.next_hop for x in announcements
                     if not is_empty(x.next_hop)]
        origin_next_hop = 'Zero.Zero.Zero.Zero'
        read_list.append(origin_next_hop)
        next_hope_list = list(set(read_list + next_hope_list))
        next_hope_list = [sanitize_smt_name(next_hop) for next_hop in next_hope_list]
        vsort = ctx.create_enum_type(NEXT_HOP_SORT, next_hope_list)
        ctx.communities = announcements[0].communities.keys()
        ctx.origin_next_hop = sanitize_smt_name(origin_next_hop)
        ctx.origin_next_hop_var = vsort.get_symbolic_value(ctx.origin_next_hop)
        return ctx


class AnnouncementsContext(object):
    """
    A bag of announcements
    this helps, keeping track of the items that mutates these
    announcements
    """

    def __init__(self, announcements, prev_announcements=None, mutators=None):
        self.announcements = announcements
        self.prev_announcements = prev_announcements
        mutators = mutators if mutators else []
        self._mutators = mutators

    @property
    def mutators(self):
        """List of mutators that produced this bag of announcements"""
        return self._mutators

    def __iter__(self):
        for ann in self.announcements:
            yield ann

    def __getitem__(self, item):
        return self.announcements[item]

    def __len__(self):
        return len(self.announcements)

    def create_new(self, announcements, mutator):
        """Create a new context and register a mutator as the creator"""
        mutators = []
        for tmp in self._mutators:
            mutators.append(tmp)
        mutators.append(mutator)
        ctx = AnnouncementsContext(announcements, self, mutators)
        return ctx
