#!/usr/bin/env python

"""
Helper class to keep track of SMT vars and constraints
"""

import itertools

import z3

from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Announcement


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


def is_empty(var):
    """Return true if the variable is VALUENOTSET"""
    if hasattr(var, 'get_id'):
        return False
    return str(var) == VALUENOTSET


def is_symbolic(var):
    """Return True if a given variable is symbolic (z3 var)"""
    return z3.is_const(var) or z3.is_expr(var)


def get_as_path_key(as_path):
    """Get a key for the path"""
    return 'as_path_' + '_'.join([str(n) for n in as_path])


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
            ('as_path_len', z3.IntSort(), None),
            ('next_hop', NEXT_HOP_SORT, None),
            ('local_pref', z3.IntSort(), None),
            ('med', z3.IntSort(), None),
            ('permitted', z3.BoolSort(), None),
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
                vsort=z3.BoolSort(), value=value)
            vals['communities'][community] = comm_var
        new_ann = Announcement(**vals)
        new_announcements.append(new_ann)
    return AnnouncementsContext(new_announcements)


class EnumType(object):
    """Create a enum sort"""

    def __init__(self, name, values):
        """
        :param name: Name of the type
        :param values: list of all possible values
        """
        assert values, "Requires at least one value for '%s'" % name
        self._name = name
        self._concrete_values = values
        self._sort, self._symbolic_values = z3.EnumSort(name, values)

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
            err = "Value %s is not defined in %s" % (var,
                                                     self.symbolic_values)
            raise ValueError(err)
        indexof = self.symbolic_values.index(var)
        return self.concrete_values[indexof]

    def __str__(self):
        return "EnumType(%s, %s)" % (self.name, self.concrete_values)

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
                self._value = z3.is_true(value)
            elif value.is_int:
                self._value = value.as_long()
            else:
                err = "Currently only support enums and ints"
                raise NotImplementedError(err)
            self._is_concrete = True
        return self.get_value()


class SolverContext(object):
    """
    Keep track of all variables and constraints to make sure they're unique
    """

    def __init__(self):
        self._vars = {}  # Map a name to a var id
        self._tracked = {}  # Map a name to constraints, additional info
        self._next_varnum = itertools.count(0)
        self._next_constnum = itertools.count(0)
        self._enum_types = {}

    def create_enum_type(self, name, values):
        """Create new Enum type"""
        if name in self._enum_types:
            raise ValueError("EnumSort %s is already defined" % name)
        assert values
        for value in values:
            for ename, etype in self._enum_types.iteritems():
                if value in etype.concrete_values:
                    err = "Duplicate value '%s' already defined in %s" % (
                        value, ename)
                    raise ValueError(err)
        enum_type = EnumType(name, values)
        self._enum_types[name] = enum_type
        return self._enum_types[name]

    def get_enum_type(self, name):
        """Get the EnumType object of the given type name"""
        return self._enum_types[name]

    def fresh_var_name(self):
        """
        Creates a fresh name for the next variable
        :return: basestring new variable name
        """
        name = "Var%d" % self._next_varnum.next()
        while name in self._vars:
            name = "Var%d" % self._next_varnum.next()
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

    def create_fresh_var(self, vsort, name=None, value=None):
        """
        Create new Z3 Variable
        :raise ValueError: if the variable is duplicated
        :param var_sort: The type of the variable, e.g., z3.IntSort()
        :param name: if name is not provided, a new name will be generated
        :return: z3 Variable
        """
        if not name:
            name = self.fresh_var_name()
        if name in self._vars:
            err = "Variable name '%s' is already registered" % name
            raise ValueError(err)
        var = SMTVar(name, vsort, value)
        self._register_var(var)
        return var

    def fresh_constraint_name(self):
        """
       Creates a fresh name for tracking the next constraint
       :return: basestring new variable name
       """
        name = "Const%d" % self._next_constnum.next()
        while name in self._vars:
            name = "Const%d" % self._next_constnum.next()
        return name

    def register_constraint(self, constraints, name=None, **info):
        """
        :param constraints:
        :param name:
        :param info:
        :return: name
        """
        if not name:
            name = self.fresh_constraint_name()
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

    def set_model(self, model):
        """Set the Z3 model, after solving it"""
        for var in self._vars.values():
            var.eval(model)

    @staticmethod
    def create_context(announcements, prefix_list=None, peer_list=None,
                       as_path_list=None, next_hop_list=None):
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

        ctx = SolverContext()

        # Prefixes
        read_list = [x.prefix for x in announcements if not is_empty(x.prefix)]
        prefix_list = list(set(read_list + prefix_list))
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
        read_list = [get_as_path_key(x.as_path) for x in announcements
                     if not is_empty(x.as_path)]
        as_path_list = list(set(read_list + as_path_list))
        ctx.create_enum_type(ASPATH_SORT, as_path_list)

        # Next Hop
        read_list = [x.next_hop for x in announcements
                     if not is_empty(x.next_hop)]
        next_hope_list = list(set(read_list + next_hope_list))
        ctx.create_enum_type(NEXT_HOP_SORT, next_hope_list)
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
