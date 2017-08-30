#!/usr/bin/env python

"""
Helpers with building SMT Context
"""

import z3

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


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


class SMTSymbolicObject(object):
    """Parent for symbolic objects"""

    def set_model(self, model):
        """Set z3 model to be used in value eval"""
        raise NotImplementedError()

    def get_general_constraints(self, get_prev):
        """
        Add constraints to the z3 solver that relates to this var
        :param solver:
        :return: dict name->constraints (for unsat core)
        """
        raise NotImplementedError()

    def get_var_constraints(self, ann_var, get_prev):
        """
        Return constraints specific to a var
        :return tuple name, constraint
        """
        raise NotImplementedError()

    def add_constraints(self, solver, track):
        """
        Add constraints to the z3 solver that relates to this var
        :param solver:
        :return: dict name->constraints (for unsat core)
        """
        raise NotImplementedError()

    def is_concrete(self):
        """
        Return True if this object represents currently all concrete variable
        """
        raise NotImplementedError()


class SMTValueWrapper(SMTSymbolicObject):
    """
    Help synthesizing a specific value in Announcment
    """

    def __init__(self, name, attr_name, announcement_sort,
                 announcements_var_map, fun, fun_range_sort,
                 range_map, eval_fun, getter, setter, var_correctness=None,
                 prev_ctxs=None):
        """
        :param name: ID used in generating new vars
        :param attr_name: the attribute name in the annoucement to be synthesized
        :param announcement_sort: z3 sort for the announcement
        :param announcements_var_map: ann_var -> Announcement object
        :param fun: the function that represent the value (Ann_sort->fun_range_sort)
        :param fun_range_sort: the type of the function
        :param range_map: None or dict if the function not standard
        :param eval_fun: optional to evaluate z3 model (lambda x: x.as_long())
        :param getter: function to get attribute in the announcement
        :param setter: function to set attribute in the announcement
        :param prev_ctx: previous context (if any)
        """
        if prev_ctxs is None:
            prev_ctxs = []
        self.name = name
        self.attr_name = attr_name
        self.announcement_sort = announcement_sort
        self.announcements_var_map = announcements_var_map
        self._fun = fun
        self.fun_range_sort = fun_range_sort
        self.range_map = range_map
        self._eval_fun = eval_fun
        self._getter = getter
        self._setter = setter
        self._prev_ctxs = prev_ctxs
        self._fun_used = False
        self.general_constraints = {}
        #self.var_constraints = {}
        self.var_constraints_ids = {}
        self.var_correctness = var_correctness
        self._model = None
        self._range_is_concerete = None
        self._reverse_rang_map = {}
        self._reverse_rang_map_id = {}
        self.ann_var_ids = {}
        for ann_var, ann in self.announcements_var_map.iteritems():
            new_ann = ann
            val = self._getter(ann)
            if is_empty(val):
                var = self.get_new_var(ann_var)
                new_ann = self._setter(ann, var)
            elif not is_symbolic(val) and self.range_map is not None:
                new_ann = self._setter(ann, self.range_map[val])
            self.ann_var_ids[ann_var.get_id()] = new_ann

    def add_var_constraint(self, ann_var, const):
        var_id = ann_var.get_id()
        if var_id not in self.var_constraints_ids:
            self.var_constraints_ids[var_id] = []
        self.var_constraints_ids[var_id].append(const)

    def ann_var_iter(self):
        """Iterate over the announcement variables defined for this context"""
        for ann_var in self.announcements_var_map:
            yield ann_var

    def _get_track_name(self, ann_var):
        name = "%s_%s_%s_set" % (self.name, ann_var, self.attr_name)
        return str(name)

    def set_model(self, model):
        """Set z3 model to be used in value eval"""
        for ctx in self._prev_ctxs:
            ctx.set_model(model)
        self._model = model

    @property
    def fun(self):
        """The function of the values being synthesized"""
        self._fun_used = True
        return self._fun

    def get_new_var(self, ann_var):
        """Set a new variable in the announcement"""
        name = "var_%s_%s" % (self.name, str(ann_var))
        var = z3.Const(name, self.fun_range_sort)
        return var

    def get_var(self, ann_var):
        """
        Get the value for the given ann_var
        (applies partial eval whenever possible
        """
        var_id = ann_var.get_id()
        if var_id not in self.ann_var_ids:
            fun = self.fun
            return fun(ann_var)
        value = self._getter(self.ann_var_ids[var_id])
        if is_symbolic(value):
            if self._model:
                evaluted = self._eval_fun(self._model, value)
                if str(evaluted) != str(value):
                    self._setter(self.ann_var_ids[var_id], evaluted)
                return evaluted
            else:
                if self.var_correctness and not self.range_map and \
                                var_id not in self.var_constraints_ids:
                    name = "var_%s_%s" % (self.name, str(ann_var))
                    c_name = "%s_correct" % name
                    const = self.var_correctness(value)
                    self.add_var_constraint(ann_var, (c_name, const))
                    #self.var_constraints[ann_var].append((c_name, const))
                return value

        return value

    def get_value_of_var(self, var):
        """Given a variable try to get a concrete value"""
        if is_symbolic(var) and self.range_map:
            if not self._reverse_rang_map:
                for key, value in self.range_map.iteritems():
                    self._reverse_rang_map[value] = key
                    self._reverse_rang_map_id[value.get_id] = key
            var_id = var.get_id()
            ret = self._reverse_rang_map_id.get(var_id, None)
            if ret:
                return ret
            ret2 = self._reverse_rang_map.get(var, None)
            if ret2:
                return ret2
        if is_symbolic(var) and self._model:
            return self._eval_fun(self._model, var)
        return var

    def get_value(self, ann_var):
        """Try the best to get a concerte val"""
        var = self.get_var(ann_var)
        return self.get_value_of_var(var)

    def get_var_constraints(self, ann_var, get_prev):
        var_const = []
        var_id = ann_var.get_id()
        if get_prev:
            for prev_ctx in self._prev_ctxs:
                ret = prev_ctx.get_var_constraints(ann_var, get_prev=True)
                var_const.extend(ret)
        ret = []
        if self._fun_used:
            val = self.get_var(ann_var)
            fun = self._fun
            name = self._get_track_name(ann_var)
            constraint = fun(ann_var) == val
            ret += [(name, constraint)]
        if var_id in self.var_constraints_ids:
            ret.extend(self.var_constraints_ids[var_id])
        return var_const + ret

    def get_general_constraints(self, get_prev):
        constraints = {}
        if get_prev:
            for ctx in self._prev_ctxs:
                prev_constraints = ctx.get_general_constraints(get_prev=True)
                constraints.update(prev_constraints)
        if self._fun_used and self.var_correctness:
            consts = []
            for ann_var in self.announcements_var_map:
                consts.append(self.var_correctness(self._fun(ann_var)))
            constraints["%s_fun_correct" % self.name] = z3.And(*consts)
        return constraints

    def add_constraints(self, solver, track):
        """
        Add constraints to the z3 solver that relates to this var
        :param solver:
        :return: dict name->constraints (for unsat core)
        """
        constraints = {}
        current_constraints = {}
        for ctx in self._prev_ctxs:
            prev_constraints = ctx.add_constraints(solver, track)
            for name, const in prev_constraints.iteritems():
                assert name not in constraints, "Double name %s" % name
                constraints[name] = const
        for ann_var in self.ann_var_iter():
            var_consts = self.get_var_constraints(ann_var, get_prev=False)
            for name, const in var_consts:
                assert name not in constraints, "Double name %s" % name
                constraints[name] = const
                current_constraints[name] = const
        for name, const in current_constraints.iteritems():
            if track:
                solver.assert_and_track(const, name)
            else:
                solver.add(const)
        return constraints

    def _transform_anns(self, ann_vars, transformer):
        """Transform subset of announcements and return new map"""
        new_ann_var_map = {}
        assert set(ann_vars).issubset(set(self.announcements_var_map.keys()))
        for ann_var in ann_vars:
            ann = self.announcements_var_map[ann_var]
            if transformer is not None:
                new_ann_var_map[ann_var] = transformer(ann_var, ann)
            else:
                new_ann_var_map[ann_var] = ann
        return new_ann_var_map

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        raise NotImplementedError()

    def is_range_concrete(self):
        """Return true if the values are defined for every announcement"""
        if self._range_is_concerete is None:
            self._range_is_concerete = True
            for ann_var in self.ann_var_iter():
                val = self.get_var(ann_var)
                if self.range_map is None:
                    if is_symbolic(val):
                        self._range_is_concerete = False
                        break
                else:
                    if is_symbolic(val) and val not in self.range_map.values():
                        self._range_is_concerete = False
                        break
        return self._range_is_concerete

    def is_concrete(self):
        return self.is_range_concrete()

    def __str__(self):
        return "<%s(%s)>" % (self.__class__.__name__, self.name)

    @staticmethod
    def _union_vars(*contexts):
        assert contexts
        all_vars = {}
        for ctx in contexts:
            # Context must not intersect
            curr = set(all_vars.keys())
            new_set = set(ctx.announcements_var_map.keys())
            assert not curr.intersection(new_set)
            for arg, ann in ctx.announcements_var_map.iteritems():
                all_vars[arg] = ann
        return all_vars

    @staticmethod
    def union(name, new_fun, *contexts):
        """
        Union multipe contexts
        Each context must map to different subset of the announcements
        """
        raise NotImplementedError()


class SMTPrefixWrapper(SMTValueWrapper):
    """Prefix value in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 prefix_fun, prefix_sort, prefix_map, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTPrefixWrapper)

        eval_fun = lambda model, val: model.eval(val)
        getter = lambda ann: ann.prefix

        def setter(ann, value):
            """Set the prefix value in the Announcement"""
            ann.prefix = value
            return ann

        super(SMTPrefixWrapper, self).__init__(
            name, 'prefix', announcement_sort, announcements_var_map,
            prefix_fun, prefix_sort, prefix_map, eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTPrefixWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            prefix_fun=new_fun, prefix_sort=self.fun_range_sort,
            prefix_map=self.range_map, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTPrefixWrapper(
            name, first.announcement_sort, all_vars,
            first.fun, first.fun_range_sort, first.range_map,
            prev_ctxs=contexts)


class SMTOriginWrapper(SMTValueWrapper):
    """Origin value in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 origin_fun, origin_sort, origin_map, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTOriginWrapper)

        eval_fun = lambda model, val: model.eval(val)
        getter = lambda ann: ann.origin

        def setter(ann, value):
            """Set the origin value in the Announcement"""
            ann.origin = value
            return ann

        super(SMTOriginWrapper, self).__init__(
            name, 'origin', announcement_sort, announcements_var_map,
            origin_fun, origin_sort, origin_map, eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTOriginWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            origin_fun=new_fun, origin_sort=self.fun_range_sort,
            origin_map=self.range_map, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTOriginWrapper(
            name, first.announcement_sort, all_vars,
            first.fun, first.fun_range_sort, first.range_map,
            prev_ctxs=contexts)


class SMTPeerWrapper(SMTValueWrapper):
    """Peer value in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 peer_fun, peer_sort, peer_map, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTPeerWrapper)

        eval_fun = lambda model, val: model.eval(val)
        getter = lambda ann: ann.peer

        def setter(ann, value):
            """Set the peer value in the Announcement"""
            ann.peer = value
            return ann

        super(SMTPeerWrapper, self).__init__(
            name, 'peer', announcement_sort, announcements_var_map,
            peer_fun, peer_sort, peer_map, eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTPeerWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            peer_fun=new_fun, peer_sort=self.fun_range_sort,
            peer_map=self.range_map, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTPeerWrapper(
            name, first.announcement_sort, all_vars,
            first.fun, first.fun_range_sort, first.range_map,
            prev_ctxs=contexts)


class SMTNexthopWrapper(SMTValueWrapper):
    """Nexthop value in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 next_hop_fun, next_hop_sort, next_hop_map, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTNexthopWrapper)

        eval_fun = lambda model, val: model.eval(val)
        getter = lambda ann: ann.next_hop

        def setter(ann, value):
            """Set the next hop value in the Announcement"""
            ann.next_hop = value
            return ann

        super(SMTNexthopWrapper, self).__init__(
            name, 'next_hop', announcement_sort, announcements_var_map,
            next_hop_fun, next_hop_sort, next_hop_map, eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTNexthopWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            next_hop_fun=new_fun, next_hop_sort=self.fun_range_sort,
            next_hop_map=self.range_map, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTNexthopWrapper(
            name, first.announcement_sort, all_vars,
            first.fun, first.fun_range_sort, first.range_map,
            prev_ctxs=contexts)


class SMTLocalPrefWrapper(SMTValueWrapper):
    """LocalPref value in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 localpref_fun, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTLocalPrefWrapper)

        eval_fun = lambda model, val: model.eval(val).as_long()
        getter = lambda ann: ann.local_pref

        def setter(ann, value):
            """Set the local pref value in the Announcement"""
            ann.local_pref = value
            return ann

        super(SMTLocalPrefWrapper, self).__init__(
            name, 'local_pref', announcement_sort, announcements_var_map,
            localpref_fun, z3.IntSort(), None, eval_fun=eval_fun,
            var_correctness=lambda var: var > 0,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTLocalPrefWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            localpref_fun=new_fun, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTLocalPrefWrapper(
            name, first.announcement_sort, all_vars,
            first.fun, prev_ctxs=contexts)


class SMTCommunityWrapper(SMTValueWrapper):
    """Community value in Announcement"""

    def __init__(self, name, community, announcement_sort,
                 announcements_var_map, community_fun, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTCommunityWrapper)

        eval_fun = lambda model, val: z3.is_true(model.eval(val))
        getter = lambda ann: ann.communities[community]

        def setter(ann, value):
            """Set the community value in the Announcement"""
            ann.communities[community] = value
            return ann

        super(SMTCommunityWrapper, self).__init__(
            name, 'Has_%s' % community.name, announcement_sort,
            announcements_var_map,
            community_fun, z3.BoolSort(), None, eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)
        self.community = community

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars, transformer=transformer)
        obj = SMTCommunityWrapper(
            name=name, community=self.community,
            announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            community_fun=new_fun, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTCommunityWrapper(
            name, first.community, first.announcement_sort, all_vars,
            first.fun, prev_ctxs=contexts)


class SMTASPathLenWrapper(SMTValueWrapper):
    """AS Path Length value in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 as_path_len_fun, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTASPathLenWrapper)

        eval_fun = lambda model, val: model.eval(val).as_long()
        getter = lambda ann: ann.as_path_len

        def setter(ann, value):
            """Set the AS Length value in the Announcement"""
            ann.as_path_len = value
            return ann

        super(SMTASPathLenWrapper, self).__init__(
            name=name, attr_name='as_path_len',
            announcement_sort=announcement_sort,
            announcements_var_map=announcements_var_map,
            fun=as_path_len_fun, fun_range_sort=z3.IntSort(),
            range_map=None,
            var_correctness=lambda var: var >= 0,
            eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTASPathLenWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            as_path_len_fun=new_fun, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTASPathLenWrapper(
            name, first.announcement_sort, all_vars,
            first.fun, prev_ctxs=contexts)


class SMTASPathWrapper(SMTValueWrapper):
    """AS Path value in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 as_path_fun, as_path_sort, as_path_map, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTASPathWrapper)

        eval_fun = lambda model, val: model.eval(val)

        def getter(ann):
            """Get the path key"""
            path_key = ann.as_path
            if isinstance(path_key, list):
                path_key = as_path_map[get_as_path_key(path_key)]
            return path_key

        def setter(ann, value):
            """Set the AS path value in the Announcement"""
            ann.as_path = value
            return ann

        super(SMTASPathWrapper, self).__init__(
            name, 'as_path', announcement_sort, announcements_var_map,
            as_path_fun, as_path_sort, as_path_map, eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTASPathWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            as_path_fun=new_fun, as_path_sort=self.fun_range_sort,
            as_path_map=self.range_map, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTASPathWrapper(
            name, first.announcement_sort, all_vars,
            first.fun, first.fun_range_sort, first.range_map,
            prev_ctxs=contexts)


class SMTPermittedWrapper(SMTValueWrapper):
    """Route allowed to pass through in Announcement"""

    def __init__(self, name, announcement_sort, announcements_var_map,
                 permitted_fun, prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        for ctx in prev_ctxs:
            assert isinstance(ctx, SMTPermittedWrapper)

        eval_fun = lambda model, val: z3.is_true(model.eval(val))
        getter = lambda ann: ann.permitted

        def setter(ann, value):
            """Set the local pref value in the Announcement"""
            ann.permitted = value
            return ann

        super(SMTPermittedWrapper, self).__init__(
            name, 'permitted', announcement_sort, announcements_var_map,
            permitted_fun, z3.BoolSort(), None, eval_fun=eval_fun,
            getter=getter, setter=setter, prev_ctxs=prev_ctxs)

    def get_new_context(self, name, ann_vars, new_fun, transformer):
        """Create a new context variable"""
        new_map = self._transform_anns(ann_vars=ann_vars,
                                       transformer=transformer)
        obj = SMTPermittedWrapper(
            name=name, announcement_sort=self.announcement_sort,
            announcements_var_map=new_map,
            permitted_fun=new_fun, prev_ctxs=[self])
        return obj

    @staticmethod
    def union(name, new_fun, *contexts):
        all_vars = SMTValueWrapper._union_vars(*contexts)
        first = contexts[0]
        return SMTPermittedWrapper(
            name, first.announcement_sort, all_vars, first.fun,
            prev_ctxs=contexts)


class SMTContext(SMTSymbolicObject):
    """
    Hold SMT Context needed for the policy synthesis
    """

    def __init__(self, name, announcements, announcements_map, announcement_sort,
                 prefix_ctx, peer_ctx, origin_ctx, as_path_ctx, as_path_len_ctx,
                 next_hop_ctx, local_pref_ctx, communities_ctx, permitted_ctx,
                 prev_ctxs=None):
        if prev_ctxs is None:
            prev_ctxs = []
        assert isinstance(prefix_ctx, SMTPrefixWrapper)
        assert isinstance(peer_ctx, SMTPeerWrapper)
        assert isinstance(origin_ctx, SMTOriginWrapper)
        assert isinstance(as_path_ctx, SMTASPathWrapper)
        assert isinstance(as_path_len_ctx, SMTASPathLenWrapper)
        assert isinstance(next_hop_ctx, SMTNexthopWrapper)
        assert isinstance(local_pref_ctx, SMTLocalPrefWrapper)
        assert isinstance(communities_ctx, dict)
        assert isinstance(permitted_ctx, SMTPermittedWrapper)
        for comm_ctx in communities_ctx.itervalues():
            assert isinstance(comm_ctx, SMTCommunityWrapper)
        for prev_ctx in prev_ctxs:
            assert isinstance(prev_ctx, SMTContext)

        self.name = name
        self.announcements = announcements
        self.announcements_map = announcements_map
        self.announcement_sort = announcement_sort
        self.prefix_ctx = prefix_ctx
        self.peer_ctx = peer_ctx
        self.origin_ctx = origin_ctx
        self.as_path_ctx = as_path_ctx
        self.as_path_len_ctx = as_path_len_ctx
        self.next_hop_ctx = next_hop_ctx
        self.local_pref_ctx = local_pref_ctx
        self.communities_ctx = communities_ctx
        self.permitted_ctx = permitted_ctx
        self.prev_ctxs = prev_ctxs
        self.ctx_names = ['prefix_ctx', 'peer_ctx', 'origin_ctx',
                          'as_path_ctx', 'as_path_len_ctx', 'next_hop_ctx',
                          'local_pref_ctx', 'communities_ctx', 'permitted_ctx']

        for ctx in self.iter_ctxs():
            attr_vars = set(ctx.announcements_var_map.keys())
            ctx_vars = set(self.announcements_map.values())
            err = "Different announcements for %s" % ctx.name
            assert ctx_vars == attr_vars, err

    def iter_ctxs(self):
        """
        Iterate over all the context for each variable in the Announcement
        """
        for name in self.ctx_names:
            var = getattr(self, name)
            if isinstance(var, dict):
                for value in var.itervalues():
                    yield value
            else:
                yield var

    def get_general_constraints(self, get_prev):
        constraints = {}
        if get_prev:
            for prev_ctx in self.prev_ctxs:
                prev_consts = prev_ctx.get_general_constraints(get_prev=True)
                for name, const in prev_consts.iteritems():
                    assert name not in constraints, "Double name %s" % name
                    constraints[name] = const
        for val_ctx in self.iter_ctxs():
            prev_consts = val_ctx.get_general_constraints(False)
            for name, const in prev_consts.iteritems():
                assert name not in constraints, "Double name %s" % name
                constraints[name] = const
        return constraints

    def get_var_constraints(self, ann_var, get_prev):
        var_consts = []
        for val_ctx in self.iter_ctxs():
            ret = val_ctx.get_var_constraints(ann_var, get_prev)
            var_consts.extend(ret)
        return var_consts

    def add_constraints(self, solver, track):
        """
        Add the constraints to the solver
        :param solver:
        :return: dict of constraints
        """
        constraints = self.get_general_constraints(get_prev=True)
        val_ctx = self.permitted_ctx
        for ann_var in val_ctx.ann_var_iter():
            var_consts = self.get_var_constraints(ann_var, get_prev=True)
            for name, const in var_consts:
                assert name not in constraints, "Double name %s" % name
                constraints[name] = const
        for name, const in constraints.iteritems():
            if track:
                solver.assert_and_track(const, name)
            else:
                solver.add(const)
        return constraints

    def set_model(self, model):
        """Set z3 model to be used in value eval"""
        for prev in self.prev_ctxs:
            prev.set_model(model)
        for ctx in self.iter_ctxs():
            ctx.set_model(model)

    def is_concrete(self):
        for ctx in self.iter_ctxs():
            if not ctx.is_concrete():
                return False
        for prev in self.prev_ctxs:
            if not prev.is_concrete():
                return False
        return True

    def get_new_context(self, name, announcements=None, announcements_map=None,
                        announcement_sort=None, prefix_ctx=None, peer_ctx=None,
                        origin_ctx=None, as_path_ctx=None, as_path_len_ctx=None,
                        next_hop_ctx=None, local_pref_ctx=None,
                        communities_ctx=None, permitted_ctx=None,
                        prev_ctxs=None, transformer=None):
        """Helper to create new context with ability to override one or more vars """
        announcements = announcements if announcements is not None else self.announcements
        announcements_map = announcements_map if announcements_map is not None else self.announcements_map
        announcement_sort = announcement_sort or self.announcement_sort
        ann_vars_map = {}
        for ann_name, ann_var in announcements_map.iteritems():
            ann_vars_map[ann_var] = announcements[ann_name]

        def empty_transformer(ann_var, ann):
            return ann_vars_map[ann_var]

        if not transformer:
            transformer = empty_transformer

        def get_val_context(given, original):
            """Decide on the proper value context"""
            # If a new value context then use it
            if given:
                return given
            # If the announcements in the context didn't change
            # the use the original context
            new_vals = set(ann_vars_map.values())
            old_vals = set(self.announcements_map.values())
            if transformer == empty_transformer and new_vals == old_vals:
                return original
            # Else create a new context with a subset of the args
            new_fun = z3.Function("%s_subset_%s_fun" % (name, original.name),
                                  self.announcement_sort,
                                  original.fun_range_sort)
            return original.get_new_context(
                name="%s_subset_%s" % (name, original.name),
                ann_vars=ann_vars_map.keys(),
                new_fun=new_fun,
                transformer=transformer)
        prefix_ctx = get_val_context(prefix_ctx, self.prefix_ctx)
        peer_ctx = get_val_context(peer_ctx, self.peer_ctx)
        origin_ctx = get_val_context(origin_ctx, self.origin_ctx)
        as_path_ctx = get_val_context(as_path_ctx, self.as_path_ctx)
        as_path_len_ctx = get_val_context(as_path_len_ctx, self.as_path_len_ctx)
        next_hop_ctx = get_val_context(next_hop_ctx, self.next_hop_ctx)
        local_pref_ctx = get_val_context(local_pref_ctx, self.local_pref_ctx)
        if not communities_ctx:
            communities_ctx = {}
        for comm in self.communities_ctx:
            communities_ctx[comm] = get_val_context(
                communities_ctx.get(comm, None), self.communities_ctx[comm])
        permitted_ctx = get_val_context(permitted_ctx, self.permitted_ctx)
        if prev_ctxs is None:
            prev_ctxs = []
        prev_ctxs = [self] + prev_ctxs

        ctx = SMTContext(
            name=name,
            announcements=announcements,
            announcements_map=announcements_map,
            announcement_sort=announcement_sort,
            prefix_ctx=prefix_ctx,
            peer_ctx=peer_ctx,
            origin_ctx=origin_ctx,
            as_path_ctx=as_path_ctx,
            as_path_len_ctx=as_path_len_ctx,
            next_hop_ctx=next_hop_ctx,
            local_pref_ctx=local_pref_ctx,
            communities_ctx=communities_ctx,
            permitted_ctx=permitted_ctx,
            prev_ctxs=prev_ctxs
        )
        return ctx

    @staticmethod
    def union(name, *contexts):
        assert contexts
        anns = {}
        anns_map = {}
        ann_sort = contexts[0].announcement_sort
        ctx_names = contexts[0].ctx_names
        val_ctx = {}
        for val_name in ctx_names:
            if val_name == 'communities_ctx':
                val_ctx[val_name] = {}
                for comm in contexts[0].communities_ctx:
                    all_vals = [getattr(c, val_name)[comm] for c in contexts]
                    new_fun = z3.Function(
                        "%s_union_%s_%s_fun" % (name, val_name, comm.name),
                        ann_sort,
                        all_vals[0].fun_range_sort
                    )
                    val_ctx[val_name][comm] = all_vals[0].union(
                        "%s_union_%s_%s_ctx" % (name, val_name, comm.name),
                        new_fun,
                        *all_vals)
            else:
                all_vals = [getattr(c, val_name) for c in contexts]
                new_fun = z3.Function(
                    "%s_union_%s_fun" % (name, val_name),
                    ann_sort,
                    all_vals[0].fun_range_sort
                )
                val_ctx[val_name] = all_vals[0].union(
                    "%s_union_%s_ctx" % (name, val_name),
                    new_fun,
                    *all_vals)

        for ctx in contexts:
            for name, ann in ctx.announcements.iteritems():
                assert name not in anns, "Context must be disjoint"
            anns[name] = ann
            anns_map[name] = ctx.announcements_map[name]
        val_ctx['prev_ctxs'] = contexts

        return SMTContext(name=name, announcements=anns,
                          announcements_map=anns_map,
                          announcement_sort=ann_sort,
                          **val_ctx)
