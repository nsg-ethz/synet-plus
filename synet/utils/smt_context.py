#!/usr/bin/env python

"""
Helpers with building SMT Context
"""

import z3

from synet.topo.bgp import VALUENOTSET

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


def is_empty(var):
    """Return true if the variable is VALUENOTSET"""
    return str(var) == VALUENOTSET


def is_symbolic(var):
    """Return True if a given variable is symbolic (z3 var)"""
    return z3.is_const(var)


def get_as_path_key(as_path):
    """Get a key for the path"""
    return 'as_path_' + '_'.join([str(n) for n in as_path])


class SMTValueWrapper(object):
    """
    Help synthesizing a specific value in Announcment
    """

    def __init__(self, name, attr_name, announcement_sort,
                 announcements_var_map, fun, fun_range_sort,
                 range_map, eval_fun, getter, setter, prev_ctxs=None):
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
        self.constraints = {}
        self._model = None
        self._range_is_concerete = None
        if self.range_map is None:
            self._reverse_rang_map = None
        else:
            rev = dict([(v, k) for k, v in self.range_map.iteritems()])
            self._reverse_rang_map =  rev
        for ann_var, ann in self.announcements_var_map.iteritems():
            val = self._getter(ann)
            if is_empty(val):
                self.set_new_var(ann_var)
            elif not is_symbolic(val) and self.range_map is not None:
                self._setter(ann, self.range_map[val])

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

    def set_new_var(self, ann_var):
        """Set a new variable in the announcement"""
        name = "var_%s_%s" % (self.name, str(ann_var))
        value = z3.Const(name, self.fun_range_sort)
        self._setter(self.announcements_var_map[ann_var], value)
        return value

    def get_var(self, ann_var):
        """
        Get the value for the given ann_var
        (applies partial eval whenever possible
        """
        if ann_var not in self.announcements_var_map:
            fun = self.fun
            return fun(ann_var)
        value = self._getter(self.announcements_var_map[ann_var])
        if is_symbolic(value):
            if self._model:
                evaluted = self._eval_fun(self._model, value)
                if str(evaluted) != str(value):
                    self._setter(self.announcements_var_map[ann_var], evaluted)
                return evaluted
            else:
                return value

        return value

    def get_value_of_var(self, var):
        if is_symbolic(var) and self._reverse_rang_map:
            if var in self._reverse_rang_map:
                return self._reverse_rang_map[var]
        return var

    def get_value(self, ann_var):
        """Try the best to get a concerte val"""
        var = self.get_var(ann_var)
        return self.get_value_of_var(var)

    def add_constraints(self, solver):
        """
        Add constraints to the z3 solver that relates to this var
        :param solver:
        :return: dict name->constraints (for unsat core)
        """
        for ctx in self._prev_ctxs:
            prev_constraints = ctx.add_constraints(solver)
            self.constraints.update(prev_constraints)
        if self._fun_used:
            fun = self.fun
            for ann_var in self.ann_var_iter():
                name = self._get_track_name(ann_var)
                val = self.get_var(ann_var)
                constraint = fun(ann_var) == val
                self.constraints[name] = constraint
                solver.assert_and_track(constraint, name)
        return self.constraints

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

    @staticmethod
    def _union_vars(*contexts):
        assert contexts
        all_vars = {}
        for ctx in contexts:
            print contexts
            print ctx
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

        super(SMTLocalPrefWrapper, self).__init__(
            name, 'local_pref', announcement_sort, announcements_var_map,
            localpref_fun, z3.IntSort(), None, eval_fun=eval_fun,
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

        super(SMTASPathLenWrapper, self).__init__(
            name, 'as_path_len', announcement_sort, announcements_var_map,
            as_path_len_fun, z3.IntSort(), None, eval_fun=eval_fun,
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


class SMTContext(object):
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
        self.constraints = {}

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

    def add_constraints(self, solver):
        """
        Add the constraints to the solver
        :param solver:
        :return: dict of constraints
        """
        for prev in self.prev_ctxs:
            self.constraints.update(prev.add_constraints(solver))
        for ctx in self.iter_ctxs():
            self.constraints.update(ctx.add_constraints(solver))
        return self.constraints

    def set_model(self, model):
        """Set z3 model to be used in value eval"""
        for prev in self.prev_ctxs:
            prev.set_model(model)
        for ctx in self.iter_ctxs():
            ctx.set_model(model)

    def get_new_context(self, name, announcements=None, announcements_map=None,
                        announcement_sort=None, prefix_ctx=None, peer_ctx=None,
                        origin_ctx=None, as_path_ctx=None, as_path_len_ctx=None,
                        next_hop_ctx=None, local_pref_ctx=None,
                        communities_ctx=None, permitted_ctx=None,
                        prev_ctxs=None):
        """Helper to create new context with ability to override one or more vars """
        announcements = announcements or self.announcements
        announcements_map = announcements_map or self.announcements_map
        announcement_sort = announcement_sort or self.announcement_sort
        prefix_ctx = prefix_ctx or self.prefix_ctx
        peer_ctx = peer_ctx or self.peer_ctx
        origin_ctx = origin_ctx or self.origin_ctx
        as_path_ctx = as_path_ctx or self.as_path_ctx
        as_path_len_ctx = as_path_len_ctx or self.as_path_len_ctx
        next_hop_ctx = next_hop_ctx or self.next_hop_ctx
        local_pref_ctx = local_pref_ctx or self.local_pref_ctx
        communities_ctx = communities_ctx or self.communities_ctx
        permitted_ctx = permitted_ctx or self.permitted_ctx
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
