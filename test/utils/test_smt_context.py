import unittest

import z3

from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community

from synet.utils.smt_context import SMTASPathWrapper
from synet.utils.smt_context import SMTASPathLenWrapper
from synet.utils.smt_context import SMTContext
from synet.utils.smt_context import SMTCommunityWrapper
from synet.utils.smt_context import SMTLocalPrefWrapper
from synet.utils.smt_context import SMTNexthopWrapper
from synet.utils.smt_context import SMTOriginWrapper
from synet.utils.smt_context import SMTPeerWrapper
from synet.utils.smt_context import SMTPrefixWrapper
from synet.utils.smt_context import SMTPermittedWrapper
from synet.utils.smt_context import get_as_path_key
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import is_symbolic
from synet.utils.smt_context import VALUENOTSET


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class SMTSetup(unittest.TestCase):
    def _pre_load(self):
        raise NotImplementedError()

    def get_solver(self):
        solver = z3.Solver()
        return solver

    def _define_types(self, prefix_list=None, nexthope_list=None,
                      peer_list=None, as_path_list=None):
        # Ann Type
        (self.ann_sort, self.announcements) = \
            z3.EnumSort('AnnouncementSort', self.anns.keys())


        ann_map = dict([(str(ann), ann) for ann in self.announcements])
        self.ann_map = ann_map
        self.ann_var_map = dict([(self.ann_map[ann], self.anns[str(ann)]) for ann in self.ann_map])

        self.local_pref_fun = z3.Function('LocalPref', self.ann_sort, z3.IntSort())
        self.permitted_fun = z3.Function('PermittedFun', self.ann_sort, z3.BoolSort())

        if not prefix_list:
            l = [ann.prefix for ann in self.anns.values() if not is_empty(ann.prefix)]
            prefix_list = list(set(l))
        (self.prefix_sort, self.prefixes) = z3.EnumSort('PrefixSort', prefix_list)

        prefix_map = dict([(str(prefix), prefix) for prefix in self.prefixes])
        self.prefix_map = prefix_map
        self.prefix_fun = z3.Function('PrefixFunc', self.ann_sort, self.prefix_sort)

        if not peer_list:
            l = [x.peer for x in self.anns.values() if not is_empty(x.peer)]
            peer_list = list(set(l))
        (self.peer_sort, self.peers) = z3.EnumSort('PeerSort', peer_list)
        peer_map = dict([(str(p), p) for p in self.peers])
        self.peer_map = peer_map
        self.peer_fun = z3.Function('PeerFun', self.ann_sort, self.peer_sort)

        origin_list = BGP_ATTRS_ORIGIN.__members__.keys()
        (self.origin_sort, self.origins) = z3.EnumSort('OriginSort', origin_list)
        origin_map = dict([(str(p), p) for p in self.origins])
        for k, v in BGP_ATTRS_ORIGIN.__members__.iteritems():
            origin_map[v] = origin_map[k]
        self.origin_map = origin_map
        self.origin_fun = z3.Function('OriginFun', self.ann_sort, self.origin_sort)

        if not as_path_list:
            l = [get_as_path_key(x.as_path) for x in self.anns.values()
                 if not is_empty(x.as_path)]
            as_path_list = list(set(l))
        (self.as_path_sort, self.as_paths) = z3.EnumSort('PrefixSort', as_path_list)

        as_path_map = dict([(str(p), p) for p in self.as_paths])
        self.as_path_map = as_path_map
        self.as_path_fun = z3.Function('AsPathFunc', self.ann_sort, self.as_path_sort)
        self.as_path_len_fun = z3.Function('AsPathLenFunc', self.ann_sort, z3.IntSort())

        if not nexthope_list:
            l = [x.next_hop for x in self.anns.values() if not is_empty(x.next_hop)]
            nexthope_list = list(set(l))
        (self.nexthop_sort, self.nexthops) = z3.EnumSort('NexthopSort', nexthope_list)

        nexthop_map = dict([(str(p), p) for p in self.nexthops])
        self.nexthop_map = nexthop_map
        self.nexthop_fun = z3.Function('NexthopFunc', self.ann_sort, self.nexthop_sort)

        # Create functions for communities
        self.communities_fun = {}
        self.reverse_communities = {}
        for c in self.all_communities:
            name = 'Has_%s' % c.name
            self.communities_fun[c] = z3.Function(name, self.ann_sort, z3.BoolSort())
            self.reverse_communities[name] = c

        self.route_denied_fun = z3.Function('route_denied', self.ann_sort, z3.BoolSort())

    def setUp(self):
        self._pre_load()
        self._define_types()


class TestSMTPrefixWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix=VALUENOTSET, peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_NotSet': ann2,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_NotSet']
        google = self.prefix_map['Google']

        # Create wrapper
        w = SMTPrefixWrapper(
            name='wprefix', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            prefix_fun=self.prefix_fun, prefix_sort=self.prefix_sort,
            prefix_map=self.prefix_map)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(len(constraints), 0)
        self.assertEquals(w.get_var(ann1), google)
        self.assertEquals(w.get_value(ann1), 'Google')
        self.assertTrue(is_symbolic(w.get_var(ann2)))
        self.assertTrue(is_symbolic(w.get_value(ann2)))

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_NotSet']
        google = self.prefix_map['Google']
        # Create wrapper
        w = SMTPrefixWrapper(
            name='wprefix', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            prefix_fun=self.prefix_fun, prefix_sort=self.prefix_sort,
            prefix_map=self.prefix_map)
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.get_var(tmp) == google))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), google)
        self.assertEquals(w.get_value(ann1), 'Google')
        self.assertEquals(w.get_var(ann2), google)
        self.assertEquals(w.get_value(ann2), 'Google')

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_NotSet']
        google = self.prefix_map['Google']
        # Create wrapper
        w = SMTPrefixWrapper(
            name='wprefix', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            prefix_fun=self.prefix_fun, prefix_sort=self.prefix_sort,
            prefix_map=self.prefix_map)
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.fun(tmp) == google))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), google)
        self.assertEquals(w.get_value(ann1), 'Google')
        self.assertEquals(w.get_var(ann2), google)
        self.assertEquals(w.get_value(ann2), 'Google')

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_NotSet']
        self._define_types(prefix_list=['Google', 'Yahoo'])
        google = self.prefix_map['Google']
        yahoo = self.prefix_map['Yahoo']

        new_fun = z3.Function('NewFunc', self.ann_sort, self.prefix_sort)

        def transformer(ann_var, ann):
            new_ann = ann.copy()
            new_ann.prefix = yahoo
            return new_ann

        # Create wrapper
        w1 = SMTPrefixWrapper(
            name='wprefix1', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            prefix_fun=self.prefix_fun, prefix_sort=self.prefix_sort,
            prefix_map=self.prefix_map)

        w2 = w1.get_new_context(name='wp2', ann_vars=self.ann_var_map.keys(),
                                new_fun=new_fun, transformer=transformer)

        # Assumptions
        solver = self.get_solver()
        tmp1 = z3.Const('test_tmp1', self.ann_sort)
        tmp2 = z3.Const('test_tmp2', self.ann_sort)
        solver.add(z3.ForAll([tmp1], w1.get_var(tmp1) == google))
        solver.add(z3.ForAll([tmp2], w2.get_var(tmp1) == yahoo))
        w2.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        w2.set_model(model)
        self.assertEquals(w1.get_var(ann1), google)
        self.assertEquals(w1.get_var(ann2), google)
        self.assertEquals(w2.get_var(ann1), yahoo)
        self.assertEquals(w2.get_var(ann2), yahoo)


class TestSMTPeerWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer=VALUENOTSET, origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        swisscom = self.peer_map['SwissCom']

        # Create wrapper
        w = SMTPeerWrapper(
            name='wprefix', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            peer_fun=self.peer_fun, peer_sort=self.peer_sort,
            peer_map=self.peer_map)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(len(constraints), 0)
        self.assertEquals(w.get_var(ann1), swisscom)
        self.assertTrue(is_symbolic(w.get_var(ann2)))

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        swisscom = self.peer_map['SwissCom']

        # Create wrapper
        w = SMTPeerWrapper(
            name='wprefix', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            peer_fun=self.peer_fun, peer_sort=self.peer_sort,
            peer_map=self.peer_map)

        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.get_var(tmp) == swisscom))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), swisscom)
        self.assertEquals(w.get_var(ann2), swisscom)

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        swisscom = self.peer_map['SwissCom']

        # Create wrapper
        w = SMTPeerWrapper(
            name='wprefix', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            peer_fun=self.peer_fun, peer_sort=self.peer_sort,
            peer_map=self.peer_map)

        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.fun(tmp) == swisscom))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), swisscom)
        self.assertEquals(w.get_var(ann2), swisscom)

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        self._define_types(peer_list=['SwissCom', 'DT'])
        swisscom = self.peer_map['SwissCom']
        dt = self.peer_map['DT']

        new_fun = z3.Function('NewFunc', self.ann_sort, self.peer_sort)

        def transformer(ann_var, ann):
            new_ann = ann.copy()
            new_ann.peer = dt
            return new_ann

        # Create wrapper
        w1 = SMTPeerWrapper(
            'wp1', self.ann_sort, self.ann_var_map,
            self.peer_fun, self.peer_sort,
            self.peer_map)

        w2 = w1.get_new_context(name='wp2', ann_vars=self.ann_var_map.keys(),
                                new_fun=new_fun,
                                transformer=transformer)
        # Assumptions
        solver = self.get_solver()
        tmp1 = z3.Const('test_tmp', self.ann_sort)
        tmp2 = z3.Const('test_tmp2', self.ann_sort)
        solver.add(z3.ForAll([tmp1], w1.fun(tmp1) == swisscom))
        solver.add(z3.ForAll([tmp1], w2.get_var(tmp2) == dt))
        w2.add_constraints(solver, True)
        # Assertions
        ret = solver.check()
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        w2.set_model(model)
        self.assertEquals(w1.get_var(ann1), swisscom)
        self.assertEquals(w1.get_var(ann2), swisscom)
        self.assertEquals(w2.get_var(ann1), dt)
        self.assertEquals(w2.get_var(ann2), dt)


class TestSMTOriginWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Google', peer='DT', origin=BGP_ATTRS_ORIGIN.IGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann3 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.INCOMPLETE,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=True)

        ann4 = Announcement(
            prefix='Yahoo', peer='DT', origin=VALUENOTSET,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Google': ann2,
            'Ann3_Yahoo': ann3,
            'Ann4_Yahoo': ann4,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Google']
        ann3 = self.ann_map['Ann3_Yahoo']
        ann4 = self.ann_map['Ann4_Yahoo']
        ebgp = self.origin_map['EBGP']
        igp = self.origin_map['IGP']
        incomplete = self.origin_map['INCOMPLETE']

        # Create wrapper
        w = SMTOriginWrapper(
            name='worigin', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            origin_fun=self.origin_fun, origin_sort=self.origin_sort,
            origin_map=self.origin_map)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(len(constraints), 0)
        self.assertEquals(w.get_var(ann1), ebgp)
        self.assertEquals(w.get_var(ann2), igp)
        self.assertEquals(w.get_var(ann3), incomplete)
        self.assertTrue(is_symbolic(w.get_var(ann4)))

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Google']
        ann3 = self.ann_map['Ann3_Yahoo']
        ann4 = self.ann_map['Ann4_Yahoo']
        ebgp = self.origin_map['EBGP']
        igp = self.origin_map['IGP']
        incomplete = self.origin_map['INCOMPLETE']

        # Create wrapper
        w = SMTOriginWrapper(
            name='worigin', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            origin_fun=self.origin_fun, origin_sort=self.origin_sort,
            origin_map=self.origin_map)

        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(tmp == ann4)
        solver.add(w.get_var(tmp) == ebgp)
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), ebgp)
        self.assertEquals(w.get_var(ann2), igp)
        self.assertEquals(w.get_var(ann3), incomplete)
        self.assertEquals(w.get_var(ann4), ebgp)

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Google']
        ann3 = self.ann_map['Ann3_Yahoo']
        ann4 = self.ann_map['Ann4_Yahoo']
        ebgp = self.origin_map['EBGP']
        igp = self.origin_map['IGP']
        incomplete = self.origin_map['INCOMPLETE']

        # Create wrapper
        w = SMTOriginWrapper(
            name='worigin', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            origin_fun=self.origin_fun, origin_sort=self.origin_sort,
            origin_map=self.origin_map)

        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(tmp == ann4)
        solver.add(w.fun(tmp) == ebgp)
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), ebgp)
        self.assertEquals(w.get_var(ann2), igp)
        self.assertEquals(w.get_var(ann3), incomplete)
        self.assertEquals(w.get_var(ann4), ebgp)

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Google']
        ann3 = self.ann_map['Ann3_Yahoo']
        ann4 = self.ann_map['Ann4_Yahoo']
        ebgp = self.origin_map['EBGP']
        igp = self.origin_map['IGP']
        incomplete = self.origin_map['INCOMPLETE']

        new_fun = z3.Function('NewFun', self.ann_sort, self.origin_sort)

        def transorm(ann_var, ann):
            new_ann = ann.copy()
            new_ann.origin = BGP_ATTRS_ORIGIN.EBGP
            return new_ann

        # Create wrapper
        w1 = SMTOriginWrapper(
            name='wo1', announcement_sort=self.ann_sort,
            announcements_var_map=self.ann_var_map,
            origin_fun=self.origin_fun, origin_sort=self.origin_sort,
            origin_map=self.origin_map)

        w2 = w1.get_new_context(name='wo2', ann_vars=[ann1, ann2],
                                new_fun=new_fun, transformer=transorm)

        # Assumptions
        solver = self.get_solver()
        tmp1 = z3.Const('test_tmp', self.ann_sort)
        solver.add(tmp1 == ann4)
        solver.add(w1.get_var(tmp1) == ebgp)
        solver.add(w2.get_var(ann1) == ebgp)
        solver.add(w2.get_var(ann2) == ebgp)
        w2.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w2.set_model(model)
        print solver.to_smt2()
        print model
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w1.get_var(ann1), ebgp)
        self.assertEquals(w1.get_var(ann2), igp)
        self.assertEquals(w1.get_var(ann3), incomplete)
        self.assertEquals(w1.get_var(ann4), ebgp)
        self.assertEquals(w2.get_var(ann1), ebgp)


class TestSMTNexthopWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop=VALUENOTSET,
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        swisscom = self.nexthop_map['SwissCom']
        # Create wrapper
        w = SMTNexthopWrapper(
            'nxthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), swisscom)
        self.assertEquals(len(constraints), 0)

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        swisscom = self.nexthop_map['SwissCom']
        # Create wrapper
        w = SMTNexthopWrapper(
            'nxthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), swisscom)
        self.assertTrue(is_symbolic(w.get_var(ann2)))
        self.assertEquals(len(constraints), 0)
        w.set_model(solver.model())
        #self.assertEquals(w.get_val(ann2), swisscom)

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        solver = self.get_solver()
        swisscom = self.nexthop_map['SwissCom']
        # Create wrapper
        w = SMTNexthopWrapper(
            'nxthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)
        tmp = z3.Const('test_tmp', self.ann_sort)

        solver.add(z3.ForAll([tmp], w.fun(tmp) == swisscom))
        constraints = w.add_constraints(solver, True)
        # Assertions
        ret = solver.check()
        self.assertEquals(ret, z3.sat)
        self.assertTrue(len(constraints) > 0)
        self.assertEquals(str(w.get_var(ann1)), str(swisscom))
        self.assertTrue(is_symbolic(w.get_var(ann2)))
        self.assertEquals(len(constraints), 2)

    def test_concrete_stress(self):
        num_communities = 1
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            nexthop = 'nexthop_%d' % i
            cs = [(c, 'F') for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                prefix=name, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop=nexthop,
                local_pref=100, communities=cs, permitted=True)
            self.anns[name] = ann
        self._define_types()

        # Create Wrapper
        w = SMTNexthopWrapper(
            'nxthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(constraints, {})
        for ann_name, ann_var in self.ann_map.iteritems():
            ann = self.anns[ann_name]
            self.assertEquals(w.get_var(ann_var), ann.next_hop)
            self.assertEquals(w.get_value(ann_var), str(ann.next_hop))

    def test_symbolic_stress(self):
        # Generate announcements
        num_communities = 1
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        nexthoplist = []
        nexthop_map = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            nexthop = 'nexthop_%d' % i
            nexthop_map[name] = nexthop
            nexthoplist.append(nexthop)
            cs = [(c, 'F') for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                prefix=name, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop=VALUENOTSET,
                local_pref=100, communities=cs, permitted=True)
            self.anns[name] = ann
        self._define_types(nexthope_list=nexthoplist)

        # Create Wrapper
        w = SMTNexthopWrapper(
            'nxthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)

        # Assumptions
        solver = self.get_solver()
        for ann_name, ann_var in self.ann_map.iteritems():
            ann = self.anns[ann_name]
            nxthop = self.nexthop_map[nexthop_map[ann.prefix]]
            solver.add(w.get_var(ann_var) == nxthop)
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(constraints, {})
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        w.set_model(model)
        for ann_name, ann_var in self.ann_map.iteritems():
            ann = self.anns[ann_name]
            nxthop = self.nexthop_map[nexthop_map[ann.prefix]]
            self.assertEquals(w.get_var(ann_var), nxthop)
            self.assertEquals(self.ann_var_map[ann_var].next_hop, nxthop)

    def test_symbolic_fun_stress(self):
        # Generate announcements
        num_communities = 1
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        nexthoplist = []
        nexthop_map = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            nexthop = 'nexthop_%d' % i
            nexthop_map[name] = nexthop
            nexthoplist.append(nexthop)
            cs = [(c, 'F') for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                prefix=name, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop=VALUENOTSET,
                local_pref=100, communities=cs, permitted=True)
            self.anns[name] = ann
        self._define_types(nexthope_list=nexthoplist)

        # Create wrapper
        w = SMTNexthopWrapper(
            'nxthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)
        # Assumptions
        solver = self.get_solver()
        for ann_name, ann_var in self.ann_map.iteritems():
            ann = self.anns[ann_name]
            nxthop = self.nexthop_map[nexthop_map[ann.prefix]]
            solver.add(w.fun(ann_var) == nxthop)
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertTrue(len(constraints) > 0)
        model = solver.model()
        w.set_model(model)
        for ann_name, ann_var in self.ann_map.iteritems():
            ann = self.anns[ann_name]
            nxthop = self.nexthop_map[nexthop_map[ann.prefix]]
            self.assertEquals(model.eval(w.fun(ann_var)), nxthop)
            self.assertEquals(w.get_var(ann_var), nxthop)
            self.assertEquals(self.ann_var_map[ann_var].next_hop, nxthop)

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        self._define_types(nexthope_list=['SwissCom', 'DT'])
        swisscom = self.nexthop_map['SwissCom']
        dt = self.nexthop_map['DT']

        new_fun = z3.Function('NewFunc', self.ann_sort, self.nexthop_sort)

        def transformer(ann_var, ann):
            new_ann = ann.copy()
            new_ann.next_hop = dt
            return new_ann

        # Create wrapper
        w1 = SMTNexthopWrapper(
            'nxthop1', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)

        w2 = w1.get_new_context(name='nxthop2', ann_vars=self.ann_var_map.keys(),
                                new_fun=new_fun,
                                transformer=transformer)
        # Assumptions
        solver = self.get_solver()
        tmp1 = z3.Const('test_tmp', self.ann_sort)
        tmp2 = z3.Const('test_tmp2', self.ann_sort)
        solver.add(z3.ForAll([tmp1], w1.fun(tmp1) == swisscom))
        solver.add(z3.ForAll([tmp1], w2.get_var(tmp2) == dt))
        w2.add_constraints(solver, True)
        # Assertions
        ret = solver.check()
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        w2.set_model(model)
        self.assertEquals(w1.get_var(ann1), swisscom)
        self.assertEquals(w1.get_var(ann2), swisscom)
        self.assertEquals(w2.get_var(ann1), dt)
        self.assertEquals(w2.get_var(ann2), dt)

    def test_union_stress(self):
        num_communities = 1
        num_anns = 100
        self.all_communities = [Community("100:%d" % i) for i in range(num_communities)]
        self.anns = {}
        for i in range(num_anns):
            name = 'Prefix_%d' % i
            nexthop = 'nexthop_%d' % i
            cs = [(c, 'F') for c in self.all_communities]
            cs = dict(cs)
            ann = Announcement(
                prefix=name, peer='N', origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[1, 2, 5], as_path_len=3, next_hop=nexthop,
                local_pref=100, communities=cs, permitted=True)
            self.anns[name] = ann
        self._define_types()

        nxt1 = self.nexthop_map.values()[0]
        nxt2 = self.nexthop_map.values()[1]
        f1 = z3.Function('F1', self.ann_sort, self.nexthop_sort)
        f2 = z3.Function('F2', self.ann_sort, self.nexthop_sort)
        unionf = z3.Function('unionF', self.ann_sort, self.nexthop_sort)

        def transform(ann_var, ann):
            n = ann.copy()
            n.next_hop = VALUENOTSET
            return n
        # Create Wrapper
        w1 = SMTNexthopWrapper(
            'n1', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort,
            self.nexthop_map)
        first_half = self.ann_var_map.keys()[:num_anns/2]
        second_half = self.ann_var_map.keys()[num_anns/2:]
        w2 = w1.get_new_context(name='w2', ann_vars=first_half, new_fun=f1, transformer=transform)
        w3 = w1.get_new_context(name='w3', ann_vars=second_half, new_fun=f2, transformer=transform)
        u = SMTNexthopWrapper.union('union', unionf, w2, w3)

        solver = self.get_solver()

        tmp1 = z3.Const('tmp1', self.ann_sort)
        tmp2= z3.Const('tmp2', self.ann_sort)
        solver.add(z3.ForAll([tmp1], w2.fun(tmp1) == nxt1))
        solver.add(z3.ForAll([tmp2], w3.fun(tmp2) == nxt2))
        u.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        u.set_model(model)
        for ann_name, ann_var in self.ann_map.iteritems():
            ann = self.anns[ann_name]
            self.assertEquals(w1.get_var(ann_var), ann.next_hop)
            self.assertEquals(w1.get_value(ann_var), str(ann.next_hop))
        for ann_var in w2.announcements_var_map:
            self.assertEquals(u.get_var(ann_var), nxt1)
        for ann_var in w3.announcements_var_map:
            self.assertEquals(u.get_var(ann_var), nxt2)


class TestSMTLocalPrefWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=VALUENOTSET, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']

        w = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEqual(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), 100)
        self.assertEquals(len(constraints), 0)

    def test_incorrect(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        ann_var_map = {}
        ann_var_map[ann1] = self.anns['Ann1_Google'].copy()
        ann_var_map[ann2] = self.anns['Ann1_Google'].copy()
        ann_var_map[ann1].local_pref = VALUENOTSET
        ann_var_map[ann2].local_pref = VALUENOTSET
        # Create wrapper
        w = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, ann_var_map,
            self.local_pref_fun)
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(w.get_var(ann1) == -1)
        w.add_constraints(solver, True)
        ret = solver.check()

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        # Create wrapper
        w = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)

        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.get_var(tmp) == 100))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        w.set_model(solver.model())
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), 100)
        self.assertEquals(w.get_var(ann2), 100)

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Create wrapper
        w = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.fun(tmp) == 100))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertTrue(len(constraints) > 0)
        self.assertEquals(w.get_var(ann1), 100)
        self.assertEquals(w.get_var(ann2), 100)
        self.assertEquals(len(constraints), 3)

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        new_fun = z3.Function('NewF', self.ann_sort, z3.IntSort())

        def transformer(ann_var, ann):
            new_ann = ann.copy()
            new_ann.local_pref = VALUENOTSET
            return new_ann

        # Create wrapper
        w1 = SMTLocalPrefWrapper(
            'wp1', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)

        w2 = w1.get_new_context(
            name='wp2', ann_vars=self.ann_var_map.keys(),
            new_fun=new_fun, transformer=transformer)

        solver = self.get_solver()
        tmp1 = z3.Const('tmp1', self.ann_sort)
        tmp2 = z3.Const('tmp2', self.ann_sort)
        solver.add(z3.ForAll([tmp1], w1.get_var(tmp1) == 100))
        solver.add(z3.ForAll([tmp2], w2.get_var(tmp2) == 200))
        w2.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        w2.set_model(solver.model())
        self.assertEquals(w1.get_var(ann1), 100)
        self.assertEquals(w1.get_var(ann2), 100)
        self.assertEquals(w2.get_var(ann1), 200)
        self.assertEquals(w2.get_var(ann2), 200)


class TestSMTCommunityWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True, c2: False, c3: True},
            permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: VALUENOTSET, c2: False, c3: False},
            permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Create wrapper
        wc1 = SMTCommunityWrapper(
            'wc1', c1, self.ann_sort, self.ann_var_map, self.communities_fun[c1])
        wc2 = SMTCommunityWrapper(
            'wc2', c2, self.ann_sort, self.ann_var_map, self.communities_fun[c2])
        wc3 = SMTCommunityWrapper(
            'wc3', c3, self.ann_sort, self.ann_var_map, self.communities_fun[c3])
        # Assumptions
        solver = self.get_solver()
        constraints1 = wc1.add_constraints(solver, True)
        constraints2 = wc2.add_constraints(solver, True)
        constraints3 = wc3.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        wc1.set_model(model)
        wc2.set_model(model)
        wc3.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(len(constraints1), 0)
        self.assertEquals(len(constraints2), 0)
        self.assertEquals(len(constraints3), 0)
        self.assertTrue(wc1.get_var(ann1))
        self.assertFalse(wc2.get_var(ann1))
        self.assertTrue(wc3.get_var(ann1))
        self.assertTrue(is_symbolic(wc1.get_var(ann2)))
        self.assertFalse(wc2.get_var(ann2))
        self.assertFalse(wc3.get_var(ann2))

    def test_symbolic(self):
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Create wrapper
        wc1 = SMTCommunityWrapper(
            'wc1', c1, self.ann_sort, self.ann_var_map, self.communities_fun[c1])
        wc2 = SMTCommunityWrapper(
            'wc2', c2, self.ann_sort, self.ann_var_map, self.communities_fun[c2])
        wc3 = SMTCommunityWrapper(
            'wc3', c3, self.ann_sort, self.ann_var_map, self.communities_fun[c3])
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], wc1.get_var(tmp) == True))
        constraints1 = wc1.add_constraints(solver, True)
        constraints2 = wc2.add_constraints(solver, True)
        constraints3 = wc3.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        wc1.set_model(model)
        wc2.set_model(model)
        wc3.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertTrue(wc1.get_var(ann1))
        self.assertFalse(wc2.get_var(ann1))
        self.assertTrue(wc3.get_var(ann1))
        self.assertTrue(wc1.get_var(ann2))
        self.assertFalse(wc2.get_var(ann2))
        self.assertFalse(wc3.get_var(ann2))

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        # Create wrapper
        w = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.fun(tmp) == 100))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        model = solver.model()
        w.set_model(model)
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertTrue(len(constraints) > 0)
        self.assertEquals(w.get_var(ann1), 100)
        self.assertEquals(w.get_var(ann2), 100)
        self.assertEquals(len(constraints), 2)

    def test_new_ctx(self):
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        new_c1 = z3.Function('NewC1', self.ann_sort, z3.BoolSort())
        new_c2 = z3.Function('NewC2', self.ann_sort, z3.BoolSort())
        new_c3 = z3.Function('NewC3', self.ann_sort, z3.BoolSort())

        def t1(ann_var, ann):
            new_ann = ann.copy()
            new_ann.communities[c1] = True
            return new_ann

        def t2(ann_var, ann):
            new_ann = ann.copy()
            new_ann.communities[c2] = VALUENOTSET
            return new_ann

        def t3(ann_var, ann):
            new_ann = ann.copy()
            new_ann.communities[c3] = VALUENOTSET
            return new_ann

        # Create wrapper
        wc1 = SMTCommunityWrapper(
            'wc1', c1, self.ann_sort, self.ann_var_map, self.communities_fun[c1])
        wc2 = SMTCommunityWrapper(
            'wc2', c2, self.ann_sort, self.ann_var_map, self.communities_fun[c2])
        wc3 = SMTCommunityWrapper(
            'wc3', c3, self.ann_sort, self.ann_var_map, self.communities_fun[c3])

        w11 = wc1.get_new_context('w11', self.ann_var_map, new_c1, t1)
        w12 = wc2.get_new_context('w12', self.ann_var_map, new_c2, t2)
        w13 = wc3.get_new_context('w13', self.ann_var_map, new_c3, t3)

        # Assumptions
        solver = self.get_solver()
        tmp1 = z3.Const('tmp1', self.ann_sort)
        tmp2 = z3.Const('tmp2', self.ann_sort)
        tmp3 = z3.Const('tmp3', self.ann_sort)
        tmp4 = z3.Const('tmp4', self.ann_sort)
        solver.add(z3.ForAll([tmp1], wc1.get_var(tmp1) == True))
        solver.add(z3.ForAll([tmp2], w11.get_var(tmp2) == True))
        solver.add(z3.ForAll([tmp3], w12.get_var(tmp3) == False))
        solver.add(z3.ForAll([tmp4], w13.get_var(tmp4) == False))
        wc1.add_constraints(solver, True)
        wc2.add_constraints(solver, True)
        wc3.add_constraints(solver, True)
        w11.add_constraints(solver, True)
        w12.add_constraints(solver, True)
        w13.add_constraints(solver, True)

        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        wc1.set_model(model)
        wc2.set_model(model)
        wc3.set_model(model)
        w11.set_model(model)
        w12.set_model(model)
        w13.set_model(model)
        self.assertTrue(wc1.get_var(ann1))
        self.assertFalse(wc2.get_var(ann1))
        self.assertTrue(wc3.get_var(ann1))
        self.assertTrue(wc1.get_var(ann2))
        self.assertFalse(wc2.get_var(ann2))
        self.assertFalse(wc3.get_var(ann2))
        self.assertTrue(w11.get_var(ann1))
        self.assertTrue(w11.get_var(ann2))
        self.assertFalse(w12.get_var(ann1))
        self.assertFalse(w12.get_var(ann2))
        self.assertFalse(w13.get_var(ann1))
        self.assertFalse(w13.get_var(ann2))


class TestSMTASPathWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 3], as_path_len=3, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=VALUENOTSET, as_path_len=2, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']
        as_p1 = get_as_path_key([1, 2, 3])
        p1 = self.as_path_map[as_p1]

        w = SMTASPathWrapper(
            'was', self.ann_sort, self.ann_var_map,
            self.as_path_fun, self.as_path_sort,
            self.as_path_map)

        solver = self.get_solver()
        ret = solver.check()
        self.assertEqual(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), p1)
        self.assertEquals(w.add_constraints(solver, True), {})

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        paths = [[1, 2, 3], [4, 5]]
        as_path_list = [get_as_path_key(p) for p in paths]
        self._define_types(as_path_list=as_path_list)
        as_p1 = as_path_list[0]
        as_p2 = as_path_list[1]
        p1 = self.as_path_map[as_p1]
        p2 = self.as_path_map[as_p2]

        # Create wrapper
        w = SMTASPathWrapper(
            'was', self.ann_sort, self.ann_var_map,
            self.as_path_fun, self.as_path_sort,
            self.as_path_map)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), p1)
        self.assertTrue(is_symbolic(w.get_var(ann2)))
        self.assertEquals(len(constraints), 0)

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        paths = [[1, 2, 3], [4, 5]]
        as_path_list = [get_as_path_key(p) for p in paths]
        self._define_types(as_path_list=as_path_list)
        as_p1 = as_path_list[0]
        as_p2 = as_path_list[1]
        p1 = self.as_path_map[as_p1]
        p2 = self.as_path_map[as_p2]

        # Create wrapper
        w = SMTASPathWrapper(
            'was', self.ann_sort, self.ann_var_map,
            self.as_path_fun, self.as_path_sort,
            self.as_path_map)
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.fun(tmp) == p1))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), p1)
        self.assertTrue(is_symbolic(w.get_var(ann2)))
        self.assertEquals(len(constraints), 2)
        model = solver.model()
        w.set_model(model)
        self.assertEquals(w.get_var(ann2), p1)

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        paths = [[1, 2, 3], [4, 5]]
        as_path_list = [get_as_path_key(p) for p in paths]
        self._define_types(as_path_list=as_path_list)
        as_p1 = as_path_list[0]
        as_p2 = as_path_list[1]
        p1 = self.as_path_map[as_p1]
        p2 = self.as_path_map[as_p2]

        newf = z3.Function('NewF', self.ann_sort, self.as_path_sort)

        def transformer(ann_var, ann):
            new_ann = ann.copy()
            new_ann.as_path = p2
            return new_ann

        # Create wrapper
        w1 = SMTASPathWrapper(
            'was1', self.ann_sort, self.ann_var_map,
            self.as_path_fun, self.as_path_sort,
            self.as_path_map)

        w2 = w1.get_new_context('w2', self.ann_var_map, newf, transformer)

        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w1.fun(tmp) == p1))
        solver.add(z3.ForAll([tmp], w2.fun(tmp) == p2))
        constraints = w2.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        self.assertEquals(w1.get_var(ann1), p1)
        self.assertTrue(is_symbolic(w1.get_var(ann2)))
        self.assertEquals(len(constraints), 4)
        model = solver.model()
        w2.set_model(model)
        self.assertEquals(w1.get_var(ann2), p1)


class TestSMTASPathLenWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=VALUENOTSET, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']

        w = SMTASPathLenWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.as_path_len_fun)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEqual(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), 5)
        self.assertEquals(len(constraints), 0)

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        # Create wrapper
        w = SMTASPathLenWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.as_path_len_fun)
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.get_var(tmp) == 5))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        w.set_model(solver.model())
        self.assertTrue(len(constraints) > 0)
        self.assertEquals(w.get_var(ann1), 5)
        self.assertEquals(w.get_var(ann2), 5)

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Create wrapper
        w = SMTASPathLenWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.as_path_len_fun)
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.fun(tmp) == 5))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        w.set_model(model)
        self.assertTrue(len(constraints) > 0)
        self.assertEquals(w.get_var(ann1), 5)
        self.assertEquals(w.get_var(ann2), 5)

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        new_fun = z3.Function('NewF', self.ann_sort, z3.IntSort())

        def transformer(ann_var, ann):
            new_ann = ann.copy()
            new_ann.as_path_len = VALUENOTSET
            return new_ann

        # Create wrapper
        w1 = SMTASPathLenWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.as_path_len_fun)

        w2 = w1.get_new_context(
            name='wp2', ann_vars=self.ann_var_map.keys(),
            new_fun=new_fun, transformer=transformer)

        solver = self.get_solver()
        tmp1 = z3.Const('tmp1', self.ann_sort)
        tmp2 = z3.Const('tmp2', self.ann_sort)
        solver.add(z3.ForAll([tmp1], w1.get_var(tmp1) == 5))
        solver.add(z3.ForAll([tmp2], w2.get_var(tmp2) == 10))
        w2.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        w2.set_model(solver.model())
        self.assertEquals(w1.get_var(ann1), 5)
        self.assertEquals(w1.get_var(ann2), 5)
        self.assertEquals(w2.get_var(ann1), 10)
        self.assertEquals(w2.get_var(ann2), 10)


class TestSMTPermittedWrapper(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        self.all_communities = (c1,)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: True}, permitted=VALUENOTSET)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        ann1 = self.ann_map['Ann1_Google']

        w = SMTPermittedWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.permitted_fun)
        # Assumptions
        solver = self.get_solver()
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEqual(ret, z3.sat)
        self.assertEquals(w.get_var(ann1), True)
        self.assertEquals(constraints, {})

    def test_symbolic(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        # Create wrapper
        w = SMTPermittedWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.permitted_fun)
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.get_var(tmp) == True))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        w.set_model(solver.model())
        self.assertTrue(len(constraints) > 0)
        self.assertEquals(w.get_var(ann1), True)
        self.assertEquals(w.get_var(ann2), True)

    def test_symbolic_fun(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Create wrapper
        w = SMTPermittedWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.permitted_fun)
        # Assumptions
        solver = self.get_solver()
        tmp = z3.Const('test_tmp', self.ann_sort)
        solver.add(z3.ForAll([tmp], w.fun(tmp) == True))
        constraints = w.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        w.set_model(model)
        self.assertTrue(len(constraints) > 0)
        self.assertEquals(w.get_var(ann1), True)
        self.assertEquals(w.get_var(ann2), True)

    def test_new_ctx(self):
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']

        new_fun = z3.Function('NewF', self.ann_sort, z3.BoolSort())

        def transformer(ann_var, ann):
            new_ann = ann.copy()
            new_ann.permitted = VALUENOTSET
            return new_ann

        # Create wrapper
        w1 = SMTPermittedWrapper(
            'w1', self.ann_sort, self.ann_var_map,
            self.permitted_fun)

        w2 = w1.get_new_context(
            name='wp2', ann_vars=self.ann_var_map.keys(),
            new_fun=new_fun, transformer=transformer)

        solver = self.get_solver()
        tmp1 = z3.Const('tmp1', self.ann_sort)
        tmp2 = z3.Const('tmp2', self.ann_sort)
        solver.add(z3.ForAll([tmp1], w1.get_var(tmp1) == True))
        solver.add(z3.ForAll([tmp2], w2.get_var(tmp2) == False))
        w2.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        w2.set_model(solver.model())
        self.assertEquals(w1.get_var(ann1), True)
        self.assertEquals(w1.get_var(ann2), True)
        self.assertEquals(w2.get_var(ann1), False)
        self.assertEquals(w2.get_var(ann2), False)


class TestSMTContext(SMTSetup):
    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='SwissCom',
            local_pref=100, communities={c1: True, c2: False, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Yahoo', peer='SwissCom', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5, next_hop='DT',
            local_pref=100, communities={c1: True, c2: False, c3: False}, permitted=True)

        self.anns = {
            'Ann1_Google': ann1,
            'Ann2_Yahoo': ann2,
        }

    def test_concrete(self):
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Create wrapper
        wprefix = SMTPrefixWrapper(
            'prefixw', self.ann_sort, self.ann_var_map,
            self.prefix_fun, self.prefix_sort, self.prefix_map)

        wpeer = SMTPeerWrapper(
            'wpeer', self.ann_sort, self.ann_var_map,
            self.peer_fun, self.peer_sort, self.peer_map)

        worigin = SMTOriginWrapper(
            'worigin', self.ann_sort, self.ann_var_map,
            self.origin_fun, self.origin_sort, self.origin_map)

        waspath = SMTASPathWrapper(
            'waspath', self.ann_sort, self.ann_var_map,
            self.as_path_fun, self.as_path_sort, self.as_path_map)

        waspathlen = SMTASPathLenWrapper(
            'waspathlen', self.ann_sort, self.ann_var_map,
            self.as_path_len_fun)

        wnexthop = SMTNexthopWrapper(
            'wnexthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort, self.nexthop_map)

        wlocalpref = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)

        wpermitted = SMTPermittedWrapper(
            'wpermitted', self.ann_sort, self.ann_var_map,
            self.permitted_fun)

        wc1 = SMTCommunityWrapper(
            'wc1', c1, self.ann_sort, self.ann_var_map, self.communities_fun[c1])
        wc2 = SMTCommunityWrapper(
            'wc2', c2, self.ann_sort, self.ann_var_map, self.communities_fun[c2])
        wc3 = SMTCommunityWrapper(
            'wc3', c3, self.ann_sort, self.ann_var_map, self.communities_fun[c3])

        wcommunities = {}
        wcommunities[c1] = wc1
        wcommunities[c2] = wc2
        wcommunities[c3] = wc3

        ctx = SMTContext(
            name='ctx1',
            announcements=self.anns,
            announcements_map=self.ann_map,
            announcement_sort=self.ann_sort,
            prefix_ctx=wprefix,
            peer_ctx=wpeer,
            origin_ctx=worigin,
            as_path_ctx=waspath,
            as_path_len_ctx=waspathlen,
            next_hop_ctx=wnexthop,
            local_pref_ctx=wlocalpref,
            communities_ctx=wcommunities,
            permitted_ctx=wpermitted)

        # Assumptions
        solver = self.get_solver()
        constraints1 = ctx.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        ctx.set_model(model)
        self.assertFalse(len(constraints1))
        self.assertTrue(wc1.get_var(ann1))
        self.assertFalse(wc2.get_var(ann1))
        self.assertTrue(wc3.get_var(ann1))
        self.assertTrue(wc1.get_var(ann2))
        self.assertFalse(wc2.get_var(ann2))
        self.assertFalse(wc3.get_var(ann2))

    def test_get_new_context(self):
        c1 = self.all_communities[0]
        c2 = self.all_communities[1]
        c3 = self.all_communities[2]
        ann1 = self.ann_map['Ann1_Google']
        ann2 = self.ann_map['Ann2_Yahoo']
        # Create wrapper
        wprefix = SMTPrefixWrapper(
            'prefixw', self.ann_sort, self.ann_var_map,
            self.prefix_fun, self.prefix_sort, self.prefix_map)

        wpeer = SMTPeerWrapper(
            'wpeer', self.ann_sort, self.ann_var_map,
            self.peer_fun, self.peer_sort, self.peer_map)

        worigin = SMTOriginWrapper(
            'worigin', self.ann_sort, self.ann_var_map,
            self.origin_fun, self.origin_sort, self.origin_map)

        waspath = SMTASPathWrapper(
            'waspath', self.ann_sort, self.ann_var_map,
            self.as_path_fun, self.as_path_sort, self.as_path_map)

        waspathlen = SMTASPathLenWrapper(
            'waspathlen', self.ann_sort, self.ann_var_map,
            self.as_path_len_fun)

        wnexthop = SMTNexthopWrapper(
            'wnexthop', self.ann_sort, self.ann_var_map,
            self.nexthop_fun, self.nexthop_sort, self.nexthop_map)

        wlocalpref = SMTLocalPrefWrapper(
            'wlocalpref', self.ann_sort, self.ann_var_map,
            self.local_pref_fun)

        new_pref = z3.Function('NewLocalPref', self.ann_sort, z3.IntSort())

        def pref_trans(ann_var, ann):
            new_ann = ann.copy()
            new_ann.local_pref = VALUENOTSET
            return new_ann

        wlocalpref2 = wlocalpref.get_new_context(
            name='wlocalpref2',ann_vars=self.ann_var_map,
            new_fun=new_pref, transformer=pref_trans)

        wpermitted = SMTPermittedWrapper(
            'wpermitted', self.ann_sort, self.ann_var_map,
            self.permitted_fun)

        wc1 = SMTCommunityWrapper(
            'wc1', c1, self.ann_sort, self.ann_var_map, self.communities_fun[c1])
        wc2 = SMTCommunityWrapper(
            'wc2', c2, self.ann_sort, self.ann_var_map, self.communities_fun[c2])
        wc3 = SMTCommunityWrapper(
            'wc3', c3, self.ann_sort, self.ann_var_map, self.communities_fun[c3])

        wcommunities = {}
        wcommunities[c1] = wc1
        wcommunities[c2] = wc2
        wcommunities[c3] = wc3

        ctx = SMTContext(
            name='ctx1',
            announcements=self.anns,
            announcements_map=self.ann_map,
            announcement_sort=self.ann_sort,
            prefix_ctx=wprefix,
            peer_ctx=wpeer,
            origin_ctx=worigin,
            as_path_ctx=waspath,
            as_path_len_ctx=waspathlen,
            next_hop_ctx=wnexthop,
            local_pref_ctx=wlocalpref,
            communities_ctx=wcommunities,
            permitted_ctx=wpermitted)

        ctx2 = ctx.get_new_context('ctx2', local_pref_ctx=wlocalpref2)
        # Assumptions
        solver = self.get_solver()
        tmp1 = z3.Const('tmp1', self.ann_sort)
        solver.add(z3.ForAll([tmp1], ctx2.local_pref_ctx.fun(tmp1) == 200))
        constraints1 = ctx2.add_constraints(solver, True)
        ret = solver.check()
        # Assertions
        self.assertEquals(ret, z3.sat)
        model = solver.model()
        ctx.set_model(model)
        self.assertTrue(len(constraints1))
        self.assertTrue(wc1.get_var(ann1))
        self.assertFalse(wc2.get_var(ann1))
        self.assertTrue(wc3.get_var(ann1))
        self.assertTrue(wc1.get_var(ann2))
        self.assertFalse(wc2.get_var(ann2))
        self.assertFalse(wc3.get_var(ann2))
