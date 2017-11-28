import unittest

import z3
from nose.plugins.attrib import attr

from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.utils.fnfree_policy import SMTAction
from synet.utils.fnfree_policy import SMTMatchASPath
from synet.utils.fnfree_policy import SMTMatchASPathLen
from synet.utils.fnfree_policy import SMTMatchAll
from synet.utils.fnfree_policy import SMTMatchAnd
from synet.utils.fnfree_policy import SMTMatchAttribute
from synet.utils.fnfree_policy import SMTMatchCommunity
from synet.utils.fnfree_policy import SMTMatchLocalPref
from synet.utils.fnfree_policy import SMTMatchOr
from synet.utils.fnfree_policy import SMTMatchOrigin
from synet.utils.fnfree_policy import SMTMatchPeer
from synet.utils.fnfree_policy import SMTMatchPermitted
from synet.utils.fnfree_policy import SMTMatchPrefix
from synet.utils.fnfree_policy import SMTMatchSelectOne
from synet.utils.fnfree_policy import SMTMatchNextHop
from synet.utils.fnfree_policy import SMTSetASPath
from synet.utils.fnfree_policy import SMTSetASPathLen
from synet.utils.fnfree_policy import SMTSetLocalPref
from synet.utils.fnfree_policy import SMTSetOrigin
from synet.utils.fnfree_policy import SMTSetPeer
from synet.utils.fnfree_policy import SMTSetPermitted
from synet.utils.fnfree_policy import SMTSetPrefix
from synet.utils.fnfree_policy import SMTSetNextHop
from synet.utils.fnfree_smt_context import ASPATH_SORT
from synet.utils.fnfree_smt_context import BGP_ORIGIN_SORT
from synet.utils.fnfree_smt_context import PEER_SORT
from synet.utils.fnfree_smt_context import PREFIX_SORT
from synet.utils.fnfree_smt_context import NEXT_HOP_SORT
from synet.utils.fnfree_smt_context import SolverContext
from synet.utils.fnfree_smt_context import get_as_path_key
from synet.utils.fnfree_smt_context import read_announcements


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


@attr(speed='fast')
class TestSMTMatchAttribute(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_enum_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)
        # Provide concrete value for the match
        p1_val = prefix_sort.get_symbolic_value('Prefix1')
        p1_sym = ctx.create_fresh_var(prefix_sort, value=p1_val)
        # Act
        match = SMTMatchAttribute('prefix', p1_sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)

    def test_match_enum_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)
        p1_sym = ctx.create_fresh_var(prefix_sort)
        # Act
        match = SMTMatchAttribute('prefix', p1_sym, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(p1_sym.get_value(), concrete_anns[0].prefix)
        self.assertNotEquals(p1_sym.get_value(), concrete_anns[1].prefix)

    def test_match_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        pref = ctx.create_fresh_var(z3.IntSort(), value=100)
        # Act
        match = SMTMatchAttribute('local_pref', pref, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        ann1_value = match.is_match(sym_anns[1]).get_value()
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertTrue(ann0_is_concrete)
        self.assertTrue(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertFalse(ann1_value)
        self.assertEquals(is_sat, z3.sat)

    def test_match_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        # Provide symbolic variable for the match
        pref = ctx.create_fresh_var(z3.IntSort())
        # Act
        match = SMTMatchAttribute('local_pref', pref, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(pref.get_value(), concrete_anns[0].local_pref)
        self.assertNotEquals(pref.get_value(), concrete_anns[1].local_pref)


@attr(speed='fast')
class TestSMTMatchCommunity(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        value = ctx.create_fresh_var(z3.BoolSort(), value=True)
        # Provide concrete value for the match
        c1 = Community("100:16")
        # Act
        match = SMTMatchCommunity(c1, value, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        ann1_value = match.is_match(sym_anns[1]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertTrue(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertFalse(ann1_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())


@attr(speed='fast')
class TestSMTMatchAnd(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)
        p1_val = prefix_sort.get_symbolic_value('Prefix1')
        prefix = ctx.create_fresh_var(prefix_sort, value=p1_val)
        match_prefix = SMTMatchAttribute('prefix', prefix, sym_anns, ctx)

        pref = ctx.create_fresh_var(z3.IntSort(), value=100)
        match_pref = SMTMatchAttribute('local_pref', pref, sym_anns, ctx)
        matches = [match_prefix, match_pref]
        # Act
        match = SMTMatchAnd(matches, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)

        p1_val = prefix_sort.get_symbolic_value('Prefix1')
        prefix = ctx.create_fresh_var(prefix_sort)
        match_prefix = SMTMatchAttribute('prefix', prefix, sym_anns, ctx)

        pref = ctx.create_fresh_var(z3.IntSort())
        match_pref = SMTMatchAttribute('local_pref', pref, sym_anns, ctx)
        matches = [match_prefix, match_pref]
        # Act
        match = SMTMatchAnd(matches, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.add(const)
        solver.add(match.is_match(sym_anns[0]).var == True)
        solver.add(match.is_match(sym_anns[1]).var == False)
        is_sat = solver.check()
        print solver.to_smt2()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(match_prefix.value.get_value(), 'Prefix1')
        self.assertEquals(match_pref.value.get_value(), 100)


@attr(speed='fast')
class TestSMTMatchOr(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)

        p1_val = prefix_sort.get_symbolic_value('Prefix1')
        prefix = ctx.create_fresh_var(prefix_sort, value=p1_val)
        match_prefix = SMTMatchAttribute('prefix', prefix, sym_anns, ctx)

        pref = ctx.create_fresh_var(z3.IntSort(), value=110)
        match_pref = SMTMatchAttribute('local_pref', pref, sym_anns, ctx)
        matches = [match_prefix, match_pref]
        # Act
        match = SMTMatchOr(matches, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertTrue(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)

        p1_val = prefix_sort.get_symbolic_value('Prefix1')
        prefix = ctx.create_fresh_var(prefix_sort)
        match_prefix = SMTMatchAttribute('prefix', prefix, sym_anns, ctx)

        pref = ctx.create_fresh_var(z3.IntSort())
        match_pref = SMTMatchAttribute('local_pref', pref, sym_anns, ctx)
        matches = [match_prefix, match_pref]
        # Act
        match = SMTMatchOr(matches, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.add(const)
        solver.add(match.is_match(sym_anns[0]).var == True)
        solver.add(match.is_match(sym_anns[1]).var == True)
        is_sat = solver.check()
        print solver.to_smt2()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(match_prefix.value.get_value(), 'Prefix1')
        self.assertEquals(match_pref.value.get_value(), 110)


@attr(speed='fast')
class TestSMTMatchPrefix(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)
        # Provide concrete value for the match
        p1_val = prefix_sort.get_symbolic_value('Prefix1')
        p1_sym = ctx.create_fresh_var(prefix_sort, value=p1_val)
        # Act
        match = SMTMatchPrefix(p1_sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)
        p1_sym = ctx.create_fresh_var(prefix_sort)
        # Act
        match = SMTMatchAttribute('prefix', p1_sym, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(p1_sym.get_value(), concrete_anns[0].prefix)
        self.assertNotEquals(p1_sym.get_value(), concrete_anns[1].prefix)


@attr(speed='fast')
class TestSMTMatchPeer(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        peer_sort = ctx.get_enum_type(PEER_SORT)
        # Provide concrete value for the match
        p1_val = peer_sort.get_symbolic_value('Peer1')
        p1_sym = ctx.create_fresh_var(peer_sort, value=p1_val)
        # Act
        match = SMTMatchPeer(p1_sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        peer_sort = ctx.get_enum_type(PEER_SORT)
        p1_sym = ctx.create_fresh_var(peer_sort)
        # Act
        match = SMTMatchPeer(p1_sym, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(p1_sym.get_value(), concrete_anns[0].peer)
        self.assertNotEquals(p1_sym.get_value(), concrete_anns[1].peer)


@attr(speed='fast')
class TestSMTMatchNextHop(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = ctx.get_enum_type(NEXT_HOP_SORT)
        # Provide concrete value for the match
        val = vsort.get_symbolic_value('Hop1')
        sym = ctx.create_fresh_var(vsort, value=val)
        # Act
        match = SMTMatchNextHop(sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        # Act
        match = SMTMatchNextHop(None, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(match.value.get_value(), concrete_anns[0].next_hop)
        self.assertNotEquals(match.value.get_value(), concrete_anns[1].next_hop)


@attr(speed='fast')
class TestSMTMatchAsPath(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = ctx.get_enum_type(ASPATH_SORT)
        # Provide concrete value for the match
        as_path = get_as_path_key([1, 2, 5, 7, 6])
        val = vsort.get_symbolic_value(as_path)
        sym = ctx.create_fresh_var(vsort, value=val)
        # Act
        match = SMTMatchASPath(sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = ctx.get_enum_type(ASPATH_SORT)
        as_path = get_as_path_key([1, 2, 5, 7, 6])
        sym = ctx.create_fresh_var(vsort)
        # Act
        match = SMTMatchASPath(sym, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(sym.get_value(), as_path)


@attr(speed='fast')
class TestSMTMatchAsPathLen(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = z3.IntSort()
        # Provide concrete value for the match
        val = concrete_anns[0].as_path_len
        sym = ctx.create_fresh_var(vsort, value=val)
        # Act
        match = SMTMatchASPathLen(sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertTrue(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = z3.IntSort()
        sym = ctx.create_fresh_var(vsort)
        # Act
        match = SMTMatchASPathLen(sym, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(sym.get_value(), concrete_anns[0].as_path_len)


@attr(speed='fast')
class TestSMTMatchPermitted(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=False)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = z3.BoolSort()
        # Provide concrete value for the match
        val = concrete_anns[0].permitted
        sym = ctx.create_fresh_var(vsort, value=val)
        # Act
        match = SMTMatchPermitted(sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertTrue(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = z3.BoolSort()
        sym = ctx.create_fresh_var(vsort)
        # Act
        match = SMTMatchPermitted(sym, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(sym.get_value(), concrete_anns[0].permitted)

@attr(speed='fast')
class TestSMTMatchOrigin(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.IGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = ctx.get_enum_type(BGP_ORIGIN_SORT)
        # Provide concrete value for the match
        val = vsort.get_symbolic_value('EBGP')
        sym = ctx.create_fresh_var(vsort, value=val)
        # Act
        match = SMTMatchOrigin(sym, sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        ann0_value = match.is_match(sym_anns[0]).get_value()
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertTrue(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertTrue(ann0_value)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())

    def test_match_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        vsort = ctx.get_enum_type(BGP_ORIGIN_SORT)
        sym = ctx.create_fresh_var(vsort)
        # Act
        match = SMTMatchOrigin(sym, sym_anns, ctx)
        match0 = match.is_match(sym_anns[0])
        match1 = match.is_match(sym_anns[1])
        ann0_is_concrete = match0.is_concrete
        ann1_is_concrete = match0.is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(match0.var == True)
        solver.add(match1.var == False)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match0.get_value())
        self.assertFalse(match1.get_value())
        self.assertEquals(sym.get_value(), 'EBGP')


@attr(speed='fast')
class TestSMTMatchSelectOne(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.communities = [c1, c2, c3]

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: False, c2: True, c3: True}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=100, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)
        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_match(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        # Act
        match = SMTMatchSelectOne(sym_anns, ctx)
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete
        # Evaluate constraints
        solver = z3.Solver()
        solver.add(match.is_match(sym_anns[0]).var == True)
        solver.add(match.is_match(sym_anns[1]).var == False)
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertTrue(match.is_match(sym_anns[0]).get_value())
        self.assertFalse(match.is_match(sym_anns[1]).get_value())
        self.assertIsNotNone(match.get_used_match())

    def test_unsat(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        c2_match = SMTMatchCommunity(self.communities[0], None, sym_anns, ctx)
        lpref_match = SMTMatchLocalPref(None, sym_anns, ctx)
        # Act
        match = SMTMatchSelectOne(sym_anns, ctx, matches=[c2_match, lpref_match])
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete

        # Evaluate constraints
        solver = z3.Solver()
        solver.add(match.is_match(sym_anns[0]).var == True)
        solver.add(match.is_match(sym_anns[1]).var == False)
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.unsat)

    def test_only_one(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        c1_match = SMTMatchCommunity(self.communities[1], None, sym_anns, ctx)
        lpref_match = SMTMatchLocalPref(None, sym_anns, ctx)
        # Act
        match = SMTMatchSelectOne(sym_anns, ctx, matches=[c1_match, lpref_match])
        ann0_is_concrete = match.is_match(sym_anns[0]).is_concrete
        ann1_is_concrete = match.is_match(sym_anns[1]).is_concrete

        # Evaluate constraints
        solver = z3.Solver()
        solver.add(match.is_match(sym_anns[0]).var == True)
        solver.add(match.is_match(sym_anns[1]).var == False)
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        # Check the partial evaluation
        self.assertFalse(ann0_is_concrete)
        self.assertFalse(ann1_is_concrete)
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEqual(match.get_used_match(), c1_match)


@attr(speed='fast')
class TestAction(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        pref = ctx.create_fresh_var(z3.IntSort(), value=200)
        # Act
        action = SMTAction(match, 'local_pref', pref, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].local_pref.get_value(), 200)
        self.assertEquals(new_anns[1].local_pref.get_value(), 200)

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        value = ctx.create_fresh_var(z3.IntSort())
        match = SMTMatchAll(ctx)
        # Act
        action = SMTAction(match, 'local_pref', value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].local_pref.var == 200)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(value.get_value(), 200)
        self.assertEquals(new_anns[0].local_pref.get_value(), 200)
        self.assertEquals(new_anns[1].local_pref.get_value(), 200)

    def test_enum_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)
        sym_val = prefix_sort.get_symbolic_value('Prefix1')
        p1_sym = ctx.create_fresh_var(prefix_sort, value=sym_val)
        # Act
        action = SMTAction(match, 'prefix', p1_sym, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].prefix.get_value(), 'Prefix1')
        self.assertEquals(new_anns[1].prefix.get_value(), 'Prefix1')

    def test_enum_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        prefix_sort = ctx.get_enum_type(PREFIX_SORT)
        sym_val = prefix_sort.get_symbolic_value('Prefix1')
        p1_sym = ctx.create_fresh_var(prefix_sort)
        # Act
        action = SMTAction(match, 'prefix', p1_sym, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].prefix.var == sym_val)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].prefix.get_value(), 'Prefix1')
        self.assertEquals(new_anns[1].prefix.get_value(), 'Prefix1')


@attr(speed='fast')
class TestSMTSetLocalPref(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        pref = ctx.create_fresh_var(z3.IntSort(), value=200)
        # Act
        action = SMTSetLocalPref(match, pref, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].local_pref.get_value(), 200)
        self.assertEquals(new_anns[1].local_pref.get_value(), 200)

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetLocalPref(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].local_pref.var == 200)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), 200)
        self.assertEquals(new_anns[0].local_pref.get_value(), 200)
        self.assertEquals(new_anns[1].local_pref.get_value(), 200)


@attr(speed='fast')
class TestSMTSetPrefix(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        vsort = ctx.get_enum_type(PREFIX_SORT)
        value = ctx.create_fresh_var(vsort, value=concrete_anns[0].prefix)
        # Act
        action = SMTSetPrefix(match, value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].prefix.get_value(), 'Prefix1')
        self.assertEquals(new_anns[1].prefix.get_value(), 'Prefix1')

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetPrefix(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].prefix.var == sym_anns[0].prefix.var)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), 'Prefix1')
        self.assertEquals(new_anns[0].prefix.get_value(), 'Prefix1')
        self.assertEquals(new_anns[1].prefix.get_value(), 'Prefix1')


@attr(speed='fast')
class TestSMTSetPeer(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        vsort = ctx.get_enum_type(PEER_SORT)
        value = ctx.create_fresh_var(vsort, value=concrete_anns[0].peer)
        # Act
        action = SMTSetPeer(match, value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].peer.get_value(), 'Peer1')
        self.assertEquals(new_anns[1].peer.get_value(), 'Peer1')

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetPeer(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].peer.var == sym_anns[0].peer.var)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), 'Peer1')
        self.assertEquals(new_anns[0].peer.get_value(), 'Peer1')
        self.assertEquals(new_anns[1].peer.get_value(), 'Peer1')


@attr(speed='fast')
class TestSMTSetOrigin(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.IGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        vsort = ctx.get_enum_type(BGP_ORIGIN_SORT)
        value = ctx.create_fresh_var(vsort, value='EBGP')
        # Act
        action = SMTSetOrigin(match, value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].origin.get_value(), 'EBGP')
        self.assertEquals(new_anns[1].origin.get_value(), 'EBGP')

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetOrigin(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].origin.var == sym_anns[0].origin.var)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), 'EBGP')
        self.assertEquals(new_anns[0].origin.get_value(), 'EBGP')
        self.assertEquals(new_anns[1].origin.get_value(), 'EBGP')


@attr(speed='fast')
class TestSMTSetPermitted(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.IGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        vsort = z3.BoolSort()
        value = ctx.create_fresh_var(vsort, value=False)
        # Act
        action = SMTSetPermitted(match, value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].permitted.get_value(), False)
        self.assertEquals(new_anns[1].permitted.get_value(), False)

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetPermitted(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].permitted.var == False)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), False)
        self.assertEquals(new_anns[0].permitted.get_value(), False)
        self.assertEquals(new_anns[1].permitted.get_value(), False)


@attr(speed='fast')
class TestSMTSetASPath(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.IGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        vsort = ctx.get_enum_type(ASPATH_SORT)
        as_path = get_as_path_key(concrete_anns[0].as_path)
        value = ctx.create_fresh_var(vsort, value=as_path)
        # Act
        action = SMTSetASPath(match, value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].as_path.get_value(), as_path)
        self.assertEquals(new_anns[1].as_path.get_value(), as_path)

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        as_path = get_as_path_key(concrete_anns[0].as_path)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetASPath(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].as_path.var == sym_anns[0].as_path.var)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), as_path)
        self.assertEquals(new_anns[0].as_path.get_value(), as_path)
        self.assertEquals(new_anns[1].as_path.get_value(), as_path)


@attr(speed='fast')
class TestSMTSetASPathLen(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.IGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        vsort = z3.IntSort()
        value = ctx.create_fresh_var(vsort, value=10)
        # Act
        action = SMTSetASPathLen(match, value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].as_path_len.get_value(), 10)
        self.assertEquals(new_anns[1].as_path_len.get_value(), 10)

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetASPathLen(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].as_path_len.var == 10)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), 10)
        self.assertEquals(new_anns[0].as_path_len.get_value(), 10)
        self.assertEquals(new_anns[1].as_path_len.get_value(), 10)


@attr(speed='fast')
class TestSMTSetNextHop(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix1', peer='Peer1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 6], as_path_len=5,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Prefix2', peer='Peer2', origin=BGP_ATTRS_ORIGIN.IGP,
            as_path=[9, 2, 5, 7, 8, 3, 10], as_path_len=7,
            next_hop='Hop2', local_pref=110, med=10,
            communities={c1: False, c2: False, c3: True}, permitted=True)

        return ann1, ann2

    def get_ctx(self, concrete_anns):
        ctx = SolverContext.create_context(concrete_anns)
        return ctx

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    def test_int_concrete(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        vsort = ctx.get_enum_type(NEXT_HOP_SORT)
        value = ctx.create_fresh_var(vsort, value=concrete_anns[0].next_hop)
        # Act
        action = SMTSetNextHop(match, value, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(new_anns[0].next_hop.get_value(), concrete_anns[0].next_hop)
        self.assertEquals(new_anns[1].next_hop.get_value(), concrete_anns[0].next_hop)

    def test_int_sym(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = self.get_ctx(concrete_anns)
        sym_anns = self.get_sym(concrete_anns, ctx)
        match = SMTMatchAll(ctx)
        # Act
        action = SMTSetNextHop(match, None, sym_anns, ctx)
        new_anns = action.announcements
        solver = z3.Solver()
        for name, const in ctx.constraints_itr():
            solver.assert_and_track(const, name)
        solver.add(new_anns[0].next_hop.var == sym_anns[0].next_hop.var)
        #solver.add(new_anns[0].local_pref.var == 200)
        is_sat = solver.check()
        # Assert
        self.assertEquals(is_sat, z3.sat)
        ctx.set_model(solver.model())
        self.assertEquals(action.value.get_value(), concrete_anns[0].next_hop)
        self.assertEquals(new_anns[0].next_hop.get_value(), concrete_anns[0].next_hop)
        self.assertEquals(new_anns[1].next_hop.get_value(), concrete_anns[0].next_hop)
