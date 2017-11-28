
import unittest

import z3
from nose.plugins.attrib import attr

from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community


from synet.utils.fnfree_smt_context import EnumType
from synet.utils.fnfree_smt_context import SolverContext
from synet.utils.fnfree_smt_context import VALUENOTSET
from synet.utils.fnfree_smt_context import SMTVar
from synet.utils.fnfree_smt_context import get_as_path_key
from synet.utils.fnfree_smt_context import is_empty
from synet.utils.fnfree_smt_context import is_symbolic
from synet.utils.fnfree_smt_context import read_announcements


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


@attr(speed='fast')
class EnumTypeTest(unittest.TestCase):
    def test_create(self):
        # Arrange
        values = ['A', 'B', 'C']
        name = 'TestType'
        # Act
        enum_type = EnumType(name, values)
        # Assert
        self.assertEquals(enum_type.name, name)
        self.assertEquals(enum_type.concrete_values, values)
        self.assertEquals(len(enum_type.symbolic_values), len(values))
        for value in values:
            symb = enum_type.get_symbolic_value(value)
            self.assertEquals(str(symb), value)
            self.assertTrue(is_symbolic(symb))
            concrete = enum_type.get_concrete_value(symb)
            self.assertEquals(concrete, value)
        with self.assertRaises(ValueError):
            enum_type.get_symbolic_value('D')
        with self.assertRaises(Exception):
            enum_type.get_concrete_value('D')


@attr(speed='fast')
class VarTest(unittest.TestCase):
    def test_builitin_eq_hash(self):
        # Arrange
        name1 = 'TestVar1'
        value1 = 10
        name2 = 'TestVar2'
        value2 = 15
        vsort = z3.IntSort()
        var1 = SMTVar(name1, vsort, value1)
        var2 = SMTVar(name2, vsort, value2)
        # Act
        eq1 = var1 == var2
        eq2 = var1 == var1
        eq3 = var2 == var2
        hash1 = hash(var1)
        hash2 = hash(var2)
        # Assert
        self.assertFalse(eq1)
        self.assertTrue(eq2)
        self.assertTrue(eq3)
        self.assertNotEquals(hash1, hash2)

    def test_check_eq_int(self):
        # Arrange
        name1 = 'TestVar1'
        value1 = 10
        name2 = 'TestVar2'
        value2 = 15
        name3 = 'TestVar3'
        value3 = 10
        name4 = 'TestVar4'
        vsort = z3.IntSort()
        var1 = SMTVar(name1, vsort, value1)
        var2 = SMTVar(name2, vsort, value2)
        var3 = SMTVar(name3, vsort, value3)
        var4 = SMTVar(name4, vsort)
        # Act
        eq1 = var1.check_eq(var1)
        eq2 = var1.check_eq(var2)
        eq3 = var1.check_eq(var3)
        eq4 = var1.check_eq(var4)
        # Assert
        self.assertTrue(eq1)
        self.assertFalse(eq2)
        self.assertTrue(eq3)
        self.assertTrue(is_symbolic(eq4))

    def test_concrete_int(self):
        # Arrange
        name = 'TestVar1'
        value = 10
        vsort = z3.IntSort()
        # Act
        var = SMTVar(name, vsort, value)
        # Assert
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertEquals(var.var, value)
        self.assertEquals(var.get_value(), value)
        self.assertTrue(is_symbolic(var.get_var()))

    def test_symbolic_int(self):
        # Arrange
        name = 'TestVar1'
        vsort = z3.IntSort()
        value = 10
        # Act
        var = SMTVar(name, vsort)
        var_before = var.var
        get_var_before = var.get_var()
        with self.assertRaises(RuntimeError):
            self.assertEquals(var.get_value(), value)
        # Concertize the value
        solver = z3.Solver()
        solver.add(var.var == value)
        self.assertEquals(solver.check(), z3.sat)
        model = solver.model()
        var.eval(model)
        # Assert
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertTrue(is_symbolic(var_before))
        self.assertTrue(is_symbolic(get_var_before))
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertEquals(var.var, value)
        self.assertEquals(var.get_value(), value)
        self.assertTrue(is_symbolic(var.get_var()))

    def test_concrete_enum(self):
        # Arrange
        values = ['A', 'B', 'C']
        sort_name = 'TestType'
        name = 'TestVar1'
        value = 'A'
        vsort = EnumType(sort_name, values)
        # Act
        var = SMTVar(name, vsort, value)
        # Assert
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertEquals(var.var, vsort.get_symbolic_value(value))
        self.assertEquals(var.get_value(), value)
        self.assertTrue(is_symbolic(var.get_var()))

    def test_symbolic_enum(self):
        # Arrange
        values = ['A', 'B', 'C']
        sort_name = 'TestType'
        name = 'TestVar1'
        value = 'A'
        vsort = EnumType(sort_name, values)
        # Act
        var = SMTVar(name, vsort)
        # Assert
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertTrue(is_symbolic(var.var))
        self.assertTrue(is_symbolic(var.get_var()))
        with self.assertRaises(RuntimeError):
            self.assertEquals(var.get_value(), 10)

        # Concertize the value
        solver = z3.Solver()
        solver.add(var.var == vsort.get_symbolic_value(value))
        self.assertEquals(solver.check(), z3.sat)
        model = solver.model()
        var.eval(model)
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertEquals(var.var, vsort.get_symbolic_value(value))
        self.assertEquals(var.get_value(), value)
        self.assertTrue(is_symbolic(var.get_var()))

    def test_concrete_bool(self):
        # Arrange
        name = 'TestVar1'
        value = True
        vsort = z3.BoolSort()
        # Act
        var = SMTVar(name, vsort, value)
        # Assert
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertEquals(var.var, value)
        self.assertEquals(var.get_value(), value)
        self.assertTrue(is_symbolic(var.get_var()))

    def test_symbolic_bool(self):
        # Arrange
        name = 'TestVar1'
        vsort = z3.BoolSort()
        value = True
        # Act
        var = SMTVar(name, vsort)
        var_before = var.var
        get_var_before = var.get_var()
        with self.assertRaises(RuntimeError):
            self.assertEquals(var.get_value(), value)
        # Concertize the value
        solver = z3.Solver()
        solver.add(var.var == value)
        self.assertEquals(solver.check(), z3.sat)
        model = solver.model()
        var.eval(model)
        # Assert
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertTrue(is_symbolic(var_before))
        self.assertTrue(is_symbolic(get_var_before))
        self.assertEquals(var.name, name)
        self.assertEquals(var.vsort, vsort)
        self.assertEquals(var.var, value)
        self.assertEquals(var.get_value(), value)
        self.assertTrue(is_symbolic(var.get_var()))


@attr(speed='fast')
class SolverContextTest(unittest.TestCase):
    def test_new_var(self):
        ctx = SolverContext()
        name1 = ctx.fresh_var_name()
        name2 = ctx.fresh_var_name()
        self.assertTrue(isinstance(name1, basestring))
        self.assertTrue(isinstance(name2, basestring))
        self.assertFalse(name1 == name2)

    def test_register_var(self):
        name = 'TestVar1'
        vsort = z3.IntSort()
        var = SMTVar(name, vsort)

        ctx = SolverContext()
        ctx._register_var(var)
        self.assertTrue(var.name in ctx._vars)
        with self.assertRaises(ValueError):
            ctx._register_var(var)

    def test_create_var(self):
        ctx = SolverContext()
        var = ctx.create_fresh_var(z3.IntSort(), value=10)
        self.assertTrue(isinstance(var, SMTVar))
        with self.assertRaises(ValueError):
            var = ctx.create_fresh_var(z3.IntSort(), name=var.name, value=10)

    def test_fresh_const_name(self):
        ctx = SolverContext()
        name1 = ctx.fresh_constraint_name()
        name2 = ctx.fresh_constraint_name()
        self.assertTrue(isinstance(name1, basestring))
        self.assertTrue(isinstance(name2, basestring))
        self.assertFalse(name1 == name2)

    def test_register_const(self):
        # Arrange
        var1 = SMTVar('var1', z3.IntSort())
        var2 = SMTVar('var1', z3.IntSort())
        const = var1.var + var2.var > 10
        # Act
        ctx = SolverContext()
        name = ctx.register_constraint(const)
        with self.assertRaises(ValueError):
            ctx.register_constraint(const, name)
        constraints = list(ctx.constraints_itr())
        # Assert
        self.assertIsNotNone(ctx.get_constraint(name))
        self.assertIsNotNone(ctx.get_constraints_info(name))
        self.assertEquals(len(constraints), 1)
        self.assertEquals(constraints[0][0], name)
        self.assertEquals(constraints[0][1], const)

    def test_get_constraints(self):
        var1 = SMTVar('var1', z3.IntSort())
        var2 = SMTVar('var1', z3.IntSort())
        const = var1.var + var2.var > 10
        name = 'cosnt1'
        ctx = SolverContext()
        ctx.register_constraint(const, name)
        self.assertIsNotNone(ctx.get_constraint(name))
        self.assertIsNotNone(ctx.get_constraints_info(name))
        with self.assertRaises(ValueError):
            ctx.get_constraint('NotRegistered')
        with self.assertRaises(ValueError):
            ctx.get_constraints_info('NotRegistered')

    def test_create_enum_type(self):
        # Arrange
        values = ['A', 'B', 'C']
        sort_name = 'TestType'
        ctx = SolverContext()
        # Act
        vsort = ctx.create_enum_type(sort_name, values)
        # Assert
        self.assertTrue(isinstance(vsort, EnumType))
        self.assertEquals(vsort.name, sort_name)
        self.assertEquals(vsort.concrete_values, values)
        with self.assertRaises(ValueError):
            ctx.create_enum_type(sort_name, values)
        with self.assertRaises(ValueError):
            ctx.create_enum_type("name2", values)

    def test_set_model(self):
        # Arrange
        values = ['A', 'B', 'C']
        sort_name = 'TestType'
        ctx = SolverContext()
        vsort = ctx.create_enum_type(sort_name, values)
        var1 = ctx.create_fresh_var(vsort)
        val1 = vsort.get_symbolic_value('A')
        var2 = ctx.create_fresh_var(z3.IntSort())
        var3 = ctx.create_fresh_var(z3.BoolSort())
        solver = z3.Solver()
        solver.add(var1.var == val1)
        solver.add(var2.var == 10)
        solver.add(var3.var == True)
        solver.check()
        # Act
        ctx.set_model(solver.model())
        # Assert
        self.assertTrue(var1.is_concrete)
        self.assertTrue(var2.is_concrete)
        self.assertTrue(var3.is_concrete)
        self.assertEquals(var1.get_value(), 'A')
        self.assertEquals(var2.get_value(), 10)
        self.assertEquals(var3.get_value(), True)


@attr(speed='fast')
class ReadAnnouncementsTest(unittest.TestCase):
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
            as_path=[9, 2, 5, 7, 8], as_path_len=VALUENOTSET,
            next_hop='Hop2', local_pref=VALUENOTSET, med=10,
            communities={c1: False, c2: False, c3: VALUENOTSET},
            permitted=True)
        return ann1, ann2

    def test_read(self):
        concrete_anns = self.get_anns()
        ctx = SolverContext.create_context(concrete_anns)
        sym_anns = read_announcements(concrete_anns, ctx)
        self.assertEqual(len(sym_anns), len(concrete_anns))
        for sym_ann, con_ann in zip(sym_anns, concrete_anns):
            for attr in Announcement.attributes:
                if attr == 'communities':
                    for community in con_ann.communities:
                        con_val = con_ann.communities[community]
                        sym_val = sym_ann.communities[community]
                        if is_empty(con_val):
                            self.assertFalse(sym_val.is_concrete)
                        else:
                            self.assertTrue(sym_val.is_concrete)
                            self.assertEquals(sym_val.get_value(), con_val)
                    continue
                con_val = getattr(con_ann, attr)
                sym_val = getattr(sym_ann, attr)
                if is_empty(con_val):
                    self.assertFalse(sym_val.is_concrete)
                else:
                    self.assertTrue(sym_val.is_concrete)
                    if attr == 'as_path':
                        con_val = get_as_path_key(con_val)
                    sym_val_concrete = sym_val.get_value()
                    if attr == 'origin':
                        sym_val_concrete = BGP_ATTRS_ORIGIN.__members__[
                            sym_val_concrete]
                    self.assertEquals(sym_val_concrete, con_val)


@attr(speed='fast')
class AnnouncementsContextTest(unittest.TestCase):
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
            as_path=[9, 2, 5, 7, 8], as_path_len=VALUENOTSET,
            next_hop='Hop2', local_pref=VALUENOTSET, med=10,
            communities={c1: False, c2: False, c3: VALUENOTSET},
            permitted=True)
        return ann1, ann2

    def test_create(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = SolverContext.create_context(concrete_anns)
        # Act
        sym_anns = read_announcements(concrete_anns, ctx)
        # Assert
        self.assertEquals(len(sym_anns), 2)

    def test_sub(self):
        # Arrange
        concrete_anns = self.get_anns()
        ctx = SolverContext.create_context(concrete_anns)
        sym_anns = read_announcements(concrete_anns, ctx)
        mutator = self
        # Act
        new_anns = sym_anns.create_new([sym_anns[0]], mutator)
        new_anns2 = new_anns.create_new([new_anns[0]], mutator)
        self.assertEquals(len(sym_anns), 2)
        self.assertEquals(len(new_anns), 1)
        self.assertEquals(len(new_anns2), 1)
        self.assertEquals(sym_anns.mutators, [])
        self.assertEquals(new_anns.mutators, [mutator])
        self.assertEquals(new_anns2.mutators, [mutator, mutator])