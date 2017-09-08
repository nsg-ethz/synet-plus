#!/usr/bin/env python
"""
Test the speed of Z3 has function vs get_id
"""

import unittest
from nose.plugins.attrib import attr
import z3

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


@attr(speed='slow')
class TestVars(unittest.TestCase):
    def test_hash(self):
        num = 100
        sort, vars = z3.EnumSort('Sort', ['Var_%d' for i in range(num)])
        names = dict([(var, str(var)) for var in vars])
        for var in vars:
            self.assertTrue(var in names)
            self.assertTrue(var in vars)

    def test_get_id(self):
        num = 100
        sort, vars = z3.EnumSort('Sort', ['Var_%d' for i in range(num)])
        names = dict([(var.get_id(), str(var)) for var in vars])
        var_ids = [var.get_id() for var in vars]
        for var in vars:
            self.assertTrue(var.get_id() in names)
            self.assertTrue(var.get_id() in var_ids)
        print len(names.keys())
