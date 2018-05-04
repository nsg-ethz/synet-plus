#!/usr/bin/env python
import unittest

from nose.plugins.attrib import attr

from synet.synthesis.static import CannotSynthesizeStaticRoute
from synet.synthesis.static import StaticSyn
from tekton.graph import NetworkGraph
from synet.utils.common import PathReq
from synet.utils.common import Protocols


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


@attr(speed='fast')
class StaticTest(unittest.TestCase):
    def get_two_nodes(self):
        g = NetworkGraph()
        g.add_router('R1')
        g.add_router('R2')
        g.add_router_edge('R1', 'R2')
        g.add_router_edge('R2', 'R1')
        return g

    def test_two_nodes(self):
        g = self.get_two_nodes()
        prefix = 'P0'
        reqs = [PathReq(Protocols.BGP, prefix, ['R1', 'R2'], False)]
        g.set_static_routes_empty('R1')
        static_syn = StaticSyn(reqs, g)
        static_syn.synthesize()
        self.assertEquals(g.get_static_routes('R1')[prefix], 'R2')

    def test_not_empty(self):
        g = self.get_two_nodes()
        prefix = 'P0'
        reqs = [PathReq(Protocols.BGP, prefix, ['R1', 'R2'], False)]
        static_syn = StaticSyn(reqs, g)
        with self.assertRaises(CannotSynthesizeStaticRoute):
            static_syn.synthesize()

    def test_two_existing(self):
        g = self.get_two_nodes()
        prefix = 'P0'
        reqs = [PathReq(Protocols.BGP, prefix, ['R1', 'R2'], False)]
        g.add_static_route('R1', prefix, 'R2')
        static_syn = StaticSyn(reqs, g)
        static_syn.synthesize()
        self.assertEquals(g.get_static_routes('R1')[prefix], 'R2')
