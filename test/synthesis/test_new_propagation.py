
import time
import z3
import unittest

import networkx as nx

from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.common import PathOrderReq
from synet.utils.topo_gen import get_ebgp_linear_topo
from synet.utils.topo_gen import get_ibgp_linear_topo
from synet.utils.topo_gen import get_griffin_graph
from synet.utils.topo_gen import get_griffin_ibgp_graph

from tekton.graph import NetworkGraph
from ipaddress import ip_network
from ipaddress import ip_interface
from tekton.bgp import Access
from tekton.bgp import RouteMap
from tekton.bgp import RouteMapLine
from tekton.bgp import IpPrefixList
from tekton.bgp import MatchIpPrefixListList
from tekton.bgp import MatchAsPath
from tekton.bgp import MatchAsPathLen
from tekton.bgp import ActionSetLocalPref
from tekton.bgp import Announcement
from tekton.bgp import BGP_ATTRS_ORIGIN
from tekton.bgp import Community

from tekton.gns3 import GNS3Topo

from synet.utils.bgp_utils import compute_next_hop_map
from synet.utils.bgp_utils import extract_all_next_hops
from synet.utils.smt_context import VALUENOTSET
from synet.synthesis.new_propagation import EBGPPropagation
from synet.synthesis.connected import ConnectedSyn


from synet.utils.fnfree_smt_context import read_announcements
from synet.utils.fnfree_smt_context import SolverContext

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class PropagationTest2(unittest.TestCase):
    def get_anns(self):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix='Prefix0', peer='R1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[100], as_path_len=1,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)
        return [ann1]

    def get_sym(self, concrete_anns, ctx):
        return read_announcements(concrete_anns, ctx)

    @unittest.skip
    def test_expand_single(self):
        # Arrange
        N = 4
        g = get_ibgp_linear_topo(N=N)
        req = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R1'], strict=False)
        ctx = self.create_context([req], g)
        propagation = EBGPPropagation([req], g, ctx)
        # Act
        # Case 1
        p1 = propagation.expand_as_path((100,), ['R1'])
        print "P1", p1
        expected = set(
            [
              ('R1',),
              ('R1', 'R2'),
              ('R1', 'R3'),
              ('R1', 'R4'),])
        self.assertEquals(p1, expected)

    def test_expand(self):
        # Arrange
        g = get_griffin_ibgp_graph()
        p0 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2_2', 'R2_0', 'R4', 'R1'], strict=False)
        p1 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2_2', 'R1'], strict=False)
        r2_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p0, p1], strict=False)

        p2 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R2_3', 'R1'], strict=False)
        p3 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R1'], strict=False)
        r3_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p2, p3], strict=False)

        r4_req = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R4', 'R1'], strict=False)

        p6 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5_3', 'R5_2', 'R5_0', 'R4', 'R1'], strict=False)
        p7 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5_3', 'R5_1', 'R3', 'R1'], strict=False)
        r5_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p6, p7], strict=False)

        reqs = [r2_req, r3_req, r4_req, r5_req]
        ctx = self.create_context(reqs, g)

        propagation = EBGPPropagation(reqs, g, ctx)
        # Act
        # Case 1: Direct eBGP
        p1 = propagation.expand_as_path((100,), ['R1'])
        p2 = propagation.expand_as_path((100, 400), ['R1'])
        self.assertEquals(p1, set([('R1',),]))
        self.assertEquals(p2, set([('R1', 'R4')]))

        # Case 2: Direct eBGP->iBGP
        p3 = propagation.expand_as_path((100, 200), ['R1'])
        paths_to_r2 = set([
            ('R1', 'R2_2'),
            ('R1', 'R2_2', 'R2_0'),
            ('R1', 'R2_2', 'R2_1'),
            ('R1', 'R2_2', 'R2_3'),
            ('R1', 'R2_3'),
            ('R1', 'R2_3', 'R2_0'),
            ('R1', 'R2_3', 'R2_1'),
            ('R1', 'R2_3', 'R2_2'),
        ])
        self.assertEquals(p3, paths_to_r2)

        ## Case 3: eBGP-> iBGP -> eBGP
        p4 = propagation.expand_as_path((100, 200, 300), ['R1'])
        paths_to_r3 = set([
            ('R1', 'R2_2', 'R2_1', 'R3'),
            ('R1', 'R2_2', 'R2_3', 'R3'),
            ('R1', 'R2_3', 'R3'),
            ('R1', 'R2_3', 'R2_1', 'R3'),
        ])
        self.assertEquals(p4, paths_to_r3)

    def create_context(self, reqs, g):
        connected = ConnectedSyn(reqs, g, full=True)
        connected.synthesize()
        next_hops_map = compute_next_hop_map(g)
        next_hops = extract_all_next_hops(next_hops_map)
        peers = [node for node in g.routers_iter() if g.is_bgp_enabled(node)]
        ctx = SolverContext.create_context(self.get_anns(),
                                           next_hop_list=next_hops,
                                           peer_list=peers,
                                           create_as_paths=False)
        return ctx

    def test_good_gadget(self):
        # Arrange
        g = get_griffin_graph()
        net = "Prefix0"
        prefix_map = {net: ip_network(u'128.0.0.0/24')}
        g.set_loopback_addr('R1', 'lo0',
                            ip_interface("%s/%d" % (prefix_map[net].hosts().next(), prefix_map[net].prefixlen)))
        g.add_bgp_announces('R1', 'lo0')

        for src in g.routers_iter():
            for dst in g.get_bgp_neighbors(src):
                if src == dst:
                    continue
                # Export
                ip_list = IpPrefixList(name="L_%s-to_%s" % (src, dst),
                             access=Access.permit,
                             networks=[VALUENOTSET])
                g.add_ip_prefix_list(src, ip_list)
                rline = RouteMapLine(
                    [MatchIpPrefixListList(ip_list)],
                    [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 10)
                rmap = RouteMap('Exp_%s' % dst, [rline])
                g.add_route_map(src, rmap)
                g.add_bgp_export_route_map(src, dst, rmap.name)
                # Import
                #rline = RouteMapLine(None, [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 10)
                #rmap = RouteMap('Imp_%s' % dst, [rline])
                #g.add_route_map(src, rmap)
                #g.add_bgp_import_route_map(src, dst, rmap.name)
                rline1 = RouteMapLine([MatchAsPath(VALUENOTSET)], [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 10)
                rline2 = RouteMapLine([MatchAsPath(VALUENOTSET)], [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 20)
                rline3 = RouteMapLine([MatchAsPath(VALUENOTSET)], [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 30)
                rmap = RouteMap('Imp_%s' % dst, [rline1, rline2, rline3])
                g.add_route_map(src, rmap)
                g.add_bgp_import_route_map(src, dst, rmap.name)

        p0 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R4', 'R1'], strict=False)
        p1 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R1'], strict=False)
        r2_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p0, p1], strict=False)

        p2 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R2', 'R1'], strict=False)
        p3 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R1'], strict=False)
        r3_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p2, p3], strict=False)

        r4_req = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R4', 'R1'], strict=False)

        p6 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5', 'R4', 'R1'], strict=False)
        p7 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5', 'R3', 'R1'], strict=False)
        r5_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p6, p7], strict=False)
        # Action
        reqs = [r2_req, r3_req, r4_req, r5_req]
        ctx = self.create_context(reqs, g)
        propagation = EBGPPropagation(reqs, g, ctx)
        unmatching_order = propagation.compute_dags()
        assert not unmatching_order
        propagation.synthesize()
        solver = z3.Solver(ctx=ctx.z3_ctx)
        ret = ctx.check(solver)
        assert ret == z3.sat, solver.unsat_core()
        print solver.model()
        propagation.update_network_graph()
        gns3 = GNS3Topo(g, prefix_map)
        gns3.write_configs('./out-configs/good_gadget')

    def test_naughty_gadget(self):
        # Arrange
        g = get_griffin_graph()
        p0 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R4', 'R1'], strict=False)
        p1 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R1'], strict=False)
        r2_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p0, p1], strict=False)

        p2 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R2', 'R1'], strict=False)
        p3 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R1'], strict=False)
        r3_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p2, p3], strict=False)

        p4 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R4', 'R5', 'R3', 'R1'], strict=False)
        p5 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R4', 'R1'], strict=False)
        r4_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p4, p5], strict=False)

        p6 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5', 'R4', 'R1'], strict=False)
        p7 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5', 'R3', 'R1'], strict=False)
        r5_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p6, p7], strict=False)
        reqs = [r2_req, r3_req, r4_req, r5_req]
        # Action
        ctx = self.create_context(reqs, g)
        propagation = EBGPPropagation(reqs, g, ctx)
        unmatching_order = propagation.compute_dags()
        dag = propagation.ebgp_graphs['Prefix0']
        # Assert
        assert unmatching_order

    def test_bad_gadget(self):
        # Arrange
        g = get_griffin_graph()
        p0 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R4', 'R1'], strict=False)
        p1 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R1'], strict=False)
        r2_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p0, p1], strict=False)

        p2 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R2', 'R1'], strict=False)
        p3 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R1'], strict=False)
        r3_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p2, p3], strict=False)

        p4 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R4', 'R5', 'R3', 'R1'], strict=False)
        p5 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R4', 'R1'], strict=False)
        r4_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p4, p5], strict=False)

        p6 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5', 'R3', 'R1'], strict=False)
        p7 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5', 'R4', 'R1'], strict=False)
        r5_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p6, p7], strict=False)
        reqs = [r2_req, r3_req, r4_req, r5_req]
        # Action
        ctx = self.create_context(reqs, g)
        propagation = EBGPPropagation(reqs, g, ctx)
        unmatching_order = propagation.compute_dags()
        dag = propagation.ebgp_graphs['Prefix0']
        # Assert
        assert unmatching_order

    def test_good_gadget_ibgp(self):
        # Arrange
        g = get_griffin_ibgp_graph()

        for src in g.routers_iter():
            for dst in g.get_bgp_neighbors(src):
                if src == dst:
                    continue
                # Export
                matches1 = [MatchAsPath(VALUENOTSET)]
                matches2 = [MatchAsPath(VALUENOTSET)]
                rline1 = RouteMapLine(matches1, [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 10)
                rline2 = RouteMapLine(matches2, [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 20)
                rmap = RouteMap('Exp_%s' % dst, [rline1, rline2])
                g.add_route_map(src, rmap)
                g.add_bgp_export_route_map(src, dst, rmap.name)
                # Import
                matches1 = [MatchAsPath(VALUENOTSET)]
                matches2 = [MatchAsPath(VALUENOTSET)]
                rline1 = RouteMapLine(matches1, [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 10)
                rline2 = RouteMapLine(matches2, [ActionSetLocalPref(VALUENOTSET)], VALUENOTSET, 20)
                rmap = RouteMap('Imp_%s' % dst, [rline1, rline2])
                g.add_route_map(src, rmap)
                g.add_bgp_import_route_map(src, dst, rmap.name)

        p0 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2_2', 'R2_0', 'R4', 'R1'], strict=False)
        p1 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2_2', 'R1'], strict=False)
        r2_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p0, p1], strict=False)

        p2 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R2_3', 'R1'], strict=False)
        p3 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R3', 'R1'], strict=False)
        r3_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p2, p3], strict=False)

        r4_req = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R4', 'R1'], strict=False)

        p6 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5_3', 'R5_2', 'R5_0', 'R4', 'R1'], strict=False)
        p7 = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R5_3', 'R5_1', 'R3', 'R1'], strict=False)
        r5_req = PathOrderReq(Protocols.BGP, dst_net='Prefix0', paths=[p6, p7], strict=False)

        reqs = [r2_req, r3_req, r4_req, r5_req]
        ctx = self.create_context(reqs, g)

        # Act
        propagation = EBGPPropagation(reqs, g, ctx)
        unmatching_order = propagation.compute_dags()
        ebgp = propagation.ebgp_graphs['Prefix0']
        ibgp = propagation.ibgp_graphs['Prefix0']
        #nx.nx_pydot.write_dot(ibgp, '/tmp/ibgp_good.xdot')
        #nx.nx_pydot.write_dot(ebgp, '/tmp/ebgp_good.xdot')

        # Assert
        assert not unmatching_order
        # Assert eBGP propagation
        self.assertEqual(ebgp.node[100]['order'], [set([(100,)])])
        self.assertEqual(ebgp.node[200]['order'], [set([(100,400, 200)]), set([(100, 200)])])
        self.assertEqual(ebgp.node[300]['order'], [set([(100, 200, 300)]), set([(100, 300)])])
        self.assertEqual(ebgp.node[400]['order'], [set([(100, 400)])])
        self.assertEqual(ebgp.node[500]['order'], [set([(100, 400, 500)]), set([(100, 300, 500)])])
        # Assert iBGP propagation
        self.assertEqual(ibgp.node['R1']['order'], [set([('R1',)])])
        self.assertEqual(ibgp.node['R2_0']['order'], [set([('R1', 'R4', 'R2_0')])])
        self.assertEqual(ibgp.node['R2_1']['order'], [])
        self.assertEqual(ibgp.node['R2_2']['order'], [set([('R1', 'R4', 'R2_0', 'R2_2')]), set([('R1', 'R2_2')])])
        self.assertEqual(ibgp.node['R2_3']['order'], [set([('R1', 'R2_3')])])
        self.assertEqual(ibgp.node['R3']['order'], [set([('R1', 'R2_3', 'R3')]), set([('R1', 'R3')])])
        self.assertEqual(ibgp.node['R4']['order'], [set([('R1', 'R4')])])
        self.assertEqual(ibgp.node['R5_0']['order'], [set([('R1', 'R4', 'R5_0')])])
        self.assertEqual(ibgp.node['R5_1']['order'], [set([('R1', 'R3', 'R5_1')])])
        self.assertEqual(ibgp.node['R5_2']['order'], [set([('R1', 'R4', 'R5_0', 'R5_2')])])
        self.assertEqual(ibgp.node['R5_3']['order'], [set([('R1', 'R4', 'R5_0', 'R5_2', 'R5_3')]), set([('R1', 'R3', 'R5_1', 'R5_3')])])
        propagation.synthesize()

    def test_ibgp_linear(self):
        # Arrange
        N = 4
        g = get_ibgp_linear_topo(N=N)
        net = "Prefix0"
        prefix_map = {net: ip_network(u'128.0.0.0/24')}
        g.set_loopback_addr('R1', 'lo0',
                            ip_interface("%s/%d" % (prefix_map[net].hosts().next(),
                                                    prefix_map[net].prefixlen)))
        g.add_bgp_announces('R1', 'lo0')
        for i, node in enumerate(sorted(g.routers_iter())):
            g.set_loopback_addr('R%d' % (i + 1), 'lo100', ip_interface(u'192.168.0.%d/32' % i))
        for i in range(1, N):
            r1 = 'R1'
            r2 = "R%d" % (i + 1)
            g.set_bgp_neighbor_iface(r1, r2, 'lo100')

        for i in range(2, N + 1):
            r1 = 'R1'
            node = 'R%s' % i
            rline = RouteMapLine(None, None, VALUENOTSET, 10)
            #rmap = RouteMap('Exp_%s' % node, [rline])
            #g.add_route_map(r1, rmap)
            #g.add_bgp_export_route_map('R1', 'R%d' % i, rmap.name)
            rmap = RouteMap('Imp_%s' % r1, [rline])
            g.add_route_map(node, rmap)
            g.add_bgp_import_route_map(node, r1, rmap.name)

        #nx.nx_pydot.write_dot(g, '/tmp/linear.dot')
        req = PathReq(Protocols.BGP, dst_net='Prefix0',
                      path=['R3', 'R2', 'R1'], strict=False)
        ctx = self.create_context([req], g)
        # Act
        propagation = EBGPPropagation([req], g, ctx)
        propagation.compute_dags()

        # Assert
        #ebgp = propagation.ebgp_graphs['Prefix0']
        #ibgp = propagation.ibgp_graphs['Prefix0']
        #nx.nx_pydot.write_dot(ebgp, '/tmp/ebgp_linear.dot')
        #nx.nx_pydot.write_dot(ibgp, '/tmp/ibgp_linear.dot')
        propagation.synthesize()

        solver = z3.Solver(ctx=ctx.z3_ctx)
        ret = ctx.check(solver)
        assert ret == z3.sat, solver.unsat_core()
        propagation.update_network_graph()

        for router in g.routers_iter():
            g.enable_ospf(router, 100)
            for iface in g.get_ifaces(router):
                g.add_ospf_network(router, iface, 0)
            if router != 'R1':
                g.add_ospf_network(router,
                                   g.get_loopback_addr(router, 'lo100').network, 0)
        g.add_ospf_network('R1', g.get_loopback_addr('R1', 'lo0').network, 0)

        gns3 = GNS3Topo(g, prefix_map)
        gns3.write_configs('./out-configs/ibgp-linear-%d' % N)

    def test_ebgp_linear(self):
        # Arrange
        N = 4
        g = get_ebgp_linear_topo(N)
        net = "Prefix0"
        prefix_map = {net: ip_network(u'128.0.0.0/24')}
        g.set_loopback_addr('R1', 'lo0', ip_interface("%s/%d" % (prefix_map[net].hosts().next(), prefix_map[net].prefixlen)))
        g.add_bgp_announces('R1', 'lo0')

        for i in range(1, N + 1):
            first = 'R%d' % (i - 1) if i > 1 else None
            middle = 'R%d' % i
            last = 'R%d' % (i + 1) if i < N else None
            if last:
                #if middle == 'R1':
                #    continue
                rline = RouteMapLine(None, None, VALUENOTSET, 10)
                rmap = RouteMap('Exp_%s' % last, [rline])
                g.add_route_map(middle, rmap)
                g.add_bgp_export_route_map(middle, last, rmap.name)
                print "ADD EXPORT ROUTE MAP AT", middle, rmap.name
            if first:
                rmap = RouteMap('Imp_%s' % first, [rline])
                g.add_route_map(middle, rmap)
                g.add_bgp_import_route_map(middle, first, rmap.name)
                print "ADD IMPORT ROUTE MAP AT", middle, rmap.name

        #nx.nx_pydot.write_dot(g, '/tmp/linear.xdot')
        req = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R1'], strict=False)
        ctx = self.create_context([req], g)
        # Act
        propagation = EBGPPropagation([req], g, ctx)
        propagation.compute_dags()

        # Assert
        ebgp = propagation.ebgp_graphs['Prefix0']
        ibgp = propagation.ibgp_graphs['Prefix0']
        nx.nx_pydot.write_dot(ebgp, '/tmp/ebgp_linear.xdot')
        nx.nx_pydot.write_dot(ibgp, '/tmp/ibgp_linear.xdot')
        propagation.synthesize()

        solver = z3.Solver(ctx=ctx.z3_ctx)
        ret = ctx.check(solver)
        assert ret == z3.sat, solver.unsat_core()
        propagation.update_network_graph()
        gns3 = GNS3Topo(g, prefix_map)
        gns3.write_configs('./out-configs/ebgp-linear-%s' % N)
