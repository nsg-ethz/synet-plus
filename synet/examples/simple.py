#!/usr/bin/env python
"""
Examples showing how to use SyNET over simple networks.
"""

from ipaddress import ip_interface
from ipaddress import ip_network

import argparse
import z3

from synet.synthesis.connected import ConnectedSyn
from synet.synthesis.new_propagation import EBGPPropagation
from tekton.bgp import Access
from tekton.bgp import ActionSetCommunity
from tekton.bgp import ActionSetLocalPref
from tekton.bgp import Announcement
from tekton.bgp import BGP_ATTRS_ORIGIN
from tekton.bgp import Community
from tekton.bgp import CommunityList
from tekton.bgp import IpPrefixList
from tekton.bgp import MatchAsPath
from tekton.bgp import MatchCommunitiesList
from tekton.bgp import MatchIpPrefixListList
from tekton.bgp import MatchNextHop
from tekton.bgp import RouteMap
from tekton.bgp import RouteMapLine
from tekton.gns3 import GNS3Topo
from tekton.graph import NetworkGraph
from synet.utils.bgp_utils import compute_next_hop_map
from synet.utils.bgp_utils import extract_all_next_hops
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.fnfree_smt_context import SolverContext
from synet.utils.fnfree_smt_context import VALUENOTSET
from synet.utils.fnfree_smt_context import read_announcements
from synet.utils.topo_gen import get_ebgp_linear_topo


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


def get_sym(concrete_anns, ctx):
    return read_announcements(concrete_anns, ctx)


def create_context(reqs, g, announcements, create_as_paths=False):
    connected = ConnectedSyn([], g, full=True)
    connected.synthesize()
    next_hops_map = compute_next_hop_map(g)
    next_hops = extract_all_next_hops(next_hops_map)
    peers = [node for node in g.routers_iter() if g.is_bgp_enabled(node)]
    ctx = SolverContext.create_context(announcements, peer_list=peers,
                                       next_hop_list=next_hops, create_as_paths=create_as_paths)
    return ctx


def get_announcement(prefix, peer, comms):

    ann = Announcement(prefix=prefix, peer=peer,
                       origin=BGP_ATTRS_ORIGIN.EBGP,
                       next_hop='%sHop' % peer,
                       as_path=[100], as_path_len=1,
                       local_pref=100, med=100,
                       communities=comms,
                       permitted=True)
    return ann


def two_ebgp_nodes(export_path):
    """
    Two routers connected via eBGP
    Very simple once router announces a single prefix and the other selects it
    """
    graph = NetworkGraph()
    r1, r2 = 'R1', 'R2'
    graph.add_router(r1)
    graph.add_router(r2)
    graph.add_router_edge(r1, r2)
    graph.add_router_edge(r2, r1)

    # BGP configs
    graph.set_bgp_asnum(r1, 100)
    graph.set_bgp_asnum(r2, 200)
    # Establish peering
    # The actual network interfaces used for peering will be synthesized
    graph.add_bgp_neighbor(r1, r2, router_a_iface=VALUENOTSET, router_b_iface=VALUENOTSET)

    # Some internal network
    net = ip_network(u'128.0.0.0/24')
    prefix = '128_0_0_0'
    prefix_map = {prefix: net}
    lo0 = 'lo0'
    graph.set_loopback_addr(r1, lo0, ip_interface("%s/%d" % (net.hosts().next(), net.prefixlen)))
    # Announce the internal network
    graph.add_bgp_announces(r1, lo0)

    # The communities recognized by us
    comms = [Community("100:10"), Community("100:20")]

    # The announcement that will be propagated by R1
    ann = Announcement(prefix=prefix, peer=r1,
                       origin=BGP_ATTRS_ORIGIN.EBGP,
                       next_hop='R1Hop',
                       as_path=[100], as_path_len=1,
                       local_pref=100, med=100,
                       communities=dict([(c, False) for c in comms]),
                       permitted=True)

    path = PathReq(Protocols.BGP, prefix, ['R2', 'R1'], False)
    reqs = [path]

    # Get SMT Context
    ctx = create_context(reqs, graph, [ann])

    propagation = EBGPPropagation(reqs, graph, ctx)

    propagation.compute_dags()
    propagation.synthesize()

    # Synthesize all the interfaces and link configurations
    connecte_syn = ConnectedSyn([], graph, full=True)
    connecte_syn.synthesize()

    # SMT Solving
    solver = z3.Solver(ctx=ctx.z3_ctx)
    assert ctx.check(solver) == z3.sat, solver.unsat_core()

    # Update graph with the concrete values after solver
    propagation.update_network_graph()
    gns3 = GNS3Topo(graph=graph, prefix_map=prefix_map)
    gns3.write_configs('%s/ibgp-simple' % export_path)


def two_ebgp_nodes_route_map(export_path):
    """
    Two routers connected via eBGP with route maps
    Very simple one router announces a single prefix and the other selects it
    """
    graph = NetworkGraph()
    r1, r2 = 'R1', 'R2'
    graph.add_router(r1)
    graph.add_router(r2)
    graph.add_router_edge(r1, r2)
    graph.add_router_edge(r2, r1)

    # BGP configs
    graph.set_bgp_asnum(r1, 100)
    graph.set_bgp_asnum(r2, 200)
    # Establish peering
    # The actual network interfaces used for peering will be synthesized
    graph.add_bgp_neighbor(r1, r2, router_a_iface=VALUENOTSET, router_b_iface=VALUENOTSET)

    # Some internal network
    net = ip_network(u'128.0.0.0/24')
    prefix = '128_0_0_0'
    prefix_map = {prefix: net}
    lo0 = 'lo0'
    graph.set_loopback_addr(r1, lo0, ip_interface("%s/%d" % (net.hosts().next(), net.prefixlen)))
    # Announce the internal network
    graph.add_bgp_announces(r1, lo0)

    # The communities recognized by us
    comms = [Community("100:10"), Community("100:20")]

    # The announcement that will be propagated by R1
    ann = Announcement(prefix=prefix, peer=r1,
                       origin=BGP_ATTRS_ORIGIN.EBGP,
                       next_hop='R1Hop',
                       as_path=[100], as_path_len=1,
                       local_pref=100, med=100,
                       communities=dict([(c, False) for c in comms]),
                       permitted=True)

    path = PathReq(Protocols.BGP, prefix, ['R2', 'R1'], False)
    reqs = [path]

    # Create a route map to export from R1 to R2
    iplist = IpPrefixList(name='IpList1', access=Access.permit, networks=[prefix])
    graph.add_ip_prefix_list(r1, iplist)
    ip_match = MatchIpPrefixListList(iplist)
    set_community = ActionSetCommunity([comms[0]])
    rline = RouteMapLine(matches=[ip_match], actions=[set_community], access=Access.permit, lineno=10)
    export_map = RouteMap(name="Export_R1_to_R2", lines=[rline])
    # Register the route map
    graph.add_route_map(r1, export_map)
    # Set the route map as an export route map
    graph.add_bgp_export_route_map(r1, r2, export_map.name)

    # Create a route map to import at R2 to from R1
    comm_list = CommunityList(list_id=1, access=Access.permit, communities=[comms[0]])
    graph.add_bgp_community_list(r2, comm_list)
    comm_match = MatchCommunitiesList(comm_list)
    set_local_pref = ActionSetLocalPref(200)
    rline = RouteMapLine(matches=[MatchNextHop(VALUENOTSET)], actions=[set_local_pref], access=Access.permit, lineno=10)
    import_map = RouteMap(name="Import_R2_from_R1", lines=[rline])
    # Register the route map
    graph.add_route_map(r2, import_map)
    # Set the route map as an import route map
    graph.add_bgp_import_route_map(r2, r1, import_map.name)

    # Get SMT Context
    ctx = create_context(reqs, graph, [ann])
    propagation = EBGPPropagation(reqs, graph, ctx)
    propagation.compute_dags()
    propagation.synthesize()

    # Synthesize all the interfaces and link configurations
    connecte_syn = ConnectedSyn([], graph, full=True)
    connecte_syn.synthesize()

    # SMT Solving
    solver = z3.Solver(ctx=ctx.z3_ctx)
    assert ctx.check(solver) == z3.sat, solver.unsat_core()

    # Update graph with the concrete values after solver
    propagation.update_network_graph()
    gns3 = GNS3Topo(graph=graph, prefix_map=prefix_map)
    gns3.write_configs('%s/ebgp-route-map' % export_path)
    graph.write_graphml('%s/ebgp-route-map/topology.graphml' % export_path)


def two_ibgp_nodes(export_path):
    """
    Two routers connected via iBGP
    Very simple once router announces a single prefix and the other selects it
    """
    graph = NetworkGraph()
    r1, r2 = 'R1', 'R2'
    graph.add_router(r1)
    graph.add_router(r2)
    graph.add_router_edge(r1, r2)
    graph.add_router_edge(r2, r1)

    # BGP configs
    graph.set_bgp_asnum(r1, 100)
    graph.set_bgp_asnum(r2, 100)
    # Establish peering
    # The actual network interfaces used for peering will be synthesized
    graph.add_bgp_neighbor(r1, r2, router_a_iface=VALUENOTSET, router_b_iface=VALUENOTSET)

    # Enable OSPF
    graph.enable_ospf(r1, 100)
    graph.enable_ospf(r2, 100)
    graph.add_ospf_network(r1, 'lo100', 0)
    graph.add_ospf_network(r2, 'lo100', 0)
    for iface in graph.get_ifaces(r1):
        graph.add_ospf_network(r1, iface, 0)
    for iface in graph.get_ifaces(r2):
        graph.add_ospf_network(r2, iface, 0)

    # Some internal network
    net = ip_network(u'128.0.0.0/24')
    prefix = '128_0_0_0'
    prefix_map = {prefix: net}
    lo0 = 'lo10'
    graph.set_loopback_addr(r1, lo0, ip_interface("%s/%d" % (net.hosts().next(), net.prefixlen)))
    # Announce the internal network
    graph.add_bgp_announces(r1, lo0)

    # The communities recognized by us
    comms = [Community("100:10"), Community("100:20")]

    # The announcement that will be propagated by R1
    ann = Announcement(prefix=prefix, peer=r1,
                       origin=BGP_ATTRS_ORIGIN.EBGP,
                       next_hop='R1Hop',
                       as_path=[100], as_path_len=1,
                       local_pref=100, med=100,
                       communities=dict([(c, False) for c in comms]),
                       permitted=True)

    path = PathReq(Protocols.BGP, prefix, ['R2', 'R1'], False)
    reqs = [path]

    # Get SMT Context
    ctx = create_context(reqs, graph, [ann])
    propagation = EBGPPropagation(reqs, graph, ctx)
    propagation.compute_dags()
    propagation.synthesize()

    # SMT Solving
    solver = z3.Solver(ctx=ctx.z3_ctx)
    assert ctx.check(solver) == z3.sat, solver.unsat_core()

    # Update graph with the concrete values after solver
    ConnectedSyn([], graph, full=True).synthesize()
    propagation.update_network_graph()

    gns3 = GNS3Topo(graph=graph, prefix_map=prefix_map)
    gns3.write_configs('%s/ibgp-simple' % export_path)


def linear_ebgp(N, export_path):
    """
    Routers connected in a line and each eBGP pair with it's direct neighbors
    """
    # Topology
    g = get_ebgp_linear_topo(N)
    # Announce locally
    prefix = "Prefix0"
    net = ip_network(u'128.0.0.0/24')
    prefix_map = {prefix: net}
    g.set_loopback_addr('R1', 'lo0', ip_interface("%s/%d" % (net.hosts().next(), net.prefixlen)))
    g.add_bgp_announces('R1', 'lo0')

    # Announcement
    comms = [Community("100:10"), Community("100:20")]
    cs = dict([(c, False) for c in comms])
    # The announcement that will be propagated by R1
    ann = get_announcement(prefix=prefix, peer='R1', comms=cs)

    # Set up route maps
    for i in range(1, N + 1):
        first = 'R%d' % (i - 1) if i > 1 else None
        middle = 'R%d' % i
        last = 'R%d' % (i + 1) if i < N else None
        if last:
            matches = [MatchAsPath(VALUENOTSET)]
            #matches = None
            rline = RouteMapLine(matches, None, VALUENOTSET, 10)
            deny_line = RouteMapLine(None, None, Access.deny, 100)
            rmap = RouteMap('Exp_%s' % last, [rline, deny_line])
            g.add_route_map(middle, rmap)
            g.add_bgp_export_route_map(middle, last, rmap.name)
        if first:
            matches = [MatchAsPath(VALUENOTSET)]
            #matches = None
            rline = RouteMapLine(matches, None, VALUENOTSET, 10)
            deny_line = RouteMapLine(None, None, Access.deny, 100)
            rmap = RouteMap('Imp_%s' % first, [rline, deny_line])
            g.add_route_map(middle, rmap)
            g.add_bgp_import_route_map(middle, first, rmap.name)

    # nx.nx_pydot.write_dot(g, '/tmp/linear.xdot')
    req = PathReq(Protocols.BGP, dst_net='Prefix0', path=['R2', 'R1'], strict=False)

    ctx = create_context([req], g, [ann])

    propagation = EBGPPropagation([req], g, ctx)
    propagation.compute_dags()
    propagation.synthesize()

    solver = z3.Solver(ctx=ctx.z3_ctx)
    ret = ctx.check(solver)
    assert ret == z3.sat, solver.unsat_core()
    propagation.update_network_graph()

    gns3 = GNS3Topo(g, prefix_map)
    gns3.write_configs('%s/linear-ebgp-%d' % (export_path, N))


def test_double_import():
    """Unit test of Route maps"""
    graph = NetworkGraph()
    r1, r2 = 'R1', 'R2'
    graph.add_router(r1)
    graph.add_router(r2)
    graph.add_router_edge(r1, r2)
    graph.add_router_edge(r2, r1)

    # BGP configs
    graph.set_bgp_asnum(r1, 100)
    graph.set_bgp_asnum(r2, 200)
    # Establish peering
    # The actual network interfaces used for peering will be synthesized
    graph.add_bgp_neighbor(r1, r2, router_a_iface=VALUENOTSET, router_b_iface=VALUENOTSET)

    # Some internal network
    net = ip_network(u'128.0.0.0/24')
    prefix = '128_0_0_0'
    prefix_map = {prefix: net}
    lo0 = 'lo0'
    graph.set_loopback_addr(r1, lo0, ip_interface("%s/%d" % (net.hosts().next(), net.prefixlen)))
    # Announce the internal network
    graph.add_bgp_announces(r1, lo0)

    # The communities recognized by us
    comms = [Community("100:10"), Community("100:20")]

    # The announcement that will be propagated by R1
    ann = Announcement(prefix=prefix, peer=r1,
                       origin=BGP_ATTRS_ORIGIN.EBGP,
                       next_hop='R1Hop',
                       as_path=[100], as_path_len=1,
                       local_pref=100, med=100,
                       communities=dict([(c, False) for c in comms]),
                       permitted=True)

    path = PathReq(Protocols.BGP, prefix, ['R2', 'R1'], False)
    reqs = [path]

    ctx = create_context(reqs, graph, [ann], create_as_paths=True)

    from synet.utils.fnfree_policy import SMTRouteMap
    rline1 = RouteMapLine(matches=None, actions=None, access=VALUENOTSET, lineno=10)
    deny_line1 = RouteMapLine(matches=None, actions=None, access=Access.deny, lineno=100)
    rmap1 = RouteMap(name='Rmap1', lines=[rline1, deny_line1])
    rline2 = RouteMapLine(matches=None, actions=None, access=VALUENOTSET, lineno=10)
    deny_line2 = RouteMapLine(matches=None, actions=None, access=Access.deny, lineno=100)
    rmap2 = RouteMap(name='Rmap1', lines=[rline2, deny_line2])
    sym = get_sym([ann], ctx)

    smt1 = SMTRouteMap(rmap1, sym, ctx)
    smt2 = SMTRouteMap(rmap2, smt1.announcements, ctx)
    print "Original permitted", sym.announcements[0].permitted
    print "SMT 1 permitted", smt1.announcements[0].permitted
    print "SMT 2 permitted", smt2.announcements[0].permitted
    ctx.register_constraint(smt1.announcements[0].permitted.var == True)
    ctx.register_constraint(smt2.announcements[0].permitted.var == False)
    solver = z3.Solver(ctx=ctx.z3_ctx)
    ret = ctx.check(solver)
    #print solver.to_smt2()
    assert ret == z3.sat, solver.unsat_core()
    #print solver.model()
    print "Original permitted", sym.announcements[0].permitted
    print "SMT 1 permitted", smt1.announcements[0].permitted
    print "SMT 2 permitted", smt2.announcements[0].permitted


def main():
    parser = argparse.ArgumentParser(description='Example of how to use NetComplete programmatically')
    parser.add_argument('path', type=str, default='./out_configs',
                        help='The directory the configuration is exported to')
    args = parser.parse_args()
    export_path = args.path

    two_ebgp_nodes(export_path)
    two_ebgp_nodes_route_map(export_path)
    two_ibgp_nodes(export_path)
    linear_ebgp(4, export_path)
    test_double_import()


if __name__ == '__main__':
    main()
