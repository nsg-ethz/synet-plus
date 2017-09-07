#!/usr/bin/env python

import argparse
import random
import sys
import time

import networkx as nx
import z3

from synet.synthesis.connected import ConnectedSyn
from synet.synthesis.propagation import EBGPPropagation
from synet.topo.bgp import Access
from synet.topo.bgp import ActionSetCommunity
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList
from synet.topo.bgp import MatchCommunitiesList
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine
from synet.topo.graph import NetworkGraph
from synet.utils.common import Protocols
from synet.utils.common import PathReq
from synet.utils.smt_context import VALUENOTSET
from synet.utils.topo_gen import read_topology_zoo_netgraph

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"

z3.set_option('unsat-core', True)


def add_peers(graph, num_peers, communities, rand, first_asnum=5000, asnum_inc=100):
    """
    Add additional routers as external peers
    :param graph: NetworkGraph
    :param num_peers: number of peers to be added
    :param rand: random.Random
    :param first_asnum: the first AS Num to assign to the peer
    :param asnum_inc: the increment from the previous peer ASNum to the new one
    :return: list of newly added peers, and route maps
    """
    assert isinstance(graph, NetworkGraph)
    routers = list(graph.nodes())
    asnum = first_asnum
    peers = []
    route_maps = []
    for i in range(num_peers):
        node = rand.choice(routers)
        peer = "Peer_%d" % i
        peers.append(peer)
        graph.add_peer(peer)
        graph.set_bgp_asnum(peer, asnum)
        graph.add_peer_edge(node, peer)
        graph.add_peer_edge(peer, node)
        graph.add_bgp_neighbor(node, peer, VALUENOTSET, VALUENOTSET)
        asnum += asnum_inc
        # Don't export
        line1 = RouteMapLine(matches=None, actions=[],
                             access=Access.deny, lineno=10)
        name = "%s_export_to_%s" % (node, peer)
        rmap = RouteMap(name=name, lines=[line1])
        graph.add_route_map(node, rmap)
        graph.add_bgp_export_route_map(node, peer, rmap.name)
        route_maps.append(rmap)
        # Tag Peer
        set_c = ActionSetCommunity([communities[i]])
        line1 = RouteMapLine(matches=None, actions=[set_c],
                             access=Access.permit, lineno=10)
        line2 = RouteMapLine(matches=None, actions=[],
                             access=Access.deny, lineno=500)
        name = "%s_import_from_%s" % (node, peer)
        rmap = RouteMap(name=name, lines=[line1, line2])
        graph.add_route_map(node, rmap)
        graph.add_bgp_import_route_map(node, peer, rmap.name)
        route_maps.append(rmap)
    return peers, route_maps


def assign_setup_bgp(graph, first_asnum, asnum_inc=10):
    """
    Establish BGP connectivity
    Assigns AS Number and establish peering relation
    :param graph: NetworkGraph
    :param first_asnum: the first AS Num to assign to router
    :param asnum_inc:
    :return: None
    """
    assert isinstance(graph, NetworkGraph)
    asnum = first_asnum
    # Assigns AS Number
    for node in sorted(list(graph.routers_iter())):
        graph.set_bgp_asnum(node, asnum)
        asnum += asnum_inc
    for src, dst in graph.edges_iter():
        # Skip non-local routers
        if not graph.is_router(src):
            continue
        if not graph.is_router(dst):
            continue
        # Establish peering
        graph.add_bgp_neighbor(src, dst, VALUENOTSET, VALUENOTSET)


def set_announcements(graph, num_prefixes, communities):
    """
    Set Announcements by external peers
    :param graph: NetworkGraph
    :param num_prefixes: number of prefixes announced by each peer
    :param communities: list of Communities (all set to False)
    :return: None
    """
    assert isinstance(graph, NetworkGraph)
    for peer in graph.peers_iter():
        for i in range(num_prefixes):
            prefix = "Prefix_%s_%d" % (peer.strip('_')[-1], i)
            cs = dict([(c, False) for c in communities])
            ann = Announcement(
                prefix=prefix, peer=peer,
                origin=BGP_ATTRS_ORIGIN.EBGP,
                as_path=[999, i],
                as_path_len=2,
                next_hop='%sHop' % peer,
                local_pref=100,
                communities=cs,
                permitted=True)
            graph.add_bgp_advertise(peer, ann)


def get_shortest_path_reqs(g, peers, communities):
    assert isinstance(g, NetworkGraph)
    reqs = []
    route_maps = []
    for peer in peers:
        for node in g.routers_iter():
            all_short = list(nx.all_shortest_paths(g, peer, node))
            path = all_short[0]
            for ann in g.get_bgp_advertise(peer):
                prefix = ann.prefix
                req = PathReq(Protocols.BGP, prefix, path, False)
                reqs.append(req)
            # Add route maps
            if len(all_short) > 1:
                lines = []
                lineno = 10
                for comm in communities:
                    clist = CommunityList(list_id="A_%s" % comm.name,
                                          access=Access.permit,
                                          communities=[VALUENOTSET])
                    match = MatchCommunitiesList(clist)
                    set_pref = ActionSetLocalPref(VALUENOTSET)
                    line1 = RouteMapLine(matches=[match], actions=[set_pref],
                                         access=Access.permit, lineno=lineno)
                    lineno += 10
                    lines.append(line1)
                lineDeny = RouteMapLine(matches=None, actions=[],
                                        access=Access.deny, lineno=500)
                lines.append(lineDeny)
                router = path[-1]
                neighbor = path[-2]
                name = "%s_import_from_%s" % (router, neighbor)
                rmap = RouteMap(name=name, lines=lines)
                g.add_route_map(router, rmap)
                g.add_bgp_import_route_map(router, neighbor, rmap.name)
                route_maps.append(rmap)
    return reqs, route_maps


def main():
    parser = argparse.ArgumentParser(description='EBGP baseline experiment.')
    parser.add_argument('file', type=str,
                        help='read topology zoo graphml file')
    parser.add_argument('--peers', type=int, default=1,
                        help='Number of peers')
    parser.add_argument('--prefixes', type=int, default=1,
                        help='Number of prefixes per peer')
    parser.add_argument('--comms', type=int, default=1,
                        help='The number of communities')
    parser.add_argument('--seed', type=int, default=0,
                        help='The seed of the random generator')

    args = parser.parse_args()
    topo_file = args.file
    num_peers = args.peers
    num_prefixes = args.prefixes
    num_comms = args.comms
    seed = args.seed
    # Generate new random number seed if need
    if not seed:
        seed = random.randint(0, sys.maxint)
        print "Generated new seed", seed
    rand = random.Random(seed)
    g = read_topology_zoo_netgraph(topo_file)
    print "Num nodes", len(g.nodes())
    print "Num Edges", len(g.edges())
    assign_setup_bgp(g, 100)
    communities = [Community("100:%d" % i) for i in range(num_comms)]
    peers, export_route_maps = add_peers(g, num_peers, communities=communities, rand=rand)
    print "Export route maps", len(export_route_maps), "lines", sum([len(rmap.lines) for rmap in export_route_maps])
    set_announcements(g, num_prefixes, communities)
    reqs, inner_route_maps = get_shortest_path_reqs(g, peers, communities)
    print "Inner route maps", len(inner_route_maps), "lines", sum([len(rmap.lines) for rmap in inner_route_maps])
    print "Connected Synthesizes"
    connected_syn = ConnectedSyn(reqs, g)
    connected_syn.synthesize()
    print "STARTING PROPAGATION"
    start = time.time()
    p = EBGPPropagation(reqs, g)
    end = time.time()
    print "Propagation time", (end - start)
    print "STARTING SYN"
    start = time.time()
    p.synthesize()
    end = time.time()
    print "Synthesize time", (end - start)
    print "ADDING CONSTRAINTS"
    solver = z3.Solver()
    start = time.time()
    p.add_constraints(solver, True)
    end = time.time()
    print "Adding constraints time", (end - start)
    print "SMT SOLVER"
    start = time.time()
    ret = solver.check()
    end = time.time()
    print "SMT Solving time", (end - start)
    assert ret == z3.sat, solver.unsat_core()
    p.set_model(solver.model())
    # for node in g.routers_iter():
    #    box = p.network_graph.node[node]['syn']['box']
    #    print box.get_config()


if __name__ == '__main__':
    main()
