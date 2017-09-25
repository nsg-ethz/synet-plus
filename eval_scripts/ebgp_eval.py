
import argparse
import random
import sys
from functools import partial
from timeit import default_timer as timer

import networkx as nx
from networkx.drawing.nx_agraph import write_dot
import xmltodict
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
from synet.utils.common import ECMPPathsReq
from synet.utils.common import KConnectedPathsReq
from synet.utils.common import PathOrderReq
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.smt_context import VALUENOTSET
from synet.utils.topo_gen import read_topology_zoo_netgraph


def generate_policy(topo, custs, providers, peers):
    out = ''
    out += "define Peer = {%s}\n" % ', '.join(peers)
    out += "define Provider = {%s}\n" % ', '.join(providers)
    out += "define Cust = {%s}\n" % ', '.join(custs)
    out += "\n"
    out += "define NonCust = Peer + Provider\n"
    out += "\n"
    out += "define transit(X,Y) = enter(X+Y) & exit(X+Y)\n"
    out += "\n"
    out += "define notransit = {\n"
    out += "  true => not transit(NonCust, NonCust)\n"
    out += "}\n"
    out += "\n"
    out += "define routing = {\n"
    for index, node in enumerate(sorted(list(topo.local_routers_iter()))):
        out += "  128.0.%d.0/24 => end(%s),\n" % (index + 1, node)
    out += "  true => exit(Cust >> Peer >> Provider)\n"
    out += "}\n"
    out += "define main = routing & notransit\n"
    return out


def read_propane(file):
    doc = {}
    topo = NetworkGraph()
    with open(file) as fd:
        doc = xmltodict.parse(fd.read())
        doc = doc['topology']

    for node in doc['node']:
        internal = node['@internal']
        asn = node['@asn']
        name = node['@name']
        topo.add_router(name)

    for edge in doc['edge']:
        source = edge['@source']
        target = edge['@target']
        topo.add_router_edge(source, target)
        topo.add_router_edge(target, source)
    topo.write_dot("/tmp/p.dot")


def setup_logging():
    import logging
    # create logger
    logger = logging.getLogger('synet')
    logger.setLevel(logging.DEBUG)

    # create console handler and set level to debug
    ch = logging.StreamHandler()
    ch.setLevel(logging.DEBUG)

    # create formatter
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')

    # add formatter to ch
    ch.setFormatter(formatter)

    # add ch to logger
    logger.addHandler(ch)


def assign_ebgp(topo):
    # Assigning eBGP
    asnum = 10
    for node in sorted(topo.local_routers_iter()):
        topo.set_bgp_asnum(node, asnum)
        asnum += 10
    for src, dst in topo.edges():
        if dst not in topo.get_bgp_neighbors(src):
            topo.add_bgp_neighbor(src, dst, VALUENOTSET, VALUENOTSET)


def set_access(line, access):
    line.access = access
    return line

def set_comms(match, comms):
    match.match.communities = comms
    return match

def syn_pref(setpref, pref):
    setpref.value = pref
    return setpref


def gen_simple(topo, ospf_reqs, all_communities):
    assign_ebgp(topo)
    peer_asnum = 10000
    all_reqs = []
    syn_vals = []
    for index, req in enumerate(ospf_reqs):
        egress = req.path[-1]
        peer = "Peer%s_%d" % (egress, index)
        topo.add_peer(peer)
        peer_asnum += 10
        topo.set_bgp_asnum(peer, peer_asnum)
        topo.add_peer_edge(peer, egress)
        topo.add_peer_edge(egress, peer)
        topo.add_bgp_neighbor(peer, egress, VALUENOTSET, VALUENOTSET)

        peer_comm = all_communities[index]
        set_comm = ActionSetCommunity([peer_comm])
        line = RouteMapLine(matches=[], actions=[set_comm], access=VALUENOTSET, lineno=10)
        syn_vals.append(partial(set_access, line=line, access=Access.permit))
        rname = "RMap_%s_from_%s" % (egress, peer)
        rmap = RouteMap(rname, lines=[line])
        topo.add_route_map(egress, rmap)
        topo.add_bgp_import_route_map(egress, peer, rname)

        cs = dict([(c, False) for c in all_communities])
        prefix = 'P_%s' % (peer,)
        ann = Announcement(
            prefix=prefix,
            peer=peer,
            origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2], as_path_len=2,
            next_hop='%sHop' % peer, local_pref=100,
            communities=cs, permitted=True)
        topo.add_bgp_advertise(peer, ann)
        bgp_req = PathReq(Protocols.BGP, prefix, req.path + [peer], False)
        all_reqs.append(bgp_req)
        for node in req.path:
            for _, neighbor in topo.out_edges(node):
                if neighbor in req.path:
                    continue
                clist = CommunityList("t_%s" % neighbor, Access.permit, [VALUENOTSET])
                match = MatchCommunitiesList(clist)
                syn_vals.append(partial(set_comms, match=match, comms=[peer_comm]))
                line = RouteMapLine(matches=[match], actions=[], access=VALUENOTSET, lineno=10)
                syn_vals.append(partial(set_access, line=line, access=Access.deny))
                rname = "RMap_%s_from_%s" % (neighbor, node)
                rmap = RouteMap(rname, lines=[line])
                topo.add_route_map(neighbor, rmap)
                topo.add_bgp_import_route_map(neighbor, node, rname)
    return all_reqs, syn_vals


def gen_order(topo, ospf_reqs, all_communities):
    assign_ebgp(topo)
    peer_asnum = 10000
    all_reqs = []

    syn_vals = []
    deny_map = {}
    pref_map = {}
    route_map_lines = {}
    export_route_maps = {}
    comm_subg = {}
    for index, req in enumerate(ospf_reqs):
        subg = nx.DiGraph()
        egress = req.paths[0].path[-1]
        peer = "Peer%s_%d" % (egress, index)
        topo.add_peer(peer)
        peer_asnum += 10
        topo.set_bgp_asnum(peer, peer_asnum)
        topo.add_peer_edge(peer, egress)
        topo.add_peer_edge(egress, peer)
        topo.add_bgp_neighbor(peer, egress, VALUENOTSET, VALUENOTSET)

        peer_comm = all_communities[index]
        comm_subg[peer_comm] = nx.DiGraph()
        subg.add_edge(egress, peer, rank=0)
        comm_subg[peer_comm].add_edge(egress, peer, rank=0)
        set_comm = ActionSetCommunity([peer_comm])
        set_pref = ActionSetLocalPref(VALUENOTSET)
        #syn_vals.append(partial(syn_pref, set_pref, VALUENOTSET))
        line = RouteMapLine(matches=[], actions=[set_comm, set_pref], access=VALUENOTSET, lineno=10)
        syn_vals.append(partial(set_access, line=line, access=Access.permit))
        if egress not in route_map_lines:
            route_map_lines[egress] = {}
        if peer not in route_map_lines[egress]:
            route_map_lines[egress][peer] = []
        route_map_lines[egress][peer] = [line] + route_map_lines[egress][peer]
        cs = dict([(c, False) for c in all_communities])
        prefix = 'P_%s' % (peer,)
        ann = Announcement(
            prefix=prefix,
            peer=peer,
            origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2], as_path_len=2,
            next_hop='%sHop' % peer, local_pref=100,
            communities=cs, permitted=True)
        topo.add_bgp_advertise(peer, ann)
        sub = []
        covered_nodes = [peer]
        for rank, path in enumerate(req.paths):
            covered_nodes.extend(path.path)
            for src, dst in zip(path.path[0::1], path.path[1::1]):
                subg.add_edge(src, dst, rank=rank)
                comm_subg[peer_comm].add_edge(src, dst, rank=rank)
            sub.append(PathReq(Protocols.BGP, prefix, path.path + [peer], False))
        bgp_req = PathOrderReq(Protocols.BGP, prefix, sub, False)
        all_reqs.append(bgp_req)
        write_dot(subg, '/tmp/subg.dot')

    for node in topo:
        for from_node, _ in topo.in_edges_iter(node):
            if topo.is_peer(node):
                continue
            lineno = 10
            lines = []
            for comm in all_communities:
                if comm_subg[comm].has_node(node) and comm_subg[comm].out_degree(node) > 1:
                    clist = CommunityList("t_%s_import_%s_%s" % (node, from_node, comm), Access.permit, [VALUENOTSET])
                    match = MatchCommunitiesList(clist)
                    syn_vals.append(partial(set_comms, match=match, comms=[peer_comm]))
                    set_pref = ActionSetLocalPref(VALUENOTSET)
                    if comm_subg[comm].has_edge(node, from_node):
                        syn_vals.append(partial(syn_pref, set_pref, 200 - comm_subg[comm][node][from_node]['rank']))
                    else:
                        syn_vals.append(partial(syn_pref, set_pref, 100))
                    line = RouteMapLine(matches=[match], actions=[set_pref], access=VALUENOTSET, lineno=lineno)
                    lineno += 10
                    syn_vals.append(partial(set_access, line=line, access=Access.permit))
                    lines.append(line)
                if node not in route_map_lines:
                    route_map_lines[node] = {}
                if from_node not in route_map_lines[node]:
                    route_map_lines[node][from_node] = []
                route_map_lines[node][from_node].extend(lines)

        for _, to_node in topo.out_edges_iter(node):
            if topo.is_peer(node):
                continue
            lineno = 10
            lines = []
            for comm in all_communities:
                if not comm_subg[comm].has_node(node):
                    continue
                clist = CommunityList("t_%s_export_%s_%s" % (node, to_node, comm), Access.permit, [VALUENOTSET])
                match = MatchCommunitiesList(clist)
                syn_vals.append(partial(set_comms, match=match, comms=[comm]))
                line = RouteMapLine(matches=[match], actions=[], access=VALUENOTSET, lineno=lineno)
                lineno += 10
                if comm_subg[comm].has_edge(to_node, node):
                    syn_vals.append(partial(set_access, line=line, access=Access.permit))
                else:
                    syn_vals.append(partial(set_access, line=line, access=Access.deny))
                lines.append(line)
            if node not in export_route_maps:
                export_route_maps[node] = {}
            if from_node not in export_route_maps[node]:
                export_route_maps[node][to_node] = []
                export_route_maps[node][to_node].extend(lines)

    for node in route_map_lines:
        for from_node, lines in route_map_lines[node].iteritems():
            if not lines:
                continue
            rname = "RMap_%s_from_%s" % (node, from_node)
            #if rname == 'RMap_Lille_from_London':
            #    assert False, lines
            rmap = RouteMap(rname, lines=lines)
            topo.add_route_map(node, rmap)
            topo.add_bgp_import_route_map(node, from_node, rname)
    for node in export_route_maps:
        for to_node, lines in export_route_maps[node].iteritems():
            if not lines:
                continue
            rname = "RMap_%s_to_%s" % (node, to_node)
            rmap = RouteMap(rname, lines=lines)
            topo.add_route_map(node, rmap)
            topo.add_bgp_export_route_map(node, to_node, rname)
    return all_reqs, syn_vals


def gen_kconnected(topo, ospf_reqs, all_communities):
    assign_ebgp(topo)
    peer_asnum = 10000
    all_reqs = []
    subg = nx.DiGraph()
    for index, req in enumerate(ospf_reqs):
        egress = req.paths[0].path[-1]
        peer = "Peer%s_%d" % (egress, index)
        topo.add_peer(peer)
        peer_asnum += 10
        topo.set_bgp_asnum(peer, peer_asnum)
        topo.add_peer_edge(peer, egress)
        topo.add_peer_edge(egress, peer)
        topo.add_bgp_neighbor(peer, egress, VALUENOTSET, VALUENOTSET)

        set_comm = ActionSetCommunity([all_communities[index]])
        line = RouteMapLine(matches=[], actions=[set_comm], access=VALUENOTSET, lineno=10)
        rname = "RMap_%s_from_%s" % (egress, peer)
        rmap = RouteMap(rname, lines=[line])
        topo.add_route_map(egress, rmap)
        topo.add_bgp_import_route_map(egress, peer, rname)

        cs = dict([(c, False) for c in all_communities])
        prefix = 'P_%s' % (peer,)
        ann = Announcement(
            prefix=prefix,
            peer=peer,
            origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2], as_path_len=2,
            next_hop='%sHop' % peer, local_pref=100,
            communities=cs, permitted=True)
        topo.add_bgp_advertise(peer, ann)
        sub = []
        covered_nodes = []
        for path in req.paths:
            covered_nodes.extend(path.path)
            for src, dst in zip(path.path[0::1], path.path[1::1]):
                subg.add_edge(src, dst)
            sub.append(PathReq(Protocols.BGP, prefix, path.path + [peer], False))
        bgp_req = KConnectedPathsReq(Protocols.BGP, prefix, sub, False)
        all_reqs.append(bgp_req)
        for node in covered_nodes:
            for _, neighbor in topo.out_edges(node):
                if neighbor in covered_nodes:
                    continue
                clist = CommunityList("t", Access.permit, [VALUENOTSET])
                match = MatchCommunitiesList(clist)
                line = RouteMapLine(matches=[match], actions=[], access=VALUENOTSET, lineno=10)
                rname = "RMap_%s_from_%s" % (neighbor, node)
                rmap = RouteMap(rname, lines=[line])
                topo.add_route_map(neighbor, rmap)
                topo.add_bgp_import_route_map(neighbor, node, rname)
        for node in subg.nodes():
            if subg.out_degree(node) > 1:
                for _, neighbor in subg.out_edges(node):
                    clist = CommunityList("t", Access.permit, [VALUENOTSET])
                    match = MatchCommunitiesList(clist)
                    set_pref = ActionSetLocalPref(VALUENOTSET)
                    line = RouteMapLine(matches=[match], actions=[set_pref], access=VALUENOTSET, lineno=10)
                    rname = "RMap_%s_from_%s" % (neighbor, node)
                    print "ADD IMPORT", rname
                    rmap = RouteMap(rname, lines=[line])
                    topo.add_route_map(neighbor, rmap)
                    topo.add_bgp_import_route_map(neighbor, node, rname)
    return all_reqs


def gen_ecmp(topo, ospf_reqs, all_communities):
    # Assigning iBGP
    asnum = 10
    for node in sorted(topo.local_routers_iter()):
        topo.set_bgp_asnum(node, asnum)
    peer_asnum = 10000
    all_reqs = []

    for index, req in enumerate(ospf_reqs):
        subg = nx.DiGraph()
        egress = req.paths[0].path[-1]
        peer = "Peer%s_%d" % (egress, index)
        subg.add_edge(egress, peer)
        topo.add_peer(peer)
        peer_asnum += 10
        topo.set_bgp_asnum(peer, peer_asnum)
        topo.add_peer_edge(peer, egress)
        topo.add_peer_edge(egress, peer)
        for lnode in topo.local_routers_iter():
            topo.add_bgp_neighbor(peer, lnode, VALUENOTSET, VALUENOTSET)

        set_comm = ActionSetCommunity([all_communities[index]])
        line = RouteMapLine(matches=[], actions=[set_comm], access=VALUENOTSET, lineno=10)
        rname = "RMap_%s_from_%s" % (egress, peer)
        rmap = RouteMap(rname, lines=[line])
        topo.add_route_map(egress, rmap)
        topo.add_bgp_import_route_map(egress, peer, rname)

        cs = dict([(c, False) for c in all_communities])
        prefix = 'P_%s' % (peer,)
        ann = Announcement(
            prefix=prefix,
            peer=peer,
            origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2], as_path_len=2,
            next_hop='%sHop' % peer, local_pref=100,
            communities=cs, permitted=True)
        topo.add_bgp_advertise(peer, ann)
        sub = []
        covered_nodes = []
        for path in req.paths:
            covered_nodes.extend(path.path)
            for src, dst in zip(path.path[0::1], path.path[1::1]):
                subg.add_edge(src, dst)
            sub.append(PathReq(Protocols.BGP, prefix, path.path + [peer], False))
        bgp_req = ECMPPathsReq(Protocols.BGP, prefix, sub, False)
        all_reqs.append(bgp_req)
        source = bgp_req.paths[0].path[0]
        for node in subg.nodes():
            if node in [source, peer]:
                continue
            all_paths = list(nx.all_shortest_paths(subg, node, peer))
            bgp_req2 = ECMPPathsReq(Protocols.BGP, prefix, [
                PathReq(Protocols.BGP, prefix, path, False) for path in all_paths
            ], False)
            all_reqs.append(bgp_req2)
        #for node in covered_nodes:
        #    for _, neighbor in topo.out_edges(node):
        #        if neighbor in covered_nodes:
        #            continue
        #        clist = CommunityList("t", Access.permit, [VALUENOTSET])
        #        match = MatchCommunitiesList(clist)
        #        line = RouteMapLine(matches=[match], actions=[], access=VALUENOTSET, lineno=10)
        #        rname = "RMap_%s_from_%s" % (neighbor, node)
        #        rmap = RouteMap(rname, lines=[line])
        #        topo.add_route_map(neighbor, rmap)
        #        topo.add_bgp_import_route_map(neighbor, node, rname)
        #for node in subg.nodes():
        #    if subg.out_degree(node) > 1:
        #        for _, neighbor in subg.out_edges(node):
        #            clist = CommunityList("t", Access.permit, [VALUENOTSET])
        #            match = MatchCommunitiesList(clist)
        #            set_pref = ActionSetLocalPref(VALUENOTSET)
        #            line = RouteMapLine(matches=[match], actions=[set_pref], access=VALUENOTSET, lineno=10)
        #            rname = "RMap_%s_from_%s" % (neighbor, node)
        #            print "ADD IMPORT", rname
        #            rmap = RouteMap(rname, lines=[line])
        #            topo.add_route_map(neighbor, rmap)
        #            topo.add_bgp_import_route_map(neighbor, node, rname)
    return all_reqs


def main():
    #setup_logging()
    parser = argparse.ArgumentParser(description='EBGP baseline experiment.')
    parser.add_argument('file', type=str, help='graphml topology')
    parser.add_argument('--reqsize', type=int, required=True,
                        help='Number of peer of each type')
    parser.add_argument('--type', required=True, type=str,
                        choices=['simple', 'ecmp', 'kconnected', 'order'],
                        help='simple, ecmp, kconnected, ordered')
    parser.add_argument('--values', type=str, required=True, default=None,
                        help='Input python file for the given topology (generated by OSPF generator)')
    parser.add_argument(
        '--fixed', type=float, default=1,
        help='The percentage of fixed holes (0 to 1)')
    parser.add_argument('--seed', type=int, default=0,
                        help='The seed of the random generator')

    args = parser.parse_args()
    topo_file = args.file
    req_type = args.type
    reqsize = args.reqsize
    fixed = args.fixed
    reqs_file = args.values
    seed = args.seed
    assert 0 <= fixed <= 1.0

    if not seed:
        seed = random.randint(0, sys.maxint)
        print "Generated new seed", seed
        # This random generator MUST be used everywhere!!!!
    rand = random.Random(seed)


    with open(reqs_file, 'r') as fd:
        exec (fd.read())


    topo = read_topology_zoo_netgraph(topo_file)
    reqsize = reqsize

    k = 2
    if req_type == 'simple':
        ospf_reqs = eval('reqs_simple_%d' % reqsize)
        all_communities = [Community("100:%d" % i) for i in range(len(ospf_reqs))]
        all_reqs, syn_vals = gen_simple(topo, ospf_reqs, all_communities)
    elif req_type == 'ecmp':
        ospf_reqs = eval('reqs_ecmp_%d_%d' % (reqsize, k))
        all_communities = [Community("100:%d" % i) for i in range(len(ospf_reqs))]
        all_reqs, syn_vals = gen_ecmp(topo, ospf_reqs, all_communities)
    elif req_type == 'kconnected':
        ospf_reqs = eval('reqs_kconnected_%d_%d' % (reqsize, k))
        all_communities = [Community("100:%d" % i) for i in range(len(ospf_reqs))]
        #all_reqs, syn_vals = gen(topo, ospf_reqs, all_communities)
        raise NotImplementedError()
    elif req_type == 'order':
        ospf_reqs = eval('reqs_order_%d_%d' % (reqsize, k))
        all_communities = [Community("100:%d" % i) for i in range(len(ospf_reqs))]
        all_reqs, syn_vals = gen_order(topo, ospf_reqs, all_communities)
    else:
        raise ValueError("Unknow req type %s", req_type)

    if fixed == 1.0:
        sample = len(syn_vals)
    else:
        sample = int(round(len(syn_vals) * fixed))
    sampled = rand.sample(syn_vals, sample)
    for f in sampled:
        f()

    #ospf_reqs = eval('reqs_simple_%d' % reqsize)
    #ospf_reqs = eval('reqs_order_%d_2' % reqsize)
    #ospf_reqs = eval('reqs_kconnected_%d_2' % reqsize)
    #ospf_reqs = eval('reqs_ecmp_%d_2' % reqsize)
    #all_communities = [Community("100:%d" % i) for i in range(len(ospf_reqs))]

    #all_reqs = gen_simple(topo, ospf_reqs, all_communities)
    #all_reqs = gen_order(topo, ospf_reqs, all_communities)
    #all_reqs = gen_kconnected(topo, ospf_reqs, all_communities)
    #all_reqs = gen_ecmp(topo, ospf_reqs, all_communities)

    conn = ConnectedSyn([], topo, full=True)
    conn.synthesize()

    begin = timer()
    t1 = timer()
    p = EBGPPropagation(all_reqs, topo, allow_igp=False)
    t2 = timer()
    prep = t2 - t1
    t1 = timer()
    p.synthesize()
    t2 = timer()
    bgp_syn = t2 -t1
    t1 = timer()
    solver = z3.Solver()
    p.add_constraints(solver)
    #print solver.to_smt2()
    ret = solver.check()
    t2 = timer()
    z3_syn = t2 - t1
    end = timer()
    assert ret == z3.sat, solver.unsat_core()

    print "Propagation Synthesis Time:", prep
    print "BGP partial eval Time:", bgp_syn
    print "Z3 Synthesis Time:", z3_syn
    print "TOTAL SYN TIME:", end - begin
    p.set_model(solver.model())
    p.update_network_graph()


if __name__ == '__main__':
    main()