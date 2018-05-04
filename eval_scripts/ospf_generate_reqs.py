#!/usr/bin/env python
import argparse
import random
import sys
import os

import numpy

import networkx as nx

from synet.utils.common import PathReq
from synet.utils.common import ECMPPathsReq
from synet.utils.common import PathOrderReq
from synet.utils.common import Protocols
from synet.utils.common import KConnectedPathsReq
from synet.utils.topo_gen import read_topology_zoo_netgraph
from synet.utils.smt_context import VALUENOTSET
from synet.synthesis.ospf_heuristic import OSPFSyn
from synet.synthesis.connected import ConnectedSyn


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


def set_levels(graph, node, level):
    """
    Number levels in the tree
    g.node[node]['level'] = level
    This function is called recurivesly on the children with level +1
    Return the max level reached
    """
    graph.node[node]['level'] = level
    rets = []
    for _, neighbor in graph.out_edges(node):
        rets.append(set_levels(graph, neighbor, level + 1))
    if graph.out_degree(node) == 0:
        rets = [level]
    return max(rets)


def get_different_paths(g, source, min_disjoint, rand):
    # First get a BFS Tree
    stree = nx.bfs_tree(g, source)
    max_level = set_levels(stree, source, 0)

    # Then connect all nodes in the BFS Tree to all nodes
    # the on a level lower than itself (if the edge exists on the original graph)
    for slevel in range(0, max_level):
        snodes = [node for
                  node in stree.nodes()
                  if stree.node[node]['level'] == slevel]
        for dlevel in range(slevel + 1, max_level + 1):
            dnodes = [node for
                      node in
                      stree.nodes()
                      if stree.node[node]['level'] == dlevel]
            for src in snodes:
                for dst in dnodes:
                    if g.has_edge(src, dst):
                        stree.add_edge(src, dst)

    # Connect leave nodes to each other if they don't create cycles
    leaves = [node for node in stree.nodes() if stree.out_degree(node) == 0]
    while len(leaves) > 0:
        node = rand.choice(leaves)
        for neighbor, _ in g.in_edges(node):
            if not stree.has_edge(node, neighbor):
                stree.add_edge(neighbor, node)
        # New leaves
        new_leaves = [node for node in stree.nodes() if stree.out_degree(node) == 1]
        if set(new_leaves) == set(leaves):
            # We hit a stable point and we cannot connect new leaves
            # Without creating cycles
            break
        else:
            leaves = new_leaves

    all_paths = []
    for node in g.nodes():
        if node == source:
            continue
        paths = list(nx.all_simple_paths(stree, source, node))
        unique = []
        for path in paths:
            if path not in unique:
                unique.append(path)
        if len(paths) >= min_disjoint:
            all_paths.append(paths)
    return all_paths


def get_reqs(graph, reqsize, k, rand):
    paths = []
    nodes = list(graph.nodes())
    rand.shuffle(nodes)
    for source in nodes:
        paths = get_different_paths(graph, source, k, rand)
        if len(paths) < reqsize:
            break
    selected = rand.sample(paths, min(reqsize, len(paths)))
    reqs = {}
    for lpaths in selected:
        edges = []
        for path in lpaths:
            for pair in zip(path[0::1], path[1::1]):
                edges.append(pair)
        pmap = {}
        for pair in edges:
            if pair in pmap:
                continue
            pmap[pair] = float(edges.count(pair)) / len(edges)
        path_prop = []
        for path in lpaths:
            curr_prop = 0.0
            for pair in zip(path[0::1], path[1::1]):
                curr_prop += pmap[pair]
            path_prop.append(curr_prop / len(lpaths))
        diff = (1.0 - sum(path_prop)) / len(path_prop)
        path_prop = [p + diff for p in path_prop]
        sindex = list(numpy.random.choice([i for i in range(len(lpaths))], size=k, replace=False, p=path_prop))
        reqs[(lpaths[0][0], lpaths[0][-1])] = [lpaths[i] for i in sindex]
    return reqs


def generate_simple_reqs(topo, reqsize, rand):
    """Generate reqsize of PathReq"""
    paths = get_reqs(graph=topo, reqsize=reqsize, k=1, rand=rand)
    reqs = []
    for plist in paths.values():
        assert len(plist) >= 1
        path = plist[0]
        req = PathReq(Protocols.OSPF, path[-1], path, False)
        reqs.append(req)
    return reqs


def generate_ecmp_reqs(topo, reqsize, ecmp, rand):
    """Generate reqsize of ECMPPathsReq each has ecmp paths"""
    paths = get_reqs(graph=topo, reqsize=reqsize, k=ecmp, rand=rand)
    reqs = []
    for plist in paths.values():
        assert len(plist) >= ecmp
        req = ECMPPathsReq(Protocols.OSPF, plist[0][-1],
                         [PathReq(Protocols.OSPF, path[-1], path, False)
                          for path in plist[:ecmp]], False)
        reqs.append(req)
    return reqs


def generate_ordered_reqs(topo, reqsize, ordered, rand):
    """Generate reqsize of PathOrderReq each has ordered paths"""
    graph = nx.DiGraph()
    for src, dst in topo.edges():
        graph.add_edge(src, dst)

    computed_paths = {}
    tmp_cost = 'tmp-cost'
    for src, dst in graph.edges():
        graph[src][dst][tmp_cost] = rand.randint(1, sys.maxint)

    for src in graph.nodes():
        for dst in graph.nodes():
            if src == dst:
                continue
            if (src, dst) not in computed_paths:
                shortest = nx.shortest_path(graph, src, dst, weight=tmp_cost)
                computed_paths[(src, dst)] = [shortest]

    edges = list(graph.edges())
    for src, dst in edges:
        cost = graph[src][dst][tmp_cost]
        graph.remove_edge(src, dst)
        if nx.has_path(graph, src, dst):
            shortest = nx.shortest_path(graph, src, dst, weight=tmp_cost)
            if shortest not in computed_paths[(src, dst)]:
                computed_paths[(src, dst)].append(shortest)
        graph.add_edge(src, dst, **{tmp_cost: cost})

    valid = []
    for (src, dst) in computed_paths:
        k = len(computed_paths[(src, dst)])
        if k == ordered:
            valid.append(computed_paths[(src, dst)])

    if len(valid) >= reqsize:
        sampled = random.sample(valid, reqsize)
        reqs = []
        for plist in sampled:
            req = PathOrderReq(Protocols.OSPF, plist[0][-1],
                               [PathReq(Protocols.OSPF, path[-1], path, False)
                                for path in plist], False)
            reqs.append(req)
        return reqs
    else:
        print "Regenerating random ordered paths"
        return generate_ordered_reqs(topo, reqsize, ordered, rand)


def get_simple_reqs(topo, reqsize, rand):
    """Get simple reqs to be written to out file"""
    out_file = ""
    generated = False
    while not generated:
        # All OSPF Costs are initially empty
        for src, dst in topo.edges():
            if not topo.is_local_router_edge(src, dst):
                continue
            topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
        print "X" * 40
        print "Generating Simple for reqsize=%d" % (reqsize,)
        reqs = generate_simple_reqs(topo, reqsize, rand)
        print "Done Generating Simple"
        ospf = OSPFSyn(topo, gen_paths=100, random_obj=rand)
        for req in reqs:
            ospf.add_req(req)
        ret = ospf.synthesize()
        if ospf.removed_reqs or not ret:
            print "Generated Simple Reqs are unsatifiable for reqsize", reqsize, "Trying again"
            continue
        generated = True
        ospf.update_network_graph()
        req_name = "reqs_simple_%d" % reqsize
        out_file += "%s = [\n" % (req_name)
        for req in reqs:
            out_file += "    %s,\n" % repr(req)
        out_file += "]\n\n"
        vals_name = "edges_cost_simple_%d" % reqsize
        out_file += "%s = [\n" % vals_name
        for src, dst in topo.edges():
            out_file += '    ("%s", "%s", %d),\n' % (
                src, dst, topo.get_edge_ospf_cost(src, dst))
        out_file += "]\n\n"
    out_file += "#" * 20
    out_file += "\n\n"
    return out_file, reqs, req_name, vals_name


def get_ecmp_reqs(topo, reqsize, ecmp, rand):
    out_file = ""
    generated = False
    while not generated:
        # All OSPF Costs are intially empty
        for src, dst in topo.edges():
            if not topo.is_local_router_edge(src, dst):
                continue
            topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
        print "X" * 40
        print "Generating ECMP for reqsize=%d, ecmp=%d" % (reqsize, ecmp)
        reqs = generate_ecmp_reqs(topo, reqsize, ecmp, rand)
        print "Done Generating ECMP"
        ospf = OSPFSyn(topo, gen_paths=100, random_obj=rand)
        for req in reqs:
            ospf.add_req(req)
        ret = ospf.synthesize()
        if ospf.removed_reqs or not ret:
            print "Generated ECMP Reqs are unsatifiable for reqsize", reqsize, "Trying again"
            continue
        generated = True

        ospf.update_network_graph()
        req_name = "reqs_ecmp_%d_%d" % (reqsize, ecmp)

        out_file += "%s = [\n" % (req_name)
        for req in reqs:
            out_file += "    %s,\n" % repr(req)
        out_file += "]\n\n"
        vals_name = "edges_cost_ecmp_%d_%d" % (reqsize, ecmp)
        out_file += "%s = [\n" % vals_name
        for src, dst in topo.edges():
            out_file += '    ("%s", "%s", %d),\n' % (
                src, dst, topo.get_edge_ospf_cost(src, dst))
        out_file += "]\n\n"
    return out_file, reqs, req_name, vals_name


def get_kconnected(topo, ecmp_reqs, reqsize, k, rand):
    out_file = ""
    print "X" * 40
    print "Generating KConneced for reqsize=%d, k=%d" % (reqsize, k)
    for src, dst in topo.edges():
        if not topo.is_local_router_edge(src, dst):
            continue
        topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
    kreqs = []
    for req in ecmp_reqs:
        kreqs.append(KConnectedPathsReq(req.protocol, req.dst_net, req.paths, False))

    ospf2 = OSPFSyn(topo, gen_paths=100, random_obj=rand)
    for req in kreqs:
        ospf2.add_req(req)
    ospf2.synthesize()
    assert not ospf2.removed_reqs
    ospf2.update_network_graph()
    req_name = "reqs_kconnected_%d_%d" % (reqsize, k)
    out_file += "%s = [\n" % (req_name)
    for req in kreqs:
        out_file += "    %s,\n" % repr(req)
    out_file += "]\n\n"
    vals_name = "edges_cost_kconnected_%d_%d" % (reqsize, k)
    out_file += "%s = [\n" % vals_name
    for src, dst in topo.edges():
        out_file += '    ("%s", "%s", %d),\n' % (
            src, dst, topo.get_edge_ospf_cost(src, dst))
    out_file += "]\n\n"
    return out_file, kreqs, req_name, vals_name


def get_path_order(topo, reqsize, pathorder, rand):
    out_file = ""
    generated = False
    while not generated:
        # All OSPF Costs are intially empty
        for src, dst in topo.edges():
            if not topo.is_local_router_edge(src, dst):
                continue
            topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
        print "X" * 40
        print "Generating PathOrder for reqsize=%d, ordered paths=%d" % (reqsize, pathorder)
        reqs = generate_ordered_reqs(topo, reqsize, pathorder, rand)
        print "Done Generating PathOrdered"

        ospf = OSPFSyn(topo, gen_paths=100, random_obj=rand)
        for req in reqs:
            print req
            ospf.add_req(req)

        ret = ospf.synthesize()
        if ospf.removed_reqs or not ret:
            print "Generated Ordered Reqs are unsatifiable for reqsize", reqsize, "Trying again"
            continue
        generated = True
        ospf.update_network_graph()
        req_name = "reqs_order_%d_%d" % (reqsize, pathorder)
        out_file += "%s = [\n" % (req_name)
        for req in reqs:
            out_file += "    %s,\n" % repr(req)
        out_file += "]\n\n"
        vals_name = "edges_cost_order_%d_%d" % (reqsize, pathorder)
        out_file += "%s = [\n" % vals_name
        for src, dst in topo.edges():
            out_file += '    ("%s", "%s", %d),\n' % (
                src, dst, topo.get_edge_ospf_cost(src, dst))
        out_file += "]\n\n"
    return out_file, reqs, req_name, vals_name


def main():
    parser = argparse.ArgumentParser(
        description='Generate OSPF Requiremetns for a given topology.')
    parser.add_argument('-f', type=str, required=True, default=None,
                        help='read topology zoo graphml file')
    parser.add_argument('--seed', type=int, default=0,
                        help='The seed of the random generator')

    args = parser.parse_args()
    topology_file = args.f
    seed = args.seed

    assert topology_file
    print "Y" * 50
    print "Generating reqs for:", topology_file
    print "Y" * 50
    if not seed:
        seed = random.randint(0, 2**32 - 1)
        print "Generated new seed", seed

    print "Using SEED:", seed

    out_file = """
from synet.utils.common import PathReq
from synet.utils.common import ECMPPathsReq
from synet.utils.common import PathOrderReq
from synet.utils.common import Protocols
from synet.utils.common import KConnectedPathsReq\n
"""
    out_file += "topology_file = '%s'\n" % topology_file
    out_file += "seed = %d\n" % seed

    rand = random.Random(seed)
    numpy.random.seed(seed)

    topo = read_topology_zoo_netgraph(topology_file)

    # Synthesize Connected
    conn_syn = ConnectedSyn([], topo, full=True)
    conn_syn.synthesize()
    # All routers are OSPF Enabled
    for node in topo.local_routers_iter():
        topo.enable_ospf(node, 100)

    simple_reqs = []
    simple_vals = []
    ecmp_reqs = []
    ecmp_vals = []
    kconnected_reqs = []
    kconnected_vals = []
    order_reqs = []
    order_vals = []
    for reqsize in [1, 2, 4, 8, 16]:
        s_out, s_reqs, s_req_name, s_vals_name = get_simple_reqs(
            topo, reqsize, rand)
        out_file += s_out
        simple_reqs.append(s_req_name)
        simple_vals.append(s_vals_name)
        for ecmp in [2]:
            e_out, e_reqs, e_req_name, e_vals_name = get_ecmp_reqs(
                topo, reqsize, ecmp, rand)
            out_file += e_out
            ecmp_reqs.append(e_req_name)
            ecmp_vals.append(e_vals_name)
            # We can use the ECMP to generate kconnected
            print "ECMP reqs", e_reqs
            k_out, k_reqs, k_req_name, k_vals_name = get_kconnected(
                topo, e_reqs, reqsize, ecmp, rand)
            out_file += k_out
            print "APPENDING", k_req_name
            kconnected_reqs.append(k_req_name)
            kconnected_vals.append(k_vals_name)
        for pathorder in [2]:
            o_out, o_reqs, o_req_name, o_vals_name = get_path_order(
                topo, reqsize, pathorder, rand)
            out_file += o_out
            order_reqs.append(o_req_name)
            order_vals.append(o_vals_name)
    out_file += "#" * 20
    out_file += "\n\n"
    out_file += "reqs_simple = [%s]\n\n" % ",".join(simple_reqs)
    out_file += "reqs_simple_vals = [%s]\n\n" % ",".join(simple_vals)
    out_file += "#" * 20
    out_file += "\n\n"
    out_file += "reqs_ecmp = [%s]\n\n" % ",".join(ecmp_reqs)
    out_file += "reqs_ecmp_vals = [%s]\n\n" % ",".join(ecmp_vals)
    out_file += "#" * 20
    out_file += "\n\n"

    out_file += "reqs_kconnected = [%s]\n\n" % ",".join(kconnected_reqs)
    out_file += "reqs_kconnected_vals = [%s]\n\n" % ",".join(kconnected_vals)
    out_file += "#" * 20
    out_file += "\n\n"
    out_file += "reqs_order = [%s]\n\n" % ", ".join(order_reqs)
    out_file += "reqs_order_vals = [%s]\n\n" % ", ".join(order_vals)
    out_file += "#" * 20
    out_file += "\n\n"

    dirname = os.path.dirname(topology_file)
    topo_name = os.path.basename(topology_file).split('.graphml')[0]
    out_name = "%s_ospf_reqs.py" % topo_name
    out_path = os.path.join(dirname, out_name)
    with open(out_path, 'w') as file:
        print "Writing to", out_path
        file.write(out_file)


if __name__ == '__main__':
    main()
