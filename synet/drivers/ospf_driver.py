#!/usr/bin/env python

import argparse
import random
import sys
import os

import networkx as nx

from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.common import random_requirement_path
from synet.utils.common import generate_second_path
from synet.utils.topo_gen import gen_grid_topology
from synet.utils.topo_gen import read_topology_zoo_netgraph
from synet.synthesis.ospf_heuristic import OSPFSyn


def main():
    parser = argparse.ArgumentParser(description='Process some integers.')
    parser.add_argument('-f', type=str, default='',
                        help='read topology zoo graphml file')
    parser.add_argument('-s', type=int, default=5, help='grid size')
    parser.add_argument(
        '-r', type=int, default=20,
        help='number of generated random paths as reqs')
    parser.add_argument(
        '-p', type=int, default=1000,
        help='number of generated random paths for each round of synthesis')
    parser.add_argument(
        '-u', type=int, default=0,
        help='number of unsatisfiable requirements,'
             'it is added to the total number of requirements')
    parser.add_argument('--seed', type=int, default=0,
                        help='The seed of the random generator')
    parser.add_argument(
        '--fixed', type=float, default=0,
        help='The percentage of fixed edge costs of the total edges (0 to 1)')

    # Parse command line args
    args = parser.parse_args()
    gsize = args.s
    reqsize = args.r
    pathsize = args.p
    seed = args.seed
    unsatisfiable_reqs = args.u
    topology_file = args.f
    fixed = args.fixed

    # Generate new random number seed if need
    if not seed:
        seed = random.randint(0, sys.maxint)
        print "Generated new seed", seed

    # This random generator MUST be used everywhere!!!!
    ospfRand = random.Random(seed)

    # If zoo topology file is specified, then read it
    # Otherwise generate a grid topo
    if topology_file:
        g = read_topology_zoo_netgraph(topology_file)
        results_name = os.path.basename(topology_file)[:-len('.graphml')]
    else:
        g = gen_grid_topology(gsize, gsize, 0)
        results_name = "grid%x%s" % (gsize, gsize)

    if not topology_file:
        print "Grid size %dx%d" % (gsize, gsize)
    else:
        print "Topology file:", topology_file
    print "Number of nodes:", len(list(g.nodes()))
    print "Number of edges:", len(list(g.edges()))
    print "Percentage of fixed edge costs:", fixed
    print "Number of requirements: %d" % reqsize
    print "Number of paths per iteration %d" % pathsize
    print "Random Seed", seed

    paths = []
    tmp_weight_name = 'tmp-weight'
    print "Generating random paths for requirements"
    for i in range(0, reqsize):
        src, dst = ospfRand.sample(list(g.nodes()), 2)
        assert src != dst
        path = random_requirement_path(g, src, dst, ospfRand, tmp_weight_name)
        paths.append(path)

    if fixed > 0:
        weights = []
        for src, dst in g.edges_iter():
            weights.append((src, dst, g[src][dst][tmp_weight_name]))
        population = int(round(len(weights) * fixed))
        sampled = ospfRand.sample(weights, population)
        for src, dst, w in sampled:
            g[src][dst]['cost'] = w

    cl = nx.DiGraph()
    for n in g.nodes():
        cl.add_node(n)
    for s, d in g.edges():
        cl.add_edge(s, d)

    if unsatisfiable_reqs:
        print "Generating counter paths"
    chosen = []
    for i in range(unsatisfiable_reqs):
        candidate = ospfRand.choice(paths)
        counter_path = None
        while counter_path is None:
            while candidate in chosen:
                candidate = ospfRand.choice(paths)
            counter_path = generate_second_path(g, candidate)
        chosen.append(candidate)
        print "Generating counter path for path", candidate
        paths.append(counter_path)
    unsatisfiable_reqs = len(chosen)
    ospf = OSPFSyn([], g, gen_paths=pathsize)

    for path in paths:
        req = PathReq(Protocols.OSPF, path[-1], path, False)
        ospf.add_path_req(req)

    ospf.synthesize(retries_before_rest=10)


if __name__ == '__main__':
    main()
