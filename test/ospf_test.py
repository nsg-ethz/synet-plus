#!/usr/bin/env python

import sys
sys.path = ['/usr/local/lib/python2.7/site-packages/'] + sys.path


import argparse
import random
import networkx as nx
from timeit import default_timer as timer
import sys
import os

from synet.utils.common import PathReq
from synet.utils.common import PathProtocols
from synet.utils.topo_gen import gen_grid_topo_no_iface
from synet.utils.topo_gen import read_topology_zoo
from synet.synthesis.ospf import OSPFSyn


def time_exploring_paths(name, g, src, dst):
    """Time exploring all paths"""
    deltas = []
    for i in range(5):
        start = timer()
        tmp = [p for p in nx.all_simple_paths(g, src, dst)]
        end = timer()
        deltas.append(end - start)
    return deltas, tmp


def random_requirement_path(G, source, target, ospfRand, fixed_percentage = 0):
    """
    Generate path requirements with a guaranteed solution

    ospfRand: is an instance of random.Random
    fixed_percentage: the percentage of edges that the cost will be fixed
                i.e. as an attribute called 'cost', the SMT has to read it
    """
    assert fixed_percentage <= 1 and fixed_percentage >= 0
    max_size = 10000
    weights = []
    # Assign weights
    for src, dst in G.edges():
        tmpname = 'temp-weight'
        if tmpname not in G[src][dst]:
            w = ospfRand.randint(1, max_size)
            G[src][dst][tmpname] = w
        weights.append((src, dst, G[src][dst][tmpname]))
    # Fixing certain percentage
    if fixed_percentage != 0:
        size = int(round(len(weights) * fixed_percentage))
        sampled = ospfRand.sample(weights, size)
        for src, dst, w in sampled:
            G[src][dst]['cost'] = w
    return nx.shortest_path(G, source, target, tmpname)


def main():
    parser = argparse.ArgumentParser(description='Process some integers.')
    parser.add_argument('-s', type=int, default=5, help='grid size')
    parser.add_argument('-r', type=int, default=20, help='number of generated random requirements')
    parser.add_argument('-p', type=int, default=1000, help='number of generated random paths for each round')
    parser.add_argument('-u', type=int, default=0,
                        help='number of unsatisfiable requirements, it is added to the total number of requirements')
    parser.add_argument('--seed', type=int, default=0,
                        help='The seed of the random generator')

    parser.add_argument('--fixed', type=float, default=0,
                        help='The percentage of fixed edge costs of the total edges (0 to 1)')
    parser.add_argument('-f', type=str, default='', help='read topology zoo graphml file')

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

    # Our random generator. MUST be used everywhere!!!!
    ospfRand = random.Random(seed)

    # If zoo topology file is specified, then read it
    # Otherwise generate a grid topo
    if topology_file:
        g = read_topology_zoo(topology_file)
        results_name = os.path.basename(topology_file)[:-len('.graphml')]
    else:
        g = gen_grid_topo_no_iface(gsize, gsize, 0)
        results_name = "grid%x%s" % (gsize, gsize)

    if not topology_file:
        print "Grid size %dx%d" % (gsize, gsize)
    else:
        print "Topology file:", topology_file
        print "Number of nodes:", len(list(g.nodes()))
        print "Number of edges:", len(list(g.edges()))
    print "Percentage of fixed edge costs:", fixed
    print "Number of requirements: %d" % reqsize
    #print "Number of paths per iteration %d" % pathsize
    print "Random Seed", seed#



    paths = []
    print "Generating random paths for requirements"
    for i in range(0, reqsize):
        src, dst = ospfRand.sample(list(g.nodes()), 2)
        assert src != dst
        path = random_requirement_path(g, src, dst, ospfRand, fixed_percentage=fixed)
        paths.append(path)

    print "Benchmarking exploring paths for one single requirement"
    deltas, tmp = time_exploring_paths(results_name, g, paths[0][0], paths[0][-1])
    print "Exploring time (%d): %f" % (len(tmp), sum(deltas) / len(deltas))
    # For memory free
    tmp = None
    deltas = None

    #cl = nx.DiGraph()
    #for n in g.nodes():
    #    cl.add_node(n)
    #for s, d in g.edges():
    #    cl.add_edge(s, d)
    #nx.write_dot(cl, "/tmp/g.dot")
    #if unsatisfiable_reqs:
    #    print "Generating counter paths"
    #chosen = []
    #for i in range(unsatisfiable_reqs):
    #    candidate = ospfRand.choice(paths)
    #    counter_path = None
    #    while counter_path is None:
    #        while candidate in chosen:
    #            candidate = ospfRand.choice(paths)
    #        counter_path = generate_second_path(g, candidate)
    #    chosen.append(candidate)
    #    print "Generating counter path for path", candidate
    #    paths.append(counter_path)
    #unsatisfiable_reqs = len(chosen)
    ospf = OSPFSyn([], g, gen_paths=pathsize)

    for path in paths:
        req = PathReq(PathProtocols.OSPF, path[-1], path, 10)
        ospf.add_path_req(req)

    ospf.solve()

    sys.stdout.flush()


if __name__ == '__main__':
    main()
