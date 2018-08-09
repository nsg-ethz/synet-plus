#!/usr/bin/env python

import argparse
import logging
import random
import sys
import os

from timeit import default_timer as timer
from synet.utils.topo_gen import read_topology_zoo_netgraph
from synet.utils.smt_context import VALUENOTSET
from synet.synthesis.ospf_heuristic import OSPFSyn as OSPFCEGIS
from synet.synthesis.ospf import OSPFSyn as OSPFConcrete
from synet.synthesis.connected import ConnectedSyn


def setup_logging():
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


def main():
    setup_logging()
    parser = argparse.ArgumentParser(description='Run OSPF experiment.')
    parser.add_argument('--topo', required=True, type=str,
                        help='read topology zoo graphml file')
    parser.add_argument('--values', required=True, type=str,
                        help='python file with reqs vals')
    parser.add_argument('--type', required=True, type=str,
                        choices=['simple', 'ecmp', 'kconnected', 'order'],
                        help='simple, ecmp, kconnected, ordered')
    parser.add_argument('--reqsize', type=int, required=True,
                        help='Number of reqs to be used')
    parser.add_argument('--syn', required=True, type=str,
                        choices=['cegis', 'concrete'],
                        help='simple, ecmp, kconnected, ordered')
    parser.add_argument('-k', type=int, default=2,
                        help='Number of paths used per requirement (ecmp, ordered, etc..)')
    parser.add_argument(
        '-p', type=int, default=100,
        help='number of generated random paths for each round of synthesis')
    parser.add_argument('--seed', type=int, default=0,
                        help='The seed of the random generator')
    parser.add_argument(
        '--fixed', type=float, default=0,
        help='The percentage of fixed edge costs of the total edges (0 to 1)')

    # Parse command line args
    args = parser.parse_args()
    topo_file = args.topo
    reqs_file = args.values
    req_type = args.type
    reqsize = args.reqsize
    k = args.k
    path_gen = args.p
    seed = args.seed
    fixed = args.fixed
    syn = args.syn
    print "Syntype", syn
    assert 0 <= fixed <= 1.0

    # Generate new random number seed if need
    if not seed:
        seed = random.randint(0, sys.maxint)
        print "Generated new seed", seed
    # This random generator MUST be used everywhere!!!!
    ospfRand = random.Random(seed)

    topo = read_topology_zoo_netgraph(topo_file)

    with open(reqs_file, 'r') as file:
        exec(file.read())

    if req_type == 'simple':
        reqs = eval('reqs_simple_%d' % reqsize)
        vals = eval('edges_cost_simple_%d' % reqsize)
    elif req_type == 'ecmp':
        reqs = eval('reqs_ecmp_%d_%d' % (reqsize, k))
        vals = eval('edges_cost_ecmp_%d_%d' % (reqsize, k))
    elif req_type == 'kconnected':
        reqs = eval('reqs_kconnected_%d_%d' % (reqsize, k))
        vals = eval('edges_cost_kconnected_%d_%d' % (reqsize, k))
    elif req_type == 'order':
        reqs = eval('reqs_order_%d_%d' % (reqsize, k))
        vals = eval('edges_cost_order_%d_%d' % (reqsize, k))
    else:
        raise ValueError("Unknow req type %s", req_type)

    for node in topo.nodes():
        topo.enable_ospf(node, 100)
    # Initially all costs are empty
    for src, dst in topo.edges():
        topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
    # how many is fixed
    fixed_edges = ospfRand.sample(vals, int(round(len(vals) * fixed)))
    for src, dst, cost in fixed_edges:
        #print "Fixing", src, dst, cost
        topo.set_edge_ospf_cost(src, dst, cost)
    # Establish basic connectivity
    conn = ConnectedSyn([], topo, full=True)
    conn.synthesize()

    t1 = timer()
    if syn == 'cegis':
        print "Syn CEGIS"
        ospf = OSPFCEGIS(topo, gen_paths=path_gen, random_obj=ospfRand)
        for req in reqs:
            ospf.add_req(req)
        assert ospf.synthesize()
        assert not ospf.removed_reqs
    elif syn == "concrete":
        print "Syn Concrete"
        ospf = OSPFConcrete(topo)
        for req in reqs:
            ospf.add_req(req)
        assert ospf.solve()
    else:
        raise ValueError("Unknow syn type %s" % syn)
    t2 = timer()
    print "TOTAL SYN TIME:", t2 - t1
    if fixed == 1.0:
        t1 = timer()
        print "Updating network graph, to assert full values"
        ospf.update_network_graph()
        for src, dst, cost in vals:
            new_cost = topo.get_edge_ospf_cost(src, dst)
            assert cost == new_cost, "Diff (%s, %s) old=%s new=%s" % (
                src, dst, cost, new_cost)
        t2 = timer()
        print "Update Network graph TIME:", t2 - t1


    from tekton.gns3 import GNS3Topo
    ospf.update_network_graph()
    gns3 = GNS3Topo(topo)
    basename = os.path.basename(topo_file).strip('.graphml')
    out_name = "%s_%s_%s_%s" % (basename, fixed, req_type, reqsize)
    out_dir = 'out-configs/%s_%d' % (out_name, ospfRand.randint(0, 1000))
    print "Writing configs to:", out_dir
    gns3.write_configs(out_dir)


if __name__ == '__main__':
    main()
