#!/usr/bin/env python
import argparse
import logging
import random
import re
import networkx as nx
from timeit import default_timer as timer

from synet.utils.topo_gen import gen_grid_topology
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.synthesis.ospf_heuristic import OSPFSyn as OSPFCEGIS
from synet.synthesis.ospf import OSPFSyn as OSPFConcrete
from synet.synthesis.static import StaticSyn
from synet.synthesis.connected import ConnectedSyn
from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.synthesis.propagation import EBGPPropagation

from synet.utils.smt_context import VALUENOTSET


def parse_inputs(inputs):
    """
    Parse logicblox input of the form +Name(args,...) and returns
    a list of tuples such as (Name, (args)).
    """
    p = re.compile(r'^(?P<op>[\+|\-])(?P<name>\w[\w\d_]*)\((?P<args>.*)\)\.$')
    init_inputs = []
    for line in inputs.split("\n"):
        line = line.strip()
        if not line: continue
        if not re.match(p, line):
            if line.startswith("//"):
                continue
            print "Not valid input, skipping", line
            continue
        m = re.match(p, line)
        op = m.group('op')
        func_name = m.group('name')
        args = m.group('args').replace(' ', '').replace('"', '').split(',')
        init_inputs.append((op, func_name, args))
    return init_inputs


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


def read_reqs(req_file):
    with open(req_file) as f:
        s = f.read()
    parsed = parse_inputs(s)
    nets = {}
    for line in parsed:
        op, predicate, values = line
        assert op == '+', op
        assert predicate == 'Fwd', predicate
        net = values[0]
        protocol = values[-1]
        src, dst = values[1:-1]
        if net not in nets:
            nets[net] = {}
        if protocol not in nets[net]:
            nets[net][protocol] = []
        paths = nets[net][protocol]
        appened = False
        for path in paths:
            assert isinstance(path, list)
            if path[-1] == src:
                path.append(dst)
                appened = True
            elif path[0] == dst:
                path.insert(0, src)
                appened = True
        if not appened:
            paths.append([src, dst])

    proto_map = {'ospf': Protocols.OSPF, 'static': Protocols.Static, 'bgp': Protocols.BGP}
    ospf_reqs = []
    static_reqs = []
    bgp_reqs = []
    for net in nets:
        for protocol in nets[net]:
            paths = nets[net][protocol]
            proto = proto_map[protocol]
            for path in paths:
                req = PathReq(protocol=proto, dst_net=net, path=path, strict=False)
                if proto == Protocols.OSPF:
                    ospf_reqs.append(req)
                elif proto == Protocols.Static:
                    static_reqs.append(req)
                elif proto == Protocols.BGP:
                    bgp_reqs.append(req)
                else:
                    raise ValueError("Unknown protocol")

    return static_reqs, ospf_reqs, bgp_reqs


def ospf(n, nreqs=10):
    req_file = './topos/cav/gridrand%d-ospf-%d-req.logic' % (n, nreqs)
    topo = gen_grid_topology(n, n, 0)
    static_reqs, ospf_reqs, bgp_reqs = read_reqs(req_file)
    seed = 159734782
    path_gen = 200
    ospfRand = random.Random(seed)
    for node in topo.nodes():
        topo.enable_ospf(node, 100)
        # Initially all costs are empty
        topo.set_static_routes_empty(node)
    for src, dst in topo.edges_iter():
        topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
    conn = ConnectedSyn([], topo, full=True)
    conn.synthesize()

    static_syn = StaticSyn(static_reqs, topo)
    static_syn.synthesize()

    ospf = OSPFCEGIS(topo, gen_paths=path_gen, random_obj=ospfRand)
    for req in ospf_reqs:
        ospf.add_req(req)
    assert ospf.synthesize(allow_ecmp=True)
    assert not ospf.removed_reqs


def static(n, nreqs=10):
    req_file = './topos/cav/gridrand%d-static-%d-req.logic' % (n, nreqs)
    topo = gen_grid_topology(n, n, 0)
    static_reqs, ospf_reqs, bgp_reqs = read_reqs(req_file)
    for node in topo.nodes():
        topo.enable_ospf(node, 100)
        # Initially all costs are empty
        topo.set_static_routes_empty(node)
    for src, dst in topo.edges_iter():
        topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
    conn = ConnectedSyn([], topo, full=True)
    conn.synthesize()

    static_syn = StaticSyn(static_reqs, topo)
    static_syn.synthesize()

def bgp(n, nreqs=10):
    req_file = './topos/cav/gridrand%d-bgp-%d-req.logic' % (n, nreqs)
    topo = gen_grid_topology(n, n, 0)
    for node in topo.local_routers_iter():
        topo.set_bgp_asnum(node, 100)

    static_reqs, ospf_reqs, bgp_reqs = read_reqs(req_file)

    peer = 'ATT'
    egresses = ['R11']
    topo.add_peer(peer)
    topo.set_bgp_asnum(peer, 5000)
    for req in bgp_reqs:
        req.path.append(peer)

    for egress in egresses:
        topo.add_peer_edge(peer, egress)
        topo.add_peer_edge(egress, peer)
        topo.add_bgp_neighbor(peer, egress, VALUENOTSET, VALUENOTSET)
    for src in topo.local_routers_iter():
        for dst in topo.local_routers_iter():
            if src == dst or dst in topo.get_bgp_neighbors(src):
                continue
            print "ADD BGP NEIGHBOR", src, dst
            topo.add_bgp_neighbor(src, dst, VALUENOTSET, VALUENOTSET)
    prefix = 'GOOGLE'
    communities = [Community("100:%d" % i) for i in range(5)]
    ann = Announcement(
        prefix=prefix,
        peer=peer,
        origin=BGP_ATTRS_ORIGIN.EBGP,
        as_path=[1, 2, 5000], as_path_len=3,
        next_hop='%sHop' % peer, local_pref=100,
        communities=dict([(c, False) for c in communities]), permitted=True)
    topo.add_bgp_advertise(peer, ann)

    conn = ConnectedSyn([], topo, full=True)
    conn.synthesize()

    p = EBGPPropagation(bgp_reqs, topo, allow_igp=True)
    p.synthesize()

def main():
    parser = argparse.ArgumentParser(description='EBGP baseline experiment.')
    parser.add_argument('-n', type=int, required=True, help='load grid nxn')
    parser.add_argument('-p', required=True, type=str, choices=['static', 'ospf', 'bgp'])
    args = parser.parse_args()
    setup_logging()
    if args.p == 'static':
        t1 = timer()
        static(args.n)
        t2 = timer()
        print "TOTAL_STATIC_TIME:", t2 - t1
    elif args.p == 'ospf':
        t1 = timer()
        ospf(args.n)
        t2 = timer()
        print "TOTAL_OSPF_TIME:", t2 - t1
    #bgp(3, nreqs=1)


if __name__ == '__main__':
    main()
