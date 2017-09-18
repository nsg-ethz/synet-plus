#!/usr/bin/env python

"""
CEGIS style synthesis for OSPF
with heuristic path generator
"""

import logging
import random
from timeit import default_timer as timer

import networkx as nx
import z3

from synet.topo.graph import NetworkGraph
from synet.utils.common import ECMPPathsReq
from synet.utils.common import PathOrderReq
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.common import Req
from synet.utils.common import SynthesisComponent
from synet.utils.ospf_utils import extract_ospf_graph
from synet.utils.ospf_utils import get_output_configs
from synet.utils.ospf_utils import get_output_network_graph
from synet.utils.ospf_utils import load_graph_constrains
from synet.utils.ospf_utils import synthesize_ospf_announce


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


def get_path_key(src, dst):
    """
    For a given path return a tuple of source and dst
    Useful for storing paths in dicts
    """
    return src, dst


def get_path_name(path):
    """Return a string name for the path (to used used in unsat core"""
    return '_'.join(path)


class OSPFSyn(SynthesisComponent):

    def __init__(self, network_graph,
                 solver=None, gen_paths=1000, random_obj=None):
        assert isinstance(network_graph, NetworkGraph)
        self.log = logging.getLogger('%s.%s' % (
            self.__module__, self.__class__.__name__))
        super(OSPFSyn, self).__init__([], network_graph, solver)

        self.random_gen = random_obj or random.Random()
        self.ospf_graph = None
        # Number of paths to generate at each iterations
        self.gen_paths = gen_paths
        # Keep track of the generators for new random paths for a given req
        self.saved_path_gen = {}
        # Counter examples of wrong paths
        self.counter_examples = {}
        # Requirements that couldn't be satisfied by ospf
        self.removed_reqs = []
        self.all_req_paths = None  # Keep track of all paths in the reqs

    def reset_solver(self):
        """Reset and clear all caches and create new solver"""
        self.solver = z3.Solver()
        load_graph_constrains(self.solver, self.ospf_graph)
        self.saved_path_gen = {}

    def random_walk_path(self, source, target):
        """
        Generate a random path between a source and target
        This uses a random walk across the graph
        it might return None if the random walk hits a dead end
        """
        G = self.ospf_graph
        visited = [source]
        while True:
            children = G[visited[-1]]
            none_visited_children = []
            for child in children:
                if child not in visited:
                    none_visited_children.append(child)
            # Check if we hit a dead end
            if not none_visited_children:
                # Just abort at dead end
                return None
            # Select one random next hop
            next_node = self.random_gen.choice(none_visited_children)
            visited.append(next_node)
            if next_node == target:
                # We reached our destination
                return visited

    def random_dijkstra_path(self, source, target, max_weight=1000000):
        """
        Generate a random path between a source and target
        First generates random weights for each edge in the graph
        then we select the shortest paths based on dijkstra algorithm
        """
        G = nx.DiGraph()
        for src, dst in self.ospf_graph.edges():
            G.add_edge(src, dst)
        for src, dst in G.edges():
            w = self.random_gen.randint(1, max_weight)
            G[src][dst]['test-weight'] = w
        return nx.shortest_path(G, source, target, 'test-weight')

    def generate_random_paths(self, source, target, dijsktra_prob, random_obj):
        """
        A generator for random paths
        This generator keeps history of the generated paths such that we
        don't generate the same path twice.
        """
        generated_paths = []
        counter = 0
        while True:
            # First give a priority to the counter examples (if any)
            key = get_path_key(source, target)
            if self.counter_examples.get(key, None):
                p = self.counter_examples[key].pop()
            else:
                if random_obj.random() < dijsktra_prob:
                    p = self.random_dijkstra_path(source, target)
                else:
                    p = self.random_walk_path(source, target)
            if not p or p in generated_paths:
                # Path already generated or random walk hit a dead end
                # Try again
                counter += 1
                if counter > 10:
                    counter = 0
                    yield None
                continue
            else:
                counter = 0
                generated_paths.append(p)
                yield p

    def generate_path_smt(self, path):
        src, dst = path[0], path[-1]
        path_cost = self._get_path_cost(path)
        cuttoff = self.gen_paths
        count = 0
        path_key_req = tuple(path)
        if path_key_req not in self.saved_path_gen:
            self.saved_path_gen[path_key_req] = self.generate_random_paths(
                src, dst, 0.6, self.random_gen)
        elif path_key_req not in self.counter_examples:
            return
        path_name = get_path_name(path)

        oo = 1
        for rand_path in self.saved_path_gen[path_key_req]:
            # Skip if we generated the same path as the requirement
            if path == rand_path:
                continue
            if rand_path:
                rand_path_name = '_'.join(rand_path)
                rand_path_cost = self._get_path_cost(rand_path)
                track_name = '%s_ISLESS_%s' % (path_name, rand_path_name)
                if isinstance(rand_path_cost, int) and isinstance(path_cost, int):
                    t1, t2 = z3.Consts('p1_cost_%d, p2_cost_%d' % (oo, oo), z3.IntSort())
                    oo += 1
                    err = "path cost %d and rand cost %s" % (path_cost, rand_path_cost)
                    assert path_cost <= rand_path_cost, err
                    const = z3.And(t1 == path_cost, t2 == rand_path_cost, t1 <= t2)
                    self.solver.assert_and_track(const, track_name)
                else:
                    self.solver.assert_and_track(path_cost < rand_path_cost,
                                                 track_name)
            count += 1
            if count > cuttoff:
                break

    def generate_ecmp_smt(self, paths):
        src, dst = paths[0][0], paths[0][-1]
        path_costs = [self._get_path_cost(path) for path in paths]
        cuttoff = self.gen_paths
        count = 0
        path_key_req = tuple(paths[0])
        if path_key_req not in self.saved_path_gen:
            self.saved_path_gen[path_key_req] = self.generate_random_paths(
                src, dst, 0.6, self.random_gen)
        elif path_key_req not in self.counter_examples:
            return
        path_name = get_path_name(paths[0])

        # Assert ECMP
        for cost in path_costs[1:]:
            self.solver.add(path_costs[0] == cost)

        oo = 1
        for rand_path in self.saved_path_gen[path_key_req]:
            # Skip if we generated the same path as the requirement
            if rand_path in paths:
                continue
            if rand_path:
                rand_path_name = '_'.join(rand_path)
                rand_path_cost = self._get_path_cost(rand_path)
                track_name = '%s_ISLESS_%s' % (path_name, rand_path_name)
                if isinstance(rand_path_cost, int) and isinstance(path_costs[0], int):
                    t1, t2 = z3.Consts('p1_cost_%d, p2_cost_%d' % (oo, oo), z3.IntSort())
                    oo += 1
                    err = "path cost %d and rand cost %s" % (path_costs[0], rand_path_cost)
                    assert path_costs[0] <= rand_path_cost, err
                    const = z3.And(t1 == path_costs[0], t2 == rand_path_cost, t1 <= t2)
                    self.solver.assert_and_track(const, track_name)
                else:
                    self.solver.assert_and_track(path_costs[0] < rand_path_cost, track_name)
            count += 1
            if count > cuttoff:
                break

    def generate_path_order_smt(self, paths):
        src, dst = paths[0][0], paths[0][-1]
        path_costs = [self._get_path_cost(path) for path in paths]
        cuttoff = self.gen_paths
        count = 0
        path_key_req = tuple(paths[0])
        if path_key_req not in self.saved_path_gen:
            self.saved_path_gen[path_key_req] = self.generate_random_paths(
                src, dst, 0.6, self.random_gen)
        elif path_key_req not in self.counter_examples:
            return
        path_name = get_path_name(paths[0])

        # Assert Ordering
        for p0, p1 in zip(path_costs[0::1], path_costs[1::1]):
            print "ADDING", p0 < p1
            self.solver.add(p0 < p1)

        oo = 1
        for rand_path in self.saved_path_gen[path_key_req]:
            # Skip if we generated the same path as the requirement
            if rand_path in paths:
                continue
            if rand_path:
                rand_path_name = '_'.join(rand_path)
                rand_path_cost = self._get_path_cost(rand_path)
                track_name = '%s_ISLESS_%s' % (path_name, rand_path_name)
                if isinstance(rand_path_cost, int) and isinstance(path_costs[-1], int):
                    t1, t2 = z3.Consts(
                        'p1_cost_%d, p2_cost_%d' % (oo, oo), z3.IntSort())
                    oo += 1
                    err = "path cost %d and rand cost %s" % (path_costs[-1], rand_path_cost)
                    assert path_costs[-1] <= rand_path_cost, err
                    const = z3.And(t1 == path_costs[-1], t2 == rand_path_cost, t1 <= t2)
                    self.solver.assert_and_track(const, track_name)
                else:
                    self.solver.assert_and_track(
                        path_costs[-1] < rand_path_cost, track_name)
            count += 1
            if count > cuttoff:
                break

    def push_requirements(self):
        self.solver.push()
        self.log.info("Start pushing OSPF requirements")
        start = timer()
        self.all_req_paths = []
        simple_reqs = []
        ordered_reqs = []
        ecmp_reqs = []
        for req in self.reqs:
            if isinstance(req, PathReq):
                simple_reqs.append(req.path)
                self.all_req_paths.append(req.path)
            elif isinstance(req, PathOrderReq):
                paths = [r.path for r in req.paths]
                ordered_reqs.append(paths)
                self.all_req_paths.extend(paths)
            elif isinstance(req, ECMPPathsReq):
                paths = [r.path for r in req.paths]
                ecmp_reqs.append(paths)
                self.all_req_paths.extend(paths)
        for path in simple_reqs:
            self.generate_path_smt(path)
        for paths in ordered_reqs:
            self.generate_path_order_smt(paths)
        for paths in ecmp_reqs:
            self.generate_ecmp_smt(paths)
        end = timer()
        self.log.info("End pushing OSPF requirements: %s seconds", (end - start))

    def get_output_routing_graphs(self):
        """
        Returns one graph per each destination network.
        """
        return self.get_output_network_graph()

    def get_output_routing_graph(self):
        """
        Returns one graph annotated with the OSPF Routes and Best Routes
        """
        return self.get_output_network_graph()

    def get_output_configs(self):
        """Returns list of (src, dst, cost)"""
        return get_output_configs(self.solver.model(), self.ospf_graph)

    def get_output_network_graph(self):
        """Return OSPF graph annotated with synthesized costs"""
        return get_output_network_graph(self.solver.model(), self.ospf_graph)

    def update_network_graph(self):
        """Set concrete costs on the network graph"""
        configs = self.get_output_configs()
        for src, dst, cost in configs:
            self.network_graph.set_edge_ospf_cost(src, dst, cost)
        synthesize_ospf_announce(self.network_graph, self.ospf_graph, self.reqs)

    def _get_edge_cost(self, src, dst):
        """Shortcut function to get the cost function of an edge"""
        cost = self.ospf_graph[src][dst].get('cost')
        return cost

    def _get_path_cost(self, path):
        """Shortcut function to get the cost function of aa given path"""
        edge_costs = []
        for i in range(len(path) - 1):
            src = path[i]
            dst = path[i + 1]
            edge_costs.append(self._get_edge_cost(src, dst))
        return sum(edge_costs)

    def add_req(self, req):
        assert isinstance(req, Req)
        assert req.protocol == Protocols.OSPF
        self.reqs.append(req)

    def remove_unsat_paths(self):
        """
        Remove one path from to the requirements if it's part of the unsat core.
        :return: PathReq
        """
        unsat_paths = self.solver.unsat_core()
        assert unsat_paths
        for t in unsat_paths:
            path = str(t).split('_ISLESS_')[0].split('_')
            path_req = None
            for req in self.reqs[:]:
                if isinstance(req, PathReq):
                    if req.path == path:
                        self.reqs.remove(req)
                        path_req = req
                        break
                elif isinstance(req, ECMPPathsReq):
                    found = False  # To break outer loop
                    for p in req.paths:
                        if path == p.path:
                            self.reqs.remove(req)
                            path_req = req
                            found = True
                    if found:
                        break
                else:
                    raise ValueError("Cannot remove req %s" % req)
            assert path_req, "Couldn't find path in requirements %s" % path
            self.removed_reqs.append(path_req)
            break
        self.reset_solver()
        return self.removed_reqs[-1]

    def check_req_satisfied(self, out_graph, req):
        recompute = False
        if isinstance(req, PathReq):
            computed = list(nx.all_shortest_paths(out_graph, req.path[0], req.path[-1], 'cost'))
            if len(computed) > 1 or computed[0] != req.path:
                print "#" * 20
                print "Required shortest path", req.path
                print "Computed shortest path", computed
                print "#" * 20
                recompute = True
                key = get_path_key(req.path[0], req.path[-1])
                if key not in self.counter_examples:
                    self.counter_examples[key] = []
                for c_path in computed:
                    print "ADDING COUNTER example", c_path
                    self.counter_examples[key].append(c_path)
        elif isinstance(req, ECMPPathsReq):
            req_paths = [tuple(r.path) for r in req.paths]
            computed = set(
                [tuple(p) for p in
                 nx.all_shortest_paths(
                     out_graph, req_paths[0][0], req_paths[0][-1], 'cost')])
            if computed != set(req_paths):
                print "#" * 20
                print "Required ECMP paths", req_paths
                print "Computed ECMP paths", computed
                print "#" * 20
                recompute = True
                key = get_path_key(req_paths[0][0], req_paths[0][-1])
                if key not in self.counter_examples:
                    self.counter_examples[key] = []
                for c_path in computed:
                    print "ADDING ECMP COUNTER example", c_path
                    self.counter_examples[key].append(c_path)
        elif isinstance(req, PathOrderReq):
            req_paths = [r.path for r in req.paths]
            prev_graph = out_graph.copy()
            all_edges = [(None, None)] + list(out_graph.edges_iter())
            for src, dst in all_edges:
                if src is not None and dst is not None:
                    prev_graph.remove_edge(src, dst)
                curr_path = None
                for path in req_paths:
                    if False not in [prev_graph.has_edge(x, y) for x, y in zip(path[0::1], path[1::1])]:
                        curr_path = path
                        break
                if not curr_path:
                    #print "Curr path doesn't exist afer removing", src, dst, req_paths
                    continue
                computed = list(nx.all_shortest_paths(out_graph, curr_path[0], curr_path[-1], 'cost'))
                if len(computed) > 1 or computed[0] != curr_path:
                    print "#" * 20
                    print "Required shortest path", curr_path
                    print "Computed shortest path", computed[0]
                    print "#" * 20
                    recompute = True
                    key = get_path_key(req_paths[0][0], req_paths[0][-1])
                    if key not in self.counter_examples:
                        self.counter_examples[key] = []
                    for c_path in computed:
                        print "ADDING COUNTER example", c_path
                        self.counter_examples[key].append(c_path)
                if src is not None and dst is not None:
                    prev_graph.add_edge(src, dst)

        return recompute

    def synthesize(self, retries_before_rest=5, gen_path_increment=500):
        """
        The main synthesis method
        :param retries_before_rest: how many time to try before resetting
                                    for new instance of the SMT solver
        :param gen_path_increment: how many paths to generate per iterations
        :return: bool
        """
        # Load Graph
        self.ospf_graph = extract_ospf_graph(self.network_graph, self.log)
        load_graph_constrains(self.solver, self.ospf_graph)

        origianl_gen_paths = self.gen_paths

        # First try to synthesize with all requirements
        while not self.solve():
            # At this point any unsat is dirctly caused by the requirements
            # So remove one of them
            print self.solver.unsat_core()
            self.remove_unsat_paths()

        # Now the actual synthesis
        retries = 0
        while True:
            recompute = False
            # Check if all requirements are already satisfied
            # Using dijkstra algorithm
            for req in self.reqs:
                g_ospf = self.get_output_network_graph()
                recompute = self.check_req_satisfied(g_ospf, req)
            if not recompute:
                break
            print "Recomputing ospf costs"
            retries += 1
            if retries > retries_before_rest:
                self.gen_paths += gen_path_increment
                print "RESET SOLVER and increase the number of paths to", self.gen_paths, "#" * 10
                self.reset_solver()
            while not self.solve():
                print "UNSAT"
                print self.solver.unsat_core()
                removed_path = self.remove_unsat_paths()
                print "#" * 40
                print "Removed path from req", removed_path
                self.gen_paths = origianl_gen_paths
                print "#" * 40
        return True

    def print_costs(self):
        """Print the synthesized edge costs"""
        print "Synthesized OSPF Link Costs"
        for t in self.get_output_configs():
            print "\t", t
