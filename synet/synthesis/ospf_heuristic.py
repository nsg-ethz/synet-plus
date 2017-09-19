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
from synet.utils.common import KConnectedPathsReq
from synet.utils.common import PathOrderReq
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.common import Req
from synet.utils.common import SynthesisComponent
from synet.utils.common import path_exists
from synet.utils.ospf_utils import extract_ospf_graph
from synet.utils.ospf_utils import get_output_configs
from synet.utils.ospf_utils import get_output_network_graph
from synet.utils.ospf_utils import load_graph_constrains
from synet.utils.ospf_utils import synthesize_ospf_announce
from synet.utils.smt_context import is_symbolic


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
        self.ospf_graph = extract_ospf_graph(self.network_graph, self.log)
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

        if not is_symbolic(path_cost):
            var = z3.Const("%s_cost" % path_name, z3.IntSort())
            self.solver.add(var == path_cost)
            path_cost = var

        for rand_path in self.saved_path_gen[path_key_req]:
            # Skip if we generated the same path as the requirement
            if path == rand_path:
                continue
            if rand_path:
                rand_path_name = get_path_name(rand_path)
                rand_path_cost = self._get_path_cost(rand_path)
                track_name = '%s_ISLESS_%s' % (path_name, rand_path_name)
                self.solver.assert_and_track(path_cost < rand_path_cost, track_name)
            count += 1
            if count > cuttoff:
                break

    def generate_ecmp_smt(self, paths):
        src, dst = paths[0][0], paths[0][-1]
        path_costs = [self._get_path_cost(path) for path in paths]
        path_names = [get_path_name(path) for path in paths]
        cuttoff = self.gen_paths
        count = 0
        path_key_req = tuple(paths[0])
        if path_key_req not in self.saved_path_gen:
            self.saved_path_gen[path_key_req] = self.generate_random_paths(
                src, dst, 0.6, self.random_gen)
        elif path_key_req not in self.counter_examples:
            return
        primary_name = path_names[0]
        primary_cost = path_costs[0]
        if not is_symbolic(primary_cost):
            var = z3.Const("%s_cost" % path_names[0], z3.IntSort())
            self.solver.add(var == primary_cost)
            primary_cost = var

        # Assert ECMP
        for p_index in range(1, len(paths)):
            path_name = path_names[p_index]
            track_name = '%s_ISEQUAL_%s' % (primary_name, path_name)
            cost = path_costs[p_index]
            self.solver.assert_and_track(primary_cost == cost, track_name)

        for rand_path in self.saved_path_gen[path_key_req]:
            # Skip if we generated the same path as the requirement
            if rand_path in paths:
                continue
            if rand_path:
                rand_path_name = get_path_name(rand_path)
                rand_path_cost = self._get_path_cost(rand_path)
                track_name = '%s_ISLESS_%s' % (path_name, rand_path_name)
                self.solver.assert_and_track(primary_cost < rand_path_cost, track_name)
            count += 1
            if count > cuttoff:
                break

    def generate_path_order_smt(self, paths):
        src, dst = paths[0][0], paths[0][-1]
        path_costs = [self._get_path_cost(path) for path in paths]

        path_names = [get_path_name(path) for path in paths]
        cuttoff = self.gen_paths
        count = 0
        path_key_req = tuple(paths[0])
        if path_key_req not in self.saved_path_gen:
            self.saved_path_gen[path_key_req] = self.generate_random_paths(
                src, dst, 0.6, self.random_gen)
        elif path_key_req not in self.counter_examples:
            return
        path_name = path_names[0]

        # Assert Ordering
        for p0, p1 in zip(range(len(paths))[0::1],range(len(paths))[1::1]):
            p0_name = get_path_name(paths[p0])
            p1_name = get_path_name(paths[p1])
            track_name = '%s_ORDER_%s' % (p0_name, p1_name)
            p0_cost = path_costs[p0]
            p1_cost = path_costs[p1]
            if is_symbolic(p0_cost):
                p0_var = p0_cost
            else:
                p0_var = z3.Const("%s_cost" % p0_name, z3.IntSort())
                self.solver.add(p0_var == p0_cost)
            if is_symbolic(p1_cost):
                p1_var = p1_cost
            else:
                p1_var = z3.Const("%s_cost" % p1_name, z3.IntSort())
                self.solver.add(p1_var == p1_cost)
            self.solver.assert_and_track(p0_var < p1_var, track_name)

        least_cost = path_costs[-1]
        if not is_symbolic(least_cost):
            var = z3.Const("%s_cost" % path_names[-1], z3.IntSort())
            self.solver.add(var == least_cost)
            least_cost = var

        for rand_path in self.saved_path_gen[path_key_req]:
            # Skip if we generated the same path as the requirement
            if rand_path in paths:
                continue
            if rand_path:
                rand_path_name = get_path_name(rand_path)
                rand_path_cost = self._get_path_cost(rand_path)
                track_name = '%s_ISLESS_%s' % (path_name, rand_path_name)
                self.solver.assert_and_track( least_cost < rand_path_cost, track_name)
            count += 1
            if count > cuttoff:
                break

    def generate_kconnected_smt(self, paths):
        src, dst = paths[0][0], paths[0][-1]
        path_costs = [self._get_path_cost(path) for path in paths]
        path_names = [get_path_name(path) for path in paths]
        cuttoff = self.gen_paths
        count = 0
        path_key_req = tuple(paths[0])
        if path_key_req not in self.saved_path_gen:
            self.saved_path_gen[path_key_req] = self.generate_random_paths(
                src, dst, 0.6, self.random_gen)
        elif path_key_req not in self.counter_examples:
            return

        for index, cost in enumerate(path_costs):
            if is_symbolic(cost):
                continue
            var = z3.Const("%s_cost" % path_names[index], z3.IntSort())
            self.solver.add(var == cost)
            path_costs[index] = var

        for rand_path in self.saved_path_gen[path_key_req]:
            # Skip if we generated the same path as the requirement
            if rand_path in paths:
                continue
            if rand_path:
                for index, path in enumerate(paths):
                    path_name = path_names[index]
                    path_cost = path_costs[index]
                    rand_path_name = get_path_name(rand_path)
                    rand_path_cost = self._get_path_cost(rand_path)
                    track_name = '%s_ISLESS_%s' % (path_name, rand_path_name)
                    self.solver.assert_and_track(path_cost < rand_path_cost, track_name)
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
        kconnected_reqs = []
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
            elif isinstance(req, KConnectedPathsReq):
                paths = [r.path for r in req.paths]
                kconnected_reqs.append(paths)
                self.all_req_paths.extend(paths)
            else:
                raise ValueError("Not supported req: %s", req)
        for path in simple_reqs:
            self.generate_path_smt(path)
        for paths in ordered_reqs:
            self.generate_path_order_smt(paths)
        for paths in ecmp_reqs:
            self.generate_ecmp_smt(paths)
        for paths in kconnected_reqs:
            self.generate_kconnected_smt(paths)
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
            t = str(t)
            if 'ISLESS' not in str(t):
                continue
            path = t.split('_ISLESS_')[0].split('_')
            path_req = None
            for req in self.reqs[:]:
                if isinstance(req, PathReq):
                    if req.path == path:
                        self.reqs.remove(req)
                        path_req = req
                        break
                elif isinstance(req, (ECMPPathsReq, PathOrderReq, KConnectedPathsReq)):
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

    def _check_simple_path_req(self, out_graph, req):
        """
        Check if a PathReq is satisfied
        :param out_graph: the current ospf graph
        :param req: PathReq
        :return: True if satisfied
        """
        sat = True
        path = req.path
        try:
            spath = nx.all_shortest_paths(out_graph, path[0], path[-1], 'cost')
            computed = list(spath)
        except nx.NetworkXNoPath:
            sat = False
            return sat

        if len(computed) > 1 or computed[0] != path:
            print "#" * 20
            print "Required Simple shortest path", path
            print "Computed Simple shortest path", computed
            print "#" * 20
            sat = False
            key = get_path_key(path[0], path[-1])
            if key not in self.counter_examples:
                self.counter_examples[key] = []
            for c_path in computed:
                self.log.debug("ADDING COUNTER Simple example: %s", c_path)
                self.counter_examples[key].append(c_path)
        return sat

    def _check_ecmp_path_req(self, out_graph, req):
        """
        Check if a ECMPPathsReq is satisfied
        :param out_graph: the current ospf graph
        :param req: ECMPPathsReq
        :return: True if satisfied
        """
        sat = True
        req_paths = [tuple(r.path) for r in req.paths]
        primary = req_paths[0]
        try:
            shortest = nx.all_shortest_paths(
                out_graph, primary[0], primary[-1], 'cost')
            computed = set([tuple(p) for p in shortest])
        except nx.NetworkXNoPath:
            sat = False
            return sat
        if computed != set(req_paths):
            print "#" * 20
            print "Required ECMP paths", req_paths
            print "Computed ECMP paths", computed
            print "#" * 20
            sat = False
            key = get_path_key(primary[0], primary[-1])
            if key not in self.counter_examples:
                self.counter_examples[key] = []
            for c_path in computed:
                self.log.debug("ADDING COUNTER ECMP example: %s", c_path)
                self.counter_examples[key].append(c_path)
        return sat

    def _check_order_path_req(self, out_graph, req):
        """
        Check if a PathOrder is satisfied
        :param out_graph: the current ospf graph
        :param req: PathOrder
        :return: True if satisfied
        """
        sat = True
        req_paths = [r.path for r in req.paths]
        all_edges = [(None, None)] + list(out_graph.edges_iter())
        primary = req_paths[0]
        for src, dst in all_edges:
            out_copy = out_graph.copy()
            if src is not None and dst is not None:
                out_copy.remove_edge(src, dst)
            curr_path = None
            for path in req_paths:
                if path_exists(path, out_copy):
                    curr_path = path
                    break
            if not curr_path:
                # None of the requirements paths exists anymore
                continue
            shortest = nx.all_shortest_paths(
                out_copy, curr_path[0], curr_path[-1], 'cost')
            computed = list(shortest)
            if len(computed) > 1 or computed[0] != curr_path:
                print "#" * 20
                print "Required Order shortest path", curr_path
                print "Computed Order shortest path", computed
                print "#" * 20
                sat = False
                key = get_path_key(primary[0], primary[-1])
                if key not in self.counter_examples:
                    self.counter_examples[key] = []
                for c_path in computed:
                    self.log.debug("ADDING COUNTER PathOrder example: %s", c_path)
                    self.counter_examples[key].append(c_path)
                break
        return sat

    def _check_kconnected_req(self, out_graph, req):
        """
        Check if a KConnected is satisfied
        :param out_graph: the current ospf graph
        :param req: KConnected
        :return: True if satisfied
        """
        sat = True
        req_paths = [r.path for r in req.paths]
        all_edges = [(None, None)] + list(out_graph.edges_iter())
        primary = req_paths[0]
        for src, dst in all_edges:
            out_copy = out_graph.copy()
            if src is not None and dst is not None:
                out_copy.remove_edge(src, dst)
            try:
                shortest = nx.all_shortest_paths(
                    out_copy, primary[0], primary[-1], 'cost')
                computed = list(shortest)
            except nx.NetworkXNoPath:
                continue
            curr_reqs = []
            for path in req_paths:
                if path_exists(path, out_copy):
                    curr_reqs.append(path)
            if not curr_reqs:
                continue
            not_valid_path = None
            for p in computed:
                if p not in curr_reqs:
                    not_valid_path = p
                    break
            if not_valid_path:
                print "#" * 20
                print "Required KConnected shortest path", curr_reqs
                print "Computed KConnected shortest path", not_valid_path
                print "#" * 20
                sat = False
                key = get_path_key(primary[0], primary[-1])
                if key not in self.counter_examples:
                    self.counter_examples[key] = []
                self.log.debug("ADDING COUNTER KConnected example: %s", not_valid_path)
                self.counter_examples[key].append(not_valid_path)
                break
        return sat

    def check_req_satisfied(self, out_graph, req):
        sat = True
        if isinstance(req, PathReq):
            sat = self._check_simple_path_req(out_graph, req)
        elif isinstance(req, ECMPPathsReq):
            sat = self._check_ecmp_path_req(out_graph, req)
        elif isinstance(req, PathOrderReq):
            sat = self._check_order_path_req(out_graph, req)
        elif isinstance(req, KConnectedPathsReq):
            sat = self._check_kconnected_req(out_graph, req)
        else:
            raise ValueError("Cannot check req for %s", req)
        return sat

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
            # At this point any unsat is directly caused by the requirements
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
                recompute = not self.check_req_satisfied(g_ospf, req)
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
