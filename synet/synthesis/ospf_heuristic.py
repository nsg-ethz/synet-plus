#!/usr/bin/env python

"""
CEGIS style synthesis for OSPF
with heuristic path generator
"""

import random

import networkx as nx
import z3

from synet.utils.common import BestOSPFRoute
from synet.utils.common import NODE_TYPE
from synet.utils.common import OSPFBestRoutes
from synet.utils.common import OSPFBestRoutesCost
from synet.utils.common import PathOrderReq
from synet.utils.common import PathProtocols
from synet.utils.common import PathReq
from synet.utils.common import SetOSPFEdgeCost
from synet.utils.common import SynthesisComponent
from synet.utils.common import VERTEX_TYPE
from synet.utils.common import datatypes_unique
from synet.utils.common import z3_is_network
from synet.utils.common import z3_is_node

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


# For a given path return a tuple of source and dst
# Useful for storing paths in dicts
path_key = lambda src, dst: (src, dst)


class OSPFSyn(SynthesisComponent):
    valid_inputs = (SetOSPFEdgeCost, BestOSPFRoute)

    def __init__(self, initial_configs, network_graph,
                 solver=None, gen_paths=1000, random_obj=None):
        g = network_graph.copy()
        # Only local routers
        for node, data in g.nodes(data=True)[:]:
            if data[VERTEX_TYPE] != NODE_TYPE:
                del g.node[node]
        super(OSPFSyn, self).__init__(initial_configs, g, solver)
        self.random_gen = random_obj or random.Random()
        # Read vertices
        self._create_vertices('OSPFVertex', self.initial_configs,
                              self.network_graph, True)
        # Function declarations
        # Vertex types
        self.is_node = z3_is_node(self.vertex)
        self.is_network = z3_is_network(self.vertex)
        # True is an edge exists between two vertices
        self.edge = z3.Function('EdgePhyOSPF', self.vertex,
                                self.vertex, z3.BoolSort())
        # Assign a cost to each edge
        self.edge_cost = z3.Function('OSPFEdgeCost', self.vertex, self.vertex,
                                     z3.IntSort())
        # Read input
        self._read_input_graph()
        self._add_general_constrains()
        # Number of paths to generate at each iterations
        self.gen_paths = gen_paths
        # Keep track of the generators for new random paths for a given req
        self.saved_path_gen = {}
        # Counter examples of wrong paths
        self.counter_examples = {}
        # Requirements that couldn't be satisfied by ospf
        self.removed_reqs = []

    def reset_solver(self):
        """Reset and clear all caches and create new solver"""
        self.solver = z3.Solver()
        self._read_input_graph()
        self._add_general_constrains()
        self.saved_path_gen = {}

    def random_walk_path(self, source, target):
        """
        Generate a random path between a source and target
        This uses a random walk across the graph
        it might return None if the random walk hits a dead end
        """
        G = self.network_graph
        visited = [source]
        while True:
            children = G[visited[-1]]
            none_visited_children = []
            for child in children:
                if child not in self.node_names:
                    continue
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
        for src, dst in self.network_graph.edges():
            if src not in self.node_names:
                continue
            if dst not in self.node_names:
                continue
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
            key = path_key(source, target)
            if self.counter_examples.get(key, None):
                p = self.counter_examples[key].pop()
                #print "Using counter example for", key, p
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

    def push_requirements(self):
        self.solver.push()
        print "Start pushing requirements"
        for req in self.reqs:
            if isinstance(req, PathReq):
                path = req.path
                src = path[0]
                dst = path[-1]
                path_cost = self._get_path_cost(path)
                cuttoff = self.gen_paths
                count = 0
                path_key = tuple(req.path)
                if path_key not in self.saved_path_gen:
                    self.saved_path_gen[path_key] = self.generate_random_paths(
                        src, dst, 0.6, self.random_gen)
                elif path_key not in self.counter_examples:
                    continue
                path_name = '_'.join(path) # This name is used in tracking unsat core
                for rand_path in self.saved_path_gen[path_key]:
                    # Skip if we generated the same path as the requirement
                    if path == rand_path: continue
                    if rand_path:
                        rand_path_name = '_'.join(rand_path)
                        rand_path_cost = self._get_path_cost(rand_path)
                        self.solver.assert_and_track(path_cost < rand_path_cost,
                                                     '%s_ISLESS_%s' % (
                                                         path_name, rand_path_name))
                    count += 1
                    if count > cuttoff:
                        break
                #if cost:
                #    self.solver.add(path_cost == cost)
        print "Done pushing requirements"

    def _add_general_constrains(self):
        """
        Constraints that are defined independent of the inputs.
        And constraints that are generally defined per destination network
        """
        # Free variables to be used later
        v1, v2 = z3.Consts('v1 v2', self.vertex)

        common_types = [self.is_node, self.is_network]
        self.solver.add(datatypes_unique(self.vertex, common_types))

        # Cost must be positive value
        self.solver.add(
            z3.ForAll(
                [v1, v2],
                z3.Implies(
                    self.edge(v1, v2),
                    self.edge_cost(v1, v2) > 0
                )))

    def _read_input_graph(self):
        """
        Reads the inputs and add them as constraints to the solver
        """
        for tmp in self.initial_configs:
            if isinstance(tmp, SetOSPFEdgeCost):
                self.network_graph.edge[tmp.src][tmp.dst]['cost'] = int(tmp.cost)
        # Fix vertices datatypes
        for node in self.nodes:
            self.solver.append(self.is_node(node) == True)
        # Stop the solver from adding a new edges
        for src in self.network_graph.nodes():
            if src in self.network_names: continue
            for dst in self.network_graph.nodes():
                if dst in self.network_names: continue
                src_v = self.get_vertex(src)
                dst_v = self.get_vertex(dst)
                self.solver.add(self.edge_cost(src_v, dst_v) >= 0)
                if self.network_graph.has_edge(src, dst):
                    cost = self.network_graph.edge[src][dst].get('cost', None)
                    self.solver.add(self.edge(src_v, dst_v))
                    if cost:
                        self.solver.add(self.edge_cost(src_v, dst_v) == cost)
                else:
                    self.solver.add(z3.Not(self.edge(src_v, dst_v)))
        for t in self.initial_configs:
            if not isinstance(t, BestOSPFRoute): continue
            assert t.src != t.nxt, t
            if OSPFBestRoutes not in self.network_graph.node[t.src]:
                self.network_graph.node[t.src][OSPFBestRoutes] = {}
            if OSPFBestRoutesCost not in self.network_graph.node[t.src]:
                self.network_graph.node[t.src][OSPFBestRoutesCost] = {}
            self.network_graph.node[t.src][OSPFBestRoutes][t.net] = t.nxt
            self.network_graph.node[t.src][OSPFBestRoutesCost][t.net] = int(t.cost)

        def get_shortest(net, src):
            if OSPFBestRoutes not in self.network_graph.node[src]:
                return None
            nxt = self.network_graph.node[src][OSPFBestRoutes].get(net, None)
            if not nxt: return None
            path = nx.shortest_path(self.network_graph, src, nxt)
            if path[-1] != net:
                a = get_shortest(net, path[-1])
                if a:
                    return path + a[1:]
                else:
                    return path

        for net in self.network_names:
            for node in self.node_names:
                path = get_shortest(net, node)
                if not path: continue
                req = PathReq(PathProtocols.OSPF,
                              net,
                              path,
                              self.network_graph.node[node][OSPFBestRoutesCost][net])
                self.add_path_req(req)

    def get_output_network_graph(self):
        m = self.solver.model()
        g = nx.DiGraph()
        check = lambda x: z3.is_true(m.eval(x))
        for src, src_v in self.name_to_vertex.iteritems():
            g.add_node(src,
                       **self._get_vertex_attributes(self.network_graph, src_v))
            for dst, dst_v in self.name_to_vertex.iteritems():
                if not g.has_node(dst):
                    g.add_node(dst,
                               **self._get_vertex_attributes(self.network_graph,
                                                             dst_v))
                if check(self.edge(src_v, dst_v)):
                    cost = m.eval(self.edge_cost(src_v, dst_v)).as_long()
                    g.add_edge(src, dst, cost=cost,
                               **self._get_edge_attributes(src_v, dst_v))

        return g

    def get_output_routing_graphs(self):
        """
        Returns one graph per each destination network.
        """
        m = self.solver.model()
        g_phy = self.get_output_network_graph()
        graphs = {}
        for dst_net in self.networks:
            dst_net_name = self.get_name(dst_net)
            g = nx.DiGraph()
            g.graph['dst'] = dst_net_name
            graphs[dst_net_name] = g
            for node, node_v in self.name_to_vertex.iteritems():
                if not nx.has_path(g_phy, node, dst_net_name):
                    continue
                path = nx.shortest_path(g_phy, node, dst_net_name, 'cost')
                for i in range(len(path) - 1):
                    src = path[i]
                    dst = path[i + 1]
                    if not g.has_node(src):
                        g.add_node(src,
                                   **self._get_vertex_attributes(g_phy, src))
                    if not g.has_node(dst):
                        g.add_node(dst,
                                   **self._get_vertex_attributes(g_phy, dst))

                    cost = m.eval(
                        self.edge_cost(self.get_vertex(src),
                                       self.get_vertex(dst))).as_long()
                    g.add_edge(src, dst, cost=cost,
                               **self._get_edge_attributes(src, dst))
        return graphs

    def get_output_routing_graph(self):
        """
        Returns one graph annotated with the OSPF Routes and Best Routes
        """
        return self.get_output_network_graph()

    def get_output_configs(self):
        m = self.solver.model()
        outputs = []
        check = lambda x: z3.is_true(m.eval(x))
        for src, src_v in self.name_to_vertex.iteritems():
            for dst, dst_v in self.name_to_vertex.iteritems():
                if not check(self.edge(src_v, dst_v)):
                    continue
                cost = m.eval(self.edge_cost(src_v, dst_v)).as_long()
                outputs.append(SetOSPFEdgeCost(src, dst, cost))
        return outputs

    def _get_edge_cost(self, src, dst):
        """Shortcut function to get the cost function of an edge"""
        cost = self.network_graph[src][dst].get('cost', 0)
        if cost > 0:
            return cost
        else:
            src = self.get_vertex(src)
            dst = self.get_vertex(dst)
            return self.edge_cost(src, dst)

    def _get_path_cost(self, path):
        """Shortcut function to get the cost function of aa given path"""
        edge_costs = []
        for i in range(len(path) - 1):
            src = path[i]
            dst = path[i + 1]
            edge_costs.append(self._get_edge_cost(src, dst))
        return sum(edge_costs)

    def add_path_req(self, req):
        assert isinstance(req, PathReq)
        self.reqs.append(req)

    def add_path_order_req(self, req):
        assert isinstance(req, PathOrderReq)
        self.reqs.append(req)

    def remove_unsat_paths(self):
        """
        Remoove one path from to the requirements if it's part of the unsat core.
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
            assert path_req, "Couldn't find path in requirements %s" % path
            self.removed_reqs.append(req)
            break
        self.reset_solver()
        return self.removed_reqs[-1]

    def synthesize(self, retries_before_rest=5, gen_path_increment=500):
        origianl_gen_paths = self.gen_paths

        # First try to synthesize with all requirements
        while not self.solve():
            # At this point any unsat is dirctly caused by the requirements
            # So remove one of them
            self.remove_unsat_paths()

        # Now the actual synthesis
        retries = 0
        while True:
            recompute = False
            # Check if all requirements are already satisfied
            # Using dijkstra algorithm
            for req in self.reqs:
                g_ospf = self.get_output_network_graph()
                computed = nx.shortest_path(g_ospf, req.path[0], req.path[-1], 'cost')
                if computed != req.path:
                    print "#" * 20
                    print "Required shortest path", req.path
                    print "Computed shortest path", computed
                    print "#" * 20
                    recompute = True
                    key = path_key(req.path[0], req.path[-1])
                    if key not in self.counter_examples:
                        self.counter_examples[key] = []
                    print "ADDING COUNTER example", computed
                    self.counter_examples[key].append(computed)
            if not recompute:
                break
            print "Recomputing ospf costs"
            retries += 1
            if retries > retries_before_rest:
                self.gen_paths += gen_path_increment
                print "RESET SOLVER and increaset the number of paths to", self.gen_paths, "#" * 10
                self.reset_solver()
            while not self.solve():
                print "UNSAT"
                print self.solver.unsat_core()
                removed_path = self.remove_unsat_paths()
                print "#" * 40
                print "Removed path from req", removed_path
                self.gen_paths = origianl_gen_paths
                print "#" * 40

        for req in self.reqs:
            path = req.path
            computed = nx.shortest_path(g_ospf, path[0], path[-1], 'cost')
            assert path == computed
        return True

    def print_costs(self):
        print "Synthesized OSPF Link Costs"
        for t in self.get_output_configs():
            print "\t", t
