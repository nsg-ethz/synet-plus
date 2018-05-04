#!/usr/bin/env python

"""
The slow version of the OSPF synthesizer.
"""

import logging
from timeit import default_timer as timer

import networkx as nx
import z3

from tekton.graph import NetworkGraph
from synet.utils.common import ECMPPathsReq
from synet.utils.common import KConnectedPathsReq
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


class OSPFSyn(SynthesisComponent):
    """
    Synthesizer for OSPF costs, this version validate the complete network model,
    that makes it a slow but complete version.
    """

    def __init__(self, network_graph, solver=None):
        """
        :param initial_configs: List of SetOSPFEdgeCost, ignores anything else
        :param network_graph: an instance of Networkx.DiGraph
        :param solver: optional instance of Z3 solver, otherwise create an new one
        """
        assert isinstance(network_graph, NetworkGraph)
        self.log = logging.getLogger('%s.%s' % (
            self.__module__, self.__class__.__name__))
        super(OSPFSyn, self).__init__([], network_graph, solver)
        self.ospf_graph = None
        # Requirements
        self.reqs = []

    def add_req(self, req):
        """
        Add new path requirement
        :param req: instance of PathReq
        :return: None
        """
        assert isinstance(req, Req)
        assert req.protocol == Protocols.OSPF
        self.reqs.append(req)

    def _get_edge_cost(self, src, dst):
        """Shortcut function to get the cost function of an edge"""
        return self.ospf_graph[src][dst]['cost']

    def _get_path_cost(self, path):
        """Return a sum of all the costs along the path"""
        edge_costs = []
        for i in range(len(path) - 1):
            src = path[i]
            dst = path[i + 1]
            edge_costs.append(self._get_edge_cost(src, dst))
        return sum(edge_costs)

    def _generate_simple_path(self, req):
        """Generate SMT for PathReq"""
        path = req.path
        src = path[0]
        dst = path[-1]
        path_cost = self._get_path_cost(path)
        # Enumerate all paths
        for rand_path in nx.all_simple_paths(self.network_graph, src, dst):
            if path != rand_path:
                simple_path_cost = self._get_path_cost(rand_path)
                self.solver.add(path_cost < simple_path_cost)

    def _generate_ecmp_path(self, req):
        """Generate SMT for ECMPPathsReq"""
        paths = [p.path for p in req.paths]
        src = paths[0][0]
        dst = paths[0][-1]
        path_cost = self._get_path_cost(paths[0])
        for path in paths:
            next_cost = self._get_path_cost(path)
            self.solver.add(path_cost == next_cost)
        for rand_path in nx.all_simple_paths(self.network_graph, src, dst):
            if rand_path not in paths:
                simple_path_cost = self._get_path_cost(rand_path)
                self.solver.add(path_cost < simple_path_cost)

    def _generate_ordered_path(self, req):
        """Generate SMT for PathOrderReq"""
        paths = [p.path for p in req.paths]
        src = paths[0][0]
        dst = paths[0][-1]
        for path0, path1 in zip(paths[0::1], paths[1::1]):
            p0_cost = self._get_path_cost(path0)
            p1_cost = self._get_path_cost(path1)
            self.solver.add(p0_cost < p1_cost)
        for rand_path in nx.all_simple_paths(self.network_graph, src, dst):
            if rand_path not in paths:
                for path in paths:
                    path_cost = self._get_path_cost(path)
                    simple_path_cost = self._get_path_cost(rand_path)
                    self.solver.add(path_cost < simple_path_cost)

    def _generate_connected_path(self, req):
        """Generate SMT for PathOrderReq"""
        paths = [p.path for p in req.paths]
        src = paths[0][0]
        dst = paths[0][-1]
        for rand_path in nx.all_simple_paths(self.network_graph, src, dst):
            if rand_path not in paths:
                for path in paths:
                    path_cost = self._get_path_cost(path)
                    simple_path_cost = self._get_path_cost(rand_path)
                    self.solver.add(path_cost < simple_path_cost)

    def push_requirements(self):
        """Push the requirements we care about to the solver"""
        # Load Graph
        self.ospf_graph = extract_ospf_graph(self.network_graph, self.log)
        load_graph_constrains(self.solver, self.ospf_graph)

        self.solver.push()
        start = timer()
        for req in self.reqs:
            if isinstance(req, PathReq):
                self._generate_simple_path(req)
            elif isinstance(req, ECMPPathsReq):
                self._generate_ecmp_path(req)
            elif isinstance(req, PathOrderReq):
                self._generate_ordered_path(req)
            elif isinstance(req, KConnectedPathsReq):
                self._generate_connected_path(req)
            else:
                raise ValueError("Unrecognized path requirement %s" % req)
        end = timer()
        return end - start

    def get_output_configs(self):
        """Returns list of (src, dst, cost)"""
        return get_output_configs(self.solver.model(), self.ospf_graph)

    def get_output_network_graph(self):
        """Return OSPF graph annotated with synthesized costs"""
        return get_output_network_graph(self.solver.model(), self.ospf_graph)

    def get_output_routing_graphs(self):
        """
        Returns one graph per each destination network.
        """
        return self.get_output_network_graph()

    def update_network_graph(self):
        """Set concrete costs on the network graph"""
        configs = self.get_output_configs()
        for src, dst, cost in configs:
            self.network_graph.set_edge_ospf_cost(src, dst, cost)
        synthesize_ospf_announce(self.network_graph, self.ospf_graph, self.reqs)
