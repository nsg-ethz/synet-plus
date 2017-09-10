"""
Common utilities used in the OSPF boxes
"""

import networkx as nx
import z3

from synet.utils.smt_context import is_empty
from synet.utils.smt_context import is_symbolic

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


def extract_ospf_graph(network_graph, log):
    """
    Extract a sub graph from the network graph that is relevant to the
    OSPF Computations
    :param network_graph: NetworkGraph
    :param log: logger
    :return: nx.DiGraph() of the OSPF enabled subgraph
    """
    ospf_graph = nx.DiGraph()
    # Only local routers
    for node in network_graph.nodes():
        if network_graph.is_local_router(node):
            ospf_graph.add_node(node)
    for src, dst in network_graph.edges_iter():
        # First skip an edge that is not connecting
        # two OSPF enabled routers
        if not network_graph.is_ospf_enabled(src):
            continue
        if not network_graph.is_ospf_enabled(dst):
            continue
        cost = network_graph.get_edge_ospf_cost(src, dst)
        if not cost:
            log.warn("Edge OSPF cost (%s, %s) is None", src, dst)
        if is_empty(cost):
            cost = None
        if not cost:
            cost = z3.Const("cost_%s_%s" % (src, dst), z3.IntSort())
        ospf_graph.add_edge(src, dst, cost=cost)
    return ospf_graph


def load_graph_constrains(solver, graph):
    """Add constrains specific to the OSPF graph"""
    for src, dst in graph.edges_iter():
        cost = graph[src][dst]['cost']
        if is_empty(cost):
            cost = None
        if is_symbolic(cost):
            solver.add(cost > 0)


def get_output_configs(model, ospf_graph):
    """Returns list of (src, dst, cost)"""
    outputs = []
    for src, dst in ospf_graph.edges_iter():
        cost = ospf_graph[src][dst]['cost']
        if is_symbolic(cost):
            cost = model.eval(cost).as_long()
            ospf_graph[src][dst]['cost'] = cost
        outputs.append((src, dst, cost))
    return outputs


def get_output_network_graph(model, ospf_graph):
    """Return OSPF graph annotated with synthesized costs"""
    configs = get_output_configs(model, ospf_graph)
    for src, dst, cost in configs:
        ospf_graph[src][dst]['cost'] = cost
    return ospf_graph
