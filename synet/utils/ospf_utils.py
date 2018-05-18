"""
Common utilities used in the OSPF boxes
"""

from ipaddress import ip_network
import networkx as nx
import z3

from synet.utils.common import Protocols
from synet.utils.networks import gather_networks
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import is_symbolic


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


# Special network that will announce all directly connected works
ALL_V4_NET = ip_network(u"0.0.0.0/0")


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
        if network_graph.is_local_router(node) and network_graph.is_ospf_enabled(node):
            ospf_graph.add_node(node)
    for src, dst in network_graph.edges():
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
    for src, dst in graph.edges():
        cost = graph[src][dst]['cost']
        if is_empty(cost):
            cost = None
        if is_symbolic(cost):
            solver.add(cost > 0)


def get_output_configs(model, ospf_graph):
    """Returns list of (src, dst, cost)"""
    outputs = []
    for src, dst in ospf_graph.edges():
        cost = ospf_graph[src][dst]['cost']
        if is_symbolic(cost):
            cost = model.eval(cost).as_long()
            ospf_graph[src][dst]['cost'] = cost
        outputs.append((src, dst, cost))
    return outputs


def get_output_network_graph(model, ospf_graph):
    """Return OSPF graph annotated with synthesized costs"""
    configs = get_output_configs(model, ospf_graph)
    out_graph = ospf_graph.copy()
    for src, dst, cost in configs:
        out_graph[src][dst]['cost'] = cost
    return out_graph


def synthesize_ospf_announce(network_graph, ospf_graph, reqs):
    """
    This is very simple with mostly add (unless 0.0.0.0 is announced)
    TODO: More work to consider existing configs and longest prefix matches
    """
    # Collect all announced network
    node_announces = gather_networks(reqs, protocols=[Protocols.OSPF])
    for node in ospf_graph.nodes():
        curr_announced = network_graph.get_ospf_networks(node)
        if ALL_V4_NET in curr_announced:
            # This node already announced everything, no need
            continue
        neighbor_addrs = []
        for neighbor in ospf_graph.neighbors(node):
            iface = network_graph.get_edge_iface(node, neighbor)
            iface_addr = network_graph.get_iface_addr(node, iface)
            neighbor_addrs.append(iface_addr.network)
        all_addrs = node_announces.get(node, []) + neighbor_addrs
        for addr in all_addrs:
            if addr in curr_announced:
                continue
            network_graph.add_ospf_network(node, addr, '0.0.0.0')
