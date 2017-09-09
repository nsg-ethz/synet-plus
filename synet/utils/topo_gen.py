#!/usr/bin/env python
"""
Network topology generators
"""

import networkx as nx

from synet.utils.common import INTERFACE_TYPE
from synet.utils.common import INTERNAL_EDGE
from synet.utils.common import LINK_EDGE
from synet.utils.common import NETWORK_TYPE
from synet.utils.common import NODE_TYPE
from synet.utils.common import VERTEX_TYPE
from synet.utils.smt_context import VALUENOTSET

from synet.topo.graph import NetworkGraph


__author__ = "Ahmed El-Hassany"
__email__ = "eahmed@ethz.ch"


def gen_grid_topo_no_iface(m, n, nets_per_router):
    """
    Generate 2D m*n routers topology
    each router is connected to `net_per_router` networks
    """
    g = nx.DiGraph()
    rows = range(1, m + 1)
    columns = range(1, n + 1)
    networks = range(1, nets_per_router + 1)
    for i in rows:
        for j in columns:
            node = 'R%d%d' % (i, j)
            g.add_node(node, **{VERTEX_TYPE: NODE_TYPE})
            for n in networks:
                net = 'N%d%d_%d' % (i, j, n)
                g.add_node(net, **{VERTEX_TYPE: NETWORK_TYPE})
                g.add_edge(net, node, edge_type=NETWORK_TYPE)
                g.add_edge(node, net, edge_type=NETWORK_TYPE)

    for i in rows:
        for j in columns:
            # Connect rows
            if j > 1:
                iface1 = 'R%d%d' % (i, j)
                iface2 = 'R%d%d' % (i, j - 1)
                g.add_edge(iface1, iface2, edge_type=LINK_EDGE)
                g.add_edge(iface2, iface1, edge_type=LINK_EDGE)
            # Connect columns
            if i > 1:
                iface1 = 'R%d%d' % (i, j)
                iface2 = 'R%d%d' % (i - 1, j)
                g.add_edge(iface1, iface2, edge_type=LINK_EDGE)
                g.add_edge(iface2, iface1, edge_type=LINK_EDGE)

    return g


def gen_i2_topology(nets_per_router):
    """
    Generate topology similar to Internet2
    # Reference: http://www.internet2.edu/media/medialibrary/2013/10/01/I2-Network-Infrastructure-Layer-3.pdf
    """
    g = nx.DiGraph()
    routers = {}
    routers['SEAT'] = 0
    routers['SALT'] = 0
    routers['LAX'] = 0
    routers['KANS'] = 0
    routers['HOUS'] = 0
    routers['ATL'] = 0
    routers['CHIC'] = 0
    #routers['CLEV'] = 0
    routers['DC'] = 0
    routers['NYC'] = 0

    connected = [
        ('SEAT', 'LAX'),
        ('SEAT', 'SALT'),
        ('SEAT', 'CHIC'),

        ('LAX', 'SALT'),
        ('LAX', 'HOUS'),

        ('SALT', 'KANS'),

        ('KANS', 'CHIC'),
        ('KANS', 'HOUS'),

        #('CHIC', 'CLEV'),
        ('CHIC', 'ATL'),
        ('CHIC', 'DC'),
        ('CHIC', 'NYC'),

        ('HOUS', 'ATL'),

        ('ATL', 'DC'),

        #('CLEV', 'DC'),
        #('CLEV', 'NYC'),

        ('NYC', 'DC'),
    ]

    for router in routers:
        g.add_node(router, **{VERTEX_TYPE: NODE_TYPE})

    # Add networks
    for router in routers:
        for i in range(1, nets_per_router + 1):
            net = "%s_N_%d" % (router, i)
            g.add_node(net, **{VERTEX_TYPE: NETWORK_TYPE})
            g.add_edge(net, router, edge_type=NETWORK_TYPE)
            g.add_edge(router, net, edge_type=NETWORK_TYPE)

    # Add interfaces
    for src, dst in connected:
        routers[src] += 1
        routers[dst] += 1
        i_src = routers[src]
        i_dst = routers[dst]
        siface = "%s_I_%s" % (src, i_src)
        diface = "%s_I_%s" % (dst, i_dst)

        g.add_node(siface, **{VERTEX_TYPE: INTERFACE_TYPE})
        g.add_edge(src, siface, edge_type=INTERNAL_EDGE)
        g.add_edge(siface, src, edge_type=INTERNAL_EDGE)

        g.add_node(diface, **{VERTEX_TYPE: INTERFACE_TYPE})
        g.add_edge(dst, diface, edge_type=INTERNAL_EDGE)
        g.add_edge(diface, dst, edge_type=INTERNAL_EDGE)

        g.add_edge(siface, diface, edge_type=LINK_EDGE)
        g.add_edge(diface, siface, edge_type=LINK_EDGE)
    return g


def gen_overview_topology():
    """
    Generate topology used in the paper overview
    Four routers a mesh topology
    """
    g = nx.DiGraph()
    routers = {}
    routers['A'] = 0
    routers['B'] = 0
    routers['C'] = 0
    routers['D'] = 0

    connected = [
        ('A', 'B'),
        ('A', 'C'),
        ('A', 'D'),

        ('B', 'C'),
        ('B', 'D'),

        ('C', 'D'),
    ]

    for router in routers:
        g.add_node(router, **{VERTEX_TYPE: NODE_TYPE})

    # Add networks

    for router, net in [('D', 'N1'), ('D', 'N2'), ('C', 'C_BGP'), ('B', 'B_BGP')]:
        #net = "%s_N_%d" % (router, i)
        g.add_node(net, **{VERTEX_TYPE: NETWORK_TYPE})
        g.add_edge(net, router, edge_type=NETWORK_TYPE)
        g.add_edge(router, net, edge_type=NETWORK_TYPE)

    # Add interfaces
    for src, dst in connected:
        routers[src] += 1
        routers[dst] += 1
        i_src = routers[src]
        i_dst = routers[dst]
        siface = "%s_I_%s" % (src, i_src)
        diface = "%s_I_%s" % (dst, i_dst)

        g.add_node(siface, **{VERTEX_TYPE: INTERFACE_TYPE})
        g.add_edge(src, siface, edge_type=INTERNAL_EDGE)
        g.add_edge(siface, src, edge_type=INTERNAL_EDGE)

        g.add_node(diface, **{VERTEX_TYPE: INTERFACE_TYPE})
        g.add_edge(dst, diface, edge_type=INTERNAL_EDGE)
        g.add_edge(diface, dst, edge_type=INTERNAL_EDGE)

        g.add_edge(siface, diface, edge_type=LINK_EDGE)
        g.add_edge(diface, siface, edge_type=LINK_EDGE)
    return g


def read_topology_zoo(filename):
    assert filename.endswith('.graphml'), 'wrong file type "%s"' % filename
    graphml = nx.read_graphml(filename)
    g = nx.DiGraph()
    lbl_map = {}
    for node in graphml.nodes():
        label = str(graphml.node[node]['label'])
        # remove whitespaces
        label = label.replace(' ', 'TT')
        if label == 'None':
            label = 'NodeID%s' % node
        if g.has_node(label):
            label = '%sID%s' % (label, node)
        assert not g.has_node(label), 'Duplicate node %s with label %s' % (node, label)
        lbl_map[node] = label
        g.add_node(label, **{VERTEX_TYPE: NODE_TYPE})
    for src, dst in graphml.edges():
        g.add_edge(lbl_map[src], lbl_map[dst], edge_type=INTERNAL_EDGE)
        g.add_edge(lbl_map[dst], lbl_map[src], edge_type=INTERNAL_EDGE)
    return g


def read_topology_zoo_netgraph(filename):
    assert filename.endswith('.graphml'), 'wrong file type "%s"' % filename
    graphml = nx.read_graphml(filename)
    g = NetworkGraph()
    lbl_map = {}
    for node in graphml.nodes():
        label = str(graphml.node[node]['label'])
        # remove whitespaces
        label = label.replace(' ', 'TT')
        if label == 'None':
            label = 'NodeID%s' % node
        if g.has_node(label):
            label = '%sID%s' % (label, node)
        assert not g.has_node(label), 'Duplicate node %s with label %s' % (node, label)
        lbl_map[node] = label
        g.add_router(label)
    for src, dst in graphml.edges():
        g.add_router_edge(lbl_map[src], lbl_map[dst])
        g.add_router_edge(lbl_map[dst], lbl_map[src])
    return g


def gen_mesh(mesh_size, asnum=None):
    """Generate a full mesh topology"""
    g_phy = NetworkGraph()
    for num in range(mesh_size):
        node = 'R%d' % (num + 1)
        g_phy.add_router(node)
        if asnum:
            g_phy.set_bgp_asnum(node, asnum)

    for src in g_phy.nodes():
        for dst in g_phy.nodes():
            if src == dst:
                continue
            g_phy.add_router_edge(src, dst)
            if asnum:
                if dst not in g_phy.get_bgp_neighbors(src):
                    g_phy.add_bgp_neighbor(router_a=src,
                                           router_b=dst,
                                           router_a_iface=VALUENOTSET,
                                           router_b_iface=VALUENOTSET)
    return g_phy
