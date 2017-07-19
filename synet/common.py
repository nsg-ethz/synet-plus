"""
Common functions for synthesis
"""


import z3
import networkx as nx
from abc import ABCMeta
from abc import abstractmethod
from enum import Enum
from collections import namedtuple
from networkx.drawing import nx_pydot
from timeit import default_timer as timer



# Keys for annotations used in nx graphs
NODE_TYPE = '"node"'
EXTERNAL_NODE_TYPE = '"external_node"'
INTERFACE_TYPE = '"interface"'
NETWORK_TYPE = '"network"'
INTERNAL_EDGE = '"internal"'
LINK_EDGE = '"link"'
StaticRoutes = 'StaticRoutes'
OSPFRoutes = 'OSPFRoutes'
OSPFBestRoutes = 'OSPFBestRoutes'
OSPFBestRoutesCost = 'OSPFBestRoutesCost'
FwdRoutes = 'FwdRoutes'
VERTEX_TYPE = 'vertex_type'
EDGE_TYPE = 'edge_type'
ANNOUNCEMENT_EDGE='annoucement_edge'
ANNOUNCED_NETWORK='announced_network'
PEER_TYPE="peer"
ORIGIN_TYPE="as_origin"
AS_NUM = 'AS'


class PathProtocols(Enum):
    """List all protocols"""
    Forwarding = 1
    Static = 2
    OSPF = 3
    BGP = 4
    ASPATH = 5


# Define requirements signature.
(z3_proto, all_protocols) = z3.EnumSort('Protocols', ['Static',  'OSPF', 'BGP'])
z3_static, z3_ospf, z3_bgp = all_protocols

PathReq = namedtuple('PathRequirement', ['protocol', 'dst_net', 'path', 'cost'])
PathOrderReq = namedtuple('PathOrderRequirement', ['protocol', 'dst_net', 'paths', 'cost'])
NotPathReq = namedtuple('NotPathRequirement', ['protocol', 'dst_net', 'path'])
ReachabilityReq = namedtuple('ReachabilityRequirement',
                             ['protocol', 'dst_net', 'src', 'dst',
                              'min_k', 'max_k'])
NotReachabilityReq = namedtuple('NotReachabilityRequirement',
                                ['protocol', 'dst_net', 'src', 'dst',
                                 'min_k', 'max_k'])
WayPointReq = namedtuple('WayPointRequirement',
                         ['protocol', 'dst_net', 'vertices'])
NotWayPointReq = namedtuple('NotWayPointRequirement',
                            ['protocol', 'dst_net', 'vertices'])


# OSPF Edge cost
SetOSPFEdgeCost = namedtuple('SetOSPFEdgeCost', ['src', 'dst', 'cost'])

# Define common functions
# Data types
def z3_is_node(vertex):
    """Returns True if the vertex is of type node (aka router)"""
    return z3.Function('IsNode', vertex, z3.BoolSort())


def z3_is_interface(vertex):
    """Returns True if the vertex is of type interface"""
    return z3.Function('IsInterface', vertex, z3.BoolSort())


def z3_is_network(vertex):
    """Returns True if the vertex is of type network"""
    return z3.Function('IsNetwork', vertex, z3.BoolSort())

def z3_is_bgp_node(vertex):
    """Returns True if the vertex is configured to be BGP router"""
    return z3.Function('IsBGPNode', vertex, z3.BoolSort())


# Simulating input configurations
def z3_set_node(vertex):
    """Add a node"""
    return z3.Function('SetNode', vertex, z3.BoolSort())


def z3_set_interface(vertex):
    """Assign an interface to a router"""
    return z3.Function('SetInterface', vertex, vertex, z3.BoolSort())


def z3_set_network(vertex):
    """Add a network"""
    return z3.Function('SetNetwork', vertex, vertex, z3.BoolSort())


def z3_set_link(vertex):
    """Creates a physical ethernet link between two interfaces"""
    return z3.Function('SetLink', vertex, vertex, z3.BoolSort())

def z3_edge(vertex):
    """True is an edge exists between two vertices"""
    return z3.Function('Edge', vertex, vertex, z3.BoolSort())


def datatypes_unique(common_type, type_checkers=[]):
    ret = []
    v = z3.Const('v', common_type)
    for check1 in type_checkers:
        for check2 in type_checkers:
            if str(check1) == str(check2): continue
            ret.append(
                z3.ForAll([v], z3.Not(z3.And(check1(v), check2(v)))))
    return ret


def datatype_route(route, is_network, is_node, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                route(v1, v2, v3),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3))))))
    c2 = z3.ForAll([v1, v2, v3], z3.Not(z3.And(route(v1, v2, v3), v2 == v3)))
    return [c, c2]


def datatype_route_protocol(route, is_network, is_node, is_protocol, protocol_type, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    v4 = z3.Const('v4', protocol_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                route(v1, v2, v3, v4),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3)),
                    z3.Not(is_protocol(v4))))))
    c2 = z3.ForAll([v1, v2, v3], z3.Not(z3.And(route(v1, v2, v3, v4), v2 == v3)))
    return [c, c2]


def datatype_route_cost(route, is_network, is_node, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    v4 = z3.Const('v4', z3.IntSort())
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                route(v1, v2, v3, v4),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3))))))
    #c2 = z3.ForAll([v1, v2, v3], z3.Not(z3.And(route(v1, v2, v3, v4), v2 == v3)))
    c2 = z3.ForAll([v1, v2, v3, v4], z3.Implies(v2 == v3, z3.Not(route(v1, v2, v3, v4))))
    return [c, c2]


def datatype_route_bgp(route, is_network, is_node, is_as_path_length, as_path_type, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    v4 = z3.Const('v4', as_path_type)
    v5 = z3.Const('v5', z3.IntSort())
    v6 = z3.Const('v6', z3.IntSort())
    c = z3.ForAll(
        [v1, v2, v3, v4, v5, v6],
        z3.Not(
            z3.And(
                route(v1, v2, v3, v4, v5, v6),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3)),
                    z3.Not(is_as_path_length(v4, v5))))))
    c2 = z3.ForAll([v1, v2, v3, v4, v5, v6], z3.Not(z3.And(route(v1, v2, v3, v4, v5, v6), v2 == v3)))
    return [c2]
    return [c, c2]


def datatype_network_node_interface(func, is_network, is_node, is_interface, vertex_type):
    """
    Constrain a function  with (network, node, interface) signature
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                func(v1, v2, v3),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_interface(v3))))))
    return [c]


def datatype_network_interface_node(func, is_network, is_node, is_interface, vertex_type):
    """
    Constrain a function  with (node, interface) signature
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                func(v1, v2, v3),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_interface(v2)),
                    z3.Not(is_node(v3))))))
    return [c]


def z3_interface_links(vertex, is_interface, edge, bidir=True):
    v1, v2, v3, v4 = z3.Consts('v1 v2 v3 v4', vertex)
    # Make sure we don't have more than one outgoing link from each interface
    # to another interface
    outgoing = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                is_interface(v1),
                is_interface(v2),
                is_interface(v3),
                z3.Distinct(v1, v2, v3),
                edge(v1, v2),
                edge(v1, v3)
            )))

    # Make sure we don't have more than one incoming link from each interface
    # to another interface
    incoming = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                is_interface(v1),
                is_interface(v2),
                is_interface(v3),
                z3.Distinct(v1, v2, v3),
                edge(v2, v1),
                edge(v3, v1)
            )))

    # We're modeling an ethernet network, so we get the second link for free
    if bidir:
        bidir_c = z3.ForAll(
            [v1, v2],
            z3.Implies(
                z3.And(
                    is_interface(v1),
                    is_interface(v2),
                    edge(v1, v2)
                ),
                edge(v2, v1)
            ))
    constraints = [outgoing, incoming]
    if bidir:
        constraints.append(bidir_c)
    return constraints


def get_vertices(g):
    """
    Takes a networkx DiGraph and returns list
    of node_names, interface_names, network_names
    """
    assert isinstance(g, nx.DiGraph)
    node_names = []
    interface_names = []
    network_names = []
    announced_networks = []

    for vertex, attrs in g.nodes(True):
        v_type = attrs.get(VERTEX_TYPE)
        if v_type == NODE_TYPE:
            node_names.append(vertex)
        elif v_type == INTERFACE_TYPE:
            interface_names.append(vertex)
        elif v_type == NETWORK_TYPE:
            network_names.append(vertex)
        elif v_type == ANNOUNCED_NETWORK:
            announced_networks.append(vertex)
        else:
            raise ValueError("Unknown vertex_type '%s for %s'" % (v_type, vertex))

    # Avoid duplicates in the inputs
    node_names = list(set(node_names))
    interface_names = list(set(interface_names))
    network_names = list(set(network_names))
    return node_names, interface_names, network_names, announced_networks


def draw(g, out):
    """
    Write the graph in a dot file.

    This function creates a shallow copy of the graph and removes
    all unnecessary attributes for drawing, otherwise dotx wont be able to
    visualize the graph.
    """
    def _allowed_attrs(attrs):
        new_attrs = {}
        if attrs.get('shape', None):
            new_attrs['shape'] = attrs['shape']
        if attrs.get('style', None):
            new_attrs['style'] = attrs['style']
        if not attrs.get('cost', None) is None:
            new_attrs['label'] = attrs['cost']
        return new_attrs
    clean_g = g.copy()
    for n, attrs in clean_g.nodes(True):
        clean_g.node[n] = _allowed_attrs(attrs)
    for src, dst, attrs in clean_g.edges(data=True):
        clean_g.edge[src][dst] = _allowed_attrs(attrs)
    nx_pydot.write_dot(clean_g, out)


class SynthesisComponent(object):
    """
    The interface for each component.
    """
    __metaclass__ = ABCMeta

    valid_inputs = ()
    def __init__(self, initial_configs, network_graph, solver=None):
        if not network_graph:
            network_graph = nx.DiGraph()
        if not initial_configs:
            initial_configs = []

        self.network_graph = network_graph
        self.initial_configs = initial_configs
        if not solver:
            solver = z3.Solver()
        self.solver = solver
        # Requirements for the synthesis
        self.reqs = []

    def _get_names(self, configs, graph):
        node_names, interface_names, network_names, announced_networks = get_vertices(graph)
        return node_names, interface_names, network_names, announced_networks

    def _create_vertices(self, vertex_name, configs, graph, ignore_network=False, ignore_nonlocal=True):
        node_names, interface_names, network_names, announced_networks = self._get_names(
            configs, graph)
        self.node_names = node_names
        self.interface_names = interface_names
        self.network_names = network_names
        if ignore_network:
            all_names = node_names + interface_names + announced_networks
        else:
            all_names = node_names + interface_names + network_names + announced_networks
        (vertex, all_vertices) = z3.EnumSort(vertex_name, all_names)
        self.vertex = vertex
        self.all_vertices = all_vertices
        self.name_to_vertex = dict((str(v), v) for v in self.all_vertices)
        self.nodes = [self.get_vertex(name) for name in node_names]
        self.interfaces = [self.get_vertex(name) for name in interface_names]
        if not ignore_network:
            self.networks = [self.get_vertex(name) for name in network_names]

    def get_vertex(self, name):
        """Takes a name string and returns the corresponding Z3 object"""
        if isinstance(name, int):
            name = str(name)
        if isinstance(name, basestring):
            return self.name_to_vertex[name]
        else:
            return name

    def get_name(self, vetrex):
        """Takes a Z3 object and returns the corresponding name string """
        inv_map = {v: k for k, v in self.name_to_vertex.items()}
        return inv_map[vetrex]

    def solve(self):
        """
        Calls Z3 solve the constraints and the requirements.
        If Z3 comes with a valid assignment then the model is kept.
        Otherwise, we remove the requirements from the model.
        """
        t1 = timer()
        self.push_requirements()
        t2 = timer()
        result = self.solver.check()
        t3 = timer()
        treqs = t2 - t1
        tz3 = t3 - t2
        ttotal = t2 - t1
        print "%s: Pushing requirements time: %s" % (self.__class__.__name__, treqs)
        print "%s: Z3 time: %s" % (self.__class__.__name__, tz3)
        print "%s: Total synthesizes time: %s" % (self.__class__.__name__, ttotal)
        if result == z3.sat:
            return True
        else:
            self.solver.pop()
            return False

    @abstractmethod
    def get_output_network_graph(self):
        """
        Returns the network graph, the graph might be annotated with routing
        information.
        solve() must be successfully called before
        """
        raise NotImplementedError()

    @abstractmethod
    def get_output_routing_graphs(self):
        """
        Returns a flow graph for each destination network.
        solve() must be successfully called before
        """
        raise NotImplementedError()

    @abstractmethod
    def get_output_configs(self):
        """
         Return a list of configurations for the model.
         solve() must be successfully called before
        """
        raise NotImplementedError()

    @abstractmethod
    def push_requirements(self):
        """
        Add the requirements to the solver
        """
        raise NotImplementedError()

    def _get_edge_attributes(self, src, dst):
        """
        Helper method to annotate edges in the output graph.
        """
        attrs = {}
        if not isinstance(src, basestring):
            src = self.get_name(src)
        if not isinstance(dst, basestring):
            dst = self.get_name(dst)
        if src in self.interface_names and dst in self.interface_names:
            attrs['edge_type'] = INTERNAL_EDGE
            attrs['style'] = '"dashed"'
        elif src in self.network_names or dst in self.network_names:
            attrs['edge_type'] = NETWORK_TYPE
            attrs['style'] = '"dashed"'
        return attrs

    def _get_vertex_attributes(self, g, vertex):
        """
        Helper method to annotate vertices in the output graph.
        """
        name = vertex
        if not isinstance(name, basestring):
            name = self.get_name(name)
        if g and g.has_node(name):
            attrs = g.node[name]
        else:
            attrs = {}
        if OSPFBestRoutes not in attrs:
            attrs[OSPFBestRoutes] = {}
        if OSPFRoutes not in attrs:
            attrs[OSPFRoutes] = {}
        if StaticRoutes not in attrs:
            attrs[StaticRoutes] = {}
        if FwdRoutes not in attrs:
            attrs[FwdRoutes] = {}
        if name in self.interface_names:
            attrs['shape'] = 'box'
            attrs[VERTEX_TYPE] = INTERFACE_TYPE
        elif name in self.network_names:
            attrs['shape'] = 'doublecircle'
            attrs[VERTEX_TYPE] = NETWORK_TYPE
        else:
            attrs['shape'] = 'oval'
            attrs[VERTEX_TYPE] = NODE_TYPE
        return attrs