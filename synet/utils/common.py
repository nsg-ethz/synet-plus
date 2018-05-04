"""
Common functions for synthesis
"""

from abc import ABCMeta
from abc import abstractmethod
from collections import Iterable
from collections import namedtuple
from enum import Enum
from timeit import default_timer as timer

import networkx as nx
import z3
from networkx.drawing import nx_pydot

from tekton.graph import NetworkGraph


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


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
ANNOUNCEMENT_EDGE = 'annoucement_edge'
ANNOUNCED_NETWORK = 'announced_network'
PEER_TYPE = "peer"
ORIGIN_TYPE = "as_origin"
AS_NUM = 'AS'


def flatten(data):
    """
    takes [['A', 'B', 'C'], ['A', 'B']] and return ['A', 'B', 'C', 'A', 'B']
    :param data: list of lists
    :return: flat list
    """
    return [item for sublist in data for item in sublist]


def path_exists(path, graph):
    """Return True if the path exists in the graph"""
    return False not in [graph.has_edge(x, y) for x, y in zip(path[0::1], path[1::1])]


class Protocols(Enum):
    """List all protocols"""
    Forwarding = 1
    Static = 2
    OSPF = 3
    BGP = 4
    ASPATH = 5


# Define requirements signature.
class Req(object):
    """Abstract Requirement"""
    def __init__(self):
        raise NotImplementedError()


class PathReq(Req):
    """Specify single path Requirement"""

    def __init__(self, protocol, dst_net, path, strict):
        """

        :param protocol: instance of Protocols
        :param dst_net: The destination traffic class
        :param path: List of ordered routers in the graph
        :param strict: If True, traffic should be dropped when path is not available
        """
        assert isinstance(protocol, Protocols)
        assert isinstance(strict, bool)
        assert isinstance(path, Iterable)
        self.protocol = protocol
        self.dst_net = dst_net
        self.path = path
        self.strict = strict

    def __eq__(self, other):
        props = ['protocol', 'dst_net', 'path', 'strict']
        for prop in props:
            if getattr(self, prop) != getattr(other, prop, None):
                return False
        return True

    def __repr__(self):
        return 'PathReq(%s, "%s", %s, %s)' % (
            self.protocol, self.dst_net, self.path, self.strict)


class ECMPPathsReq(Req):
    """Equal cost paths"""

    def __init__(self, protocol, dst_net, paths, strict):
        """
        :param protocol: instance of Protocols
        :param dst_net: The destination traffic class
        :param paths: Set of PathReq (must have same dst_net and strict=False)
        :param strict: If True, traffic should be dropped when path is not available
        """
        assert isinstance(protocol, Protocols)
        assert isinstance(strict, bool)
        assert isinstance(paths, Iterable)
        for path in paths:
            assert isinstance(path, PathReq)
            assert path.strict == False
            assert path.dst_net == dst_net
        self.protocol = protocol
        self.dst_net = dst_net
        self.paths = paths
        self.strict = strict

    def __eq__(self, other):
        props = ['protocol', 'dst_net', 'paths', 'strict']
        for prop in props:
            if getattr(self, prop) != getattr(other, prop, None):
                return False
        return True

    def __repr__(self):
        return "ECMPPathsReq(%s, '%s', %s, %s)" % (
            self.protocol, self.dst_net, self.paths, self.strict)


class KConnectedPathsReq(Req):
    """Connectivity among certain paths with no preference"""

    def __init__(self, protocol, dst_net, paths, strict):
        """
        :param protocol: instance of Protocols
        :param dst_net: The destination traffic class
        :param paths: Set of PathReq (must have same dst_net and strict=False)
        :param strict: If True, traffic should be dropped when path is not available
        """
        assert isinstance(protocol, Protocols)
        assert isinstance(strict, bool)
        assert isinstance(paths, Iterable)
        for path in paths:
            assert isinstance(path, PathReq)
            assert path.strict == False
            assert path.dst_net == dst_net
        self.protocol = protocol
        self.dst_net = dst_net
        self.paths = paths
        self.strict = strict

    def __eq__(self, other):
        props = ['protocol', 'dst_net', 'paths', 'strict']
        for prop in props:
            if getattr(self, prop) != getattr(other, prop, None):
                return False
        return True

    def __eq__(self, other):
        props = ['protocol', 'dst_net', 'paths', 'strict']
        for prop in props:
            if getattr(self, prop) != getattr(other, prop, None):
                return False
        return True

    def __repr__(self):
        return "KConnectedPathsReq(%s, '%s', %s, %s)" % (
            self.protocol, self.dst_net, self.paths, self.strict)


class PreferredPathReq(Req):
    """
    One path is preferred then when it's not available one of the kconnected
    will be chosen arbitrary.
    """

    def __init__(self, protocol, dst_net, preferred, kconnected, strict):
        """
        :param protocol: instance of Protocols
        :param dst_net: The destination traffic class
        :param preferred: PathReq that is the most preferred
        :param kconnected: Set of PathReq (must have same dst_net and strict=False)
        :param strict: If True, traffic should be dropped when path is not available
        """
        assert isinstance(protocol, Protocols)
        assert isinstance(strict, bool)
        assert isinstance(preferred, PathReq)
        assert preferred.dst_net == dst_net
        assert preferred.strict == False
        assert isinstance(kconnected, KConnectedPathsReq)
        assert kconnected.dst_net == dst_net
        assert kconnected.strict == False
        self.protocol = protocol
        self.dst_net = dst_net
        self.preferred = preferred
        self.kconnected = kconnected
        self.strict = strict

    def __eq__(self, other):
        props = ['protocol', 'dst_net', 'preferred', 'kconnected', 'strict']
        for prop in props:
            if getattr(self, prop) != getattr(other, prop, None):
                return False
        return True

    def __repr__(self):
        return "PreferredPathReq(%s, '%s', %s, %s, %s)" % (
            self.protocol, self.dst_net, self.preferred,
            self.kconnected, self.strict)


class PathOrderReq(Req):
    """Strict Path Ordering"""

    def __init__(self, protocol, dst_net, paths, strict):
        """
        :param protocol: instance of Protocols
        :param dst_net: The destination traffic class
        :param paths: Set of PathReq (must have same dst_net and strict=False)
        :param strict: If True, traffic should be dropped when path is not available
        """
        assert isinstance(protocol, Protocols)
        assert isinstance(strict, bool)
        assert isinstance(paths, Iterable)
        for path in paths:
            assert isinstance(path, PathReq)
            assert path.strict == False
            assert path.dst_net == dst_net
        self.protocol = protocol
        self.dst_net = dst_net
        self.paths = paths
        self.strict = strict

    def __repr__(self):
        return "PathOrderReq(%s, '%s', %s, %s)" % (
            self.protocol, self.dst_net, self.paths, self.strict)


# OSPF Edge cost
SetOSPFEdgeCost = namedtuple('SetOSPFEdgeCost', ['src', 'dst', 'cost'])

BestOSPFRoute = namedtuple('BestOSPFRoute', ['net', 'src', 'nxt', 'cost'])



def generate_second_path(G, path, random_obj):
    """
    Given a path between source target fail one edge randomly
    and return find the next best path
    """
    new_g = G.copy()
    src = path[0]
    dst = path[-1]
    counter = 0
    while True:
        edges = zip(path[0::1], path[1::1])
        candidate = random_obj.choice(edges)
        new_g.remove_edge(*candidate)
        if new_g.has_edge(src, dst):
            break
        else:
            counter += 1
            if counter > 5:
                return None
            new_g.add_edge(*candidate)
    counter = nx.shortest_path(new_g, src, dst, 'test-weight')
    new_g.add_edge(*candidate)
    return counter


def random_requirement_path(G, source, target, random_obj, tmp_weight_name):
    """Generate path requirements with a guaranteed solution"""
    max_size = 100
    for src, dst in G.edges():
        if tmp_weight_name not in G[src][dst]:
            w = random_obj.randint(1, max_size)
            G[src][dst][tmp_weight_name] = w
    return nx.shortest_path(G, source, target, tmp_weight_name)


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


def get_vertices(g):
    """
    Takes a NetworkGraph and returns list
    of node_names, interface_names, network_names
    """
    assert isinstance(g, NetworkGraph)
    node_names = []
    interface_names = []
    network_names = []
    announced_networks = []

    for vertex in g.nodes():
        if g.is_router(vertex):
            node_names.append(vertex)
        # elif g.is_interface(vertex):
        #    interface_names.append(vertex)
        elif g.is_network(vertex):
            network_names.append(vertex)
        # elif g.is_network(vertex):
        #    announced_networks.append(vertex)
        else:
            raise ValueError("Unknown vertex_type for %s'" % (vertex))

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
            network_graph = NetworkGraph()
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
        name = self.__class__.__name__
        print "%s: Pushing requirements time: %s" % (name, treqs)
        print "%s: Z3 time: %s" % (name, tz3)
        print "%s: Total synthesizes time: %s" % (name, ttotal)
        print "%s: sat result: %s" % (name, result)
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
