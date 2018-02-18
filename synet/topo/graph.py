#!/usr/bin/env python
"""
Extension of the networkx.DiGraph to allow easy synthesis
and network specific annotations.
"""

import ipaddress
import enum
import networkx as nx

from synet.topo.bgp import ASPathList
from synet.topo.bgp import CommunityList
from synet.topo.bgp import RouteMap
from synet.topo.bgp import IpPrefixList
from synet.utils.fnfree_smt_context import is_empty
from synet.utils.fnfree_smt_context import VALUENOTSET


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


VERTEX_TYPE = 'VERTEX_TYPE'
EDGE_TYPE = 'EDGE_TYPE'


def is_valid_add(addr, allow_not_set=True):
    """Return True if the address is valid"""
    if allow_not_set and is_empty(addr):
        return True
    return isinstance(addr, (ipaddress.IPv4Interface, ipaddress.IPv6Interface))

def is_bool_or_notset(value):
    return value in [True, False, VALUENOTSET]


class VERTEXTYPE(enum.Enum):
    """Enum for VERTEX types in the network graph"""
    ROUTER = 'ROUTER'
    NETWORK = 'NETWORK'
    PEER = 'PEER'


class EDGETYPE(enum.Enum):
    """Enum for Edge types in the network graph"""
    ROUTER = 'ROUTER_EDGE'
    NETWORK = 'NETWORK_EDGE'
    PEER = 'PEER_EDGE'


class NetworkGraph(nx.DiGraph):
    """
    An extended version of networkx.DiGraph
    """
    def add_node(self, n, attr_dict=None, **attr):
        """
        Add a single node n and update node attributes.
        Inherits networkx.DiGraph.add_node
        Just check that VERTEX_TYPE is defined.
        :param n: node name (str)
        :param attr_dict: dict of attributes
        :param attr: dict of attributes
        :return: None
        """
        type_set = False
        if attr_dict and VERTEX_TYPE in attr_dict:
            type_set = True
        if attr and VERTEX_TYPE in attr:
            type_set = True
        if not type_set:
            raise ValueError('Cannot add directly nodes, must use add_router, add_peer etc..')
        super(NetworkGraph, self).add_node(n, attr_dict, **attr)

    def add_router(self, router):
        """
        Add a new router to the graph
        the node in the graph will be annotated with VERTEX_TYPE=NODE_TYPE
        :param router: the name of the router
        :return: None
        """
        self.add_node(router, **{VERTEX_TYPE: VERTEXTYPE.ROUTER})

    def add_peer(self, router):
        """
        Add a new router to the graph, this router is special only to model external routers
        the node in the graph will be annotated with VERTEXTYPE.PEER
        :param router: the name of the router
        :return: None
        """
        self.add_node(router, {VERTEX_TYPE: VERTEXTYPE.PEER})

    def add_network(self, network):
        """
        Add a new network to the graph
        the node in the graph will be annotated with VERTEX_TYPE=VERTEXTYPE.NETWORK
        :param router: the name of the router
        :return: None
        """
        self.add_node(network, {VERTEX_TYPE: VERTEXTYPE.NETWORK})

    def is_peer(self, node):
        """
        Checks if a given node is a Peer
        :param node: node name, must be in G
        :return: True if a node is a peering network
        """
        if not self.has_node(node):
            return False
        return self.node[node][VERTEX_TYPE] == VERTEXTYPE.PEER

    def is_local_router(self, node):
        """
        Checks if a given node is local router under the administrative domain
        (i.e., not a peering network)
        :param node: node name, must be in G
        :return: True if a node is part of the administrative domain
        """
        if not self.has_node(node):
            return False
        return self.node[node][VERTEX_TYPE] == VERTEXTYPE.ROUTER

    def is_network(self, node):
        """Node is a just a subnet (not a router)"""
        if not self.has_node(node):
            return False
        return self.node[node][VERTEX_TYPE] == VERTEXTYPE.NETWORK

    def is_router(self, node):
        """True for Nodes and Peers"""
        return self.is_peer(node) or self.is_local_router(node)

    def local_routers_iter(self):
        """Iterates over local routers"""
        for node in self.nodes():
            if self.is_local_router(node):
                yield node

    def peers_iter(self):
        """Iterates over peers"""
        for node in self.nodes():
            if self.is_peer(node):
                yield node

    def routers_iter(self):
        """Iterates over routers (local or peers)"""
        for node in self.nodes():
            if self.is_router(node):
                yield node

    def networks_iter(self):
        """Iterates over networks"""
        for node in self.nodes():
            if self.is_network(node):
                yield node

    def add_edge(self, u, v, attr_dict=None, **attr):
        """
        Add an edge u,v to G.
        Inherits networkx.DiGraph.add_Edge
        Just check that EDGE_TYPE is defined.
        :param u:
        :param v:
        :param attr_dict:
        :param attr:
        :return:
        """
        type_set = False
        if attr_dict and EDGE_TYPE in attr_dict:
            type_set = True
        if attr and EDGE_TYPE in attr:
            type_set = True
        if not type_set:
            msg = 'Cannot add directly edges, must use ' \
                  'add_router_edge, add_peer_edge etc..'
            raise ValueError(msg)
        super(NetworkGraph, self).add_edge(u, v, attr_dict, **attr)

    def add_router_edge(self, u, v, attr_dict=None, **attr):
        """
        Add an edge between two routers
        :param u: source router
        :param v: dst routers
        :param attr_dict: attributes
        :param attr: attributes
        :return: None
        """
        assert self.is_local_router(u), "Source '%s' is not a router" % u
        assert self.is_local_router(u), "Destination '%s' is not a router" % u
        if attr_dict is None:
            attr_dict = {}
        attr_dict[EDGE_TYPE] = EDGETYPE.ROUTER
        self.add_edge(u, v, attr_dict, **attr)

    def is_local_router_edge(self, src, dst):
        """Return True if the two local routers are connected"""
        if not self.has_edge(src, dst):
            return False
        return self[src][dst][EDGE_TYPE] == EDGETYPE.ROUTER

    def add_peer_edge(self, u, v, attr_dict=None, **attr):
        """
        Add an edge between two routers (one local and the other is a peer)
        :param u: source router
        :param v: dst routers
        :param attr_dict: attributes
        :param attr: attributes
        :return: None
        """
        err1 = "One side is not a peer router (%s, %s)" % (u, v)
        assert self.is_peer(u) or self.is_peer(v), err1
        err2 = "One side is not a local router (%s, %s)" % (u, v)
        assert self.is_router(u) or self.is_router(v), err2
        if attr_dict is None:
            attr_dict = {}
        attr_dict[EDGE_TYPE] = EDGETYPE.PEER
        self.add_edge(u, v, attr_dict, **attr)

    def add_network_edge(self, u, v, attr_dict=None, **attr):
        """
        Add an edge between a router and a network
        :param u: source router or network
        :param v: dst routers r network
        :param attr_dict: attributes
        :param attr: attributes
        :return: None
        """
        err1 = "One side is not a local router (%s, %s)" % (u, v)
        assert self.is_router(u) or self.is_router(v), err1
        err2 = "One side is not a network (%s, %s)" % (u, v)
        assert self.is_network(u) or self.is_network(v), err2
        if attr_dict is None:
            attr_dict = {}
        attr_dict[EDGE_TYPE] = EDGETYPE.NETWORK
        self.add_edge(u, v, attr_dict, **attr)

    def get_loopback_interfaces(self, node):
        """
        Returns the dict of the loopback interfaces
        will set empty dict if it doesn't exists
        :param node: the name of the node
        :return: a dict
        """
        if 'loopbacks' not in self.node[node]:
            self.node[node]['loopbacks'] = {}
        return self.node[node]['loopbacks']

    def set_loopback_addr(self, node, loopback, addr):
        """
        Assigns an IP address to a loopback interface
        :param node: name of the router
        :param loopback: name of loopback interface. e.g., lo0, lo1, etc..
        :param addr: an instance of ipaddress.IPv4Interface or ipaddress.IPv6Interface
        :return: None
        """
        assert is_valid_add(addr)
        loopbacks = self.get_loopback_interfaces(node)
        if loopback not in loopbacks:
            loopbacks[loopback] = {}
        assert is_empty(loopbacks[loopback].get('addr', None)), loopbacks[loopback].get('addr', None)
        loopbacks[loopback]['addr'] = addr

    def get_loopback_addr(self, node, loopback):
        """
        Gets the IP address of a loopback interface
        :param g: network graph (networkx.DiGraph)
        :param node: name of the router
        :param loopback: name of loopback interface. e.g., lo0, lo1, etc..
        :return: an instance of ipaddress.IPv4Interface or ipaddress.IPv6Interface
        """
        addr = self.node[node].get('loopbacks', {}).get(loopback, {}).get('addr', None)
        err = "IP Address is not assigned for loopback'%s'-'%s'" % (node, loopback)
        assert addr, err
        return addr

    def set_loopback_description(self, node, loopback, description):
        """
        Assigns some help text to the interface
        :param node: name of the router
        :param loopback: name of loopback interface. e.g., lo0, lo1, etc..
        :return: None
        """
        self.node[node]['loopbacks'][loopback]['description'] = description

    def get_loopback_description(self, node, loopback):
        """
        Return the help text to the interface or None
        :param node: name of the router
        :param loopback: name of loopback interface. e.g., lo0, lo1, etc..
        :return: text or none
        """
        return self.node[node]['loopbacks'][loopback].get('description', None)

    def get_ifaces(self, node):
        if 'ifaces' not in self.node[node]:
            self.node[node]['ifaces'] = {}
        return self.node[node]['ifaces']

    def add_iface(self, node, iface_name, is_shutdown=True):
        """
        Add an interface to a router
        :param node: name of the router
        :param iface_name:
        :return:
        """
        assert self.is_router(node)
        assert is_bool_or_notset(is_shutdown)
        ifaces = self.get_ifaces(node)
        assert iface_name not in ifaces, "%s in %s" % (iface_name, ifaces.keys())
        ifaces[iface_name] = {'shutdown': is_shutdown,
                              'addr': None,
                              'description': None}

    def set_iface_addr(self, node, iface_name, addr):
        """Return set the address of an interface or None"""
        assert self.is_router(node)
        assert is_valid_add(addr)
        ifaces = self.get_ifaces(node)
        err = "Undefined iface '%s' in %s" % (iface_name, ifaces.keys())
        assert iface_name in ifaces, err
        ifaces[iface_name]['addr'] = addr

    def get_iface_addr(self, node, iface_name):
        """Return the address of an interface or None"""
        assert self.is_router(node)
        ifaces = self.get_ifaces(node)
        err = "Undefined iface '%s' in %s" % (iface_name, ifaces.keys())
        assert iface_name in ifaces, err
        return ifaces[iface_name]['addr']

    def set_iface_description(self, node, iface_name, description):
        """Assigns some help text to the interface"""
        assert self.is_router(node)
        ifaces = self.get_ifaces(node)
        err = "Undefined iface '%s' in %s" % (iface_name, ifaces.keys())
        assert iface_name in ifaces, err
        ifaces[iface_name]['description'] = description

    def get_iface_description(self, node, iface_name):
        """Get help text to the interface (if exists)"""
        assert self.is_router(node)
        ifaces = self.get_ifaces(node)
        err = "Undefined iface '%s' in %s" % (iface_name, ifaces.keys())
        assert iface_name in ifaces, err
        return ifaces[iface_name]['description']

    def is_iface_shutdown(self, node, iface_name):
        """Return True if the interface is set to be shutdown"""
        assert self.is_router(node)
        ifaces = self.get_ifaces(node)
        err = "Undefined iface '%s' in %s" % (iface_name, ifaces.keys())
        assert iface_name in ifaces, err
        return ifaces[iface_name]['shutdown']

    def set_iface_shutdown(self, node, iface_name, is_shutdown):
        """Set True if the interface is set to be shutdown"""
        assert self.is_router(node)
        assert is_bool_or_notset(is_shutdown)
        ifaces = self.get_ifaces(node)
        err = "Undefined iface '%s' in %s" % (iface_name, ifaces.keys())
        assert iface_name in ifaces, err
        ifaces[iface_name]['shutdown'] = is_shutdown

    def set_edge_iface(self, src, dst, iface):
        """
        Assigns an interface name to the outgoing edge, e.g., f0/0, f1/0, etc..
        :param src: name of the source router (the one that will change)
        :param dst: name of the destination router
        :param iface: the name of the the interface
        :return: None
        """
        self[src][dst]['iface'] = iface

    def get_edge_iface(self, src, dst):
        """
        Gets the interface name to the outgoing edge, e.g., f0/0, f1/0, etc..
        :param src: name of the source router (the one that will change)
        :param dst: name of the destination router
        :return the name of the the interface
        """
        return self[src][dst].get('iface', None)

    def get_static_routes(self, node):
        """Return a dict of configured static routes or VALUENOTSET"""
        assert self.is_router(node)
        if 'static' not in self.node[node]:
            self.node[node]['static'] = {}
        return self.node[node]['static']

    def add_static_route(self, node, prefix, next_hop):
        """
        Set a static route
        :param node: Router
        :param prefix: Prefixed to be routed
        :param next_hop: Router
        :return:
        """
        attrs = self.get_static_routes(node)
        if is_empty(attrs):
            self.node[node]['static'] = {}
        self.node[node]['static'][prefix] = next_hop

    def set_static_routes_empty(self, node):
        """
        Set static routes to VALUENOTSET allowing the
        synthesizer to generate as many static routes
        """
        self.node[node]['static'] = VALUENOTSET

    def enable_ospf(self, node, process_id=100):
        """
        Enable OSPF at a given router
        :param node: local router
        :param process_id: integer
        :return: None
        """
        assert self.is_local_router(node)
        self.node[node]['ospf'] = dict(process_id=process_id, networks={})

    def get_ospf_process_id(self, node):
        """Return the OSPF process ID"""
        assert self.is_ospf_enabled(node)
        return self.node[node]['ospf']['process_id']

    def is_ospf_enabled(self, node):
        """
        Return True if the node has OSPF process
        :param node: local router
        :return: bool
        """
        if not self.is_local_router(node):
            return False
        return 'ospf' in self.node[node]

    def get_ospf_networks(self, node):
        """
        Return a dict of Announced networks in OSPF at the router
        :param node: local router
        :return: dict Network->Area
        """
        assert self.is_ospf_enabled(node)
        return self.node[node]['ospf']['networks']

    def add_ospf_network(self, node, network, area):
        """
        :param node:
        :param network:
        :param area:
        :return: None
        """
        networks = self.get_ospf_networks(node)
        networks[network] = area

    def set_edge_ospf_cost(self, src, dst, cost):
        """
        Set the OSPF cost of an edge
        :param src: OSPF enabled local router
        :param dst: OSPF enabled local router
        :param cost: int or VALUENOTSET
        :return: None
        """
        assert self.is_ospf_enabled(src)
        assert self.is_ospf_enabled(dst)
        self[src][dst]['ospf_cost'] = cost

    def get_edge_ospf_cost(self, src, dst):
        """
        Get the OSPF cost of an edge
        :param src: OSPF enabled local router
        :param dst: OSPF enabled local router
        :return: None, VALUENOTSET, int
        """
        assert self.is_ospf_enabled(src)
        assert self.is_ospf_enabled(dst)
        return self[src][dst].get('ospf_cost', None)

    def get_bgp_attrs(self, node):
        """Return a dict of all BGP related attrs given to a node"""
        assert self.is_router(node), "Node is not a router {}".format(node)
        if 'bgp' not in self.node[node]:
            self.node[node]['bgp'] = {'asnum': None,
                                      'neighbors': {},
                                      'announces': {}}
        return self.node[node]['bgp']

    def set_bgp_asnum(self, node, asnum):
        """Sets the AS number of a given router"""
        assert is_empty(asnum) or isinstance(asnum, int)
        self.get_bgp_attrs(node)['asnum'] = asnum

    def is_bgp_enabled(self, node):
        """Return True if the router has BGP configurations"""
        return self.get_bgp_asnum(node) is not None

    def get_bgp_asnum(self, node):
        """Get the AS number of a given router"""
        return self.get_bgp_attrs(node).get('asnum', None)

    def get_bgp_neighbors(self, node):
        """Get a dictionary of BGP peers"""
        return self.get_bgp_attrs(node).get('neighbors', None)

    def add_bgp_neighbor(self, router_a, router_b, router_a_iface, router_b_iface, description=None):
        """
        Add BGP peer
        Peers are added by their name in the graph
        :param router_a: Router name
        :param router_b: Router name
        :param router_a_iface: The peering interface can be
                        VALUENOTSET, Physical Iface, loop back.
        :param router_b_iface: The peering interface
        :param description:
        :return:
        """
        neighbors_a = self.get_bgp_neighbors(router_a)
        neighbors_b = self.get_bgp_neighbors(router_b)
        err1 = "Router %s already has BGP neighbor %s configured" % (router_a, router_b)
        assert router_b not in neighbors_a, err1
        err2 = "Router %s already has BGP neighbor %s configured" % (router_b, router_a)
        assert router_a not in neighbors_b, err2
        neighbors_a[router_b] = {'peering_iface': router_b_iface}
        neighbors_b[router_a] = {'peering_iface': router_a_iface}
        if not description:
            desc1 = 'To %s' % router_b
            desc2 = 'To %s' % router_a
            self.set_bgp_neighbor_description(router_a, router_b, desc1)
            self.set_bgp_neighbor_description(router_b, router_a, desc2)
        else:
            self.set_bgp_neighbor_description(router_a, router_b, description)
            self.set_bgp_neighbor_description(router_b, router_a, description)

    def set_bgp_neighbor_iface(self, node, neighbor, iface):
        """Set the interface to which the peering session to be established"""
        neighbors = self.get_bgp_neighbors(node)
        assert neighbor in neighbors
        assert iface in self.get_ifaces(neighbor) or iface in self.get_loopback_interfaces(neighbor)
        neighbors[neighbor]['peering_iface'] = iface

    def get_bgp_neighbor_iface(self, node, neighbor):
        """Get the interface to which the peering session to be established"""
        neighbors = self.get_bgp_neighbors(node)
        assert neighbor in neighbors
        return neighbors[neighbor]['peering_iface']

    def set_bgp_neighbor_description(self, node, neighbor, description):
        """Returns text description for help about the neighbor"""
        assert isinstance(description, basestring)
        # Cisco's limit
        assert len(description) <= 80
        self.get_bgp_neighbors(node)[neighbor]['description'] = description

    def get_bgp_neighbor_description(self, node, neighbor):
        """Returns text description for help about the neighbor"""
        return self.get_bgp_neighbors(node)[neighbor].get('description')

    def assert_valid_neighbor(self, node, neighbor):
        neighbors = self.get_bgp_neighbors(node)
        err = "Not not valid BGP neighbor %s->%s" % (node, neighbor)
        assert neighbor in neighbors, err

    def get_bgp_neighbor_remoteas(self, node, neighbor):
        """Get the AS number of a BGP peer (by name)"""
        self.assert_valid_neighbor(node, neighbor)
        return self.get_bgp_asnum(neighbor)

    def get_bgp_advertise(self, node):
        """
        Returns a list of advertisements announced by a peer
        :param node: router
        :return: list
        """
        assert self.is_peer(node)
        name = 'advertise'
        attrs = self.get_bgp_attrs(node)
        if name not in attrs:
            attrs['advertise'] = []
        return attrs['advertise']

    def add_bgp_advertise(self, node, announcement):
        """
        Add an advertisement by an external peer
        """
        self.get_bgp_advertise(node).append(announcement)

    def get_bgp_announces(self, node):
        """
        Returns a dict of announcements to be made by the node
        :param node: router
        :return: dic
        """
        return self.get_bgp_attrs(node)['announces']

    def add_bgp_announces(self, node, network, route_map_name=None):
        """
        Router to announce a given network over BGP
        :param node:  router
        :param network: either a Loopback, a network name, or actual ipaddress.ip_network
        :param route_map: Route-map to modify the attributes
        :return: None
        """
        is_network = self.has_node(network) and self.is_network(network)
        is_lo = network in self.get_loopback_interfaces(node)
        is_net = isinstance(network, (ipaddress.IPv4Network, ipaddress.IPv6Network))
        assert is_network or is_lo or is_net
        announcements = self.get_bgp_announces(node)
        announcements[network] = {}
        if route_map_name:
            assert route_map_name in self.get_route_maps(node)
            announcements[network]['route_map'] = route_map_name

    def get_bgp_communities_list(self, node):
        """
        Return communities list registered on the router
        :param node: the router on which the list resides
        :return: {} or a dict of communities list
        """
        comm_list = self.get_bgp_attrs(node).get('communities-list', None)
        if comm_list is None:
            self.node[node]['bgp']['communities-list'] = {}
            comm_list = self.node[node]['bgp']['communities-list']
        return comm_list

    def add_bgp_community_list(self, node, community_list):
        """
        Add a community list
        :param node: the router on which the list resides
        :param community_list: instance of CommunityList
        :return: CommunityList
        """
        assert isinstance(community_list, CommunityList)
        lists = self.get_bgp_communities_list(node)
        assert community_list.list_id not in lists
        lists[community_list.list_id] = community_list
        return community_list

    def get_as_path_list(self, node):
        """
        Return as paths list registered on the router
        :param node: the router on which the list resides
        :return: {} or a dict of communities list
        """
        as_paths_list = self.get_bgp_attrs(node).get('as-path-list', None)
        if as_paths_list is None:
            self.node[node]['bgp']['as-path-list'] = {}
            as_paths_list = self.node[node]['bgp']['as-path-list']
        return as_paths_list

    def add_as_path_list(self, node, as_path_list):
        """
        Add a As path_list list
        :param node: the router on which the list resides
        :param as_path_list: instance of CommunityList
        :return: CommunityList
        """
        assert isinstance(as_path_list, ASPathList)
        lists = self.get_as_path_list(node)
        assert as_path_list.list_id not in lists
        lists[as_path_list.list_id] = as_path_list
        return as_path_list

    def add_bgp_import_route_map(self, node, neighbor, route_map_name):
        """
        Specifies the import route map from the given neighbor
        :param node:
        :param neighbor:
        :param route_map_name:
        :return: None
        """
        assert route_map_name in self.get_route_maps(node), \
            "Route map is not defiend %s" % route_map_name
        neighbors = self.get_bgp_neighbors(node)
        self.assert_valid_neighbor(node, neighbor)
        neighbors[neighbor]['import_map'] = route_map_name

    def get_bgp_import_route_map(self, node, neighbor):
        """
        Get the name of the import route map from the given neighbor
        :param node:
        :param neighbor:
        :return: route_map_name
        """
        neighbors = self.get_bgp_neighbors(node)
        self.assert_valid_neighbor(node, neighbor)
        route_map_name = neighbors[neighbor].get('import_map', None)
        if not route_map_name:
            return None
        assert route_map_name in self.get_route_maps(node), \
            "Route map is not defiend %s" % route_map_name
        return route_map_name

    def add_bgp_export_route_map(self, node, neighbor, route_map_name):
        """
        Specifies the export route map to the given neighbor
        :param node:
        :param neighbor:
        :param route_map_name:
        :return: None
        """
        assert route_map_name in self.get_route_maps(node), \
            "Route map is not defiend %s" % route_map_name
        neighbors = self.get_bgp_neighbors(node)
        self.assert_valid_neighbor(node, neighbor)
        neighbors[neighbor]['export_map'] = route_map_name

    def get_bgp_export_route_map(self, node, neighbor):
        """
        Get the name of the export route map to the given neighbor
        :param node:
        :param neighbor:
        :return: route_map_name
        """
        neighbors = self.get_bgp_neighbors(node)
        self.assert_valid_neighbor(node, neighbor)
        route_map_name = neighbors[neighbor].get('export_map', None)
        if not route_map_name:
            return None
        assert route_map_name in self.get_route_maps(node), \
            "Route map is not defiend %s" % route_map_name
        return route_map_name

    def get_route_maps(self, node):
        """Return dict of the configured route maps for a given router"""
        assert self.is_router(node)
        maps = self.node[node].get('routemaps', None)
        if not maps:
            self.node[node]['routemaps'] = {}
            maps = self.node[node]['routemaps']
        return maps

    def add_route_map(self, node, routemap):
        assert isinstance(routemap, RouteMap)
        routemaps = self.get_route_maps(node)
        routemaps[routemap.name] = routemap
        return routemap

    def get_ip_preflix_lists(self, node):
        """Return a dict of the configured IP prefix lists"""
        if 'ip_prefix_lists' not in self.node[node]:
            self.node[node]['ip_prefix_lists'] = {}
        return self.node[node]['ip_prefix_lists']

    def add_ip_prefix_list(self, node, prefix_list):
        """Add new ip prefix list (overrides existing one with the same name"""
        assert isinstance(prefix_list, IpPrefixList)
        lists = self.get_ip_preflix_lists(node)
        lists[prefix_list.name] = prefix_list

    def set_iface_names(self):
        """Assigns interface IDs (Fa0/0,  Fa0/1, etc..) for each edge"""
        for node in sorted(list(self.nodes())):
            iface_count = 0
            for src, dst in sorted(list(self.out_edges(node))):
                if self.get_edge_iface(src, dst):
                    continue
                if self.is_router(src) and self.is_router(dst):
                    if self.get_edge_iface(src, dst):
                        continue
                    iface = "Fa%d/%d" % (iface_count // 2, iface_count % 2)
                    while iface in self.get_ifaces(src):
                        iface_count += 1
                        iface = "Fa%d/%d" % (iface_count // 2, iface_count % 2)
                    self.add_iface(src, iface, is_shutdown=False)
                    self.set_iface_addr(src, iface, VALUENOTSET)
                    self.set_edge_iface(src, dst, iface)
                    self.set_iface_description(src, iface, ''"To {}"''.format(dst))
                elif self.is_router(src) and self.is_network(dst):
                    iface = '{node}-veth{iface}'.format(node=src, iface=iface_count)
                    self.add_iface(src, iface, is_shutdown=False)
                    self.set_edge_iface(src, dst, iface)
                    self.set_iface_description(src, iface, ''"To {}"''.format(dst))
                elif self.is_network(src) and self.is_router(dst):
                    continue
                else:
                    raise ValueError('Not valid link %s -> %s' % (src, dst))

    def get_print_graph(self):
        """
        Get a plain version of the Network graph
        Mainly used to help visualizing it
        :return: networkx.DiGraph
        """
        graph = nx.DiGraph()
        for node, attrs in self.nodes(data=True):
            graph.add_node(node)
            vtype = str(attrs[VERTEX_TYPE])
            label = "%s\\n%s" % (node, vtype.split('.')[-1])
            asnum = self.get_bgp_asnum(node)
            if asnum:
                graph.node[node]['bgp_asnum'] = asnum
                label += "\nAS Num: %s" % asnum
            graph.node[node]['label'] = label
            graph.node[node][VERTEX_TYPE] = vtype

        for src, dst, attrs in self.edges_iter(data=True):
            etype = str(attrs[EDGE_TYPE])
            graph.add_edge(src, dst)
            graph[src][dst]['label'] = etype.split('.')[-1]
            graph[src][dst][EDGE_TYPE] = etype

        return graph

    def write_dot(self, out_file):
        """Write .dot file"""
        from networkx.drawing.nx_agraph import write_dot
        write_dot(self.get_print_graph(), out_file)

    def write_graphml(self, out_file):
        """Write graphml file"""
        nx.write_graphml(self.get_print_graph(), out_file)

    def write_propane(self, out_file):
        """Output propane style topology file"""
        out = '<topology asn="%d">\n' % 5
        for node in sorted(self.routers_iter()):
            internal = 'true' if self.is_local_router(node) else 'false'
            if self.is_bgp_enabled(node):
                asnum = self.get_bgp_asnum(node)
                out += '  <node internal="%s" asn="%d" name="%s"></node>\n' % (internal, asnum, node)
            else:
                out += '  <node internal="%s" name="%s"></node>\n' % (internal, node)
        seen = []
        for src, dst in self.edges_iter():
            if (src, dst) in seen:
                continue
            out += '  <edge source="%s" target="%s"></edge>\n' % (src, dst)
            seen.append((src, dst))
            seen.append((dst, src))
        out += '</topology>\n'
        with open(out_file, 'w') as fd:
            fd.write(out)
