#!/usr/bin/env python
"""
Extension of the networkx.DiGraph to allow easy synthesis
and network specific annotations.
"""

import ipaddress
import enum
import networkx as nx

from synet.topo.bgp import Access
from synet.topo.bgp import CommunityList
from synet.topo.bgp import RouteMap
from synet.topo.bgp import IpPrefixList


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


VERTEX_TYPE = 'VERTEX_TYPE'
EDGE_TYPE = 'EDGE_TYPE'


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
        return self.node[node][VERTEX_TYPE] == VERTEXTYPE.PEER

    def is_local_router(self, node):
        """
        Checks if a given node is local router under the administrative domain
        (i.e., not a peering network)
        :param node: node name, must be in G
        :return: True if a node is part of the administrative domain
        """
        return self.node[node][VERTEX_TYPE] == VERTEXTYPE.ROUTER

    def is_network(self, node):
        """Node is a just a subnet (not a router)"""
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
            msg = 'Cannot add directly edges, must use' \
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

    def add_peer_edge(self, u, v, attr_dict=None, **attr):
        """
        Add an edge between two routers (one local and the other is a peer)
        :param u: source router
        :param v: dst routers
        :param attr_dict: attributes
        :param attr: attributes
        :return: None
        """
        assert self.is_peer(u) or self.is_peer(v), "One side is not a peer router" % u
        assert self.is_router(u) or self.is_router(v), "One side is not a local router" % u
        if attr_dict is None:
            attr_dict = {}
        attr_dict[EDGE_TYPE] = EDGETYPE.ROUTER
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
        assert self.is_router(u) or self.is_router(v), "One side is not a router" % u
        assert self.is_network(u) or self.is_network(v), "One side is not a router" % u
        if attr_dict is None:
            attr_dict = {}
        attr_dict[EDGE_TYPE] = EDGETYPE.NETWORK
        self.add_edge(u, v, attr_dict, **attr)

    def set_edge_addr(self, src, dst, addr):
        """
        Assigns an IP address to the outgoing interface
        :param src: name of the source router (the one that will change)
        :param dst: name of the destination router
        :param addr: an instance of ipaddress.IPv4Interface or ipaddress.IPv6Interface
        :return: None
        """
        assert isinstance(addr, (ipaddress.IPv4Interface, ipaddress.IPv6Interface))
        self[src][dst]['addr'] = addr

    def get_edge_addr(self, src, dst):
        """
        Gets the IP address of the outgoing interface
        :param src: name of the source router
        :param dst: name of the destination router
        :return: an instance of ipaddress.IPv4Interface or ipaddress.IPv6Interface
        """
        addr = self[src][dst].get('addr', None)
        assert addr, "IP Address is not assigned for edge '%s'->'%s'" % (src, dst)
        return addr

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
        assert isinstance(addr, (ipaddress.IPv4Interface, ipaddress.IPv6Interface))
        loopbacks = self.get_loopback_interfaces(node)
        if loopback not in loopbacks:
            loopbacks[loopback] = {}
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
        assert addr, "IP Address is not assigned for loopback'%s'-'%s'" % (node, loopback)
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
        return self[src][dst]['iface']

    def set_edge_iface_description(self, src, dst, description):
        """
        Assigns some help text to the interface
        :param src: name of the source router (the one that will change)
        :param dst: name of the destination router
        :param description: some text
        :return: None
        """
        self[src][dst]['iface_description'] = description

    def get_edge_iface_description(self, src, dst):
        """
        Get help text to the interface (if exists)
        :param src: name of the source router (the one that will change)
        :param dst: name of the destination router
        :return some text if exits
        """
        return self[src][dst].get('iface_description', None)

    def get_bgp_attrs(self, node):
        """Return a dict of all BGP related attrs given to a node"""
        if 'bgp' not in self.node[node]:
            self.node[node]['bgp'] = {'asnum': None, 'neighbors': {}, 'announces': {}}
        return self.node[node]['bgp']

    def set_bgp_asnum(self, node, asnum):
        """Sets the AS number of a given router"""
        self.get_bgp_attrs(node)['asnum'] = asnum

    def get_bgp_asnum(self, node):
        """Get the AS number of a given router"""
        return self.get_bgp_attrs(node)['asnum']

    def get_bgp_neighbors(self, node):
        """Get a dictionary of BGP peers"""
        return self.get_bgp_attrs(node).get('neighbors', None)

    def add_bgp_neighbor(self, routerA, routerB, description=None):
        """
        Add BGP peer
        Peers are added by their name in the graph
        """
        neighborsA = self.get_bgp_neighbors(routerA)
        neighborsB = self.get_bgp_neighbors(routerB)
        neighborsA[routerB] = {}
        neighborsB[routerA] = {}
        if not description:
            desc1 = 'To %s' % routerB
            desc2 = 'To %s' % routerA
            self.set_bgp_neighbor_description(routerA, routerB, desc1)
            self.set_bgp_neighbor_description(routerB, routerA, desc2)
        else:
            self.set_bgp_neighbor_description(routerA, routerB, description)
            self.set_bgp_neighbor_description(routerB, routerA, description)

    def set_bgp_neighbor_description(self, node, neighbor, description):
        """Returns text description for help about the neighbor"""
        assert isinstance(description, basestring)
        # Cisco's limit
        assert len(description) <= 80
        self.get_bgp_neighbors(node)[neighbor]['description'] = description

    def get_bgp_neighbor_description(self, node, neighbor):
        """Returns text description for help about the neighbor"""
        return self.get_bgp_neighbors(node)[neighbor].get('description')

    def get_bgp_neighbor_remoteas(self, node, neighbor):
        """Get the AS number of a BGP peer (by name)"""
        neighbors = self.get_bgp_neighbors(node)
        assert neighbor in neighbors
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

    def add_bgp_imoprt_route_map(self, node, neighbor, route_map_name):
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
        assert neighbor in neighbors, "Not not valid BGP neighbors (%s, %s)" % (node, neighbor)
        neighbors[neighbor]['import_map'] = route_map_name

    def get_bgp_import_route_map(self, node, neighbor):
        """
        Get the name of the import route map from the given neighbor
        :param node:
        :param neighbor:
        :return: route_map_name
        """
        neighbors = self.get_bgp_neighbors(node)
        assert neighbor in neighbors, "Not not valid BGP neighbor"
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
        assert neighbor in neighbors, "Not not valid BGP neighbor"
        neighbors[neighbor]['export_map'] = route_map_name

    def get_bgp_export_route_map(self, node, neighbor):
        """
        Get the name of the export route map to the given neighbor
        :param node:
        :param neighbor:
        :return: route_map_name
        """
        neighbors = self.get_bgp_neighbors(node)
        assert neighbor in neighbors, "Not not valid BGP neighbor"
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
        def one_is_router(x, y):
            return (self.is_router(x) and self.is_network(y)) \
                   or (self.is_network(x) and self.is_router(y))

        for node in sorted(list(self.nodes())):
            for iface_count, (src, dst) in enumerate(sorted(list(self.out_edges(node)))):
                if self.is_router(src) and self.is_router(dst):
                    iface = "Fa%d/%d" % (iface_count // 2, iface_count % 2)
                    self.set_edge_iface(src, dst, iface)
                    self.set_edge_iface_description(src, dst, ''"To {}"''.format(dst))
                elif one_is_router(src, dst):
                    iface = '{node}-veth{iface}'.format(node=src, iface=iface_count)
                    self.set_edge_iface(src, dst, iface)
                    self.set_edge_iface_description(src, dst, ''"To {}"''.format(dst))
                else:
                    raise ValueError('Not valid link %s -> %s' % (src, dst))
