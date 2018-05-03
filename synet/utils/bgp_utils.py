#!/usr/bin/env python
"""
Common utils for BGP synthesis
"""

import networkx as nx
from synet.utils.fnfree_smt_context import VALUENOTSET
from synet.utils.fnfree_smt_context import is_empty


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


def synthesize_next_hop(network_graph, node, neighbor, ibgp_loopback=True):
    """
    Synthesizes a next hop interface between two router.

    If ibgp_loopback is set to True, iBGP peering session will
    created between loopback interfaces of the routers, otherwise
    the direct interface is used for peering between the two

    :return the name of the interface (on the neighbor)
    """
    # TODO: Synthesize proper next hop
    asnum1 = network_graph.get_bgp_asnum(node)
    asnum2 = network_graph.get_bgp_asnum(neighbor)
    if not ibgp_loopback or (asnum1 != asnum2 and network_graph.has_edge(neighbor, node)):
        iface = network_graph.get_edge_iface(neighbor, node)
    else:
        loopbacks = network_graph.get_loopback_interfaces(neighbor)
        iface = 'lo100'
        if iface not in loopbacks:
            network_graph.set_loopback_addr(neighbor, iface, VALUENOTSET)
    return iface


def compute_next_hop_map(network_graph, ibgp_loopback=True):
    """
    Compute the possible next hop values in the network

    If ibgp_loopback is set to True, iBGP peering session will
    created between loopback interfaces of the routers, otherwise
    the direct interface is used for peering between the two

    :return dict [node][neighbor]->next_hop
    """
    next_hop_map = {}
    for node in network_graph.routers_iter():
        if node not in next_hop_map:
            next_hop_map[node] = {}
        if not network_graph.get_bgp_asnum(node):
            # BGP is not configured on this router
            continue
        neighbors = network_graph.get_bgp_neighbors(node)
        for neighbor in neighbors:
            iface = network_graph.get_bgp_neighbor_iface(node, neighbor)
            if is_empty(iface):
                iface = synthesize_next_hop(network_graph, node, neighbor,
                                            ibgp_loopback=ibgp_loopback)
            network_graph.set_bgp_neighbor_iface(node, neighbor, iface)
            assert iface, "Synthesize connected first"
            iface = iface.replace("/", "-")
            nxt = "%s-%s" % (neighbor, iface)
            next_hop_map[node][neighbor] = nxt
    return next_hop_map


def extract_all_next_hops(next_hop_map):
    """
    Takes next_hop_map and just return a list of the names of the next hops
    """
    next_hops = set()
    for src in next_hop_map:
        for _, next_hop in next_hop_map[src].iteritems():
            next_hops.add(next_hop)
    return list(next_hops)


def annotate_graph(graph):
    """Annotate propagation graph with labels for prettier print out"""
    for node in graph.nodes():
        order = graph.node[node].get('order', [])
        #paths = graph.node[node].get('paths', [])
        block = graph.node[node].get('block', [])
        graph.node[node]['label'] = "%s\nAllow: %s\nBlock: %s" % (node, order, block)


def compute_propagation(graph, ordered_paths):
    """
    Takes an ordered list of BGP paths (just AS nums) and returns
    a propagation graph, such that each node is annotated with the path
    order
    :returns networkx.DiGraph
    """
    dag = nx.DiGraph()

    def add_node(node):
        """Helper to initialize a node"""
        assert graph.has_node(node), "Unknow node '%s' in the path" % node
        if dag.has_node(node):
            return
        order = [set() for _ in range(len(ordered_paths))]
        dag.add_node(node, order=order, paths=set(), block=set())

    def allow_path(node, segment, index, origin):
        # Add it to the white list
        tmp = (origin, segment)
        tmp = segment
        if segment not in dag.node[node]['paths']:
            dag.node[node]['paths'].add(tmp)
            dag.node[node]['order'][index].add(tmp)
        # Unblock it if it was blocked by another path in the requirement
        if segment in dag.node[node]['block']:
            dag.node[node]['block'].remove(tmp)

    def block_path(node, segment, origin):
        # Block it if it wasn't blocked before
        # And if the path isn't in the required paths already
        tmp = (origin, segment)
        tmp = segment
        if tmp not in dag.node[node]['block'] and \
                tmp not in dag.node[node]['paths']:
            dag.node[node]['block'].add(tmp)

    if hasattr(graph, 'get_bgp_neighbors'):
        iter_neigh = getattr(graph, 'get_bgp_neighbors')
    else:
        iter_neigh = getattr(graph, 'neighbors')
    # Iterate over each required path
    for index, paths in enumerate(ordered_paths):
        for origin, path in paths:
            add_node(path[0])
            allow_path(path[0], (path[0],), index, origin)
            dst = None
            for src, dst in zip(path[0::1], path[1::1]):
                # Add the node to the graph
                add_node(src)
                add_node(dst)
                dag.add_edge(src, dst)
                # Compute the path segment observed so far
                segment = tuple(list(path[:path.index(src) + 1]) + [dst])
                # Add it to the white list
                allow_path(dst, segment, index, origin)
                # Each BGP can advertise to all its neightbors
                for add in iter_neigh(src):
                    #print "IN NEIGH", add
                    if add not in path:
                        add_node(add)
                        segment = tuple(list(path[:path.index(src) + 1]) + [add])
                        block_path(add, segment, origin)
                        dag.add_edge(src, add)
                if dst == path[-1]:
                    for add in iter_neigh(dst):
                        if add not in path:
                            add_node(add)
                            segment = tuple(list(path[:path.index(dst) + 1]) + [add])
                            block_path(add, segment, origin)
                            dag.add_edge(dst, add)
    return dag


def write_dag(dag, file):
    from networkx.drawing.nx_agraph import write_dot
    for node, data in dag.nodes(data=True):
        label = "%s\\n" % node
        if 'selected' in data:
            label += "Selected: %s\\n" % data['selected']
        if 'ordered' in data:
            label += "Ordered: %s\\n" % data.get('ordered', None)
        if 'unordered' in data:
            label += "Unordered: %s\\n" % data.get('unordered', None)
        if 'unselected' in data:
            label += "Unselected: %s\\n" % data.get('unselected', None)
        if 'igp_pass' in data:
            label += "PASS IGP: %s\\n" % data.get('igp_pass', None)
        dag.node[node]['label'] = label
    write_dot(dag, file)


def get_propagated_info(propagation_graph, node,
                        prefix=None, from_node=None,
                        unselected=True, from_peer=None, igp_pass=False):
    all_props = []
    if not propagation_graph.has_node(node):
        return []
    for net, data in propagation_graph.node[node]['prefixes'].iteritems():
        if prefix and net != prefix:
            continue
        for ecmp in data['prop_ordered']:
            for prop in ecmp:
                all_props.append(prop)
        for prop in data['prop_unordered']:
            all_props.append(prop)
        if unselected:
            for prop in data['prop_unselected']:
                all_props.append(prop)
        if igp_pass:
            for prop in data['prop_igp_pass']:
                all_props.append(prop)
    #if not from_node:
    #    return all_props
    ret = []
    for prop in all_props:
        if from_node:
            if len(prop.path) < 2:
                continue
            if prop.path[-2] != from_node:
                continue
        if from_peer:
            if prop.peer != from_peer:
                continue
        ret.append(prop)
    return ret


class NotValidBGPPropagation(Exception):
    """Raised when the requirements violates BGP's propagation rules"""

    def __init__(self, message):
        super(NotValidBGPPropagation, self).__init__(message)


class ConflictingPreferences(Exception):
    """Raised when requirements ask router to rank routes in a conflicting order"""

    def __init__(self, node, current_order, new_pref, new_req, curr_propagation):
        err = "Conflicting requirements for path preference " \
              "at {}: currently learning {} (preference {}) " \
              "from {} while new reqs learning from {}.".format(
                  node, new_req.dst_net, new_pref, current_order,
                  curr_propagation)
        super(ConflictingPreferences, self).__init__(err)
        self.node = node
        self.current_order = current_order
        self.new_req = new_req


class ForwardingLoopError(NotValidBGPPropagation):
    """Raised when the requirement creates a forwarding loop"""

    def __init__(self, message):
        super(ForwardingLoopError, self).__init__(message)


class PropagatedInfo(object):
    """BGP Information carried in Propagation graph"""

    def __init__(self, egress, ann_name, peer, as_path, as_path_len, path):
        """
        :param egress: The first local router learns the prefix
        :param ann_name: The name of announcement variable
        :param peer: the eBGP (or first iBGP) peer propagated the route
        :param as_path: The AS Path learned till this point
        :param as_path_len: The length of AS Path
        :param path: The router path (used in IGP)
        """
        self._egress = egress
        self._ann_name = ann_name
        self._peer = peer
        self._as_path = as_path
        self._as_path_len = as_path_len
        self._path = path

    @property
    def egress(self):
        """The first local router learns the prefix"""
        return self._egress

    @property
    def ann_name(self):
        """The name of announcement variable"""
        return self._ann_name

    @property
    def peer(self):
        """the eBGP (or first iBGP) peer propagated the route"""
        return self._peer

    @property
    def as_path(self):
        """The AS Path learned till this point"""
        return self._as_path

    @property
    def as_path_len(self):
        """The length of AS Path"""
        return self._as_path_len

    @property
    def path(self):
        """The router path (used in IGP)"""
        return self._path

    def __str__(self):
        return "Prop<Egress:%s, %s, Peer:%s, %s, %s, %s>" % (
            self.egress,
            self.ann_name,
            self.peer,
            self.as_path,
            self.as_path_len,
            self.path)

    def __hash__(self):
        string = ""
        attrs = ['egress', 'ann_name', 'peer', 'as_path', 'as_path_len', 'path']
        for attr in attrs:
            string += str(getattr(self, attr))
        return hash(string)

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        attrs = ['egress', 'ann_name', 'peer', 'as_path', 'as_path_len', 'path']
        for attr in attrs:
            if getattr(self, attr) != getattr(other, attr, None):
                return False
        return True
