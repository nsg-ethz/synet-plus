#!/usr/bin/env python
"""
Common utils for BGP synthesis
"""

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


def write_dag(dag, file):
    from networkx.drawing.nx_agraph import write_dot
    for node, data in dag.nodes(data=True):
        label = "%s\\n" % node
        label += "Ordered: %s\\n" % data.get('ordered', None)
        label += "Unordered: %s\\n" % data.get('unordered', None)
        label += "Unselected: %s\\n" % data.get('unselected', None)
        dag.node[node]['label'] = label
    write_dot(dag, file)


def get_propagated_info(propagation_graph, node,
                        prefix=None, from_node=None, unselected=True):
    all_props = []
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
    if not from_node:
        return all_props
    ret = []
    for prop in all_props:
        if len(prop.path) < 2:
            continue
        if prop.path[-2] != from_node:
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
        return "Prop<%s, %s, %s, %s, %s, %s>" % (
            self.egress,
            self.ann_name,
            self.peer,
            self.as_path,
            self.as_path_len,
            self.path)

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        attrs = ['egress', 'ann_name', 'peer', 'as_path', 'as_path_len', 'path']
        for attr in attrs:
            if getattr(self, attr) != getattr(other, attr, None):
                return False
        return True
