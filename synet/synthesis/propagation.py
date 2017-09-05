#!/usr/bin/env python
"""
Synthesize configurations for eBGP protocol
"""

import copy

import networkx as nx
import z3

from synet.synthesis.bgp import BGP
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.graph import NetworkGraph
from synet.utils.common import PathReq
from synet.utils.smt_context import SMTASPathLenWrapper
from synet.utils.smt_context import SMTASPathWrapper
from synet.utils.smt_context import SMTCommunityWrapper
from synet.utils.smt_context import SMTContext
from synet.utils.smt_context import SMTLocalPrefWrapper
from synet.utils.smt_context import SMTNexthopWrapper
from synet.utils.smt_context import SMTOriginWrapper
from synet.utils.smt_context import SMTPeerWrapper
from synet.utils.smt_context import SMTPermittedWrapper
from synet.utils.smt_context import SMTPrefixWrapper
from synet.utils.smt_context import get_as_path_key
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import VALUENOTSET


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


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
        self.egress = egress
        self.ann_name = ann_name
        self.peer = peer
        self.as_path = as_path
        self.as_path_len = as_path_len
        self.path = path

    def __str__(self):
        return "Prop<%s, %s, %s, %s, %s, %s" % (
            self.egress,
            self.ann_name,
            self.peer,
            self.as_path,
            self.as_path_len,
            self.path)

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if not self.egress == getattr(other, 'egress'):
            return False
        if not self.ann_name == getattr(other, 'ann_name'):
            return False
        if not self.peer == getattr(other, 'peer'):
            return False
        if not self.as_path == getattr(other, 'as_path'):
            return False
        if not self.as_path_len == getattr(other, 'as_path_len'):
            return False
        if not self.path == getattr(other, 'path'):
            return False
        return True


class EBGPPropagation(object):
    """Computes the BGP route propagation graph"""

    def __init__(self, reqs, network_graph, allow_igp=False):
        """
        :param reqs: Path requirements
        :param network_graph: NetworkGraph
        """
        assert isinstance(network_graph, NetworkGraph)
        self.network_graph = network_graph
        self.reqs = []
        self.nets_dag = {}
        self.all_anns = {}
        self.union_graph = None
        self.prefix_list = []
        self.as_path_list = []
        self.peer_list = []
        self.next_hop_list = []
        self.communities_list = []
        self.prefix_peers = {}
        # Node -> neighbor -> nexthop
        self.next_hop_map = {}
        self.compute_next_hop_map()
        for req in reqs:
            self.add_path_req(req)
        self.assign_announcement_names()
        self.compute_dags()
        self.union_graphs()
        self.compute_additional_values()
        self.general_context = self.get_general_context()
        self.boxes = []
        # Prefix -> list of peers that announces it

        for node in self.network_graph.routers_iter():
            #if not self.network_graph.is_bgp_enabled(node):
            #    continue
            if 'syn' not in self.network_graph.node[node]:
                self.network_graph.node[node]['syn'] = {}
            box = BGP(
                node=node,
                network_graph=self.network_graph,
                propagation_graph=self.union_graph,
                general_ctx=self.general_context,
                next_hop_map=self.next_hop_map,
                allow_igp=allow_igp
            )
            self.boxes.append(box)
            self.network_graph.node[node]['syn']['box'] = box

    def assign_announcement_names(self):
        """Assigns variable names for each learned announcement from peers"""
        self.all_anns = {}
        for node in self.network_graph.peers_iter():
            anns = self.network_graph.get_bgp_advertise(node)
            if 'syn' not in self.network_graph.node[node]:
                self.network_graph.node[node]['syn'] = {}
            if 'anns' not in self.network_graph.node[node]['syn']:
                self.network_graph.node[node]['syn']['anns'] = {}
            for ann in anns:
                prefix = ann.prefix
                if prefix not in self.prefix_peers:
                    self.prefix_peers[prefix] = []
                self.prefix_peers[prefix].append(node)
                name = "%s_%s" % (node, prefix)
                assert name not in self.all_anns
                self.all_anns[name] = ann
                self.network_graph.node[node]['syn']['anns'][name] = ann

    def compute_next_hop_map(self):
        """Compute the possible next hop values in the network"""
        for node in self.network_graph.routers_iter():
            if node not in self.next_hop_map:
                self.next_hop_map[node] = {}
            if not self.network_graph.get_bgp_asnum(node):
                # BGP is not configured on this router
                continue
            neighbors = self.network_graph.get_bgp_neighbors(node)
            for neighbor in neighbors:
                iface = self.network_graph.get_bgp_neighbor_iface(node, neighbor)
                if is_empty(iface):
                    # TODO: Synthesie proper next hop
                    asnum1 = self.network_graph.get_bgp_asnum(node)
                    asnum2 = self.network_graph.get_bgp_asnum(neighbor)
                    if asnum1 != asnum2 and self.network_graph.has_edge(neighbor, node):
                        iface = self.network_graph.get_edge_iface(neighbor, node)
                    else:
                        loopbacks = self.network_graph.get_loopback_interfaces(neighbor)
                        if not loopbacks:
                            iface = 'lo0'
                            self.network_graph.set_loopback_addr(neighbor, iface, VALUENOTSET)
                        else:
                            iface = loopbacks.keys()[0]
                self.network_graph.set_bgp_neighbor_iface(node, neighbor, iface)
                assert iface, "Synthesize connected first"
                iface = iface.replace("/", "-")
                nxt = "%s-%s" % (neighbor, iface)
                self.next_hop_map[node][neighbor] = nxt
                self.next_hop_list.append(nxt)

    def compute_additional_values(self):
        """
        Fills self.as_path_list with known AS Paths
        Fills self.peer_list with all known peers
        :return: None
        """
        all_list = self.all_anns.values()
        for _, _, attrs in self.union_graph.edges_iter(data=True):
            all_list += attrs.get('best', [])
            all_list += attrs.get('nonbest', [])
        for item in all_list:
            as_path = item.as_path
            if as_path not in self.as_path_list:
                self.as_path_list.append(as_path)
        self.peer_list = list([node for node in self.network_graph.routers_iter()])

    def get_general_context(self):
        """
        Creates the SMT context that contains all the known announcements
        :return: SMTContext
        """
        name = 'general_ctx'
        prefix_list = self.prefix_list
        peer_list = self.peer_list
        as_path_list = [get_as_path_key(p) for p in self.as_path_list]
        next_hope_list = self.next_hop_list
        communities_list = self.communities_list
        all_anns = self.all_anns

        # Ann Type
        (ann_sort, announcements) = z3.EnumSort('AnnSort', all_anns.keys())

        # Create a map ann_name -> ann_var
        ann_map = dict([(str(ann), ann) for ann in announcements])
        ann_var_map = dict([(ann_map[ann], all_anns[str(ann)]) for ann in ann_map])

        # Basic functions
        local_pref_fun = z3.Function('LocalPref', ann_sort, z3.IntSort())
        permitted_fun = z3.Function('PermittedFun', ann_sort, z3.BoolSort())
        as_path_len_fun = z3.Function('AsPathLenFunc', ann_sort, z3.IntSort())

        # Functions with custom range

        # Prefixes
        read_list = [ann.prefix for ann in all_anns.values()
                     if not is_empty(ann.prefix)]
        # Make sure the list is uique
        prefix_list = list(set(read_list + prefix_list))
        (prefix_sort, prefixes) = z3.EnumSort('PrefixSort', prefix_list)
        prefix_map = dict([(str(prefix), prefix) for prefix in prefixes])
        prefix_map = prefix_map
        prefix_fun = z3.Function('PrefixFunc', ann_sort, prefix_sort)

        # Peers
        read_list = [x.peer for x in all_anns.values() if not is_empty(x.peer)]
        peer_list = list(set(read_list + peer_list))
        (peer_sort, peers) = z3.EnumSort('PeerSort', peer_list)
        peer_map = dict([(str(p), p) for p in peers])
        peer_map = peer_map
        peer_fun = z3.Function('PeerFun', ann_sort, peer_sort)

        # BGP announcement origins
        origin_list = BGP_ATTRS_ORIGIN.__members__.keys()
        (origin_sort, origins) = z3.EnumSort('OriginSort', origin_list)
        origin_map = dict([(str(p), p) for p in origins])
        for k, v in BGP_ATTRS_ORIGIN.__members__.iteritems():
            origin_map[v] = origin_map[k]
        origin_map = origin_map
        origin_fun = z3.Function('OriginFun', ann_sort, origin_sort)

        # AS path list
        read_list = [get_as_path_key(x.as_path) for x in all_anns.values()
                     if not is_empty(x.as_path)]
        as_path_list = list(set(read_list + as_path_list))
        (as_path_sort, as_paths) = z3.EnumSort('ASPathSort', as_path_list)
        as_path_map = dict([(str(p), p) for p in as_paths])
        as_path_map = as_path_map
        as_path_fun = z3.Function('AsPathFunc', ann_sort, as_path_sort)

        # Next Hop
        read_list = [x.next_hop for x in all_anns.values()
                     if not is_empty(x.next_hop)]
        next_hope_list = list(set(read_list + next_hope_list))
        (next_hop_sort, next_hops) = z3.EnumSort('NexthopSort', next_hope_list)
        next_hop_map = dict([(str(p), p) for p in next_hops])
        next_hop_map = next_hop_map
        next_hop_fun = z3.Function('NexthopFunc', ann_sort, next_hop_sort)

        # Create functions for communities
        read_list = all_anns.values()[0].communities.keys()
        communities_list = list(set(communities_list + read_list))
        communities_fun = {}
        for c in communities_list:
            name = 'Has_%s' % c.name
            communities_fun[c] = z3.Function(name, ann_sort, z3.BoolSort())

        return EBGPPropagation.create_context(name, all_anns, ann_map, ann_sort,
                                              prefix_fun, prefix_sort, prefix_map,
                                              peer_fun, peer_sort, peer_map,
                                              origin_fun, origin_sort, origin_map,
                                              as_path_fun, as_path_sort, as_path_map,
                                              as_path_len_fun,
                                              next_hop_fun, next_hop_sort, next_hop_map,
                                              local_pref_fun, permitted_fun, communities_fun)

    def add_path_req(self, req):
        """
        Add new requirement
        :param req: instance of PathReq
        :return: None
        """
        assert isinstance(req, PathReq)
        self.reqs.append(req)

    def compute_bfs(self, prefix, ann_as_path, source, best_paths):
        """
        Computes BFS for how the announcement will be propagated
        """
        def check_path(path, paths):
            """Check if the reached path is in the requirements"""
            for tmp in paths:
                if len(tmp) < len(path):
                    continue
                if path == tmp[:len(path)]:
                    return True
            return False

        def check_igbp(as_path, new_as):
            """Check AS Path is valid"""
            if len(as_path) < 2:
                return True
            if as_path[-2:] == [new_as, new_as]:
                return False
            return True

        def is_loop(as_path, new_as):
            """Check AS Path is valid"""
            # TODO check for AS PATH loops
            return False

        # This is a modified BFS Search
        visited = [source]
        stack = [iter(self.network_graph[source])]
        # List of Paths that are part of the requirements
        best = []
        # List of Paths that are NOT part of the requirements
        nonbest = []
        curr_as_path = [ann_as_path, self.network_graph.get_bgp_asnum(source)]
        while stack:
            children = stack[-1]
            child = next(children, None)
            if child is None:
                stack.pop()
                removed = visited.pop()
                if self.network_graph.get_bgp_asnum(removed):
                    curr_as_path.pop()
            else:
                if child not in visited:
                    if self.network_graph.is_bgp_enabled(child):
                        as_num = self.network_graph.get_bgp_asnum(child)
                        # The next node has BGP enabled
                        last_as = as_num
                        if check_path(visited + [child], best_paths):
                            if not check_igbp(curr_as_path, as_num):
                                err = "iBGP can only propagate once (without route reflectors)."
                                err += " Cannot propgated {} from {} to {}". \
                                    format(prefix, visited[-1], child)
                                assert False, err
                            if is_loop(curr_as_path, as_num):
                                err = "AS Path loop"
                                assert False, err
                            visited.append(child)
                            curr_as_path.append(as_num)
                            stack.append(iter(self.network_graph[child]))
                            path = tuple(copy.copy(visited))
                            if path not in best:
                                best.append(path)
                        else:
                            # Check first if valid iBGP path before
                            # adding to nonbest list
                            if check_igbp(curr_as_path, as_num):
                                path = tuple(copy.copy(visited) + [child])
                                if path not in nonbest:
                                    nonbest.append(path)
                    else:
                        # IGP Path, keep going
                        #last_as = None
                        visited.append(child)
                        stack.append(iter(self.network_graph[child]))
        # TODO: Check all requirements are statified
        return best, nonbest

    def compute_propagated_information(self, dag, path, is_best,
                                       computed_path, sources, ann_map):
        """
        Takes input the requirement path and the computed path from BFS
        Then figure out how the routes will propagated along the DAG
        :param dag: The route propagation graph for the given prefix
        :param path: The requirement path
        :param is_best: True for best path
        :param computed_path: Path computed from BFS
        :param sources: Peer->ann_name for the peers announcing the prefix
        :param ann_map: Ann_name->Announcement
        :return:
        """
        source = computed_path[0]
        ann_name = sources[source]
        ann = ann_map[ann_name]
        assert self.network_graph.is_bgp_enabled(source)
        assert self.network_graph.is_bgp_enabled(computed_path[-1])

        asnum0 = self.network_graph.get_bgp_asnum(source)
        asnum1 = self.network_graph.get_bgp_asnum(computed_path[1])
        if asnum0 == asnum1:
            egress = computed_path[0]
        else:
            egress = computed_path[1]
        first = PropagatedInfo(
            egress=egress, ann_name=ann_name, peer=source,
            as_path=ann.as_path, as_path_len=ann.as_path_len,
            path=[])
        dag.add_node(source, selected=first)
        prev_path = [source]
        last_as_neighbor = source
        previous = {}
        previous[source] = first
        for i in range(1, len(path)):
            src = path[i - 1]
            node = path[i]
            prev = previous[src]
            src_asnum = self.network_graph.get_bgp_asnum(src)
            node_asnum = self.network_graph.get_bgp_asnum(node)
            prev_path.append(node)
            if node_asnum is None:
                # IGP node
                new_as_path = prev.as_path
            else:
                # Previous node migth be IGP
                last_as = self.network_graph.get_bgp_asnum(last_as_neighbor)
                new_as = src_asnum or last_as
                new_as_path = prev.as_path + [new_as]

            prop = PropagatedInfo(
                egress=prev.egress, ann_name=prev.ann_name,
                peer=last_as_neighbor,
                as_path=new_as_path, as_path_len=len(new_as_path),
                path=prev_path)
            previous[node] = prop

            dag.add_node(node)

            if self.network_graph.is_bgp_enabled(node):
                last_as_neighbor = node
                prev_path = [node]

            # Add Edge to the propagation graph
            if is_best:
                dag.node[node]['selected'] = prop
                label = "best: %s %s" % (
                    prop.ann_name, ','.join([str(n) for n in prop.path]))
                dag.add_edge(src, node, best=prop, nonbest=None, label=label)
            else:
                label = "nonbest: %s %s" % (
                    prop.ann_name, ','.join([str(n) for n in prop.path]))
                dag.add_edge(src, node, best=None, nonbest=prop, label=label)

    def compute_dag(self, prefix, paths):
        """For a given prefix and list of paths compute the forwarding DAG"""
        # Create propagation DAG for the prefix
        dag = nx.DiGraph()
        # Keep list of sinks in the graph
        # Sinks are from where the routes are originated
        sources = {}
        all_anns = {}
        # All peers will advertise the prefix
        for peer in self.prefix_peers[prefix]:
            ann_name = None
            announcement = None
            # Announcements by the start node in the path
            anns = self.network_graph.node[peer]['syn']['anns']
            for ann_name, announcement in anns.iteritems():
                if announcement.prefix == prefix and announcement.peer == peer:
                    break
            assert announcement
            sources[peer] = ann_name
            all_anns[ann_name] = announcement

        for source in sources:
            ann_name = sources[source]
            ann = all_anns[ann_name]
            best, nonbest = self.compute_bfs(prefix, ann.as_path, source, paths)
            for path in nonbest:
                self.compute_propagated_information(dag, path, False, path, sources, all_anns)
            for path in best:
                self.compute_propagated_information(dag, path, True, path, sources, all_anns)
        return dag

    def compute_dags(self):
        """
        Compute the route propagation graphs for each prefix
        """
        # Collect the paths from the requirements for each prefix
        nets_paths = {}
        for req in self.reqs:
            if req.dst_net not in nets_paths:
                nets_paths[req.dst_net] = []
            nets_paths[req.dst_net].append(req.path)
        for prefix in self.prefix_peers:
            if prefix not in nets_paths:
                nets_paths[prefix] = []
        # For each prefix compute a route propagation graph
        self.nets_dag = {}
        for net, paths in nets_paths.iteritems():
            self.nets_dag[net] = self.compute_dag(net, paths)

        for net, g in self.nets_dag.iteritems():
            import pygraphviz
            from networkx.drawing.nx_agraph import write_dot
            write_dot(g, '/tmp/%s.dot' % net)

    def add_net_graph(self, g, propagation):
        """
        Add new route propagation graph for a specific net to the graph
        that holds all the route propagation information for all prefixes
        :param g:
        :param propagation:
        :return:
        """
        assert g.is_directed()
        assert propagation.is_directed()
        topo_nodes = set(list(self.network_graph.nodes()))
        propagation_nodes = set(list(propagation.nodes()))
        assert propagation_nodes.issubset(topo_nodes)
        for src, dst, attrs in propagation.edges_iter(data=True):
            best = attrs['best']
            nonbest = attrs['nonbest']
            src_selected = propagation.node[src].get('selected', None)
            dst_selected = propagation.node[dst].get('selected', None)
            src_selected_g = g.node[src]['selected'] if g.has_node(src) else []
            dst_selected_g = g.node[dst]['selected'] if g.has_node(dst) else []
            if src_selected and src_selected not in src_selected_g:
                src_selected_g.append(src_selected)
            if dst_selected and dst_selected not in dst_selected_g:
                dst_selected_g.append(dst_selected)
            g.add_node(src, selected=src_selected_g)
            g.add_node(dst, selected=dst_selected_g)
            if not g.has_edge(src, dst):
                g.add_edge(src, dst, nonbest=[], best=[])
            if best:
                assert isinstance(best, PropagatedInfo), best
                if best not in g[src][dst]['best']:
                    g[src][dst]['best'].append(best)
            if nonbest:
                assert isinstance(nonbest, PropagatedInfo), nonbest
                if nonbest not in g[src][dst]['nonbest']:
                    g[src][dst]['nonbest'].append(nonbest)
        return g

    def print_union(self):
        def get_path(as_path):
            return ','.join([str(n) for n in as_path])
        for src, dst, attrs in self.union_graph.edges_iter(data=True):
            best_label = []
            for prop in attrs['best']:
                tmp = "best %s from %s: %s (len %s)" % (
                    prop.ann_name, prop.egress, get_path(prop.as_path),
                    prop.as_path_len)
                best_label.append(tmp)
            nonbest_label = []
            for prop in attrs['nonbest']:
                tmp = "nonbest %s from %s: %s (len %s)" % (
                    prop.ann_name, prop.egress, get_path(prop.as_path),
                    prop.as_path_len)
                nonbest_label.append(tmp)
            best_str = "\\n".join(best_label)
            nonbest_str = "\\n".join(nonbest_label)
            self.union_graph[src][dst]['label'] = "%s\\n%s" % (best_str, nonbest_str)

        from networkx.drawing.nx_agraph import write_dot
        write_dot(self.union_graph, '/tmp/composed.dot')

    def union_graphs(self):
        """Union all the DAG per prefix to one graph"""
        union_g = nx.DiGraph()
        for propagation in self.nets_dag.values():
            union_g = self.add_net_graph(union_g, propagation)
        self.union_graph = union_g
        self.print_union()

    def add_constraints(self, solver, track=True):
        """Add constraints to the solver"""
        for box in self.boxes:
            box.add_constraints(solver, track)

    def set_model(self, model):
        """Set the Z3 model"""
        for box in self.boxes:
            box.set_model(model)

    def update_network_graph(self):
        """Update the network graph with the concrete values"""
        for box in self.boxes:
            box.update_network_graph()

    def synthesize(self):
        """Synthesize the BGP configs"""
        for node in sorted(list(self.network_graph.local_routers_iter())):
            if 'syn' not in self.network_graph.node[node]:
                continue
            box = self.network_graph.node[node]['syn']['box']
            box.synthesize()

    @staticmethod
    def create_context(name,
                       announcements, announcements_map, announcement_sort,
                       prefix_fun, prefix_sort, prefix_map,
                       peer_fun, peer_sort, peer_map,
                       origin_fun, origin_sort, origin_map,
                       as_path_fun, as_path_sort, as_path_map,
                       as_path_len_fun,
                       next_hop_fun, next_hop_sort, next_hop_map,
                       local_pref_fun, permitted_fun, communities_fun):
        """
        Creates SMTContext
        :return: SMTContext
        """

        ann_var_map = dict([(announcements_map[ann], announcements[str(ann)])
                            for ann in announcements_map])
        # Create wrapper
        wprefix = SMTPrefixWrapper(
            'prefixw', announcement_sort, ann_var_map,
            prefix_fun, prefix_sort, prefix_map)

        wpeer = SMTPeerWrapper(
            'wpeer', announcement_sort, ann_var_map,
            peer_fun, peer_sort, peer_map)

        worigin = SMTOriginWrapper(
            'worigin', announcement_sort, ann_var_map,
            origin_fun, origin_sort, origin_map)

        waspath = SMTASPathWrapper(
            'waspath', announcement_sort, ann_var_map,
            as_path_fun, as_path_sort, as_path_map)

        waspathlen = SMTASPathLenWrapper(
            'waspathlen', announcement_sort, ann_var_map,
            as_path_len_fun)

        wnext_hop = SMTNexthopWrapper(
            'wnext_hop', announcement_sort, ann_var_map,
            next_hop_fun, next_hop_sort, next_hop_map)

        wlocalpref = SMTLocalPrefWrapper(
            'wlocalpref', announcement_sort, ann_var_map,
            local_pref_fun)

        wpermitted = SMTPermittedWrapper(
            'wpermitted', announcement_sort, ann_var_map,
            permitted_fun)

        wcommunities = {}
        for community in communities_fun.keys():
            name = community.name
            wc1 = SMTCommunityWrapper(
                'w%s' % name, community, announcement_sort,
                ann_var_map, communities_fun[community])
            wcommunities[community] = wc1

        ctx = SMTContext(name, announcements, announcements_map,
                         announcement_sort, wprefix, wpeer, worigin, waspath,
                         waspathlen, wnext_hop, wlocalpref, wcommunities,
                         wpermitted)
        return ctx
