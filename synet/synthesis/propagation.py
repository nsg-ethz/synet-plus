#!/usr/bin/env python
"""
Synthesize configurations for eBGP protocol
"""

from collections import namedtuple
import z3
import networkx as nx

from synet.synthesis.ebgp import EBGP
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.utils.common import PathReq
from synet.utils.smt_context import SMTASPathWrapper
from synet.utils.smt_context import SMTASPathLenWrapper
from synet.utils.smt_context import SMTContext
from synet.utils.smt_context import SMTCommunityWrapper
from synet.utils.smt_context import SMTLocalPrefWrapper
from synet.utils.smt_context import SMTNexthopWrapper
from synet.utils.smt_context import SMTOriginWrapper
from synet.utils.smt_context import SMTPeerWrapper
from synet.utils.smt_context import SMTPrefixWrapper
from synet.utils.smt_context import SMTPermittedWrapper
from synet.utils.smt_context import get_as_path_key
from synet.utils.smt_context import is_empty


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


class EBGPPropagation(object):
    propagatedinfo = namedtuple('PropagatedInfo',
                                ['egress', 'ann_name', 'peer',
                                 'as_path', 'as_path_len'])

    def __init__(self, reqs, network_graph):
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
            if 'syn' not in self.network_graph.node[node]:
                self.network_graph.node[node]['syn'] = {}
            box = EBGP(
                node, self.network_graph, self.union_graph,
                self.general_context)
            self.boxes.append(box)
            self.network_graph.node[node]['syn']['box'] = box

    def assign_announcement_names(self):
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

    def compute_additional_values(self):
        all_list = self.all_anns.values()
        for _, _, attrs in self.union_graph.edges_iter(data=True):
            all_list += attrs.get('best', [])
            all_list += attrs.get('nonbest', [])
        for item in all_list:
            as_path = item.as_path
            if as_path not in self.as_path_list:
                self.as_path_list.append(as_path)
        # TODO better compute next hop and peers
        self.next_hop_list = list("%sHop" % r for r in self.network_graph.local_routers_iter())
        self.peer_list = list(self.network_graph.routers_iter())

    def get_general_context(self):
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
        reverse_communities = {}
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
        Add new requiremenet
        :param req: instance of PathReq
        :return: None
        """
        assert isinstance(req, PathReq)
        self.reqs.append(req)

    def _compute_net_dag(self, prefix, paths):
        """For a given prefix and list of paths compute the forwarding DAG"""
        # Create propagation DAG for the prefix
        g = nx.DiGraph()
        # Keep list of sinks in the graph
        # Sinks are from where the routes are originated
        g.graph['sources'] = []
        node_as_paths = {}
        # All peers will advertise the prefix
        for peer in self.prefix_peers[prefix]:
            ann = None
            ann_name = None
            # Announcements by the start node in the path
            anns = self.network_graph.node[peer]['syn']['anns']
            for ann_name, announcement in anns.iteritems():
                if announcement.prefix == prefix and announcement.peer == peer:
                    ann = announcement
                    break
            as_path = ann.as_path
            as_path_len = ann.as_path_len
            node_as_paths[peer] = dict(best=True, as_path=as_path,
                                          as_path_len=as_path_len)
            first = EBGPPropagation.propagatedinfo(
                egress=peer, ann_name=ann_name, peer=peer,
                as_path=as_path, as_path_len=as_path_len)
            g.add_node(peer, selected=first)

        for path in paths:
            err = "A path that is not started by announcement %s" % path
            assert g.has_node(path[0]), err
            source_p = g.node[path[0]]['selected']
            ann_name = source_p.ann_name
            ann = self.all_anns[ann_name]
            as_path = source_p.as_path
            as_path_len = source_p.as_path_len

            for i in range(len(path) - 1):
                src = path[i]
                g.graph['sources'].append(src)
                dst = path[i + 1]
                if src == '*':
                    continue
                if dst == '*':
                    # TODO: support wildcards
                    assert False
                err = "Reqs has edge (%s, %s) but that doesn't" \
                      " exist in the topology" % (src, dst)
                assert self.network_graph.has_edge(src, dst), err

                # Compute the AS PATH that led to this node
                curr = [self.network_graph.get_bgp_asnum(src)]
                as_path = curr + node_as_paths[src]['as_path']
                as_path_len = 1 + node_as_paths[src]['as_path_len']
                propagated = EBGPPropagation.propagatedinfo(
                    egress=path[1], ann_name=ann_name, peer=src,
                    as_path=as_path, as_path_len=as_path_len)

                node_as_paths[dst] = dict(best=True,
                                          as_path=as_path,
                                          as_path_len=as_path_len)
                if i < len(path) - 1:
                    g.add_node(path[i+1], selected=propagated)
                # The edge is supposed to be selected as best path
                # according to the requirements
                label = "best:%s %s" % (propagated.ann_name, ','.join([str(n) for n in propagated.as_path]))
                g.add_edge(src, dst, best=propagated,
                           nonbest=None, label=label, style='solid')

        # Till now, we must have a DAG
        assert nx.is_directed_acyclic_graph(g)
        # All the other paths, might propagate the route
        # However, wont be selected as best paths by neighboring
        # routers
        for src in self.network_graph.routers_iter():
            for _, neighbour in self.network_graph.out_edges(src):
                if g.has_edge(src, neighbour) and g[src][neighbour]['best']:
                    continue
                if g.has_edge(neighbour, src) and g[neighbour][src]['best']:
                    continue
                selected = g.node.get(src, {}).get('selected', None)
                if not selected:
                    continue
                curr = [self.network_graph.get_bgp_asnum(src)]
                as_path = curr + node_as_paths[src]['as_path']
                as_path_len = 1 + node_as_paths[src]['as_path_len']
                egress = selected.egress
                propagated = EBGPPropagation.propagatedinfo(
                    egress=egress, ann_name=selected.ann_name, peer=src,
                    as_path=as_path, as_path_len=as_path_len)

                label = "nonbest: %s %s" % (propagated.ann_name, ','.join([str(n) for n in propagated.as_path]))
                g.add_edge(src, neighbour,
                           best=None, nonbest=propagated,
                           label=label, style='dashed')

        for node, attrs in g.nodes(True):
            selected = attrs.get('selected', None)
            peer = selected.peer if selected else None
            ann_name = selected.ann_name if selected else None
            g.node[node]['label'] = "%s\\nBest Peer: %s\\n Ann_name %s" % (node, peer, ann_name)
        return g

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
        for prefix in self.prefix_peers.keys():
            if prefix not in nets_paths:
                nets_paths[prefix] = []
        # For each prefix compute a route propagation graph
        self.nets_dag = {}
        for net, paths in nets_paths.iteritems():
            self.nets_dag[net] = self._compute_net_dag(net, paths)

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
                assert isinstance(best, EBGPPropagation.propagatedinfo), best
                g[src][dst]['best'].append(best)
            if nonbest:
                assert isinstance(nonbest, EBGPPropagation.propagatedinfo), nonbest
                g[src][dst]['nonbest'].append(nonbest)
        return g

    def print_union(self):
        for src, dst, attrs in self.union_graph.edges_iter(data=True):
            best_label = []
            for prop in attrs['best']:
                tmp = "best %s from %s: %s (len %s)" % (
                    prop.ann_name, prop.egress, ','.join([str(n) for n in prop.as_path]), prop.as_path_len)
                best_label.append(tmp)
            nonbest_label = []
            for prop in attrs['nonbest']:
                tmp = "nonbest %s from %s: %s (len %s)" % (
                    prop.ann_name, prop.egress, ','.join([str(n) for n in prop.as_path]), prop.as_path_len)
                nonbest_label.append(tmp)
            best_str = "\\n".join(best_label)
            nonbest_str = "\\n".join(nonbest_label)
            self.union_graph[src][dst]['label'] = "%s\\n%s" % (best_str, nonbest_str)

        from networkx.drawing.nx_agraph import write_dot
        write_dot(self.union_graph, '/tmp/composed.dot')

    def union_graphs(self):
        g = nx.DiGraph()
        for net, propagation in self.nets_dag.iteritems():
            g = self.add_net_graph(g, propagation)
        self.union_graph = g
        for src, dst, attrs in self.union_graph.edges_iter(data=True):
            if 'syn' not in self.network_graph[src][dst]:
                self.network_graph[src][dst]['syn'] = {}
            self.network_graph[src][dst]['syn']['best'] = attrs['best']
            self.network_graph[src][dst]['syn']['nonbest'] = attrs['nonbest']
        self.print_union()

    def add_constraints(self, solver, track=True):
        for box in self.boxes:
            box.add_constraints(solver, track)

    def set_model(self, model):
        for box in self.boxes:
            box.set_model(model)

    def synthesize(self):
        for node in self.network_graph.local_routers_iter():
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
