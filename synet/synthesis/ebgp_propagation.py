#!/usr/bin/env python
"""
Synthesize configurations for eBGP protocol
"""

from collections import namedtuple
import z3
import networkx as nx

from synet.utils.common import PathReq
from synet.synthesis.ebgp import EBGP

from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import MatchPeer
from synet.topo.bgp import MatchIpPrefixListList
from synet.topo.bgp import IpPrefixList
from synet.topo.bgp import VALUENOTSET
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine
from synet.topo.bgp import Access
from synet.topo.bgp import Community

from synet.synthesis.ebgp import Announcement


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


class EBGPPropagation(object):
    propagatedinfo = namedtuple('PropagatedInfo', ['egress', 'original_ann', 'new_ann'])

    def __init__(self, announcements, network_graph):
        self.network_graph = network_graph
        self.annoucenements = announcements
        self.reqs = []
        self.nets_dag = {}

    def add_path_req(self, req):
        """
        Add new requiremenet
        :param req: instance of PathReq
        :return: None
        """
        assert isinstance(req, PathReq)
        self.reqs.append(req)

    def compute_dags(self):
        """
        Compute the route propagation graphs for each prefix
        :return:
        """
        # Collect the paths from the requirements for each prefix
        nets_paths = {}
        for req in self.reqs:
            if req.dst_net not in nets_paths:
                nets_paths[req.dst_net] = []
            nets_paths[req.dst_net].append(req.path)

        # For each prefix compute a route propagation graph
        self.nets_dag = {}
        for net, paths in nets_paths.iteritems():
            # Create a graph especially for the propagation
            g = nx.DiGraph()
            # Keep list of sinks in the graph
            # Sinks are from where the routes are origianated
            g.graph['sources'] = []
            for path in paths:
                # The announcement at the beginning of the path
                ann = None
                for announcement in self.annoucenements[path[1]]:
                    if announcement.PREFIX == net and announcement.PEER == path[0]:
                        ann = announcement
                        break
                err = "A path that is not started by announcement %s" % path
                assert ann is not None, err
                # The first AS PATH
                aspath = ann.AS_PATH
                g.add_node(path[0], aspath=aspath)
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
                    if i == 0:
                        aspath = ann.AS_PATH
                        propagated = EBGPPropagation.propagatedinfo(
                            egress=path[1], original_ann=ann, new_ann=ann)
                    else:
                        curr = [self.network_graph.get_bgp_asnum(src)]
                        aspath = curr + g.node[src]['aspath']
                        new_ann = Announcement(
                            PREFIX=ann.PREFIX, PEER=src, ORIGIN=ann.ORIGIN,
                            AS_PATH=aspath, NEXT_HOP=src, LOCAL_PREF=100, COMMUNITIES=ann.COMMUNITIES)
                        propagated = EBGPPropagation.propagatedinfo(
                            egress=path[1], original_ann=ann, new_ann=new_ann)
                    g.add_node(dst, aspath=aspath)
                    # The edge is supposed to be selected as best path
                    # according to the requirements
                    label = "best: %s" % ','.join([str(n) for n in aspath])
                    g.add_edge(src, dst, best=propagated, nonbest=None, label=label)
                    # All the other paths, might propagate the route
                    # However, wont be selected as best paths by neighboring
                    # routers
                    for node, neighbour in self.network_graph.out_edges(src):
                        # TODO: Count for route reflected from neighbors
                        if not self.network_graph.is_local_router(neighbour):
                            continue
                        if g.has_edge(node, neighbour) or g.has_edge(neighbour, node):
                            continue
                        label = "nonbest: %s" % ','.join([str(n) for n in aspath])
                        g.add_edge(node, neighbour, best=None, nonbest=propagated, label=label, style='dashed')
            # Till now, we must have a DAG
            assert nx.is_directed_acyclic_graph(g)
            # The leaf nodes in the DAG might still propagate the route
            # to other nodes, but wont be selected
            for node in g.nodes():
                # Just pick leaf nodes
                if g.out_degree(node) > 0:
                    continue
                for src, neighbour in self.network_graph.out_edges(node):
                    # A node wont propagate routes back to the neighbour that
                    # was selected as best route
                    if g.has_edge(neighbour, src) and g[neighbour][src]['best']:
                        continue
                    curr = [self.network_graph.get_bgp_asnum(src)]
                    aspath = curr + g.node[node]['aspath']
                    label = "nonbest: %s" % ','.join([str(n) for n in aspath])
                    g.add_edge(src, neighbour, best=None, nonbest=propagated, label=label, style='dotted')
            self.nets_dag[net] = g

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
        g.add_nodes_from(g.nodes())

        for src, dst, attrs in propagation.edges_iter(data=True):
            best = attrs['best']
            nonbest = attrs['nonbest']
            if not g.has_edge(src, dst):
                g.add_edge(src, dst, nonbest=[], best=[])
            if best:
                assert isinstance(best, EBGPPropagation.propagatedinfo)
                g[src][dst]['best'].append(best)
            if nonbest:
                assert isinstance(nonbest, EBGPPropagation.propagatedinfo)
                g[src][dst]['nonbest'].append(nonbest)
        return g

    def print_union(self):
        for src, dst, attrs in self.union_graph.edges_iter(data=True):
            for b in attrs.get('best', []):
                assert isinstance(b, EBGPPropagation.propagatedinfo), b

            #print src, dst, attrs
            best_label = []
            for propagated in attrs['best']:
                ann = propagated.new_ann
                tmp = "best %s from %s: %s" % (ann.PREFIX, propagated.egress, ','.join([str(n) for n in ann.AS_PATH]))
                best_label.append(tmp)
            nonbest_label = []
            for propagated in attrs['nonbest']:
                ann = propagated.new_ann
                tmp = "nonbest %s from %s: %s" % (ann.PREFIX, propagated.egress, ','.join([str(n) for n in ann.AS_PATH]))
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
            for src, dst, attrs in g.edges_iter(data=True):
                for b in attrs.get('best', []):
                    assert isinstance(b, EBGPPropagation.propagatedinfo), b

        self.union_graph = g
        self.print_union()

    def compute(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        c = (c1, c2, c3)

        for node in self.union_graph.nodes():
            if not self.network_graph.is_local_router(node):
                continue
            asnum = self.network_graph.get_bgp_asnum(node)
            best = []
            nonbest = []
            for _, neighbor, attrs in self.union_graph.in_edges(node, data=True):
                best.extend(attrs['best'])
                nonbest.extend(attrs['nonbest'])
            anns = {}
            best_anns = {}
            nonbest_anns = {}
            for propagated in best:
                ann = propagated.new_ann
                aspath = '_'.join([str(n) for n in ann.AS_PATH])
                name = "%s_%s_%s" % (node, ann.PREFIX, aspath)
                best_anns[name] = ann
                anns[name] = ann

            for propagated in nonbest:
                ann = propagated.new_ann
                aspath = '_'.join([str(n) for n in ann.AS_PATH])
                name = "%s_%s_%s" % (node, ann.PREFIX, aspath)
                nonbest_anns[name] = ann
                anns[name] = ann

            ebgp = EBGP(asnum, node, node, anns, all_communities=c)
            lines = []
            for i in range(5):
                if i % 2 == 0:
                    line = RouteMapLine(
                        matches=[MatchPeer(VALUENOTSET)],
                        actions=[ActionSetLocalPref(VALUENOTSET)],
                        access=Access.permit,
                        lineno=10 + i
                    )
                else:
                    line = RouteMapLine(
                        matches=[MatchIpPrefixListList(
                            IpPrefixList(1, Access.permit, [VALUENOTSET]))],
                        actions=[ActionSetLocalPref(VALUENOTSET)],
                        access=Access.permit,
                        lineno=10 + i
                    )

                lines.append(line)
            route_map = RouteMap('RM1', lines=lines)
            assert ebgp.solve(route_map, best_anns.keys())
            print "Router:", node
            print "\tSelected:", sorted(ebgp.exported.keys())
            print "\tRequired:", sorted(best_anns.keys())
            print "\tDiscarde:", sorted(nonbest_anns.keys())

        return
