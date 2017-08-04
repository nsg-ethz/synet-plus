#!/usr/bin/env python
"""
Synthesize configurations for eBGP protocol
"""

import z3
import networkx as nx

from synet.utils.common import PathReq
from synet.synthesis.ebgp import EBGP


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


class EBGPPropagation(object):
    def __init__(self, announcements, network_graph):
        self.network_graph = network_graph
        self.annoucenements = announcements
        self.reqs = []

    def add_path_req(self, req):
        assert isinstance(req, PathReq)
        self.reqs.append(req)
        self.nets_dag = {}

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

        # For each prefix compute a route propagation
        self.nets_dag = {}
        for net, paths in nets_paths.iteritems():
            g = nx.DiGraph()
            g.graph['sources'] = []
            for path in paths:
                i = 0
                while i < len(path) - 1:
                    src = path[i]
                    g.graph['sources'].append(src)
                    dst = path[i+1]
                    if src == '*':
                        continue
                    if dst == '*':
                        # TODO: support wildcards
                        assert False
                    assert self.network_graph.has_edge(src, dst), "No edge (%s, %s)" % (src, dst)
                    # The edge of supposed to be selected as best path
                    # according to the requirements
                    g.add_edge(src, dst, net=net, best=[net], nonbest=[], label='best')
                    # All the other paths, might propagate the route
                    # However, wont be selected as best paths by neighboring
                    # routers
                    for _, neighbour in self.network_graph.out_edges(src):
                        # TODO: Count for route reflected from neighbors
                        if not self.network_graph.is_local_router(neighbour):
                            continue
                        if g.has_edge(src, neighbour) or g.has_edge(neighbour, src):
                            continue
                        #g.add_edge(src, neighbour, best=False, label='nonbest')
                        g.add_edge(src, dst, net=net, best=[], nonbest=[net], label='nonbest')
                    i += 1
            # Till now, we must have a DAG
            assert nx.is_directed_acyclic_graph(g)
            # The leaf nodes in the DAG might still propagate the route
            # to other nodes, but wont be selected
            for node in g.nodes():
                # Just pick leaf nodes
                if g.out_degree(node) > 0:
                    continue
                for _, neighbour in self.network_graph.out_edges(node):
                    # A node wont propagate routes back to the neighbour that
                    # was selected as best route
                    if g.has_edge(neighbour, node) and g[neighbour][node]['best'] == True:
                        continue
                    g.add_edge(node, neighbour, net=net, best=[], nonbest=[net], label='nonbest')
            self.nets_dag[net] = g

        for net, g in self.nets_dag.iteritems():
            import pygraphviz
            from networkx.drawing.nx_agraph import write_dot
            write_dot(g, '/tmp/%s.dot' % net)

    def compose_graph(self, G, H, name=None):
        assert G.is_directed()
        assert H.is_directed()

        if name is None:
            name = "compose( %s, %s )" % (G.name, H.name)
        R = nx.DiGraph()
        R.name = name
        R.add_nodes_from(H.nodes())
        R.add_nodes_from(G.nodes())
        assert set(list(R.nodes())).issubset(set(list(self.network_graph.nodes())))


        all = list(G.edges_iter(data=True)) + list(H.edges_iter(data=True))
        for src, dst, attrs in all:
            print src, dst, attrs
            prev_best = R.get_edge_data(src, dst, {}).get('best', [])
            prev_nonbest = R.get_edge_data(src, dst, {}).get('nonbest', [])
            prev_best += attrs.get('best', [])
            prev_nonbest += attrs.get('nonbest', [])
            R.add_edge(src, dst, best=prev_best, nonbest=prev_nonbest)

        # add node attributes, H attributes take precedent over G attributes
        R.node.update(G.node)
        R.node.update(H.node)
        # add graph attributes, H attributes take precedent over G attributes
        R.graph.update(G.graph)
        R.graph.update(H.graph)
        return R

    def union_graphs(self):
        new = nx.DiGraph()
        for net, g in self.nets_dag.iteritems():
            new = self.compose_graph(new, g)
        for src, dst, attrs in new.edges_iter(data=True):
            print src, dst, attrs
            best = 'best: %s' % ', '.join(attrs['best'])
            nonbest = 'nonbest: %s' % ', '.join(attrs['nonbest'])
            new[src][dst]['label'] = "%s\\n%s" % (best, nonbest)
        from networkx.drawing.nx_agraph import write_dot
        write_dot(new, '/tmp/composed.dot')


    def compute(self):
        r3_anns = {}
        for ann in self.annoucenements['R3']:
            r3_anns['R3_%s' % ann.PREFIX] = ann

        r4_anns = {}
        for ann in self.annoucenements['R4']:
            r4_anns['R4_%s' % ann.PREFIX] = ann

        r4 = EBGP(400, 'R4', 'R4', r4_anns)
        r4.solve([], r4_anns.keys())

        mixed = {}
        mixed.update(r3_anns)
        mixed.update(r4.exported)
        r3 = EBGP(300, 'R3', 'R3', mixed)
        from ebgp import SetLocalPref
        from ebgp import MatchPeer
        from ebgp import EMPTY
        from ebgp import RouteMap
        RM1 = RouteMap(name='RM1', match=MatchPeer(EMPTY), action=SetLocalPref(EMPTY), permit=True)
        r3.solve([RM1], r3_anns.keys())
        print sorted(r3.exported.keys())
        #for node in self.network_graph.nodes():
        #    anns = self.annoucenements[node]
        #    ebgp = EBGP(anns)
        #    ebgp.solve()
