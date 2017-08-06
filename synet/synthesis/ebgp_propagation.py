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
                    else:
                        curr = [self.network_graph.get_bgp_asnum(src)]
                        aspath = curr + g.node[src]['aspath']
                    g.add_node(dst, aspath=aspath)
                    # The edge is supposed to be selected as best path
                    # according to the requirements
                    label = "best: %s" % ','.join([str(n) for n in aspath])
                    g.add_edge(src, dst, net=net, best=[net], aspath=[aspath],
                               nonbest=[], label=label)
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
                        g.add_edge(node, neighbour, net=net, best=[], aspath=[aspath],
                                   nonbest=[net], label=label)
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
                    g.add_edge(src, neighbour, net=net, best=[], aspath=[aspath],
                               nonbest=[net], label=label)
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
            net = attrs['net']
            best = attrs['best']
            nonbest = attrs['nonbest']
            aspath = attrs['aspath']
            if not g.has_edge(src, dst):
                g.add_edge(src, dst, aspaths={}, nonbest=[], best=[], nets=[])
            g[src][dst]['nets'].append(net)
            if best:
                g[src][dst]['best'].append((net, aspath))
            if nonbest:
                g[src][dst]['nonbest'].append((net, aspath))
        return g

    def union_graphs(self):
        g = nx.DiGraph()
        for net, propagation in self.nets_dag.iteritems():
            g = self.add_net_graph(g, propagation)

        for src, dst, attrs in g.edges_iter(data=True):
            print src, dst, attrs
            best = []
            for net, path in attrs['best']:
                tmp = "best %s: %s" % (net, ','.join([str(n) for n in path]))
                best.append(tmp)
            nonbest = []
            for net, path in attrs['nonbest']:
                tmp = "nonbest %s: %s" % (net, ','.join([str(n) for n in path]))
                best.append(tmp)
            best = "\\n".join(best)
            nonbest = "\\n".join(nonbest)
            g[src][dst]['label'] = "%s\\n%s" % (best, nonbest)
        from networkx.drawing.nx_agraph import write_dot
        write_dot(g, '/tmp/composed.dot')

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
        from synet.synthesis.ebgp import SetLocalPref
        from synet.synthesis.ebgp import MatchPeer
        from synet.synthesis.ebgp import EMPTY
        from synet.synthesis.ebgp import RouteMap
        RM1 = RouteMap(name='RM1', match=MatchPeer(EMPTY), action=SetLocalPref(EMPTY), permit=True)
        r3.solve([RM1], r3_anns.keys())
        print sorted(r3.exported.keys())
        #for node in self.network_graph.nodes():
        #    anns = self.annoucenements[node]
        #    ebgp = EBGP(anns)
        #    ebgp.solve()
