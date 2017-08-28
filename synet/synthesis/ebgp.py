#!/usr/bin/env python
"""
Synthesize configurations for eBGP protocol
"""

import z3

from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import ActionSetNextHop
from synet.topo.bgp import Access
from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine
from synet.utils.policy import SMTRouteMap
from synet.utils.smt_context import get_as_path_key

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


z3.set_option('unsat-core', True)


class EBGP(object):
    """
    Synthesize eBGP Config for one router
    """
    def __init__(self, node, network_graph, propagation_graph, general_ctx):
        """
        :param node: The router to synthesize configs for
        :param network_graph: NetworkGraph the general network gaph
        :param propagation_graph: nx.DiGraph of the propagated routes
        :param general_ctx: The general context with all the announcement variables
        """
        self.node = node
        self.network_graph = network_graph
        self.general_ctx = general_ctx
        self.propagation_graph = propagation_graph
        # Input route map -> context exported by the neighbor
        self.peer_exported_ctx = {}
        # Input Peer -> context learned from the neighbor
        # After applying the route map
        self.peer_imported_ctx = {}
        # Route maps (SMT)
        self.peer_route_map = {}
        self.constraints = {}
        self._model = None
        # Announcement name to list of peers that will advertise it
        self.prefix_ann_name_peers = {}
        # Annoucement name to the best peer that will advertise it
        self.ann_name_best = {}

        # Peer -> List of ann_names that are imported from it
        self.peer_imported_ann_names = {}
        # Peer -> List of ann_names that are exported to it
        self.peer_exported_ann_names = {}
        self.compute_exported_routes()

        self.selected_ctx = self._get_selected_sham()

        # Peer -> the export context to it
        self.export_ctx= {}
        # Peer -> the export SMT route map to it
        self.export_route_map = {}

    def _get_selected_sham(self):
        """
        To resolve circular dependencies of getting the context generate
        by each router
        First generate a context with all symbolic variables.
        Then it will be glued in the selection process to concrete values
        :return: SMTContext
        """
        anns = {}
        ann_map = {}
        exported_names = []
        selected = self.propagation_graph.node[self.node]['selected']
        for propagated in selected:
            exported_names.append(propagated.ann_name)
        for ann_name in exported_names:
            ann = self.general_ctx.announcements[ann_name]
            n = "%s_%s_sel" % (self.node, ann_name)
            gctx = self.general_ctx
            if self.network_graph.is_peer(self.node):
                # If this is a peer, then all variables are known a priori
                new_ann = ann
            else:
                new_ann = Announcement(
                    prefix=ann.prefix,
                    peer=z3.Const('%s_peer' % n,
                                  gctx.peer_ctx.fun_range_sort),
                    origin=z3.Const('%s_origin' % n,
                                    gctx.origin_ctx.fun_range_sort),
                    as_path=z3.Const('%s_as_path' % n,
                                     gctx.as_path_ctx.fun_range_sort),
                    as_path_len=z3.Const('%s_as_path_len' % n,
                                         z3.IntSort()),
                    next_hop=z3.Const('%s_next_hop' % n,
                                      gctx.next_hop_ctx.fun_range_sort),
                    local_pref=z3.Const('%s_local_pref' % n,
                                        z3.IntSort()),
                    communities=dict(
                        [(c,
                          z3.Const("%s_c_%s" % (n, c.name),
                                   z3.BoolSort())) for c in ann.communities]),
                    permitted=True
                )
            anns[ann_name] = new_ann
            ann_map[ann_name] = self.general_ctx.announcements_map[ann_name]
        return self.general_ctx.get_new_context(
            name='S_%s' % (self.node),
            announcements=anns, announcements_map=ann_map)

    def get_export_ctx(self, neighbor):
        """Get the smt context that will be exported to the neighbor"""
        if neighbor not in self.export_ctx:
            anns = {}
            ann_map = {}
            for ann_name, prop in self.peer_exported_ann_names[neighbor].iteritems():
                # Generate new context with updated values
                sctx = self.selected_ctx
                ann = sctx.announcements[ann_name]
                ann_var = sctx.announcements_map[ann_name]
                n = "%s_%s_%s_export" % (self.node, neighbor, ann_name)
                as_path_key = get_as_path_key(prop.as_path)
                as_path = sctx.as_path_ctx.range_map[as_path_key]
                as_path_len = prop.as_path_len
                new_ann = Announcement(
                    prefix=ann.prefix,
                    peer=sctx.peer_ctx.range_map[self.node],
                    origin=sctx.origin_ctx.get_var(ann_var),
                    as_path=as_path,
                    as_path_len=as_path_len,
                    next_hop=self.get_exported_next_hop(neighbor),
                    local_pref=100,
                    communities=dict(
                        [(c,
                          z3.Const("%s_c_%s" % (n, c.name),
                                   z3.BoolSort())) for c in ann.communities]),
                    permitted=True
                )
                anns[ann_name] = new_ann
                ann_map[ann_name] = self.general_ctx.announcements_map[ann_name]
            new_ctx = self.general_ctx.get_new_context(
                name='E_%s_%s' % (self.node, neighbor),
                announcements=anns, announcements_map=ann_map)

            # Apply export route maps, if any
            map_name = self.network_graph.get_bgp_export_route_map(self.node, neighbor)
            if not map_name:
                self.export_ctx[neighbor] = new_ctx
            else:
                rmap = self.network_graph.get_route_maps(self.node)[map_name]
                # The generated context after applying the imported roue maps
                exported_ctx = self.get_neighbor_ctx(neighbor)
                smap = SMTRouteMap(name=rmap.name, route_map=rmap, context=new_ctx)
                self.peer_route_map[neighbor] = smap
                new_ctx = smap.get_new_context()
            self.export_ctx[neighbor] = new_ctx
        return self.export_ctx[neighbor]

    def get_exported_next_hop(self, neigbor):
        """
        Return the next hop value to be set
        to the routes exported the neighbor
        """
        return self.general_ctx.next_hop_ctx.range_map[self.node+'Hop']

    def get_neighbor_ctx(self, neighbor):
        """
        SMT context from the neighbor (BEFORE applying the import route maps)
        :param neighbor: string, node in NetworkGraph
        :return: SMTContext
        """
        assert neighbor != self.node
        if neighbor not in self.peer_exported_ctx:
            box = self.network_graph.node[neighbor]['syn']['box']
            exported_ctx = box.get_export_ctx(self.node)
            self.peer_exported_ctx[neighbor] = exported_ctx
        return self.peer_exported_ctx[neighbor]

    def get_imported_ctx(self, neighbor):
        """
        SMT context from the neighbor (AFTER applying the import route maps)
        :param neighbor: string, node in NetworkGraph
        :return: SMTContext
        """
        if neighbor not in self.peer_imported_ctx:
            # The route map to applied to the exported announcements
            map_name = self.network_graph.get_bgp_import_route_map(self.node, neighbor)
            if not map_name:
                rmap = self.get_default_import_map(self.node, neighbor)
                self.network_graph.add_route_map(self.node, rmap)
                map_name = rmap.name
            rmap = self.network_graph.get_route_maps(self.node)[map_name]
            # The generated context after applying the imported roue maps
            exported_ctx = self.get_neighbor_ctx(neighbor)
            smap = SMTRouteMap(name=rmap.name, route_map=rmap, context=exported_ctx)
            self.peer_route_map[neighbor] = smap
            imported_ctx = smap.get_new_context()
            self.peer_imported_ctx[neighbor] = imported_ctx
        return self.peer_imported_ctx[neighbor]

    def get_default_import_map(self, node, neighbor):
        """
        Get a default import route map, when no import route map is define
        :param node:
        :param neighbor:
        :return:
        """
        line = RouteMapLine(matches=None, actions=None,
                            access=Access.permit, lineno=10)
        name = "RImport_%s_%s" % (node, neighbor)
        rmap = RouteMap(name=name, lines=[line])
        return rmap

    def compute_exported_routes(self):
        # Exported
        for neighbor in self.network_graph.neighbors(self.node):
            # The context exported by the neighbor
            if not self.propagation_graph.has_edge(self.node, neighbor):
                continue
            # The announcements learned from that given peer
            best = self.propagation_graph[self.node][neighbor].get('best', [])
            nonbest = self.propagation_graph[self.node][neighbor].get('nonbest', [])
            all_anns = best + nonbest
            for prop in all_anns:
                ann_name = prop.ann_name
                if neighbor not in self.peer_exported_ann_names:
                    self.peer_exported_ann_names[neighbor] = {}
                self.peer_exported_ann_names[neighbor][ann_name] = prop

    def compute_best_routes(self):
        """Compute self.ann_name_best and self.prefix_ann_name_peers"""
        selected_routes = self.propagation_graph.node[self.node].get('selected', [])
        for prop in selected_routes:
            prefix = self.general_ctx.announcements[prop.ann_name].prefix
            self.ann_name_best[prefix] = prop

        # Imported
        for neighbor in self.network_graph.neighbors(self.node):
            # The context exported by the neighbor
            if not self.propagation_graph.has_edge(neighbor, self.node):
                continue
            # The announcements learned from that given peer
            best = self.propagation_graph[neighbor][self.node].get('best', [])
            nonbest = self.propagation_graph[neighbor][self.node].get('nonbest', [])
            all_anns = best + nonbest
            for prop in all_anns:
                ann_name = prop.ann_name
                prefix = self.general_ctx.announcements[ann_name].prefix
                if prefix not in self.prefix_ann_name_peers:
                    self.prefix_ann_name_peers[prefix] = []
                if neighbor not in self.peer_imported_ann_names:
                    self.peer_imported_ann_names[neighbor] = []
                self.peer_imported_ann_names[neighbor].append(ann_name)
                self.prefix_ann_name_peers[prefix].append((prop.peer, prop.ann_name))

    def _set_denied_prefixes(self, ann_name_best, prefix_ann_name_peers):
        """
        Set the constraints for the prefixes that are leaned but the router
        will deny then and wont install them in the routing table
        :param ann_name_best:
        :param prefix_ann_name_peers:
        :return: None
        """
        for prefix in prefix_ann_name_peers:
            if prefix in ann_name_best:
                continue
            # Prefix was denied completely
            for (peer, ann_name) in prefix_ann_name_peers[prefix]:
                imported_ctx = self.get_imported_ctx(peer)
                ann_var = self.general_ctx.announcements_map[ann_name]
                name = '%s_deny_%s_from_%s' % (self.node, ann_name, peer)
                permitted = imported_ctx.permitted_ctx
                const = z3.And(permitted.get_var(ann_var) == False)
                self.constraints[name] = const

    def get_as_len_enabled(self):
        """
        Return True if selecting routes based on AS Path len is enabled
        Will return concrete or symbolic variable (if it's a hole)
        :return:
        """
        # TODO: "bgp bestpath as-path ignore" from configs
        return True

    def select_fun(self, ann_name_best, prefix_ann_name_peers):
        """The BGP Selection process"""
        self._set_denied_prefixes(ann_name_best, prefix_ann_name_peers)
        for prefix, propagated in ann_name_best.iteritems():
            best_peer = propagated.peer
            best_ann_name = propagated.ann_name
            best_ann_var = self.general_ctx.announcements_map[best_ann_name]
            best_ctx = self.get_imported_ctx(best_peer)
            name = "%s_sel_%s" % (self.node, best_ann_name)
            as_len_enabled = self.get_as_len_enabled()
            const_set = []
            const_selection = []
            # First assert that the learned perfix has the same attributes
            # As the one selected (because the the shim context)
            for value_ctx in self.selected_ctx.ctx_names:
                if value_ctx != 'communities_ctx':
                    ctx1 = getattr(self.selected_ctx, value_ctx)
                    ctx2 = getattr(best_ctx, value_ctx)
                    const_set.append(ctx1.get_var(best_ann_var) ==
                                       ctx2.get_var(best_ann_var))
                else:
                    ctx1 = getattr(self.selected_ctx, value_ctx)
                    ctx2 = getattr(best_ctx, value_ctx)
                    for comm in ctx1:
                        const_set.append(ctx1[comm].get_var(best_ann_var) ==
                                           ctx2[comm].get_var(best_ann_var))

            # Assert that the selected prefix is permitted
            const_set.append(
                self.selected_ctx.permitted_ctx.get_var(best_ann_var) == True)

            for (peer, other_ann_name) in prefix_ann_name_peers[prefix]:
                s_ctx = self.selected_ctx
                o_ctx = self.get_imported_ctx(peer)
                other_ann_var = self.general_ctx.announcements_map[other_ann_name]
                if peer == best_peer and other_ann_name == best_ann_name:
                    continue
                else:
                    s_localpref = s_ctx.local_pref_ctx.get_var(best_ann_var)
                    o_localpref = o_ctx.local_pref_ctx.get_var(other_ann_var)

                    s_aslen = s_ctx.as_path_len_ctx.get_var(best_ann_var)
                    o_aslen = o_ctx.as_path_len_ctx.get_var(other_ann_var)

                    s_origin = s_ctx.origin_ctx.get_var(best_ann_var)
                    o_origin = o_ctx.origin_ctx.get_var(other_ann_var)

                    igp_origin = o_ctx.origin_ctx.range_map[
                        BGP_ATTRS_ORIGIN.IGP]
                    ebgp_origin = o_ctx.origin_ctx.range_map[
                        BGP_ATTRS_ORIGIN.EBGP]
                    incomplete_origin = o_ctx.origin_ctx.range_map[
                        BGP_ATTRS_ORIGIN.INCOMPLETE]

                    other_permitted = o_ctx.permitted_ctx.get_var(other_ann_var)
                    # The BGP selection process
                    const_selection.append(
                        z3.Or(
                            # 1) Permitted
                            z3.And(other_permitted == False),
                            # 2) If Permitted, local pref
                            z3.And(other_permitted,
                                   s_localpref > o_localpref),
                            # 3) AS Path Length
                            z3.And(other_permitted,
                                   as_len_enabled, # Can we use AS Path len
                                   s_localpref == o_localpref,
                                   s_aslen < o_aslen),
                            # 4) Origin Code IGP < EGP < Incomplete
                            z3.And(other_permitted,
                                   s_localpref == o_localpref,
                                   z3.Or(
                                       as_len_enabled == False,
                                       z3.And(as_len_enabled, s_aslen == o_aslen),
                                   ),
                                   z3.Or(
                                       # IGP is the lowest
                                       z3.And(s_origin == igp_origin,
                                              o_origin != igp_origin),
                                       # EGP over incomplete
                                       z3.And(s_origin == ebgp_origin,
                                              o_origin == incomplete_origin)))
                            # TODO (AH): More selection process
                            # 5) MED Selection
                            # 6) Prefer eBGP over iBGP paths.
                            # 7) Path with the lowest IGP metric to the BGP next hop.
                            # 8) Determine if multiple paths
                            #    require installation in the
                            #    routing table for BGP Multipath.
                            #      Continue, if bestpath is not yet selected.
                            # 9) Prefer the route that comes from the BGP router
                            #    with the lowest router ID.

                        ))
                    # Make sure all variables are bound to a value
                    # (not just the best route)
                    if other_ann_name != best_ann_name:
                        for value_ctx in self.selected_ctx.ctx_names:
                            if value_ctx != 'communities_ctx':
                                ctx1 = getattr(s_ctx, value_ctx)
                                ctx2 = getattr(o_ctx, value_ctx)
                                const_set.append(ctx1.get_var(other_ann_var) ==
                                                   ctx2.get_var(other_ann_var))
                            else:
                                ctx1 = getattr(self.selected_ctx, value_ctx)
                                ctx2 = getattr(o_ctx, value_ctx)
                                for comm in ctx1:
                                    const_set.append(ctx1[comm].get_var(other_ann_var) ==
                                                       ctx2[comm].get_var(other_ann_var))

            self.constraints["%s_set" % name] = z3.And(*const_set)
            self.constraints[name] = z3.And(*const_selection)

    def synthesize(self):
        """Synthesize the BGP configurations for this box"""
        self.compute_best_routes()
        self.select_fun(self.ann_name_best, self.prefix_ann_name_peers)

    def add_constraints(self, solver, track):
        """Add the Z3 constraints to the solver"""
        self.selected_ctx.add_constraints(solver, track)
        for rmap in self.peer_route_map.values():
            rmap.add_constraints(solver, track)
        for ctx in self.peer_exported_ctx.values():
            ctx.add_constraints(solver, track)
        for ctx in self.peer_imported_ctx.values():
            ctx.add_constraints(solver, track)
        for name, const in self.constraints.iteritems():
            if isinstance(const, bool):
                assert const is True
                continue
            if track:
                solver.assert_and_track(const, name)
            else:
                solver.add(const)

    def set_model(self, model):
        """Set the Z3 Model for this box"""
        self._model = model
        self.selected_ctx.set_model(model)
        for rmap in self.peer_route_map.values():
            rmap.set_model(model)
        for ctx in self.peer_exported_ctx.values():
            ctx.set_model(model)
        for ctx in self.peer_imported_ctx.values():
            ctx.set_model(model)

    def get_config(self):
        """Get concrete route configs"""
        configs = []
        for _, rmap in self.peer_route_map.iteritems():
            configs.append(rmap.get_config())
        return configs

    def __str__(self):
        return "EBGPBox(%s)" % self.node
