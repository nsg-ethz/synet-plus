#!/usr/bin/env python
"""
Synthesize configurations for (e/i)BGP protocol
"""

import logging
import z3

from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.utils.policy import SMTRouteMap
from synet.utils.smt_context import get_as_path_key
from synet.utils.smt_context import is_symbolic
from synet.utils.bgp_utils import get_propagated_info


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


DEFAULT_LOCAL_PREF = 100


z3.set_option('unsat-core', True)


class BGP(object):
    """
    Synthesize (e/i)BGP Config for one router
    """

    def __init__(self, node, network_graph, propagation_graph,
                 general_ctx, next_hop_map, allow_igp):
        """
        :param node: The router to synthesize configs for
        :param network_graph: NetworkGraph the general network gaph
        :param propagation_graph: nx.DiGraph of the propagated routes
        :param general_ctx: The general context with all the announcement variables
        :param next_hop_map:
        """
        self.log = logging.getLogger('%s.%s' % (
            self.__module__, self.__class__.__name__))
        self.log.debug("Creating BGP box for router %s", node)
        self.node = node
        self.network_graph = network_graph
        self.general_ctx = general_ctx
        self.propagation_graph = propagation_graph
        self.next_hop_map = next_hop_map
        self.allow_igp = allow_igp

        # Input route map -> context exported by the neighbor
        self.neighbor_exported_ctx = {}
        # Input Peer -> context learned from the neighbor
        # After applying the route map
        self.neighbor_imported_ctx = {}
        # Route maps (SMT)
        self.peer_route_map = {}
        self.constraints = {}
        self._model = None
        # Announcement name to list of peers that will advertise it
        self.prefix_ann_name_neighbors = {}
        # Announcement-> best PropagatedInfo
        self.ann_name_best = {}
        # Neighbor -> List of ann_names that are imported from it
        self.neighbor_imported_ann_names = {}

        # Peer -> the export context to it
        self.export_ctx = {}
        # Peer -> the export SMT route map to it
        self.export_route_map = {}
        self.path_costs = {}
        # Pre computations
        # Neighbor -> List of ann_names that are exported to a given neighbor
        self.neighbor_exported_ann_names = self.compute_exported_routes()
        self.selected_ctx = self._get_selected_sham()

    def compute_exported_routes(self):
        """
        Compute the routes to be exported on each outgoing edge of the router
        """
        self.log.debug("compute_exported_routes at %s", self.node)
        neighbor_exported_ann_names = {}
        for neighbor in self.network_graph.neighbors(self.node):
            # Announcement that the neighbor will learn from this router
            if not self.propagation_graph.has_edge(self.node, neighbor):
                continue
            all_anns = get_propagated_info(
                self.propagation_graph, neighbor, from_node=self.node,
                unselected=True, igp_pass=False)
            for prop in all_anns:
                ann_name = prop.ann_name
                if neighbor not in neighbor_exported_ann_names:
                    neighbor_exported_ann_names[neighbor] = {}
                neighbor_exported_ann_names[neighbor][ann_name] = prop
            self.log.debug(
                "compute_exported_routes at %s export to %s: %s",
                self.node, neighbor, [p.ann_name for p in all_anns])
        return neighbor_exported_ann_names

    def _get_selected_announcement(self, ann_name):
        """Return the new announcement for the selected sham"""
        ann = self.general_ctx.announcements[ann_name]
        name = "%s_%s_sel" % (self.node, ann_name)
        gctx = self.general_ctx
        if self.network_graph.is_peer(self.node):
            # If this is a peer, then all variables are known a priori
            new_ann = ann
        else:
            new_ann = Announcement(
                prefix=ann.prefix,
                peer=z3.Const('%s_peer' % name, gctx.peer_ctx.fun_range_sort),
                origin=z3.Const('%s_origin' % name, gctx.origin_ctx.fun_range_sort),
                as_path=z3.Const('%s_as_path' % name, gctx.as_path_ctx.fun_range_sort),
                as_path_len=z3.Const('%s_as_path_len' % name, z3.IntSort()),
                next_hop=z3.Const('%s_next_hop' % name, gctx.next_hop_ctx.fun_range_sort),
                local_pref=z3.Const('%s_local_pref' % name, z3.IntSort()),
                communities=dict(
                    [(c, z3.Const("%s_c_%s" % (name, c.name), z3.BoolSort()))
                     for c in ann.communities]),
                permitted=True)
        return new_ann

    def _get_selected_sham(self):
        """
        To resolve circular dependencies of getting the context generate
        by each router
        First generate a context with all symbolic variables.
        Then it will be glued in the selection process to concrete values
        in SMT
        :return: SMTContext
        """
        anns = {}
        ann_map = {}
        selected = get_propagated_info(
            self.propagation_graph, self.node, unselected=False, igp_pass=False)
        for propagated in selected:
            ann_name = propagated.ann_name
            new_ann = self._get_selected_announcement(ann_name)
            anns[ann_name] = new_ann
            ann_map[ann_name] = self.general_ctx.announcements_map[ann_name]
        new_ctx = self.general_ctx.get_new_context(
            name='S_%s' % (self.node),
            announcements=anns, announcements_map=ann_map)
        selected_paths = []
        for prop in selected:
            selected_paths.append((prop.ann_name, prop.path))
        self.log.debug("Created a sham selected context %s for router %s: %s",
                       new_ctx.name, self.node, selected_paths)
        return new_ctx

    def can_export_communities(self, src_peer, dst_peer):
        """
        Return true if the router is configured to send
        the communities values to the neighbor
        """
        return True

    def get_exported_announcement(
            self, ann_name, propagated, src_peer, dst_router, dst_peer):
        """
        Get the Announcement that will be exported to the neighbor
        :param ann_name: The name of the announcement
        :param propagated:
        :param src_peer:
        :param dst_router:
        :param dst_peer:
        :return:
        """
        self.log.debug(
            "get_exported_announcement %s at (%s, from bgp peer %s), "
            "export to (%s, to BGP peer %s)",
            ann_name, self.node, src_peer, dst_router, dst_peer)

        sctx = self.selected_ctx
        if ann_name not in sctx.announcements_map:
            err = "Router '%s' doesn't select '%s', " \
                  "current it's selecting: %s" % (self.node, ann_name, sctx.announcements_map.keys())
            raise RuntimeError(err)
        ann = sctx.announcements[ann_name]
        ann_var = sctx.announcements_map[ann_name]
        as_path_key = get_as_path_key(propagated.as_path)
        as_path = sctx.as_path_ctx.range_map[as_path_key]
        can_send_comm = self.can_export_communities(src_peer, dst_peer)

        # Communities are sent if only allowed to.
        if not is_symbolic(can_send_comm):
            if can_send_comm:
                communities = dict(
                    [(c, val) for c, val in ann.communities.iteritems()]
                )
            else:
                communities = dict([(c, False) for c in ann.communities])
        else:
            communities = dict(
                [(c, z3.If(can_send_comm == True, val, False))
                 for c, val in ann.communities.iteritems()])

        src_as_num = self.network_graph.get_bgp_asnum(src_peer)
        dst_as_num = self.network_graph.get_bgp_asnum(dst_peer)
        if not is_symbolic(src_as_num) and not is_symbolic(dst_as_num):
            # Local pref only transitive in iBGP
            # AS Path len increase with eBGP
            if src_as_num == dst_as_num:
                local_pref = ann.local_pref
                as_path_len = ann.as_path_len
            else:
                local_pref = DEFAULT_LOCAL_PREF
                as_path_len = ann.as_path_len + 1
        else:
            local_pref = z3.If(src_as_num == dst_as_num,
                               ann.local_pref,
                               DEFAULT_LOCAL_PREF)
            as_path_len = z3.If(src_as_num == dst_as_num,
                                ann.as_path_len + 1,
                                ann.as_path_len)

        new_ann = Announcement(
            prefix=ann.prefix,
            peer=sctx.peer_ctx.range_map[self.node],
            origin=sctx.origin_ctx.get_var(ann_var),
            as_path=as_path,
            as_path_len=as_path_len,
            next_hop=self.get_exported_next_hop(src_peer, dst_peer),
            local_pref=local_pref,
            communities=communities,
            permitted=True)
        return new_ann

    def get_export_ctx(self, src_peer, dst_router, dst_peer):
        """
        Get the SMTContext that will be exported to the neighbor,
        with applying export route map.
        """
        self.log.debug(
            "get_export_ctx at (%s, BGP %s), export to (%s, BGP peer %s)",
            self.node, src_peer, dst_router, dst_peer)

        if dst_router not in self.export_ctx:
            anns = {}
            ann_map = {}
            props = self.neighbor_exported_ann_names.get(dst_router, {})
            for ann_name, prop in props.iteritems():
                new_ann = self.get_exported_announcement(
                    ann_name, prop, src_peer, dst_router, dst_peer)
                anns[ann_name] = new_ann
                ann_map[ann_name] = self.general_ctx.announcements_map[ann_name]

            new_ctx = self.general_ctx.get_new_context(
                name='E_%s_%s' % (self.node, dst_router),
                announcements=anns, announcements_map=ann_map)

            if self.network_graph.is_bgp_enabled(self.node):
                # Apply export route maps, if any
                map_name = self.network_graph.get_bgp_export_route_map(src_peer, dst_peer)
                if not map_name:
                    self.export_ctx[dst_router] = new_ctx
                else:
                    rmap = self.network_graph.get_route_maps(self.node)[map_name]
                    # The generated context after applying the imported roue maps
                    smap = SMTRouteMap(name=rmap.name, route_map=rmap, context=new_ctx)
                    self.export_route_map[dst_router] = smap
                    new_ctx = smap.get_new_context()
                    self.export_ctx[dst_router] = new_ctx
                    self.export_route_map[dst_router] = smap
                self.log.debug(
                    "get_export_ctx.apply_route_map at %s, "
                    "export from %s to %s: %s",
                    self.node, dst_router, self.node, map_name)
            else:
                self.export_ctx[dst_router] = new_ctx
        ret = self.export_ctx[dst_router]
        self.log.debug(
            "get_export_ctx.return at %s, export from %s to %s: %s",
            self.node, dst_router, self.node, ret.name)
        return ret

    def get_exported_next_hop(self, src_peer, dst_peer):
        """
        Return the next hop value to be set
        to the routes exported the neighbor
        """
        self.log.debug(
            "get_exported_next_hop at router %s: from %s to %s",
            self.node, src_peer, dst_peer)
        next_hop = self.next_hop_map[src_peer][dst_peer]

        ret = self.general_ctx.next_hop_ctx.range_map[next_hop]
        self.log.debug(
            "get_exported_next_hop.return at router %s: from %s to %s: %s",
            self.node, src_peer, dst_peer, ret)
        return ret

    def get_neighbor_ctx(self, curr_peer, from_router, from_peer):
        """
        SMT context from the neighbor (BEFORE applying the import route maps)
        :return: SMTContext
        """
        self.log.debug(
            "get_neighbor_ctx at (%s, BGP peer %s) from (%s, BGP peer %s)",
            self.node, curr_peer, from_router, from_peer)

        assert from_router != self.node

        if from_router not in self.neighbor_exported_ctx:
            box = self.network_graph.node[from_router]['syn']['box']
            exported_ctx = box.get_export_ctx(from_peer, self.node, curr_peer)
            self.neighbor_exported_ctx[from_router] = exported_ctx
        ret = self.neighbor_exported_ctx[from_router]
        self.log.debug(
            "get_neighbor_ctx.return at (%s, BGP peer %s) from "
            "(%s, BGP peer %s): %s",
            self.node, curr_peer, from_router, from_peer, ret.name)
        return ret

    def get_imported_ctx(self, curr_peer, from_router, from_peer):
        """
        SMT context from the neighbor (AFTER applying the import route maps)
        :param curr_peer: The original node with BGP enabled
        :param from_router: The immediate router neighbor
        :param from_peer: the destination node that is BGP enabled
        :return: SMTContext
        """
        self.log.debug(
            "get_imported_ctx at (%s, BGP peer %s) from (%s, BGP peer %s)",
            self.node, curr_peer, from_router, from_peer)

        if from_router not in self.neighbor_imported_ctx:
            # The context from the peer
            self.log.debug(
                "get_imported_ctx.create at (%s, BGP peer %s)"
                " from (%s, BGP peer %s)",
                self.node, curr_peer, from_router, from_peer)

            exported_ctx = self.get_neighbor_ctx(curr_peer, from_router, from_peer)
            # The route map to applied to the exported announcements
            if self.network_graph.is_bgp_enabled(self.node):
                map_name = self.network_graph.get_bgp_import_route_map(
                    self.node, from_peer)
                if map_name:
                    rmap = self.network_graph.get_route_maps(self.node)[map_name]
                    smap = SMTRouteMap(name=rmap.name, route_map=rmap, context=exported_ctx)
                    self.peer_route_map[from_peer] = smap
                    # The generated context after applying the imported roue maps
                    imported_ctx = smap.get_new_context()
                    self.neighbor_imported_ctx[from_router] = imported_ctx
                else:
                    self.neighbor_imported_ctx[from_router] = exported_ctx
                self.log.debug(
                    "get_imported_ctx.apply_route_map at (%s, BGP peer %s) "
                    "from (%s, BGP peer %s): %s",
                    self.node, curr_peer, from_router, from_peer, map_name)
            else:
                self.neighbor_imported_ctx[from_router] = exported_ctx

        ret = self.neighbor_imported_ctx[from_router]
        self.log.debug(
            "get_imported_ctx.return at (%s, BGP peer %s) "
            "from (%s, BGP peer %s): %s",
            self.node, curr_peer, from_router, from_peer, ret.name)
        return ret

    def reg_learned_route(self, neighbor, propagated_info):
        """
        Register a route learned from a neighbor
        Fills self.prefix_ann_name_neighbors & self.neighbor_imported_ann_names
        """
        self.log.debug("Route %s at %s learned from neighbor %s",
                       propagated_info.ann_name, self.node, neighbor)
        assert self.propagation_graph.has_edge(neighbor, self.node)
        ann_name = propagated_info.ann_name
        announcement = self.general_ctx.announcements[ann_name]
        prefix = announcement.prefix
        if prefix not in self.prefix_ann_name_neighbors:
            self.prefix_ann_name_neighbors[prefix] = []
        if neighbor not in self.neighbor_imported_ann_names:
            self.neighbor_imported_ann_names[neighbor] = []
        if ann_name not in self.neighbor_imported_ann_names[neighbor]:
            self.neighbor_imported_ann_names[neighbor].append(ann_name)
            tmp = (neighbor, propagated_info)
            self.prefix_ann_name_neighbors[prefix].append(tmp)

    def compute_routes_learned(self):
        """
        Compute the list of routes learned from all neighbors
        Calls register_route_learned_from_neighbor
        :return: None
        """
        # Imported
        for neighbor, _ in self.network_graph.in_edges(self.node):
            # The context exported by the neighbor
            if not self.propagation_graph.has_edge(neighbor, self.node):
                continue
            # The announcements learned from that given neighbor
            all_anns = get_propagated_info(
                self.propagation_graph, self.node, from_node=neighbor, igp_pass=False)
            for prop in all_anns:
                self.reg_learned_route(neighbor, prop)
            learned = self.neighbor_imported_ann_names.get(neighbor, None)
            self.log.debug(
                "compute_best_routes.imported at %s, imported from: %s: %s",
                self.node, neighbor, learned)

    def compute_best_routes(self):
        """Compute self.ann_name_best"""
        selected_routes = get_propagated_info(
            self.propagation_graph, self.node, unselected=False, igp_pass=False)
        self.log.debug("compute_best_routes at %s, selected: %s",
                       self.node, selected_routes)
        for prop in selected_routes:
            prefix = self.general_ctx.announcements[prop.ann_name].prefix
            self.ann_name_best[prefix] = prop

    def _set_denied_prefixes(self, ann_name_best, prefix_ann_name_peers):
        """
        Set the constraints for the prefixes that are leaned but the router
        will deny then and wont install them in the routing table
        :param ann_name_best:
        :param prefix_ann_name_peers:
        :return: None
        """
        self.log.debug("_set_denied_prefixes at %s: %s", self.node, str([p for p in prefix_ann_name_peers if p not in ann_name_best]))
        for prefix in prefix_ann_name_peers:
            if prefix in ann_name_best:
                continue
            # Prefix was denied completely
            for (neighbor, prop_other) in prefix_ann_name_peers[prefix]:
                self.log.debug("  _set_denied %s %s" % (neighbor, prop_other))
                peer = prop_other.peer
                ann_name = prop_other.ann_name
                curr_peer = self.node
                imported_ctx = self.get_imported_ctx(curr_peer, neighbor, peer)
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

    def select_igp(self, prefix_ann_name_peers):
        """
        Synthesize Selection function at IGP routers
        """
        self.log.debug(
            "select_fun IGP at %s for ann_names: %s",
            self.node, self.ann_name_best)
        for prefix in prefix_ann_name_peers:
            for (neighbor, prop_other) in prefix_ann_name_peers[prefix]:
                peer = prop_other.peer
                ann_name = prop_other.ann_name
                curr_peer = self.get_curr_peer(prop_other)
                imported_ctx = self.get_imported_ctx(curr_peer, neighbor, peer)
                ann_var = self.general_ctx.announcements_map[ann_name]
                name = "IGP_%s" % self.node
                for value_ctx in self.selected_ctx.ctx_names:
                    ctx1 = getattr(self.selected_ctx, value_ctx)
                    ctx2 = getattr(imported_ctx, value_ctx)
                    if value_ctx != 'communities_ctx':
                        c = ctx1.get_var(ann_var) == ctx2.get_var(ann_var)
                        self.constraints["%s_%s" % (name, value_ctx)] = c
                    else:
                        for comm in ctx1:
                            c = ctx1[comm].get_var(ann_var) == ctx2[comm].get_var(ann_var)
                            self.constraints["%s_c_%s" % (name, comm.name)] = c

    def get_path_cost_var(self, path):
        if not isinstance(path, tuple):
            path = tuple(path)
        if path not in self.path_costs:
            name = "PC_%s" % '_'.join(path)
            var = z3.Const(name, z3.IntSort())
            self.constraints["%s_pos" % name] = var > 0
            self.path_costs[path] = var
            return var
        else:
            return self.path_costs[path]

    def get_select_igp(self, best_propagated, other_propagated):
        best_peer = best_propagated.peer
        other_peer = other_propagated.peer
        best_as_num = self.network_graph.get_bgp_asnum(best_peer)
        other_as_num = self.network_graph.get_bgp_asnum(other_peer)
        node_as_num = self.network_graph.get_bgp_asnum(self.node)
        symbolic = is_symbolic(node_as_num) and is_symbolic(other_as_num) and is_symbolic(best_as_num)
        if not symbolic:
            if node_as_num == other_as_num == best_as_num:
                best_path = best_propagated.path
                other_path = other_propagated.path
                best_cost = self.get_path_cost_var(best_path)
                other_cost = self.get_path_cost_var(other_path)
                return z3.And(best_cost < other_cost)
            else:
                return False
        else:
            assert False, "TODO: deal with symbolic as numbers"

    def can_used_igp(self, best_propagated, other_propagated):
        # TODO: register IGP path
        best_path = best_propagated.path
        other_path = other_propagated.path
        return self.allow_igp

    def set_best_values(self, prefix, best_propagated):
        """Synthesize Selection function for a given prefix"""
        self.log.debug("prefix_select %s at %s, best=%s", prefix, self.node, best_propagated)
        best_peer = best_propagated.peer
        if best_propagated.path:
            best_neighbor = best_propagated.path[-2]
        else:
            best_neighbor = None

        best_ann_name = best_propagated.ann_name
        best_ann_var = self.general_ctx.announcements_map[best_ann_name]
        curr_peer = self.node
        best_ctx = self.get_imported_ctx(curr_peer, best_neighbor, best_peer)
        name = "%s_sel_%s" % (self.node, best_ann_name)
        # First assert that the learned perfix has the same attributes
        # As the one selected (because the the shim context)
        for value_ctx in self.selected_ctx.ctx_names:
            ctx1 = getattr(self.selected_ctx, value_ctx)
            ctx2 = getattr(best_ctx, value_ctx)
            if value_ctx != 'communities_ctx':
                c = ctx1.get_var(best_ann_var) == ctx2.get_var(best_ann_var)
                self.constraints["%s_%s" % (name, value_ctx)] = c
            else:
                for comm in ctx1:
                    c = ctx1[comm].get_var(best_ann_var) == ctx2[comm].get_var(best_ann_var)
                    self.constraints["%s_c_%s" % (name, comm.name)] = c
        # Assert that the selected prefix is permitted
        t_c = self.selected_ctx.permitted_ctx.get_var(best_ann_var) == True
        self.constraints["%s_permitted" % name] = t_c

    def selector_func(self, prefix, best_propagated, other_propagated):
        """Synthesize Selection function for a given prefix"""
        self.log.debug("prefix_select %s at %s, best=%s", prefix, self.node, best_propagated)
        best_peer = best_propagated.peer
        if best_propagated.path:
            best_neighbor = best_propagated.path[-2]
        else:
            best_neighbor = None
        other_neighbor = other_propagated.path[-2]
        best_ann_name = best_propagated.ann_name
        best_ann_var = self.general_ctx.announcements_map[best_ann_name]
        curr_peer = self.node
        best_ctx = self.get_imported_ctx(curr_peer, best_neighbor, best_peer)
        name = "%s_sel_%s" % (self.node, best_ann_name)
        as_len_enabled = self.get_as_len_enabled()
        const_set = []
        const_selection = []

        self.log.debug("select at %s: %s over %s", self.node, best_propagated, other_propagated)
        peer = other_propagated.peer
        other_ann_name = other_propagated.ann_name
        s_ctx = self.selected_ctx
        o_ctx = self.get_imported_ctx(curr_peer, other_neighbor, peer)
        other_ann_var = self.general_ctx.announcements_map[other_ann_name]

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
        best_as_num = self.network_graph.get_bgp_asnum(best_peer)
        other_as_num = self.network_graph.get_bgp_asnum(peer)
        node_as_num = self.network_graph.get_bgp_asnum(self.node)
        other_permitted = o_ctx.permitted_ctx.get_var(other_ann_var)

        # Selection based on origin
        select_origin = z3.Or(
            # IGP is the lowest
            z3.And(s_origin == igp_origin,
                   o_origin != igp_origin),
            # EGP over incomplete
            z3.And(s_origin == ebgp_origin,
                   o_origin == incomplete_origin))
        # Selection based on AS Path len
        select_as_path_len = z3.And(
            as_len_enabled == True,  # Can we use AS Path len
            s_aslen < o_aslen)
        # Prefer eBGP routes over iBGP
        select_ebgp = z3.And(node_as_num != best_as_num,
                             node_as_num == other_as_num)
        # IGP
        select_igp = self.get_select_igp(best_propagated, other_propagated)
        use_igp = z3.Const("use_igp_%s" % name, z3.BoolSort())
        self.constraints["%s_use_igp" % name] = \
            use_igp == self.can_used_igp(best_propagated, other_propagated)

        # The BGP selection process
        const_selection.append(
            z3.Or(
                # 1) Permitted
                other_permitted == False,
                # 2) If Permitted, local pref
                z3.And(other_permitted,
                       s_localpref > o_localpref),
                # 3) AS Path Length
                z3.And(other_permitted,
                       s_localpref == o_localpref,
                       select_as_path_len == True),
                # 4) Origin Code IGP < EGP < Incomplete
                z3.And(other_permitted,
                       s_localpref == o_localpref,
                       select_as_path_len == False,
                       select_origin == True),
                # 5) TODO: MED Selection
                # 6) Prefer eBGP over iBGP paths.
                z3.And(
                    other_permitted,
                    s_localpref == o_localpref,
                    select_as_path_len == False,
                    select_origin == False,
                    select_ebgp == True),
                # 7) Path with the lowest IGP metric to the BGP next hop.
                z3.And(
                    other_permitted,
                    s_localpref == o_localpref,
                    select_as_path_len == False,
                    select_origin == False,
                    select_ebgp == False,
                    select_igp == True,
                    use_igp == True,
                ),
                # TODO (AH): More selection process

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

    def select_fun(self, ann_name_best, prefix_ann_name_peers):
        """The BGP Selection process"""
        self.log.debug(
            "select_fun at %s for ann_names: %s",
            self.node, self.ann_name_best)
        self._set_denied_prefixes(ann_name_best, prefix_ann_name_peers)
        prefixes = [str(tmp) for tmp in ann_name_best]
        for prefix, best_propagated in ann_name_best.iteritems():
            ordered = self.propagation_graph.node[self.node]['prefixes'][str(prefix)]['prop_ordered']
            unordered = self.propagation_graph.node[self.node]['prefixes'][str(prefix)]['prop_unordered']
            unselected = self.propagation_graph.node[self.node]['prefixes'][str(prefix)]['prop_unselected']
            for best_ecmp in ordered[0]:
                self.set_best_values(prefix, best_ecmp)
            for high_ecmp, low_ecmp in zip(ordered[0::1], ordered[1::1]):
                for high_path in high_ecmp:
                    for low_path in low_ecmp:
                        if len(high_path.path) < 2:
                            raise ValueError("Cannot have ECMP with path length less than two: %s", high_path)
                        if len(low_path.path) < 2:
                            raise ValueError("Cannot have ECMP with path length less than two: %s", high_path)
                        self.selector_func(prefix, high_path, low_path)
            for ecmp in ordered:
                for high_prop in ecmp:
                    #  Unordered
                    for other_prop in unordered:
                        self.selector_func(prefix, high_prop, other_prop)
                    #  Unselected
                    for other_prop in unselected:
                        self.selector_func(prefix, high_prop, other_prop)

    def syn_igp_path(self, prefix, propagated, segment, from_peer):
        prefixes = self.propagation_graph.node[self.node]['prefixes']
        igp_pass = prefixes[prefix]['igp_pass']
        if segment not in igp_pass:
            return
        imported_ctx = self.get_imported_ctx(from_peer, segment[-2], propagated.peer)
        ann_var = self.general_ctx.announcements_map[propagated.ann_name]
        name = "IGP_%s" % self.node
        for value_ctx in self.selected_ctx.ctx_names:
            ctx1 = getattr(self.selected_ctx, value_ctx)
            ctx2 = getattr(imported_ctx, value_ctx)
            if value_ctx != 'communities_ctx':
                c = ctx1.get_var(ann_var) == ctx2.get_var(ann_var)
                self.constraints["%s_%s" % (name, value_ctx)] = c
            else:
                for comm in ctx1:
                    c = ctx1[comm].get_var(ann_var) == ctx2[comm].get_var(ann_var)
                    self.constraints["%s_c_%s" % (name, comm.name)] = c

    def syn_igp(self):
        for prefix in self.prefix_ann_name_neighbors:
            for (name, propagated) in self.prefix_ann_name_neighbors[prefix]:
                prefix = str(prefix)
                neighbor = propagated.path[-2]
                path = propagated.path
                igp_pass = self.propagation_graph.node[self.node]['prefixes'][prefix]['igp_pass']
                if tuple(path) in igp_pass:
                    pass
                else:
                    nbox = self.network_graph.node[neighbor]['syn']['box']
                    nbox.syn_igp_path(prefix, propagated, tuple(path[:-1]), self.node)

    def synthesize(self):
        """Synthesize the BGP configurations for this box"""
        self.compute_best_routes()
        self.compute_routes_learned()
        print "X" * 50
        print "Learned Routes at", self.node
        for prefixe in self.prefix_ann_name_neighbors:
            print "  For Prefix", prefixe
            for (name, prop) in self.prefix_ann_name_neighbors[prefixe]:
                print "    Route", prop
        print "BEST ROUTES AT", self.node, self.ann_name_best
        print "X" * 50
        if self.network_graph.is_bgp_enabled(self.node):
            if self.network_graph.is_local_router(self.node):
                self.select_fun(self.ann_name_best, self.prefix_ann_name_neighbors)
            else:
                self.log.info(
                    "No select function is synthesized for external peer %s",
                    self.node)
            #self.syn_igp()

    def add_constraints(self, solver, track):
        """Add the Z3 constraints to the solver"""
        self.selected_ctx.add_constraints(solver, track)
        for rmap in self.peer_route_map.values():
            rmap.add_constraints(solver, track)
        for rmap in self.export_route_map.values():
            rmap.add_constraints(solver, track)
        for ctx in self.neighbor_exported_ctx.values():
            ctx.add_constraints(solver, track)
        for ctx in self.neighbor_imported_ctx.values():
            ctx.add_constraints(solver, track)
        for ctx in self.export_ctx.values():
            ctx.add_constraints(solver, track)
        for name, const in self.constraints.iteritems():
            if isinstance(const, bool):
                err = "Constraint already unsatisfied %s" % name
                assert const is True, err
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
        for rmap in self.export_route_map.values():
            rmap.set_model(model)
        for ctx in self.neighbor_exported_ctx.values():
            ctx.set_model(model)
        for ctx in self.neighbor_imported_ctx.values():
            ctx.set_model(model)
        for ctx in self.export_ctx.values():
            ctx.set_model(model)

    def get_config(self):
        """Get concrete route configs"""
        configs = []
        for _, rmap in self.peer_route_map.iteritems():
            configs.append(rmap.get_config())
        for _, rmap in self.export_route_map.iteritems():
            configs.append(rmap.get_config())
        return configs

    def update_network_graph(self):
        """Update the network graph with the concrete values"""
        for name, smap in self.peer_route_map.iteritems():
            rmap = smap.get_config()
            self.network_graph.add_route_map(self.node, rmap)
        for name, smap in self.export_route_map.iteritems():
            rmap = smap.get_config()
            self.network_graph.add_route_map(self.node, rmap)

    def __str__(self):
        return "BGPBox(%s)" % self.node
