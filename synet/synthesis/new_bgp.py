#!/usr/bin/env python
"""
Synthesize configurations for (e/i)BGP protocol
"""

import copy
import logging

import networkx as nx
import z3

from synet.topo.bgp import Announcement
from synet.topo.graph import NetworkGraph
from synet.utils.fnfree_policy import SMTRouteMap
from synet.utils.fnfree_smt_context import ASPATH_SORT
from synet.utils.fnfree_smt_context import AnnouncementsContext
from synet.utils.fnfree_smt_context import BGP_ORIGIN_SORT
from synet.utils.fnfree_smt_context import NEXT_HOP_SORT
from synet.utils.fnfree_smt_context import PEER_SORT
from synet.utils.fnfree_smt_context import PREFIX_SORT
from synet.utils.fnfree_smt_context import SolverContext
from synet.utils.smt_context import get_as_path_key


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


DEFAULT_LOCAL_PREF = 100
DEFAULT_MED = 100


def get_propagated_info(propagation_graph, node,
                        prefix=None, from_node=None,
                        unselected=True, from_peer=None, igp_pass=False):
    all_props = set()
    if not propagation_graph.has_node(node):
        return all_props
    for net, data in propagation_graph.node[node]['nets'].iteritems():
        if prefix and net != prefix:
            continue
        for propgated in data['paths_info']:
            all_props.add(propgated)
        if unselected:
            for propgated in data['block_info']:
                all_props.add(propgated)
        #if igp_pass:
        #    for prop in data['prop_igp_pass']:
        #        all_props.append(prop)
    #if not from_node:
    #    return all_props
    ret = set()
    for propgated in all_props:
        if from_node:
            if len(propgated.path) < 2:
                continue
            if propgated.path[-2] != from_node:
                continue
        if from_peer:
            if propgated.peer != from_peer:
                continue
        ret.add(propgated)
    return ret


def create_sym_ann(ctx, fixed_values=None, name_prefix=None):
    """Return the new symbolic announcement announcement"""
    if not fixed_values:
        fixed_values = {}
    vals = {}
    all_attrs = [
        ('prefix', PREFIX_SORT, None),
        ('peer', PEER_SORT, None),
        ('origin', BGP_ORIGIN_SORT, lambda x: x.name),
        ('as_path', ASPATH_SORT, get_as_path_key),
        ('as_path_len', z3.IntSort(), None),
        ('next_hop', NEXT_HOP_SORT, None),
        ('local_pref', z3.IntSort(), None),
        ('med', z3.IntSort(), None),
        ('permitted', z3.BoolSort(), None),
    ]
    for attr, vsort, conv in all_attrs:
        is_enum = isinstance(vsort, basestring)
        value = None
        if is_enum:
            vsort = ctx.get_enum_type(vsort)
        if attr in fixed_values:
            if is_enum:
                value = vsort.get_symbolic_value(fixed_values[attr])
            else:
                value = fixed_values[attr]
        nprefix = "%s_" % attr
        nprefix = "%s_%s" % (name_prefix, nprefix) if name_prefix else nprefix
        vals[attr] = ctx.create_fresh_var(vsort=vsort, value=value, name_prefix=nprefix)
        #print "CREATED", vals[attr]
    comms = 'communities'
    vals[comms] = {}
    for community in ctx.communities:
        value = fixed_values.get(comms, {}).get(community, None)
        nprefix = "Comm_%s_" % str(community).replace(":", "_")
        nprefix = "%s_%s" % (name_prefix, nprefix) if name_prefix else nprefix
        comm_var = ctx.create_fresh_var(vsort=z3.BoolSort(), value=value, name_prefix=nprefix)
        vals['communities'][community] = comm_var
        #print "CREATED", comm_var
    new_ann = Announcement(**vals)
    return new_ann


class BGP(object):
    def __init__(self, node, propagation):
        log_name = '%s.%s' % (self.__module__, self.__class__.__name__)
        self.log = logging.getLogger(log_name)
        self.node = node
        self.propagation = propagation
        self.ctx = self.propagation.ctx
        assert isinstance(self.ctx, SolverContext)
        self.network_graph = self.propagation.network_graph
        assert isinstance(self.network_graph, NetworkGraph)
        self.next_hop_map = self.propagation.next_hop_map
        self.peering_graph = self.propagation.verify.peering_graph
        self.ebgp_propagation = self.propagation.ebgp_propagation
        self.ibgp_propagation = self.propagation.ibgp_propagation
        assert isinstance(self.peering_graph, nx.Graph)
        assert isinstance(self.ebgp_propagation, nx.Graph)
        assert isinstance(self.ibgp_propagation, nx.Graph)
        self.rmaps = {}
        # Symbolic variables of all (possibly) learned announcements
        self.anns_map = self.create_symbolic_announcements()
        # The context for all (possibly) learned announcements
        self.anns_ctx = AnnouncementsContext(self.anns_map.values(), mutators=[self])
        # Only the subset of announcement that are used to
        # (possibly) forward traffic
        self.selected_sham = self._get_selected_sham()
        # The set of PropagatedInfo that will be exported to neighbors
        self.exported_routes = self.compute_exported_routes()
        self.export_ctx = {}

    def create_symbolic_announcements(self):
        """
        Create symbolic variables of all (possibly) learned announcements
        :return dict PropagationInfo -> Symbolic Announcement
        """
        anns_map = dict()
        all_anns = get_propagated_info(self.ibgp_propagation, self.node, unselected=True)
        for propagated in all_anns:
            fixed = {'prefix': propagated.ann_name}
            # Partial eval the next hop
            if propagated.egress:
                # If the route is externally learned,
                # then it's the next hop of the egress
                egress_index = propagated.path.index(propagated.egress)
                egress_peer = propagated.path[egress_index + 1]
                egress_peer = egress_peer if egress_peer != self.node else propagated.egress
                fixed['next_hop'] = self.next_hop_map[self.node][egress_peer]
            elif len(propagated.as_path) == 1:
                # If the route is announced by this router
                # then pick one of the next hops
                # TODO: Make this method more accurate
                for _, vals in self.next_hop_map.iteritems():
                    for r, nxt in vals.iteritems():
                        if r == self.node:
                            fixed['next_hop'] = nxt
                            break
            assert 'next_hop' in fixed
            # Partial eval peer
            fixed['peer'] = self.node if len(propagated.path) == 1 else propagated.peer
            # TODO: support more origins
            fixed['origin'] = 'EBGP'
            # TODO: parial eval AS path
            # TODO support as path rewrites
            fixed['as_path'] = get_as_path_key(propagated.as_path)
            fixed['as_path_len'] = len(propagated.as_path) - 1
            if len(propagated.path) == 1:
                fixed['local_pref'] = DEFAULT_LOCAL_PREF
                fixed['med'] = DEFAULT_MED
                fixed['communities'] = {}
                for community in self.ctx.communities:
                    fixed['communities'][community] = False
            new_ann = create_sym_ann(self.ctx, fixed, name_prefix="Sham_%s_" % self.node)
            anns_map[propagated] = new_ann
        return anns_map

    def compute_exported_routes(self):
        """
        Compute the routes to be exported on each outgoing edge of the router
        """
        self.log.debug("compute_exported_routes at %s", self.node)
        exported_info = {}

        # First compute what is exported to each neighbor
        for neighbor in self.network_graph.get_bgp_neighbors(self.node):
            # Announcement that the neighbor will learn from this router
            all_anns = get_propagated_info(self.ibgp_propagation, neighbor,
                                           from_peer=self.node, unselected=True,
                                           igp_pass=False)
            for prop in all_anns:
                if neighbor not in exported_info:
                    exported_info[neighbor] = set()
                exported_info[neighbor].add(prop)

        for peer, props in exported_info.iteritems():
            print "Node %s Exported to %s: %s" % (self.node, peer, props)

        # Second,  map the propagated to the local announcements
        export_anns = {}
        for neighbor, propagated in exported_info.iteritems():
            n_attrs = self.ibgp_propagation.node[neighbor]
            if neighbor not in export_anns:
                export_anns[neighbor] = {}
            for prop in propagated:
                origin = n_attrs['nets'][prop.ann_name]['origins'][prop]
                if not origin:
                    continue
                export_anns[neighbor][prop] = self.anns_map[origin]
            if not export_anns[neighbor]:
                del export_anns[neighbor]
        # Third, apply export route map (if any)
        for neighbor, vals in export_anns.iteritems():
            rmap_name = self.network_graph.get_bgp_export_route_map(self.node, neighbor)
            if not rmap_name:
                continue
            rmap = self.network_graph.get_route_maps(self.node)[rmap_name]
            # Since the announcemets will change
            # We try to keep the ordering
            props = []
            anns = []
            for prop, ann in vals.iteritems():
                props.append(prop)
                anns.append(ann)
            tmp = self.anns_ctx.create_new(anns, self.compute_exported_routes)
            smt_map = SMTRouteMap(rmap, tmp, self.ctx)
            self.rmaps[rmap_name] = smt_map
            smt_map.execute()
            for index, prop in enumerate(props):
                export_anns[neighbor][prop] = smt_map.announcements[index]
        return export_anns

    def _get_selected_sham(self):
        """
        To resolve circular dependencies of getting the context generate
        by each router
        First generate a context with all symbolic variables.
        Then it will be glued in the selection process to concrete values
        in the SMT Sovler
        :return: dict (propagatedinfo->announcement)
        """
        selected = get_propagated_info(self.ibgp_propagation, self.node, unselected=False)
        print "SELECTED AT", self.node
        for s in selected:
            print "\t", s
        anns = [self.anns_map[propagated] for propagated in selected]
        return self.anns_ctx.create_new(anns, mutator=self._get_selected_sham)

    def compute_imported_routes(self):
        #attrs = ['prefix', 'peer', 'origin', 'as_path', 'as_path_len',
        #         'next_hop', 'local_pref', 'med', 'permitted']
        # The attributes that are read from the neighbor
        attrs = ['prefix', 'origin', 'local_pref', 'med', 'permitted']
        for neighbor in self.network_graph.get_bgp_neighbors(self.node):
            if not self.ibgp_propagation.has_node(neighbor):
                continue
            asnum = self.network_graph.get_bgp_asnum(self.node)
            neighbor_asnum = self.network_graph.get_bgp_asnum(neighbor)
            is_ebgp_neighbor = asnum != neighbor_asnum
            n_attrs = self.ibgp_propagation.node[neighbor]
            neighbor_exported = n_attrs['box'].exported_routes
            if self.node not in neighbor_exported:
                # The neighbor doesn't export anything to this router
                print "NODE %s doesn't import anything from %s: %s" % (self.node, neighbor, neighbor_exported.keys())
                continue
            imported = {}
            for prop, ann in neighbor_exported[self.node].iteritems():
                assert prop in self.anns_map
                ann = copy.copy(ann)  # Shallow copy
                if is_ebgp_neighbor:
                    ann.local_pref = self.ctx.create_fresh_var(
                        z3.IntSort(),
                        value=DEFAULT_LOCAL_PREF)
                imported[prop] = ann

            # Apply import route maps if any
            rmap_name = self.network_graph.get_bgp_import_route_map(self.node, neighbor)
            if rmap_name:
                rmap = self.network_graph.get_route_maps(self.node)[rmap_name]
                # Since the announcements will change
                # We try to keep the ordering
                props = []
                anns = []
                for prop, ann in imported.iteritems():
                    props.append(prop)
                    anns.append(ann)
                tmp = self.anns_ctx.create_new(anns, self.compute_exported_routes)
                smt_map = SMTRouteMap(rmap, tmp, self.ctx)
                self.rmaps[rmap_name] = smt_map
                smt_map.execute()
                cc = self.ctx._tracked.keys()[:]
                for index, prop in enumerate(props):
                    imported[prop] = smt_map.announcements[index]
            # Assign the values
            for prop, ann in imported.iteritems():
                for attr in attrs:
                    curr = getattr(self.anns_map[prop], attr)
                    imp = getattr(ann, attr)
                    prefix = 'Imp_%s_from_%s_%s_' % (self.node, neighbor, attr)
                    self.ctx.register_constraint(curr.var == imp.var,
                                                 name_prefix=prefix)
                for community in self.ctx.communities:

                    curr = self.anns_map[prop].communities[community]
                    imp = ann.communities[community]
                    prefix = 'Imp_%s_from_%s_Comm_%s_' % (self.node, neighbor, community.name)
                    self.ctx.register_constraint(curr.var == imp.var, name_prefix=prefix)

    def selector_func(self, best_propagated, best_ann_var,
                      other_propagated, other_ann_var):
        """Synthesize Selection function for a given prefix"""
        self.log.debug(
            "prefix_select %s at %s, best=%s", best_propagated.ann_name, self.node, best_propagated)
        best_peer = best_propagated.peer
        if best_propagated.path:
            best_neighbor = best_propagated.path[-2]
        else:
            best_neighbor = None
        other_neighbor = other_propagated.path[-2]
        if best_propagated.peer == other_propagated.peer:
            return

        as_len_enabled = True # self.get_as_len_enabled()
        #name = "A"
        const_set = []
        const_selection = []

        self.log.debug("select at %s: %s over %s",
                       self.node, best_propagated, other_propagated)
        peer = other_propagated.peer

        s_localpref = best_ann_var.local_pref.var
        o_localpref = other_ann_var.local_pref.var

        s_aslen = best_ann_var.as_path_len
        o_aslen = other_ann_var.as_path_len

        s_origin = best_ann_var.origin.var
        o_origin = other_ann_var.origin.var

        origin_sort = self.ctx.get_enum_type(BGP_ORIGIN_SORT)
        igp_origin = origin_sort.get_symbolic_value('IGP')
        ebgp_origin = origin_sort.get_symbolic_value('EBGP')
        incomplete_origin = origin_sort.get_symbolic_value('INCOMPLETE')

        best_as_num = self.network_graph.get_bgp_asnum(best_peer)
        other_as_num = self.network_graph.get_bgp_asnum(peer)
        node_as_num = self.network_graph.get_bgp_asnum(self.node)

        other_permitted = other_ann_var.permitted.var

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
        select_igp = False # self.get_select_igp(best_propagated, other_propagated)
        use_igp = False # z3.Const("use_igp_%s" % name, z3.BoolSort())
        #self.constraints["%s_use_igp" % name] = \
        #    use_igp == self.can_used_igp(best_propagated, other_propagated)

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
        #if other_ann_name != best_ann_name:
        #    for value_ctx in self.selected_ctx.ctx_names:
        #        if value_ctx != 'communities_ctx':
        #            ctx1 = getattr(s_ctx, value_ctx)
        #            ctx2 = getattr(o_ctx, value_ctx)
        #            const_set.append(ctx1.get_var(other_ann_var) ==
        #                             ctx2.get_var(other_ann_var))
        #        else:
        #            ctx1 = getattr(self.selected_ctx, value_ctx)
        #            ctx2 = getattr(o_ctx, value_ctx)
        #            for comm in ctx1:
        #                const_set.append(ctx1[comm].get_var(other_ann_var) ==
        #                                 ctx2[comm].get_var(other_ann_var))

        #self.constraints["%s_set" % name] = z3.And(*const_set)
        #self.constraints[name] = z3.And(*const_selection)
        self.ctx.register_constraint(z3.And(*const_selection) == True, name_prefix="SELECT_%s_" % self.node)

    def mark_selected(self):
        for propagated, ann in self.anns_map.iteritems():
            n = '_%s_from_%s_' % (self.node, propagated.peer)
            if ann not in self.selected_sham:
                self.ctx.register_constraint(ann.permitted.var == False, name_prefix='Block' + n)
            else:
                self.ctx.register_constraint(ann.permitted.var == True, name_prefix='Allow' + n)

    def synthesize(self):
        print "Synthesizing", self.node
        self.mark_selected()
        self.compute_imported_routes()

        selected = get_propagated_info(self.ibgp_propagation, self.node, unselected=False)

        anns_order = {}
        for propagated in selected:
            if propagated.ann_name not in anns_order:
                anns_order[propagated.ann_name] = []
            anns_order[propagated.ann_name].append(propagated)
        for ann_name, values in anns_order.iteritems():
            if len(values) == 1:
                # This router only learns one route
                # No need to use the perference function
                continue
            for best_prop, other_prop in zip(values[0::1], values[1::1]):
                best_ann = self.anns_map[best_prop]
                other_ann = self.anns_map[other_prop]
                self.selector_func(best_prop, best_ann, other_prop, other_ann)

    def get_config(self):
        """Get concrete route configs"""
        configs = []
        for smt_rmap in self.rmaps.values():
            configs.append(smt_rmap.get_config())
        return configs

    def update_network_graph(self):
        """Update the network graph with the concrete values"""
        for smt_rmap in self.rmaps.values():
            rmap = smt_rmap.get_config()
            self.network_graph.add_route_map(self.node, rmap)
