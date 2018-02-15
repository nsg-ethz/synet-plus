import unittest
from nose.plugins.attrib import attr
import z3
from synet.utils.common import PathReq
from synet.utils.common import PathOrderReq
from synet.utils.common import Protocols
from synet.utils.common import ECMPPathsReq
from synet.utils.common import KConnectedPathsReq
from synet.utils.common import PreferredPathReq
from synet.utils.topo_gen import get_fanout_topology
from synet.topo.graph import NetworkGraph
from synet.topo.bgp import Access
from synet.topo.bgp import ActionSetLocalPref
from synet.topo.bgp import Announcement
from synet.topo.bgp import BGP_ATTRS_ORIGIN
from synet.topo.bgp import Community
from synet.topo.bgp import RouteMap
from synet.topo.bgp import RouteMapLine

from synet.utils.smt_context import get_as_path_key
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import VALUENOTSET
from synet.utils.topo_gen import gen_mesh

from synet.synthesis.connected import ConnectedSyn
from synet.synthesis.propagation import EBGPPropagation
from synet.synthesis.propagation import NotValidBGPPropagation
from synet.synthesis.propagation import ForwardingLoopError
from synet.synthesis.propagation import ConflictingPreferences
from synet.utils.bgp_utils import get_propagated_info
from synet.utils.bgp_utils import PropagatedInfo

# Hack for interface change
from synet.topo.bgp import Announcement as FullAnnouncement
from functools import partial
Announcement = partial(FullAnnouncement, med=100)


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


@attr(speed='fast')
class EBGPPreferenceTest(unittest.TestCase):
    def get_ann(self, peer=None):
        if not peer:
            peer = 'ATT'
        next_hop = "%sHop" % peer
        c1, c2, c3 = self.all_communities
        ann = Announcement(
            prefix='Google', peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2], as_path_len=2,
            next_hop=next_hop, local_pref=100,
            communities={c1: False, c2: False, c3: False}, permitted=True)

        return ann

    def _pre_load(self):
        # Communities
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")
        self.all_communities = (c1, c2, c3)

        ann1 = Announcement(
            prefix='Google', peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2], as_path_len=2,
            next_hop='ATTHop', local_pref=100,
            communities={c1: False, c2: False, c3: False}, permitted=True)

        ann2 = Announcement(
            prefix='Google', peer='DT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[3, 2], as_path_len=2,
            next_hop='DTHop', local_pref=100,
            communities={c1: False, c2: False, c3: False}, permitted=True)

        ann3 = Announcement(
            prefix='YouTube', peer='ATT', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[1, 2, 5, 7, 8], as_path_len=5,
            next_hop='ATTHop', local_pref=100,
            communities={c1: True, c2: False, c3: True}, permitted=True)

        self.anns = {
            'ATT_Google': ann1,
            'DT_Google': ann2,
            'ATT_YouTube': ann3,
        }

    def setUp(self):
        z3._main_ctx = None
        self._pre_load()

    def get_fanout(self, fanout, is_ebgp=True):
        topo = get_fanout_topology(fanout)
        asnum = 100
        for node in topo:
            topo.set_bgp_asnum(node, asnum)
            if is_ebgp:
                asnum += 100
        for src, dst in topo.edges_iter():
            if dst not in topo.get_bgp_neighbors(src):
                topo.add_bgp_neighbor(src, dst, VALUENOTSET, VALUENOTSET)
        if not is_ebgp:
            topo.add_bgp_neighbor('source', 'sink', VALUENOTSET, VALUENOTSET)
        connsyn = ConnectedSyn([], topo, full=True)
        connsyn.synthesize()
        return topo

    def get_diamond_plus_one(self):
        g = NetworkGraph()
        asnum = 100
        for num in range(5):
            node = 'R%d' % (num + 1)
            g.add_router(node)
            g.set_bgp_asnum(node, asnum)
            asnum += 100

        g.add_router_edge('R1', 'R2')
        g.add_router_edge('R1', 'R3')
        g.add_router_edge('R2', 'R1')
        g.add_router_edge('R2', 'R4')
        g.add_router_edge('R3', 'R1')
        g.add_router_edge('R3', 'R4')
        g.add_router_edge('R4', 'R2')
        g.add_router_edge('R4', 'R3')
        g.add_router_edge('R4', 'R5')
        g.add_router_edge('R5', 'R4')

        g.add_peer('ATT')
        g.set_bgp_asnum('ATT', 2000)
        g.add_peer_edge('R1', 'ATT')
        g.add_peer_edge('ATT', 'R1')

        g.add_bgp_neighbor(router_a='R1',
                           router_b='ATT',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R1',
                           router_b='R2',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R1',
                           router_b='R3',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R2',
                           router_b='R4',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R3',
                           router_b='R4',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)
        g.add_bgp_neighbor(router_a='R4',
                           router_b='R5',
                           router_a_iface=VALUENOTSET,
                           router_b_iface=VALUENOTSET)

        conn = ConnectedSyn([], g, full=True)
        conn.synthesize()
        for ann in self.anns.values():
            if g.has_node(ann.peer):
                g.add_bgp_advertise(ann.peer, ann)
        return g

    def get_long_topo(self):
        topo = NetworkGraph()
        R1 = 'R1'
        R2 = 'R2'
        R3 = 'R3'
        R4 = 'R4'
        source = 'source'
        sink = 'sink'
        topo.add_router(R1)
        topo.add_router(R2)
        topo.add_router(R3)
        topo.add_router(R4)
        topo.add_router(source)
        topo.add_router(sink)
        topo.add_router_edge(source, R1)
        topo.add_router_edge(R1, source)
        topo.add_router_edge(source, R3)
        topo.add_router_edge(R3, source)
        topo.add_router_edge(R1, R2)
        topo.add_router_edge(R2, R1)
        topo.add_router_edge(R3, R4)
        topo.add_router_edge(R4, R3)
        topo.add_router_edge(sink, R2)
        topo.add_router_edge(R2, sink)
        topo.add_router_edge(sink, R4)
        topo.add_router_edge(R4, sink)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        return topo

    def load_import_route_maps(self, g, node, neighbor, value):
        set_localpref = ActionSetLocalPref(value)
        line = RouteMapLine(matches=None, actions=[set_localpref],
                            access=Access.permit, lineno=10)
        name = "From_%s_%s" % (node, neighbor)
        rmap = RouteMap(name=name, lines=[line])
        g.add_route_map(node, rmap)
        g.add_bgp_import_route_map(node, neighbor, rmap.name)

    def add_one_peer(self, topo, node, peer, peer_asnum):
        topo.add_peer(peer)
        topo.set_bgp_asnum(peer, peer_asnum)
        topo.add_peer_edge(node, peer)
        topo.add_peer_edge(peer, node)
        #topo.add_bgp_neighbor(node, peer, VALUENOTSET, VALUENOTSET)
        #for ann in self.anns.values():
        #    if topo.has_node(ann.peer):
        #        topo.add_bgp_advertise(ann.peer, ann)

    def test_loop(self):
        self.anns = {'ATT_Google': self.get_ann()}
        peer = 'ATT'
        topo = self.get_fanout(2, is_ebgp=False)
        self.add_one_peer(topo, 'sink', peer, 1000)
        topo.add_bgp_neighbor('sink', peer, VALUENOTSET, VALUENOTSET)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        path1 = PathReq(Protocols.BGP, 'Google',
                        ['source', 'R1', 'sink', 'R2', 'R1', 'sink', peer], True)
        reqs = [path1]
        with self.assertRaises(ForwardingLoopError):
            EBGPPropagation(reqs, topo)

    def test_conflicting_preferences(self):
        self.anns = {'ATT_Google': self.get_ann()}
        g = self.get_diamond_plus_one()

        path1 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R2', 'R1', 'ATT'], True)
        path2 = PathReq(Protocols.BGP, 'Google', ['R4', 'R3', 'R1', 'ATT'], True)

        reqs = [path1, path2]

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()

        with self.assertRaises(ConflictingPreferences):
            EBGPPropagation(reqs, g)

    @unittest.skip
    def test_ecmp_error(self):
        self.anns = {'ATT_Google': self.get_ann()}
        g = self.get_diamond_plus_one()

        ecmp1 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R3', 'R1', 'ATT'], False)
        ecmp2 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R3', 'R1', 'ATT'], False)
        path1 = PathReq(Protocols.BGP, 'Google', ['R4', 'R2', 'R1', 'ATT'], True)

        ecmp = ECMPPathsReq(Protocols.BGP, 'Google', [ecmp1, ecmp2], True)
        reqs = [path1, ecmp]

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()
        with self.assertRaises(NotValidBGPPropagation):
            EBGPPropagation(reqs, g)

    def test_kconnected_error(self):
        self.anns = {'ATT_Google': self.anns['ATT_Google']}
        g = self.get_diamond_plus_one()

        k1 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R3', 'R1', 'ATT'], False)
        k2 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R3', 'R1', 'ATT'], False)
        path1 = PathReq(Protocols.BGP, 'Google', ['R4', 'R2', 'R1', 'ATT'], True)

        kconnected = KConnectedPathsReq(Protocols.BGP, 'Google', [k1, k2], False)
        reqs = [path1, kconnected]

        connected_syn = ConnectedSyn(reqs, g)
        connected_syn.synthesize()
        with self.assertRaises(NotValidBGPPropagation):
            EBGPPropagation(reqs, g)

    def test_ordered(self):
        self.anns = {'ATT_Google': self.anns['ATT_Google']}
        g = self.get_diamond_plus_one()

        path1 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R2', 'R1', 'ATT'], False)
        path2 = PathReq(Protocols.BGP, 'Google', ['R5', 'R4', 'R3', 'R1', 'ATT'], False)
        path3 = PathReq(Protocols.BGP, 'Google', ['R3', 'R1', 'ATT', ], True)

        google_pref = PathOrderReq(Protocols.BGP, 'Google', [path1, path2], False)

        reqs = [
            google_pref,
            path3
        ]
        self.load_import_route_maps(g, 'R4', 'R2', 200)
        self.load_import_route_maps(g, 'R3', 'R1', 200)

        connected_syn = ConnectedSyn([], g, full=True)
        connected_syn.synthesize()

        p = EBGPPropagation(reqs, g)

    def test_mesh(self):
        mesh = gen_mesh(4)
        first_as = 100
        for node in sorted(list(mesh.local_routers_iter())):
            mesh.set_bgp_asnum(node, first_as)
            first_as += 100
        for src, dst in mesh.edges_iter():
            if dst not in mesh.get_bgp_neighbors(src):
                mesh.add_bgp_neighbor(src, dst, VALUENOTSET, VALUENOTSET)
        att = 'ATT'
        dt = 'DT'
        mesh.add_peer(att)
        mesh.add_peer_edge(att, 'R3')
        mesh.add_peer_edge('R3', att)
        mesh.set_bgp_asnum(att, 1000)
        mesh.add_bgp_neighbor(att, 'R3', VALUENOTSET, VALUENOTSET)
        google_att = self.anns['ATT_Google']
        mesh.add_bgp_advertise(att, google_att)

        #mesh.add_peer(dt)
        #m#esh.add_peer_edge(dt, 'R3')
        #mesh.add_peer_edge('R3', dt)
        #mesh.set_bgp_asnum(dt, 2000)
        #mesh.add_bgp_neighbor(dt, 'R3', VALUENOTSET, VALUENOTSET)
        #google_dt = self.anns['DT_Google']
        #mesh.add_bgp_advertise(dt, google_dt)

        connected_syn = ConnectedSyn([], mesh, full=True)
        connected_syn.synthesize()

        r1_att = PathReq(Protocols.BGP, 'Google', ['R1', 'R3', 'ATT'], False)
        r1_dt = PathReq(Protocols.BGP, 'Google', ['R1', 'R3', 'DT'], False)
        r2_att = PathReq(Protocols.BGP, 'Google', ['R2', 'R3', 'ATT'], False)
        r2_dt = PathReq(Protocols.BGP, 'Google', ['R2', 'R3', 'DT'], False)
        r3_att = PathReq(Protocols.BGP, 'Google', ['R3', 'ATT'], False)
        r3_dt = PathReq(Protocols.BGP, 'Google', ['R3', 'DT'], False)
        r4_att = PathReq(Protocols.BGP, 'Google', ['R4', 'R3', 'ATT'], False)
        r4_dt = PathReq(Protocols.BGP, 'Google', ['R4', 'R3', 'DT'], False)

        r1_req = PathOrderReq(Protocols.BGP, 'Google', [r1_att], False)
        r2_req = PathOrderReq(Protocols.BGP, 'Google', [r2_att], False)
        r3_req = PathOrderReq(Protocols.BGP, 'Google', [r3_att], False)
        r4_req = PathOrderReq(Protocols.BGP, 'Google', [r4_att], False)

        reqs = [
            r1_req,
            r2_req,
            r3_req,
            r4_req,
        ]

        p = EBGPPropagation(reqs, mesh)
        #p.synthesize()
        #solver = z3.Solver()
        #p.add_constraints(solver)
        #ret = solver.check()
        #if ret == z3.unsat:
        #    print solver.unsat_core()
        #self.assertEquals(ret, z3.sat)

    #@unittest.skip
    def test_ebgp(self):
        ann_name = 'ATT_Google'
        ann = self.get_ann()
        prefix = ann.prefix
        as_path = ann.as_path
        as_path_len = ann.as_path_len
        sink = 'sink'
        source = 'source'
        R1 = 'R1'
        R2 = 'R2'
        self.anns = {'ATT_Google': ann}
        peer = 'ATT'
        topo = self.get_fanout(2, is_ebgp=True)
        self.add_one_peer(topo, 'sink', peer, 1000)
        topo.add_bgp_neighbor(peer, sink, VALUENOTSET, VALUENOTSET)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        topo.add_bgp_advertise(peer, ann)
        path1 = PathReq(Protocols.BGP, 'Google', [source, R2, sink, peer], True)
        reqs = [path1]
        prop = EBGPPropagation(reqs, topo, allow_igp=False)

        # Assertions
        self.assertEquals(prop.propagation_dags.keys(), [prefix])
        self.assertEquals(prop.forwarding_dags.keys(), [prefix])
        prefix_prop = prop.propagation_dags[prefix]
        assert len(prefix_prop.nodes()) > 0
        for src, dst in prefix_prop.edges():
            print "EDGE", src, dst
        self.assertEquals(prefix_prop.node[peer]['ordered'], [set([(peer,)])])
        self.assertEquals(prefix_prop.node[peer]['unordered'], set())
        self.assertEquals(prefix_prop.node[peer]['unselected'], set())

        propagation_graph = prop.union_graph

        peer_init = PropagatedInfo(
            egress=peer, ann_name=ann_name, peer=peer,
            as_path=as_path + [topo.get_bgp_asnum(peer)],
            as_path_len=as_path_len + 1, path=[peer])

        peer_sink = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=peer,
            as_path=peer_init.as_path + [topo.get_bgp_asnum(sink)],
            as_path_len=peer_init.as_path_len + 1, path=peer_init.path + [sink])

        sink_r1 = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(R1)],
            as_path_len=peer_sink.as_path_len + 1, path=peer_sink.path + [R1])

        sink_r2 = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(R2)],
            as_path_len=peer_sink.as_path_len + 1, path=peer_sink.path + [R2])

        r2_source = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=R2,
            as_path=sink_r2.as_path + [topo.get_bgp_asnum(source)],
            as_path_len=sink_r2.as_path_len + 1, path=sink_r2.path + [source])

        source_r1 = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=source,
            as_path=r2_source.as_path + [topo.get_bgp_asnum(R1)],
            as_path_len=r2_source.as_path_len + 1, path=r2_source.path + [R1])

        peer_info = propagation_graph.node[peer]['prefixes'][prefix]
        self.assertEquals(len(peer_info['prop_ordered']), 1)
        self.assertEquals(len(peer_info['prop_unordered']), 0)
        self.assertEquals(len(peer_info['prop_unselected']), 0)
        for info in peer_info['prop_ordered'][0]:
            self.assertEquals(info, peer_init)

        sink_info = propagation_graph.node[sink]['prefixes'][prefix]
        self.assertEquals(len(sink_info['prop_ordered']), 1, sink_info['prop_ordered'])
        self.assertEquals(len(sink_info['prop_unordered']), 0)
        self.assertEquals(len(sink_info['prop_unselected']), 0)
        for info in sink_info['prop_ordered'][0]:
            self.assertEquals(info, peer_sink)

        r1_info = propagation_graph.node[R1]['prefixes'][prefix]
        self.assertEquals(len(r1_info['prop_ordered']), 0)
        self.assertEquals(len(r1_info['prop_unordered']), 0)
        self.assertEquals(len(r1_info['prop_unselected']), 2)
        tmp = list(r1_info['prop_unselected'])
        self.assertTrue(sink_r1 == tmp[0] or sink_r1 == tmp[1])
        self.assertTrue(source_r1 == tmp[0] or source_r1 == tmp[1])

        r2_info = propagation_graph.node[R2]['prefixes'][prefix]
        self.assertEquals(len(r2_info['prop_ordered']), 1)
        self.assertEquals(len(r2_info['prop_unordered']), 0)
        self.assertEquals(len(r2_info['prop_unselected']), 0)
        for info in r2_info['prop_ordered'][0]:
            self.assertEquals(info, sink_r2)

        source_info = propagation_graph.node[source]['prefixes'][prefix]
        self.assertEquals(len(source_info['prop_ordered']), 1)
        self.assertEquals(len(source_info['prop_unordered']), 0)
        self.assertEquals(len(source_info['prop_unselected']), 0)
        for info in source_info['prop_ordered'][0]:
            self.assertEquals(info, r2_source)

        for node, attrs in propagation_graph.nodes(data=True):
            print node, get_propagated_info(propagation_graph, node)

    def test_ibgp_two_ibgp_enabled_single_path(self):
        # Test with only sink and source have iBGP enabled
        # Announcement
        ann_name = 'ATT_Google'
        ann = self.get_ann()
        prefix = ann.prefix
        as_path = ann.as_path
        as_path_len = ann.as_path_len
        self.anns = {ann_name: ann}
        # Routers
        R1 = 'R1'
        R2 = 'R2'
        R3 = 'R3'
        R4 = 'R4'
        source = 'source'
        sink = 'sink'
        peer = 'ATT'
        # Setup topology
        topo = self.get_long_topo()
        self.add_one_peer(topo, sink, peer, 2000)
        topo.add_bgp_advertise(peer, ann)
        topo.set_bgp_asnum(source, 100)
        topo.set_bgp_asnum(sink, 100)
        topo.add_bgp_neighbor(source, sink, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(peer, sink, VALUENOTSET, VALUENOTSET)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        path1 = PathReq(Protocols.BGP, 'Google', [source, R1, R2, sink, peer], True)
        prop = EBGPPropagation([path1], topo)
        propagation_graph = prop.union_graph

        peer_init = PropagatedInfo(
            egress=peer, ann_name=ann_name, peer=peer,
            as_path=as_path + [topo.get_bgp_asnum(peer)],
            as_path_len=as_path_len + 1, path=[peer])

        peer_sink = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=peer,
            as_path=peer_init.as_path + [topo.get_bgp_asnum(sink)],
            as_path_len=peer_init.as_path_len + 1, path=peer_init.path + [sink])

        # The req propagation
        sink_source = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(source)],
            as_path_len=peer_sink.as_path_len + 1, path=list(reversed(path1.path)))

        peer_info = propagation_graph.node[peer]['prefixes'][prefix]
        self.assertEquals(len(peer_info['prop_ordered']), 1)
        self.assertEquals(len(peer_info['prop_unordered']), 0)
        self.assertEquals(len(peer_info['prop_unselected']), 0)
        for info in peer_info['prop_ordered'][0]:
            self.assertEquals(info, peer_init)

        sink_info = propagation_graph.node[sink]['prefixes'][prefix]
        self.assertEquals(len(sink_info['prop_ordered']), 1, sink_info['prop_ordered'])
        self.assertEquals(len(sink_info['prop_unordered']), 0)
        self.assertEquals(len(sink_info['prop_unselected']), 0)
        for info in sink_info['prop_ordered'][0]:
            self.assertEquals(info, peer_sink)

        for inner in [R1, R2, R3, R4]:
            inner_info = propagation_graph.node[inner]['prefixes'][prefix]
            self.assertEquals(len(inner_info['prop_ordered']), 0)
            self.assertEquals(len(inner_info['prop_unordered']), 0)
            self.assertEquals(len(inner_info['prop_unselected']), 0)

        source_info = propagation_graph.node[source]['prefixes'][prefix]
        self.assertEquals(len(source_info['prop_ordered']), 1)
        self.assertEquals(len(source_info['prop_unordered']), 0)
        self.assertEquals(len(source_info['prop_unselected']), 1)
        for info in source_info['prop_ordered'][0]:
            self.assertEquals(info, sink_source)

    def test_ibgp_two_ibgp_enabled_ecmp_path(self):
        # Test with only sink and source have iBGP enabled
        # Announcement
        ann_name = 'ATT_Google'
        ann = self.get_ann()
        prefix = ann.prefix
        as_path = ann.as_path
        as_path_len = ann.as_path_len
        self.anns = {ann_name: ann}
        # Routers
        R1 = 'R1'
        R2 = 'R2'
        R3 = 'R3'
        R4 = 'R4'
        source = 'source'
        sink = 'sink'
        peer = 'ATT'
        # Setup topology
        topo = self.get_long_topo()
        self.add_one_peer(topo, sink, peer, 2000)
        topo.add_bgp_advertise(peer, ann)
        topo.set_bgp_asnum(source, 100)
        topo.set_bgp_asnum(sink, 100)
        topo.add_bgp_neighbor(source, sink, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(peer, sink, VALUENOTSET, VALUENOTSET)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        path1 = PathReq(Protocols.BGP, 'Google', [source, R1, R2, sink, peer], False)
        path2 = PathReq(Protocols.BGP, 'Google', [source, R3, R4, sink, peer], False)
        ecmp = ECMPPathsReq(Protocols.BGP, 'Google', [path1, path2], True)
        prop = EBGPPropagation([ecmp], topo)
        propagation_graph = prop.union_graph

        peer_init = PropagatedInfo(
            egress=peer, ann_name=ann_name, peer=peer,
            as_path=as_path + [topo.get_bgp_asnum(peer)],
            as_path_len=as_path_len + 1, path=[peer])

        peer_sink = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=peer,
            as_path=peer_init.as_path + [topo.get_bgp_asnum(sink)],
            as_path_len=peer_init.as_path_len + 1, path=peer_init.path + [sink])

        # The req propagation
        sink_source1 = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(source)],
            as_path_len=peer_sink.as_path_len + 1, path=list(reversed(path1.path)))

        sink_source2 = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(source)],
            as_path_len=peer_sink.as_path_len + 1, path=list(reversed(path2.path)))

        peer_info = propagation_graph.node[peer]['prefixes'][prefix]
        self.assertEquals(len(peer_info['prop_ordered']), 1)
        self.assertEquals(len(peer_info['prop_unordered']), 0)
        self.assertEquals(len(peer_info['prop_unselected']), 0)
        for info in peer_info['prop_ordered'][0]:
            self.assertEquals(info, peer_init)

        sink_info = propagation_graph.node[sink]['prefixes'][prefix]
        self.assertEquals(len(sink_info['prop_ordered']), 1, sink_info['prop_ordered'])
        self.assertEquals(len(sink_info['prop_unordered']), 0)
        self.assertEquals(len(sink_info['prop_unselected']), 0)
        for info in sink_info['prop_ordered'][0]:
            self.assertEquals(info, peer_sink)

        for inner in [R1, R2, R3, R4]:
            inner_info = propagation_graph.node[inner]['prefixes'][prefix]
            self.assertEquals(len(inner_info['prop_ordered']), 0)
            self.assertEquals(len(inner_info['prop_unordered']), 0)
            self.assertEquals(len(inner_info['prop_unselected']), 0)


        source_info = propagation_graph.node[source]['prefixes'][prefix]
        self.assertEquals(len(source_info['prop_ordered']), 1)
        self.assertEquals(len(source_info['prop_unordered']), 0)
        self.assertEquals(len(source_info['prop_unselected']), 0)
        for info in source_info['prop_ordered'][0]:
            self.assertTrue(info == sink_source1 or info == sink_source2)

    def test_ibgp_three_ibgp_enabled_single_path(self):
        # Test with only sink and source have iBGP enabled
        # Announcement
        ann_name = 'ATT_Google'
        ann = self.get_ann()
        prefix = ann.prefix
        as_path = ann.as_path
        as_path_len = ann.as_path_len
        self.anns = {ann_name: ann}
        # Routers
        R1 = 'R1'
        R2 = 'R2'
        R3 = 'R3'
        R4 = 'R4'
        source = 'source'
        sink = 'sink'
        peer = 'ATT'
        # Setup topology
        topo = self.get_long_topo()
        self.add_one_peer(topo, sink, peer, 2000)
        topo.add_bgp_advertise(peer, ann)
        topo.set_bgp_asnum(source, 100)
        topo.set_bgp_asnum(sink, 100)
        topo.set_bgp_asnum(R3, 100)
        topo.add_bgp_neighbor(source, sink, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(peer, sink, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(sink, R3, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(peer, R3, VALUENOTSET, VALUENOTSET)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        path1 = PathReq(Protocols.BGP, 'Google', [source, R1, R2, sink, peer], True)
        prop = EBGPPropagation([path1], topo)
        propagation_graph = prop.union_graph

        peer_init = PropagatedInfo(
            egress=peer, ann_name=ann_name, peer=peer,
            as_path=as_path + [topo.get_bgp_asnum(peer)],
            as_path_len=as_path_len + 1, path=[peer])

        peer_sink = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=peer,
            as_path=peer_init.as_path + [topo.get_bgp_asnum(sink)],
            as_path_len=peer_init.as_path_len + 1, path=peer_init.path + [sink])

        # The req propagation
        sink_source = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(source)],
            as_path_len=peer_sink.as_path_len + 1, path=list(reversed(path1.path)))

        peer_info = propagation_graph.node[peer]['prefixes'][prefix]
        self.assertEquals(len(peer_info['prop_ordered']), 1)
        self.assertEquals(len(peer_info['prop_unordered']), 0)
        self.assertEquals(len(peer_info['prop_unselected']), 0)
        for info in peer_info['prop_ordered'][0]:
            self.assertEquals(info, peer_init)

        sink_info = propagation_graph.node[sink]['prefixes'][prefix]
        self.assertEquals(len(sink_info['prop_ordered']), 1, sink_info['prop_ordered'])
        self.assertEquals(len(sink_info['prop_unordered']), 0)
        self.assertEquals(len(sink_info['prop_unselected']), 0)
        for info in sink_info['prop_ordered'][0]:
            self.assertEquals(info, peer_sink)

        r3_info = propagation_graph.node[R3]['prefixes'][prefix]
        self.assertEquals(len(r3_info['prop_ordered']), 0)
        self.assertEquals(len(r3_info['prop_unordered']), 0)
        self.assertEquals(len(r3_info['prop_unselected']), 2)

        for inner in [R1, R2, R4]:
            inner_info = propagation_graph.node[inner]['prefixes'][prefix]
            self.assertEquals(len(inner_info['prop_ordered']), 0)
            self.assertEquals(len(inner_info['prop_unordered']), 0)
            self.assertEquals(len(inner_info['prop_unselected']), 0)

        source_info = propagation_graph.node[source]['prefixes'][prefix]
        self.assertEquals(len(source_info['prop_ordered']), 1)
        self.assertEquals(len(source_info['prop_unordered']), 0)
        self.assertEquals(len(source_info['prop_unselected']), 1)
        for info in source_info['prop_ordered'][0]:
            self.assertEquals(info, sink_source)

    def test_ibgp_three_ibgp_enabled_ecmp_path(self):
        # Test with only sink and source have iBGP enabled
        # Announcement
        ann_name = 'ATT_Google'
        ann = self.get_ann()
        prefix = ann.prefix
        as_path = ann.as_path
        as_path_len = ann.as_path_len
        self.anns = {ann_name: ann}
        # Routers
        R1 = 'R1'
        R2 = 'R2'
        R3 = 'R3'
        R4 = 'R4'
        source = 'source'
        sink = 'sink'
        peer = 'ATT'
        # Setup topology
        topo = self.get_long_topo()
        self.add_one_peer(topo, sink, peer, 2000)
        topo.add_bgp_advertise(peer, ann)
        topo.set_bgp_asnum(source, 100)
        topo.set_bgp_asnum(sink, 100)
        topo.set_bgp_asnum(R3, 100)
        topo.add_bgp_neighbor(source, sink, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(peer, sink, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(sink, R3, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(peer, R3, VALUENOTSET, VALUENOTSET)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        path1 = PathReq(Protocols.BGP, 'Google', [source, R1, R2, sink, peer], False)
        path2 = PathReq(Protocols.BGP, 'Google', [source, R3, R4, sink, peer], False)
        ecmp = ECMPPathsReq(Protocols.BGP, 'Google', [path1, path2], True)
        prop = EBGPPropagation([ecmp], topo)
        propagation_graph = prop.union_graph

        peer_init = PropagatedInfo(
            egress=peer, ann_name=ann_name, peer=peer,
            as_path=as_path + [topo.get_bgp_asnum(peer)],
            as_path_len=as_path_len + 1, path=[peer])

        peer_sink = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=peer,
            as_path=peer_init.as_path + [topo.get_bgp_asnum(sink)],
            as_path_len=peer_init.as_path_len + 1, path=peer_init.path + [sink])

        # The req propagation
        sink_source1 = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(source)],
            as_path_len=peer_sink.as_path_len + 1, path=list(reversed(path1.path)))

        sink_source2 = PropagatedInfo(
            egress=sink, ann_name=ann_name, peer=sink,
            as_path=peer_sink.as_path + [topo.get_bgp_asnum(source)],
            as_path_len=peer_sink.as_path_len + 1, path=list(reversed(path2.path)))

        peer_info = propagation_graph.node[peer]['prefixes'][prefix]
        self.assertEquals(len(peer_info['prop_ordered']), 1)
        self.assertEquals(len(peer_info['prop_unordered']), 0)
        self.assertEquals(len(peer_info['prop_unselected']), 0)
        for info in peer_info['prop_ordered'][0]:
            self.assertEquals(info, peer_init)

        sink_info = propagation_graph.node[sink]['prefixes'][prefix]
        self.assertEquals(len(sink_info['prop_ordered']), 1, sink_info['prop_ordered'])
        self.assertEquals(len(sink_info['prop_unordered']), 0)
        self.assertEquals(len(sink_info['prop_unselected']), 0)
        for info in sink_info['prop_ordered'][0]:
            self.assertEquals(info, peer_sink)

        r3_info = propagation_graph.node[R3]['prefixes'][prefix]
        self.assertEquals(len(r3_info['prop_ordered']), 1)
        self.assertEquals(len(r3_info['prop_unordered']), 0)
        self.assertEquals(len(r3_info['prop_unselected']), 1)

        for inner in [R1, R2, R4]:
            inner_info = propagation_graph.node[inner]['prefixes'][prefix]
            self.assertEquals(len(inner_info['prop_ordered']), 0)
            self.assertEquals(len(inner_info['prop_unordered']), 0)
            self.assertEquals(len(inner_info['prop_unselected']), 0)

        source_info = propagation_graph.node[source]['prefixes'][prefix]
        self.assertEquals(len(source_info['prop_ordered']), 1)
        self.assertEquals(len(source_info['prop_unordered']), 0)
        self.assertEquals(len(source_info['prop_unselected']), 0)
        for info in source_info['prop_ordered'][0]:
            ret = info == sink_source1 or info == sink_source2
            if ret:
                print "OK passed info", info
            else:
                print "NOT OK", info
                print "    S:", sink_source1
                print "    S:", sink_source2
            self.assertTrue(ret)

    def test_ebgp_two_peers(self):
        ann_name = 'ATT_Google'
        peer1 = 'ATT'
        peer2 = 'DT'
        ann1 = self.get_ann(peer1)
        ann2 = self.get_ann(peer2)
        sink = 'sink'
        source = 'source'
        self.anns = {'ATT_Google': ann1, 'DT_Google': ann2}
        topo = self.get_fanout(0, is_ebgp=True)
        self.add_one_peer(topo, 'sink', peer1, 1000)
        self.add_one_peer(topo, 'sink', peer2, 1000)
        topo.add_bgp_neighbor(peer1, sink, VALUENOTSET, VALUENOTSET)
        topo.add_bgp_neighbor(peer2, sink, VALUENOTSET, VALUENOTSET)
        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        topo.add_bgp_advertise(peer1, ann1)
        topo.add_bgp_advertise(peer2, ann2)
        path1 = PathReq(Protocols.BGP, 'Google', [source, sink, peer1], True)
        reqs = [path1]
        prop = EBGPPropagation(reqs, topo, allow_igp=False)