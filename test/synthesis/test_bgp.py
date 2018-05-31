
import time
import z3
import unittest

import networkx as nx

from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.common import PathOrderReq
from synet.utils.topo_gen import get_ebgp_linear_topo
from synet.utils.topo_gen import get_ibgp_linear_topo
from synet.utils.topo_gen import gen_mesh
from synet.utils.topo_gen import get_griffin_graph
from synet.utils.topo_gen import get_griffin_ibgp_graph

from tekton.graph import NetworkGraph
from ipaddress import ip_network
from ipaddress import ip_interface
from tekton.bgp import Access
from tekton.bgp import RouteMap
from tekton.bgp import RouteMapLine
from tekton.bgp import IpPrefixList
from tekton.bgp import MatchIpPrefixListList
from tekton.bgp import MatchAsPath
from tekton.bgp import MatchAsPathLen
from tekton.bgp import ActionSetLocalPref
from tekton.bgp import Announcement
from tekton.bgp import BGP_ATTRS_ORIGIN
from tekton.bgp import Community

from tekton.gns3 import GNS3Topo

from synet.utils.bgp_utils import compute_next_hop_map
from synet.utils.bgp_utils import extract_all_next_hops
from synet.utils.smt_context import VALUENOTSET
from synet.synthesis.new_propagation import EBGPPropagation
from synet.synthesis.connected import ConnectedSyn


from synet.utils.fnfree_smt_context import read_announcements
from synet.utils.fnfree_smt_context import SolverContext

from synet.synthesis.new_bgp import DEFAULT_LOCAL_PREF
from synet.synthesis.new_bgp import DEFAULT_MED

from synet.netcomplete import NetComplete

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class BGPTest(unittest.TestCase):
    def get_anns(self, prefix):
        c1 = Community("100:16")
        c2 = Community("100:17")
        c3 = Community("100:18")

        ann1 = Announcement(
            prefix=prefix, peer='R1', origin=BGP_ATTRS_ORIGIN.EBGP,
            as_path=[100], as_path_len=1,
            next_hop='Hop1', local_pref=100, med=10,
            communities={c1: True, c2: False, c3: False}, permitted=True)
        return [ann1]

    def get_ebgp_topo(self):
        graph = get_ebgp_linear_topo(4)
        r1, r2, r3, r4 = 'R1', 'R2', 'R3', 'R4'
        net = ip_network(u'128.0.0.0/24')
        prefix = str(net)
        prefix_map = {prefix: net}
        iface_addr = ip_interface("%s/%d" % (net.hosts().next(), net.prefixlen))
        graph.set_loopback_addr('R1', 'lo100', iface_addr)
        ann = self.get_anns(prefix)[0]
        graph.add_bgp_advertise(node=r1, announcement=ann, loopback='lo100')
        return graph, ann

    def get_ibgp_topo(self):
        graph = get_ibgp_linear_topo(4)
        r1, r2, r3, r4 = 'R1', 'R2', 'R3', 'R4'
        graph.enable_ospf(r1)
        graph.enable_ospf(r2)
        graph.enable_ospf(r3)
        graph.enable_ospf(r4)
        net = ip_network(u'128.0.0.0/24')
        prefix = str(net)
        iface_addr = ip_interface("%s/%d" % (net.hosts().next(), net.prefixlen))
        graph.set_loopback_addr('R1', 'lo10', iface_addr)
        graph.add_ospf_network(r1, 'lo100', area='0.0.0.0')
        graph.add_ospf_network(r2, 'lo100', area='0.0.0.0')
        graph.add_ospf_network(r3, 'lo100', area='0.0.0.0')
        graph.add_ospf_network(r4, 'lo100', area='0.0.0.0')
        ann = self.get_anns(prefix)[0]
        graph.add_bgp_advertise(node=r1, announcement=ann, loopback='lo10')
        return graph, ann

    def get_cust_peer_linear_topo(self):
        graph = gen_mesh(2, 100)
        r1, r2 = 'R1', 'R2'

        graph.enable_ospf(r1)
        graph.enable_ospf(r2)

        # Add two providers and one customer
        provider1 = 'Provider1'
        provider2 = 'Provider2'
        customer = 'Customer'
        graph.add_peer(provider1)
        graph.add_peer(provider2)
        graph.add_peer(customer)
        graph.set_bgp_asnum(provider1, 400)
        graph.set_bgp_asnum(provider2, 500)
        graph.set_bgp_asnum(customer, 600)
        graph.add_peer_edge(r1, provider1)
        graph.add_peer_edge(provider1, r1)
        graph.add_peer_edge(r1, provider2)
        graph.add_peer_edge(provider2, r1)
        graph.add_peer_edge(r2, customer)
        graph.add_peer_edge(customer, r2)

        # Establish BGP peering
        graph.add_bgp_neighbor(provider1, r1)
        graph.add_bgp_neighbor(provider2, r1)
        graph.add_bgp_neighbor(customer, r2)

        net1 = ip_network(u'128.0.0.0/24')
        net2 = ip_network(u'128.0.1.0/24')
        prefix1 = str(net1)
        prefix2 = str(net2)
        iface_addr1 = ip_interface("%s/%d" % (net1.hosts().next(), net1.prefixlen))
        graph.set_loopback_addr(provider1, 'lo10', iface_addr1)
        graph.set_loopback_addr(provider2, 'lo10', iface_addr1)
        iface_addr2 = ip_interface("%s/%d" % (net2.hosts().next(), net2.prefixlen))
        graph.set_loopback_addr(customer, 'lo10', iface_addr2)
        # Announce IGP internally
        graph.add_ospf_network(r1, 'lo100', area='0.0.0.0')
        graph.add_ospf_network(r2, 'lo100', area='0.0.0.0')

        # Known communities
        comms = [Community("100:{}".format(c)) for c in range(1, 4)]
        # The symbolic announcement injected by provider1
        ann1 = Announcement(prefix1,
                            peer=provider1,
                            origin=BGP_ATTRS_ORIGIN.INCOMPLETE,
                            as_path=[1000, 2000, 5000],  # We assume it learned from other upstream ASes
                            as_path_len=3,
                            next_hop='{}Hop'.format(provider1),
                            local_pref=100,
                            med=100,
                            communities=dict([(c, False) for c in comms]),
                            permitted=True)
        # The symbolic announcement injected by provider1
        # Note it has a shorter AS Path
        ann2 = Announcement(str(prefix1),
                            peer=provider2,
                            origin=BGP_ATTRS_ORIGIN.INCOMPLETE,
                            as_path=[3000, 600, 9000, 5000],  # We assume it learned from other upstream ASes
                            as_path_len=4,
                            next_hop='{}Hop'.format(provider2),
                            local_pref=100,
                            med=100,
                            communities=dict([(c, False) for c in comms]),
                            permitted=True)

        # The symbolic announcement injected by customer
        ann3 = Announcement(prefix2,
                            peer=customer,
                            origin=BGP_ATTRS_ORIGIN.INCOMPLETE,
                            as_path=[],
                            as_path_len=0,
                            next_hop='{}Hop'.format(customer),
                            local_pref=100,
                            med=100,
                            communities=dict([(c, False) for c in comms]),
                            permitted=True)

        return graph, [ann1, ann2, ann3]

    def test_next_hop_ebgp(self):
        # Arrange
        graph, origin_ann = self.get_ebgp_topo()
        r1, r2, r3, r4 = 'R1', 'R2', 'R3', 'R4'
        prefix = origin_ann.prefix
        req = PathReq(Protocols.BGP, dst_net=prefix, path=[r4, r3, r2, r1], strict=False)
        netcomplete = NetComplete([req], graph, [origin_ann])
        next_hop_vals = {
            'R1': '0.0.0.0',
            'R2': 'R1-Fa0-0',
            'R3': 'R2-Fa0-1',
            'R4': 'R3-Fa0-1',
        }
        as_path_vals = {
            'R1': 'as_path_100_100',
            'R2': 'as_path_200_100_100',
            'R3': 'as_path_300_200_100_100',
            'R4': 'as_path_400_300_200_100_100',
        }
        as_path_len_vals = {
            'R1': 1,
            'R2': 2,
            'R3': 3,
            'R4': 4,
        }
        # Act
        ret = netcomplete.synthesize()
        # Assert
        self.assertTrue(ret)
        for node, attrs in netcomplete.bgp_synthesizer.ibgp_propagation.nodes(data=True):
            for ann in attrs['box'].selected_sham:
                self.assertTrue(ann.permitted.is_concrete)
                self.assertTrue(ann.permitted.get_value())

                self.assertTrue(ann.prefix.is_concrete)
                self.assertEquals(ann.prefix.get_value(), prefix)

                self.assertTrue(ann.next_hop.is_concrete)
                self.assertEquals(ann.next_hop.get_value(), next_hop_vals[node])

                self.assertTrue(ann.as_path.is_concrete)
                self.assertEquals(ann.as_path.get_value(), as_path_vals[node])

                self.assertTrue(ann.as_path_len.is_concrete)
                self.assertEquals(ann.as_path_len.get_value(), as_path_len_vals[node])

                self.assertTrue(ann.med.is_concrete)
                self.assertEquals(ann.med.get_value(), origin_ann.med)

                self.assertTrue(ann.local_pref.is_concrete)
                self.assertEquals(ann.local_pref.get_value(), origin_ann.local_pref)

                for comm, val in ann.communities.iteritems():
                    self.assertTrue(val.is_concrete)
                    self.assertEquals(val.get_value(), origin_ann.communities[comm])

    def test_next_hop_ibgp(self):
        # Arrange
        graph, origin_ann = self.get_ibgp_topo()
        r1, r2, r3, r4 = 'R1', 'R2', 'R3', 'R4'
        prefix = origin_ann.prefix
        req1 = PathReq(Protocols.BGP, dst_net=prefix, path=[r2, r1], strict=False)
        req2 = PathReq(Protocols.BGP, dst_net=prefix, path=[r3, r1], strict=False)
        req3 = PathReq(Protocols.BGP, dst_net=prefix, path=[r4, r1], strict=False)
        netcomplete = NetComplete([req1, req2, req3], graph, [origin_ann])
        next_hop_vals = {
            'R1': '0.0.0.0',
            'R2': 'R1-lo100',
            'R3': 'R1-lo100',
            'R4': 'R1-lo100',
        }
        as_path_vals = {
            'R1': 'as_path_100_100',
            'R2': 'as_path_100_100',
            'R3': 'as_path_100_100',
            'R4': 'as_path_100_100',
        }
        as_path_len_vals = {
            'R1': 1,
            'R2': 1,
            'R3': 1,
            'R4': 1,
        }
        # Act
        ret = netcomplete.synthesize()
        netcomplete.write_configs('out-configs/ibgp')
        # Assert
        self.assertTrue(ret)
        for node, attrs in netcomplete.bgp_synthesizer.ibgp_propagation.nodes(data=True):
            for ann in attrs['box'].selected_sham:
                self.assertTrue(ann.permitted.is_concrete)
                self.assertTrue(ann.permitted.get_value())

                self.assertTrue(ann.prefix.is_concrete)
                self.assertEquals(ann.prefix.get_value(), prefix)

                self.assertTrue(ann.next_hop.is_concrete)
                self.assertEquals(ann.next_hop.get_value(), next_hop_vals[node])

                self.assertTrue(ann.as_path.is_concrete)
                self.assertEquals(ann.as_path.get_value(), as_path_vals[node])

                self.assertTrue(ann.as_path_len.is_concrete)
                self.assertEquals(ann.as_path_len.get_value(), as_path_len_vals[node])

                self.assertTrue(ann.med.is_concrete)
                self.assertEquals(ann.med.get_value(), origin_ann.med)

                self.assertTrue(ann.local_pref.is_concrete)
                self.assertEquals(ann.local_pref.get_value(), origin_ann.local_pref)

                for comm, val in ann.communities.iteritems():
                    self.assertTrue(val.is_concrete)
                    self.assertEquals(val.get_value(), origin_ann.communities[comm])


    def test_next_hop_mixed(self):
        # Arrange
        graph, (ann1, ann2, ann3) = self.get_cust_peer_linear_topo()
        r1, r2, provider1, provider2,  customer = 'R1', 'R2', 'Provider1', 'Provider2', 'Customer'
        prefix1 = ann1.prefix
        prefix2 = ann3.prefix
        graph.add_bgp_advertise(node=provider1, announcement=ann1, loopback='lo10')
        graph.add_bgp_advertise(node=provider2, announcement=ann2, loopback='lo10')
        #graph.add_bgp_advertise(node=customer, announcement=ann3, loopback='lo10')

        rline = RouteMapLine(matches=[], actions=[], access=Access.deny, lineno=100)
        rmap_export = RouteMap(name='DenyExport', lines=[rline])
        graph.add_route_map(r1, rmap_export)
        graph.add_bgp_export_route_map(r1, provider1, rmap_export.name)
        graph.add_bgp_export_route_map(r1, provider2, rmap_export.name)

        p1 = PathReq(Protocols.BGP, dst_net=prefix1, path=[customer, r2, r1, provider1], strict=False)
        p2 = PathReq(Protocols.BGP, dst_net=prefix1, path=[customer, r2, r1, provider1], strict=False)
        req1 = PathOrderReq(Protocols.BGP, prefix1, [p1, p2], strict=False)
        req2 = PathReq(Protocols.BGP, dst_net=prefix2, path=[provider1, r2, r1, customer], strict=False)
        req3 = PathReq(Protocols.BGP, dst_net=prefix2, path=[provider2, r2, r1, customer], strict=False)
        req0 = PathReq(Protocols.BGP, dst_net=prefix1, path=[provider1, r1, provider2], strict=False)
        req00 = PathReq(Protocols.BGP, dst_net=prefix1, path=[provider2, r1, provider1], strict=False)
        netcomplete = NetComplete([req1], graph, [ann1, ann2])
        next_hop_vals = {
            'R1': 'Provider1-Fa0-0',
            'R2': 'Provider1-Fa0-0',
            'Customer': 'R2-Fa0-0',
            'Provider1': '0.0.0.0',
            'Provider2': '0.0.0.0',
        }
        provider1_as = [graph.get_bgp_asnum(provider1)] + ann1.as_path
        provider2_as = [graph.get_bgp_asnum(provider2)] + ann2.as_path
        r1_as = [graph.get_bgp_asnum(r1)] + provider1_as
        customer_as = [graph.get_bgp_asnum(customer)] + r1_as
        as_path_vals = {
            'R1': 'as_path_{}'.format('_'.join([str(x) for x in r1_as])),
            'R2': 'as_path_{}'.format('_'.join([str(x) for x in r1_as])),
            'Customer': 'as_path_{}'.format('_'.join([str(x) for x in customer_as])),
            'Provider1': 'as_path_{}'.format('_'.join([str(x) for x in provider1_as])),
            'Provider2': 'as_path_{}'.format('_'.join([str(x) for x in provider2_as])),
        }
        as_path_len_vals = {
            'R1': len(r1_as) - 1,
            'R2': len(r1_as) - 1,
            'Customer': len(customer_as) - 1,
            'Provider1': len(provider1_as) - 1,
            'Provider2': len(provider2_as) - 1,
        }
        # Act
        ret = netcomplete.synthesize()
        netcomplete.write_configs('out-configs/ibgp')
        # Assert
        self.assertTrue(ret)
        for node, attrs in netcomplete.bgp_synthesizer.ibgp_propagation.nodes(data=True):
            for ann in attrs['box'].selected_sham:
                self.assertTrue(ann.permitted.is_concrete)
                self.assertTrue(ann.permitted.get_value())

                self.assertTrue(ann.prefix.is_concrete)
                self.assertEquals(ann.prefix.get_value(), prefix1)

                self.assertTrue(ann.next_hop.is_concrete)
                self.assertEquals(ann.next_hop.get_value(), next_hop_vals[node])

                self.assertTrue(ann.as_path.is_concrete)
                self.assertEquals(ann.as_path.get_value(), as_path_vals[node])

                self.assertTrue(ann.as_path_len.is_concrete)
                self.assertEquals(ann.as_path_len.get_value(), as_path_len_vals[node])

                self.assertTrue(ann.med.is_concrete)
                self.assertEquals(ann.med.get_value(), DEFAULT_MED)

                self.assertTrue(ann.local_pref.is_concrete)
                self.assertEquals(ann.local_pref.get_value(), DEFAULT_LOCAL_PREF)

                for comm, val in ann.communities.iteritems():
                    self.assertTrue(val.is_concrete)
                    self.assertFalse(val.get_value())
