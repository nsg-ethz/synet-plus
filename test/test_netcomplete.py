import unittest

from synet.netcomplete import NetComplete
from synet.netcomplete import NetCompleteConfigs
from synet.netcomplete import SketchError
from synet.utils.common import PathReq
from synet.utils.common import Protocols
from synet.utils.topo_gen import get_ibgp_linear_topo

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class NetCompleteTest(unittest.TestCase):
    def test_ospf_enabled(self):
        # Arrange
        configs1 = NetCompleteConfigs(auto_enable_ospf_process=False)
        configs2 = NetCompleteConfigs(auto_enable_ospf_process=True)
        graph1 = get_ibgp_linear_topo(2)
        graph2 = get_ibgp_linear_topo(2)
        graph2.enable_ospf('R1', 100)
        # graph2.enable_ospf('R2', 100)
        graph2.add_ospf_network('R1', 'prefix', 0)
        reqs = [PathReq(Protocols.OSPF, 'prefix', ['R2', 'R1'], False)]
        # Act
        synthesizer1 = NetComplete(reqs=reqs,
                                   topo=graph1,
                                   external_announcements=[],
                                   netcompplete_config=configs1)
        synthesizer2 = NetComplete(reqs=reqs,
                                   topo=graph2,
                                   external_announcements=[],
                                   netcompplete_config=configs2)
        ret2 = synthesizer2.synthesize()
        # Assert
        self.assertRaises(SketchError, synthesizer1.synthesize)
        self.assertTrue(ret2)
