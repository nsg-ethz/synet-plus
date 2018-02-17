import itertools

from synet.topo.cisco import CiscoConfigGen
from synet.topo.graph import NetworkGraph

class GNS3Topo(object):
    def __init__(self, graph, prefix_map=None):
        assert isinstance(graph, NetworkGraph)
        self.prefix_map = prefix_map if prefix_map else {}
        self.g = graph
        self.local_dynampis = '127.0.0.1:7200',
        self.workingdir = '/home/ahassany/tmp',
        self.idlepc = '0x631868a4'
        self.router_model = '7200'
        outdir = 'out',
        iosimage = '/home/ahassany/GNS3/images/IOS/c7200-advipservicesk9-mz.152-4.S5.image'
        self.router_info = {
            'image': iosimage,
            'npe': 'npe-400',
            'ram': '256',
            'nvram': '50',
            'idlepc': self.idlepc,
            'idlemax': '500',
        }
        console_start_port = 2501
        self.next_console = itertools.count(console_start_port)
        self.config_gen = CiscoConfigGen(self.g, prefix_map=self.prefix_map)

    def _annotate_node(self, n):
        """
        For each router annotate it with topological information needed to
        generate the topology file
        """
        assert self.g.is_router(n), "'%s' is not a router" % n
        if 'dyn' not in self.g.node[n]:
            self.g.node[n]['dyn'] = {}
        dyn = self.g.node[n]['dyn']
        dyn['model'] = self.router_model
        dyn['console'] = self.next_console.next()
        dyn['cnfg'] = "configs/%s.cfg" % n

    def get_gns3_topo(self):
        topo = ""
        topo += "autostart = False\n"
        topo += "ghostios = True\n"
        topo += "sparsemem = False\n"
        topo += "[%s]\n" % self.local_dynampis
        topo += "\tworkingdir = %s\n" % self.workingdir
        topo += "\tudp = 15000"
        topo += "\n"
        topo += "\t[[ %s ]]\n" % self.router_model
        for k, v in self.router_info.iteritems():
            topo += "\t\t%s = %s\n" % (k, v)
        for node in sorted(list(self.g.routers_iter())):
            topo += "\t[[ ROUTER %s ]]\n" % node
            self._annotate_node(node)
            for k, v in self.g.node[node]['dyn'].iteritems():
                topo += "\t\t%s = %s\n" % (k, v)
            for neighbor in self.g.neighbors(node):
                siface = self.g.get_edge_iface(node, neighbor)
                diface = self.g.get_edge_iface(neighbor, node)
                topo += "\t\t%s = %s %s\n" % (siface, neighbor, diface)
        return topo

    def gen_router_config(self, node):
        return self.config_gen.gen_router_config(node)
