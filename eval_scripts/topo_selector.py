#!/usr/bin/env python
"""
Select which topologies to be used in evaluations
"""


import glob
import os
from os.path import basename
from shutil import copyfile
from shutil import rmtree

from synet.utils.topo_gen import read_topology_zoo_netgraph


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


SMALL_DIR = 'topos/small'
MID_DIR = 'topos/mid'
LARGE_DIR = 'topos/large'


def select_topologies():
    topos = {}
    bad_topos = ['fiber', 'Fiber', 'Telcove', 'DialtelecomCz',
                 'GtsSlovakia', 'GtsPoland', 'GtsCzechRepublic',
                 'GtsRomania', ' GtsHungary', 'Renater2006',
                 'Syringa', 'Globenet'
                 ]
    for file in glob.glob("topos/topozoo/*.graphml"):
        topo = read_topology_zoo_netgraph(file)
        if len(topo.nodes()) < 32 or len(topo.nodes()) > 200:
            continue
        bad = False
        for tmp in bad_topos:
            if tmp in file:
                bad = True
                break
        if bad:
            continue
        topos[file] = topo

    def cmp(x, y):
        if len(topos[x].nodes()) < len(topos[y].nodes()):
            return -1
        elif len(topos[x].nodes()) > len(topos[y].nodes()):
            return 1
        elif len(topos[x].edges()) < len(topos[y].edges()):
            return -1
        elif len(topos[x].edges()) > len(topos[y].edges()):
            return 1
        return 0

    ordered = sorted(topos.keys(), cmp=cmp, reverse=True)
    small = ordered[-5:]
    mid = ordered[(1 * (len(ordered) / 5)) - 3:(1 * (len(ordered) / 5)) + 2]
    large = ordered[:5]

    small = dict([(name, topos[name]) for name in small])
    mid = dict([(name, topos[name]) for name in mid])
    large = dict([(name, topos[name]) for name in large])
    return small, mid, large


def copy_topolgies(small, mid, large):
    print "Cleaning folders"
    if os.path.exists(SMALL_DIR):
        rmtree(SMALL_DIR)
    if os.path.exists(MID_DIR):
        rmtree(MID_DIR)
    if os.path.exists(LARGE_DIR):
        rmtree(LARGE_DIR)
    print "Creating new dirs"
    os.mkdir(SMALL_DIR)
    os.mkdir(MID_DIR)
    os.mkdir(LARGE_DIR)

    print "Small:"
    for topo in small:
        name = basename(topo)
        print "\tCopying", name, "#nodes", len(small[topo].nodes()), \
            "#edges", len(small[topo].edges())
        copyfile(topo, "%s" % os.path.join(SMALL_DIR, name))

    print "Mid:"
    for topo in mid:
        name = basename(topo)
        print "\tCopying", name, "#nodes", len(mid[topo].nodes()), \
            "#edges", len(mid[topo].edges())
        copyfile(topo, "%s" % os.path.join(MID_DIR, name))

    print "Large:"
    for topo in large:
        name = basename(topo)
        print "\tCopying", name, "#nodes", len(large[topo].nodes()), \
            "#edges", len(large[topo].edges())
        copyfile(topo, "%s" % os.path.join(LARGE_DIR, name))


def main():
    small, mid, large = select_topologies()
    copy_topolgies(small, mid, large)


if __name__ == '__main__':
    main()
