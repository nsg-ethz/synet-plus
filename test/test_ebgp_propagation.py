#!/usr/bin/env python


from synet.topo.graph import NetworkGraph

from synet.utils.common import PathReq
from synet.utils.common import PathProtocols

from synet.synthesis.ebgp_propagation import EBGPPropagation
from synet.synthesis.ebgp import Announcement
from synet.synthesis.ebgp import BGP_ATTRS_ORIGIN


def get_g():
    """
    Get a simple graph of 4 mesh (minus one edge) connected graph
    :return: Networkx Digraph
    """
    # Start with some initial inputs
    # This input only define routers
    g_phy = NetworkGraph()
    g_phy.add_router('R1')
    g_phy.add_router('R2')
    g_phy.add_router('R3')
    g_phy.add_router('R4')
    g_phy.add_peer('L3')
    g_phy.add_peer('ATT')
    g_phy.add_peer('DT')
    g_phy.set_bgp_asnum('R1', 100)
    g_phy.set_bgp_asnum('R2', 200)
    g_phy.set_bgp_asnum('R3', 300)
    g_phy.set_bgp_asnum('R4', 400)
    g_phy.set_bgp_asnum('L3', 1000)
    g_phy.set_bgp_asnum('ATT', 2000)
    g_phy.set_bgp_asnum('DT', 3000)

    g_phy.add_router_edge('R1', 'R2')
    g_phy.add_router_edge('R1', 'R3')
    g_phy.add_router_edge('R1', 'R4')

    g_phy.add_router_edge('R2', 'R1')
    g_phy.add_router_edge('R2', 'R3')
    #g_phy.add_router_edge('R2', 'R4')

    g_phy.add_router_edge('R3', 'R1')
    g_phy.add_router_edge('R3', 'R2')
    g_phy.add_router_edge('R3', 'R4')

    g_phy.add_router_edge('R4', 'R1')
    #g_phy.add_router_edge('R4', 'R2')
    g_phy.add_router_edge('R4', 'R3')


    g_phy.add_peer_edge('L3', 'R3')
    g_phy.add_peer_edge('R3', 'L3')
    g_phy.add_peer_edge('ATT', 'R3')
    g_phy.add_peer_edge('R3', 'ATT')
    g_phy.add_peer_edge('ATT', 'R4')
    g_phy.add_peer_edge('R4', 'ATT')
    g_phy.add_peer_edge('DT', 'R4')
    g_phy.add_peer_edge('R4', 'DT')

    return g_phy


def main():
    g = get_g()

    # Announcement received at R3
    netflix = Announcement(
        PREFIX='Netflix', PEER='L3', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[1000, 1100], NEXT_HOP='L3', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R3
    youtube1 = Announcement(
        PREFIX='Youtube', PEER='L3', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[1000, 1200], NEXT_HOP='L3', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R3
    google1 = Announcement(
        PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[2000, 2100], NEXT_HOP='ATT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R4
    google2 = Announcement(
        PREFIX='Google', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[2000, 2100], NEXT_HOP='ATT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R3
    ebay1 = Announcement(
        PREFIX='eBay', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[2000, 2200], NEXT_HOP='ATT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R4
    ebay2 = Announcement(
        PREFIX='eBay', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[2000, 2200], NEXT_HOP='ATT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R3
    paypal1 = Announcement(
        PREFIX='PayPal', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[2000, 2300], NEXT_HOP='ATT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R4
    paypal2 = Announcement(
        PREFIX='PayPal', PEER='ATT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[2000, 2300], NEXT_HOP='ATT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R4
    yahoo = Announcement(
        PREFIX='Yahoo', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[3000, 3100], NEXT_HOP='DT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R4
    amazon = Announcement(
        PREFIX='Amazon', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[3000, 2200], NEXT_HOP='DT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    # Announcement received at R4
    youtube2 = Announcement(
        PREFIX='YouTube', PEER='DT', ORIGIN=BGP_ATTRS_ORIGIN.EBGP,
        AS_PATH=[3000, 3300], NEXT_HOP='DT', LOCAL_PREF=100,
        COMMUNITIES=('F', 'F', 'F'))

    r = {
        'R3': [youtube1, netflix, google1, ebay1,  paypal1],
        'R4': [google2, ebay2, paypal2, yahoo, amazon, youtube2],
    }

    p = EBGPPropagation(r, g)


    # Google reqs
    path1 = ['ATT', 'R4', 'R3', 'R1']
    path2 = ['ATT', 'R4', 'R3', 'R2']
    google_req1 = PathReq(PathProtocols.BGP, 'Google', path1, 10)
    google_req2 = PathReq(PathProtocols.BGP, 'Google', path2, 10)

    # ebay and paypal
    path1 = ['ATT', 'R4', 'R1']
    path2 = ['ATT', 'R3', 'R2']
    ebay_req1 = PathReq(PathProtocols.BGP, 'eBay', path1, 10)
    ebay_req2 = PathReq(PathProtocols.BGP, 'eBay', path2, 10)
    paypal_req1 = PathReq(PathProtocols.BGP, 'PayPal', path1, 10)
    paypal_req2 = PathReq(PathProtocols.BGP, 'PayPal', path2, 10)

    # Yahoo
    path1 = ['DT', 'R4', 'R3', 'R1']
    path2 = ['DT', 'R4', 'R3', 'R2']
    yahoo_req1 = PathReq(PathProtocols.BGP, 'Yahoo', path1, 10)
    yahoo_req2 = PathReq(PathProtocols.BGP, 'Yahoo', path2, 10)

    # youtube
    path1 = ['DT', 'R4', 'R1']
    path2 = ['DT', 'R4', 'R3', 'R2']
    youtube_req1 = PathReq(PathProtocols.BGP, 'YouTube', path1, 10)
    youtube_req2 = PathReq(PathProtocols.BGP, 'YouTube', path2, 10)

    # Amazon
    path1 = ['DT', 'R4', 'R1']
    path2 = ['DT', 'R4', 'R3']
    path3 = ['DT', 'R4', 'R3', 'R2']
    amazon_req1 = PathReq(PathProtocols.BGP, 'Amazon', path1, 10)
    amazon_req2 = PathReq(PathProtocols.BGP, 'Amazon', path2, 10)
    amazon_req3 = PathReq(PathProtocols.BGP, 'Amazon', path3, 10)

    # Netflix TODO:

    reqs = [google_req1, google_req2, ebay_req1, ebay_req2,
            paypal_req1, paypal_req2, yahoo_req1, yahoo_req2,
            amazon_req1, amazon_req2, amazon_req3,
            youtube_req1, youtube_req2,]

    # Adding reqs
    for req in reqs:
        p.add_path_req(req)

    p.compute_dags()
    p.union_graphs()
    p.compute()


if __name__ == '__main__':
    main()
