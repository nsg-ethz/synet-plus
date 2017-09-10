"""
Maps names and network addresses
"""

from ipaddress import IPv4Network
from ipaddress import IPv6Network
from ipaddress import ip_address
from ipaddress import ip_network


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class AddressRegistry(object):
    """Registry maps string names to network addresses"""

    # Map string name to list of prefixes
    NET_NAMES = {}

    _PREFIX_LEN = 24
    _NEXT_NET = ip_network(u"128.0.0.0/%d" % _PREFIX_LEN)

    @staticmethod
    def is_network_address(addr):
        """Return True if the given is ip_network address"""
        return isinstance(addr, (IPv4Network, IPv6Network))

    @classmethod
    def register_network_address(cls, network, addrs):
        """
        Register a name with a set of IP addressess
        :param network: name
        :param addrs: list of IPv(4/6)Network addresses
        :return: list of addresses
        """
        assert isinstance(network, basestring)
        for addr in addrs:
            assert cls.is_network_address(addr)
        cls.NET_NAMES[network] = addrs
        return addrs

    @classmethod
    def get_network_addr(cls, network, create=False):
        """
        Given a name get a list of network addresses
        :param network: name
        :param create: if True, an address will be created if the network
                      was not registered before
        :return: list of network addresses
        """
        if cls.is_network_address(network):
            return [network]
        ret = cls.NET_NAMES.get(network, None)
        if ret:
            return ret
        if create:
            return cls.create_new_network(network)

    @classmethod
    def create_new_network(cls, network):
        """Create new address for a network"""
        assert network not in cls.NET_NAMES
        net = cls._NEXT_NET
        inc = int(cls._NEXT_NET.network_address) + (2 ** (32 - cls._PREFIX_LEN))
        net_add = ip_address(inc)
        cls._NEXT_NET = ip_network(u"%s/%d" % (net_add, cls._PREFIX_LEN))
        return cls.register_network_address(network, [net])
