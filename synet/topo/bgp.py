#!/usr/bin/env python
"""
Various helpers with configuring BGP related Policies
"""

from enum import Enum
from collections import Iterable
from ipaddress import IPv4Network
from ipaddress import IPv6Network


class Access(Enum):
    """Used to in various matches and route maps"""
    permit = 'permit'
    deny = 'deny'


class Community(object):
    """Represent a community value"""
    def __init__(self, value, new_format=True):
        """
        Creates a new community value, e.g. 40:30
        :param value: the community value, e.g. 10:20
        :param new_format: if true only accepts 10:30 but not 78
        """
        assert isinstance(value, basestring)
        if new_format:
            assert ':' in value
        self._new_format = new_format
        self._value = value

    @property
    def value(self):
        """Community value string, ex. "10:30" """
        return self._value

    @property
    def new_format(self):
        return self._new_format

    def __eq__(self, other):
        if hasattr(other, 'value'):
            return self.value == other.value
        else:
            return self.value == other

    def __str__(self):
        return "Community(%s)" % self.value

    def __repr__(self):
        return self.__str__()


class CommunityList(object):
    """Represents a list of communities in a match"""
    def __init__(self, list_id, access, communities):
        assert isinstance(list_id, int)
        assert isinstance(communities, Iterable)
        assert isinstance(access, Access)
        for community in communities:
            assert isinstance(community, Community)
        self._list_id = list_id
        self._access = access
        self._communities = tuple(communities)

    @property
    def list_id(self):
        return self._list_id

    @property
    def access(self):
        return self._access

    @property
    def communities(self):
        return self._communities

    def __eq__(self, other):
        if not isinstance(object, CommunityList):
            return False
        comm_eq = set(self.communities) == set(other.communities)
        access_eq = self.access == other.access
        id_eq = self.list_id == other.list_id
        return id_eq and access_eq and comm_eq

    def __str__(self):
        return "CommunityList(id=%s, access=%s, communities=%s)" % \
               (self.list_id, self.access, self.communities)

    def __repr__(self):
        return self.__str__()


class IpPrefixList(object):
    def __init__(self, name, access, networks):
        nettype = (IPv4Network, IPv6Network)
        assert isinstance(access, Access)
        assert isinstance(networks, Iterable)
        assert not isinstance(networks, nettype)
        for net in networks:
            assert isinstance(net, nettype)
        self._networks = networks
        self._name = name
        self._access = access

    @property
    def name(self):
        return self._name

    @property
    def networks(self):
        return self._networks

    @property
    def access(self):
        return self._access


class Match(object):
    """Represent match action in a route map"""
    pass


class Action(object):
    pass


class MatchCommunitiesList(Match):
    def __init__(self, communities_list):
        assert isinstance(communities_list, CommunityList)
        self._match = communities_list

    @property
    def match(self):
        return self._match


class MatchIpPrefixListList(Match):
    def __init__(self, prefix_list):
        assert isinstance(prefix_list, IpPrefixList)
        self._match = prefix_list

    @property
    def match(self):
        return self._match


class ActionSetLocalPref(Action):
    def __init__(self, localpref):
        assert isinstance(localpref, int)
        self._value = localpref

    @property
    def value(self):
        return self._value


class ActionString(Action):
    def __init__(self, value):
        assert isinstance(value, basestring)
        self._value = value

    @property
    def value(self):
        return self._value


class ActionSetCommunity(Action):
    def __init__(self, communities, additive=True):
        """
        Set a list of communities to a route
        :param communities: list of Community
        :param additive:
        """
        assert isinstance(communities, Iterable)
        for community in communities:
            assert isinstance(community, Community)
        self._communities = communities
        self._additive = additive

    @property
    def communities(self):
        return self._communities

    @property
    def additive(self):
        return self._additive


class RouteMapLine(object):
    def __init__(self, matches, actions, access, lineno=None):
        if not isinstance(matches, Iterable):
            if matches is not None:
                matches = (matches, )
            else:
                matches = []
        if not isinstance(actions, Iterable):
            actions = (actions, )
        for match in matches:
            assert isinstance(match, Match)
        for action in actions:
            assert isinstance(action, Action)

        self._matches = matches
        self._actions = actions
        self._access = access
        self._lineno = lineno

    @property
    def matches(self):
        return self._matches

    @property
    def actions(self):
        return self._actions

    @property
    def access(self):
        return self._access

    @property
    def lineno(self):
        return self._lineno


class RouteMap(object):
    def __init__(self, name, lines):
        assert isinstance(name, basestring)
        assert isinstance(lines, Iterable)
        for line in lines:
            assert isinstance(line, RouteMapLine)
        self._name = name
        self._lines = lines

    @property
    def name(self):
        return self._name

    @property
    def lines(self):
        return self._lines
