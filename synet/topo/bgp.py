#!/usr/bin/env python
"""
Various helpers with configuring BGP related Policies
"""

from enum import Enum
from collections import Iterable
from ipaddress import IPv4Network
from ipaddress import IPv6Network


VALUENOTSET = 'EMPTY?Value'


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
        if isinstance(value, basestring):
            value = Community.string_to_int(value)
        assert isinstance(value, int)
        self._new_format = new_format
        self._value = value

    @property
    def value(self):
        """Community value string, ex. "10:30" """
        return self._value

    @property
    def is_new_format(self):
        return self._new_format

    @staticmethod
    def string_to_int(value):
        assert ":" in value
        high, low = value.split(":")
        bin_high = '{0:016b}'.format(int(high))
        bin_low = '{0:016b}'.format(int(low))
        return int(bin_high + bin_low, 2)

    def get_new_format(self):
        bin = '{0:032b}'.format(self.value)
        high = int(bin[:16], 2)
        low = int(bin[16:], 2)
        return "%d:%d" % (high, low)

    @property
    def name(self):
        if self.is_new_format:
            val = self.get_new_format()
            val = val.replace(':', '_')
        else:
            val = self.value
        return "Comm_%s" % val

    def __eq__(self, other):
        return self.value == getattr(other, 'value', other)

    def __str__(self):
        if self.is_new_format:
            val = self.get_new_format()
        else:
            val = self.value
        return "Community(%s)" % val

    def __repr__(self):
        return self.__str__()


class CommunityList(object):
    """Represents a list of communities in a match"""
    def __init__(self, list_id, access, communities):
        #assert isinstance(list_id, int)
        assert isinstance(communities, Iterable)
        assert isinstance(access, Access)
        if communities != [VALUENOTSET]:
            for community in communities:
                assert community == VALUENOTSET or isinstance(community, Community)
        self._list_id = list_id
        self._access = access
        self._communities = communities

    @property
    def list_id(self):
        return self._list_id

    @property
    def access(self):
        return self._access

    @property
    def communities(self):
        return self._communities

    @communities.setter
    def communities(self, value):
        if self._communities != [VALUENOTSET]:
            raise ValueError("Communities alread set to %s" % self._communities)
        for community in value:
            assert isinstance(community, Community)
        self._communities = value

    def __eq__(self, other):
        if not isinstance(other, CommunityList):
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
        self.nettype = (IPv4Network, IPv6Network)
        assert isinstance(access, Access)
        assert isinstance(networks, Iterable)
        assert not isinstance(networks, self.nettype)
        for net in networks:
            assert isinstance(net, self.nettype) or isinstance(net, basestring)
        self._networks = networks
        self._name = name
        self._access = access

    @property
    def name(self):
        return self._name

    @property
    def networks(self):
        return self._networks

    @networks.setter
    def networks(self, value):
        if self._networks != [VALUENOTSET]:
            raise ValueError("Networks alread set to %s" % self._networks)
        for net in value:
            assert isinstance(net, self.nettype) or isinstance(net, basestring)
        self._networks = value

    @property
    def access(self):
        return self._access

    def __eq__(self, other):
        if not isinstance(other, IpPrefixList):
            return False
        net_eq = set(self.networks) == set(other.networks)
        access_eq = self.access == other.access
        id_eq = self.name == other.name
        return id_eq and access_eq and net_eq

    def __str__(self):
        return "IpPrefixList(id=%s, access=%s, networks=%s)" % \
               (self.name, self.access, self.networks)

    def __repr__(self):
        return self.__str__()


class Match(object):
    """Represent match action in a route map"""

    @property
    def match(self):
        raise NotImplementedError()

    def __eq__(self, other):
        return self.match == getattr(other, 'match', None)

    def __str__(self):
        return "%s(%s)" % (self.__class__.__name__, self.match)

    def __repr__(self):
        return self.__str__()


class Action(object):
    pass


class MatchCommunitiesList(Match):
    def __init__(self, communities_list):
        assert communities_list == VALUENOTSET or\
            isinstance(communities_list, CommunityList)
        self._match = communities_list

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        assert isinstance(value, CommunityList)
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        self._match = value


class MatchIpPrefixListList(Match):
    def __init__(self, prefix_list):
        assert prefix_list == VALUENOTSET or\
            isinstance(prefix_list, IpPrefixList)
        self._match = prefix_list

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        assert isinstance(value, IpPrefixList)
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        self._match = value


class MatchPeer(Match):
    def __init__(self, peer):
        assert peer == VALUENOTSET or isinstance(peer, basestring)
        self._match = peer

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        self._match = value


class MatchNextHop(Match):
    def __init__(self, nexthop):
        assert nexthop == VALUENOTSET or isinstance(nexthop, basestring)
        self._match = nexthop

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        self._match = value


class MatchLocalPref(Match):
    def __init__(self, localpref):
        assert localpref == VALUENOTSET or isinstance(localpref, int)
        self._match = localpref

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        assert isinstance(value, int)
        self._match = value


class ActionSetLocalPref(Action):
    def __init__(self, localpref):
        assert localpref == VALUENOTSET or isinstance(localpref, int)
        self._value = localpref

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, value):
        if self._value != VALUENOTSET:
            raise ValueError("Value alread set to %s" % self._value)
        self._value = value

    def __eq__(self, other):
        if self.value == VALUENOTSET:
            return False
        return self.value == getattr(other, 'value', None)

    def __str__(self):
        return "SetLocalPref(%s)" % self.value

    def __repr__(self):
        return self.__str__()


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

    def __eq__(self, other):
        return set(self._communities) == set(getattr(other, '_communities', []))

    def __str__(self):
        return "SetCommunity(%s)" % self._communities

    def __repr__(self):
        return self.__str__()


class RouteMapLine(object):
    def __init__(self, matches, actions, access, lineno=None):
        if matches is None:
            matches = []
        if actions is None:
            actions = []
        assert isinstance(matches, Iterable)
        assert isinstance(actions, Iterable)
        for match in matches:
            assert isinstance(match, Match)
        for action in actions:
            assert isinstance(action, Action)
        assert access == VALUENOTSET or isinstance(access, Access)

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

    @access.setter
    def access(self, value):
        if self._access != VALUENOTSET:
            raise ValueError("Access already set to %s" % self._access)
        assert isinstance(value, Access)
        self._access = value

    @property
    def lineno(self):
        return self._lineno

    def __eq__(self, other):
        matches = getattr(other, 'matches', None)
        actions = getattr(other, 'actions', None)
        access = getattr(other, 'access', None)
        lineno = getattr(other, 'lineno', None)
        return self.matches == matches and \
                self.actions == actions and \
                self.access == access and \
                self.lineno == lineno

    def __str__(self):
        return "lineno: %d\n\taccess: %s, \n\tMatches: \n\t\t%s, \n\tActions: \n\t\t%s>" \
               % (self.lineno, self.access, self.matches, self.actions)

    def __repr__(self):
        return "<lineno: %d, access: %s, Matches: %s, Actions: %s>" \
               % (self.lineno, self.access, self.matches, self.actions)


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

    def __eq__(self, other):
        return self.name == getattr(other, 'name', None) and \
               self.lines == getattr(other, 'lines', None)

    def __str__(self):
        ret = "RouteMap %s\n" % self.name
        for line in self.lines:
            ret += "\t%s\n" % line
        return ret

    def __repr__(self):
        return self.__str__()
