#!/usr/bin/env python
"""
Various helpers with configuring BGP related Policies
"""

from enum import Enum
from collections import Iterable
from ipaddress import IPv4Network
from ipaddress import IPv6Network

from synet.utils.smt_context import is_symbolic
from synet.utils.smt_context import is_empty
from synet.utils.smt_context import VALUENOTSET


__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


class BGP_ATTRS_ORIGIN(Enum):
    """Enum of BGP origin types"""
    IGP = 1
    EBGP = 2
    INCOMPLETE = 3


class Announcement(object):
    """
    Carry BGP Announcement information
    """
    attributes = [
        'prefix', 'peer', 'origin', 'as_path', 'as_path_len', 'next_hop',
        'local_pref', 'med', 'communities', 'permitted']

    def __init__(self, prefix, peer, origin,
                 as_path, as_path_len, next_hop, local_pref, med, communities,
                 permitted):
        """
        :param prefix: the prefix that's being announced
        :param peer: the peer from whom that prefix has been received
                    (this is not technically in the BGP attributes set)
        :param origin: See BGP_ATTRS_ORIGIN
        :param as_path: List of AS numbers
        :param as_path_len: int
        :param next_hop:
            1. If the BGP Peers are in different AS then the next_hop IP address
               that will be sent in the update message will be the IP address of
               the advertising router.
            2. If the BGP peers are in the same AS (IBGP Peers),
                and the destination network being advertised in the update message
                is also in the same AS, then the next_hop IP address that will be sent
                in the update message will be the IP address of the advertising router
            3. If the BGP peers are in the same AS (IBGP Peers),
                and the destination network being advertised in the update message
                is in an external AS, then the next_hop IP address that will be
                sent in the update message will be the IP address of the external
                peer router which sent the advertisement to this AS.
        :param local_pref: is only used in updates sent to the IBGP Peers,
                It is not passed on to the BGP peers in other autonomous systems.
        :param med: MED value, int
        :param communities: dict Community values: Community->True/False
        :param permitted: Access.permit or Access.deny
        """
        if isinstance(as_path, list):
            if not is_symbolic(as_path_len) and not is_empty(as_path_len):
                assert len(as_path) == as_path_len

        self.prefix = prefix
        self.peer = peer
        self.origin = origin
        self.as_path = as_path
        self.as_path_len = as_path_len
        self.next_hop = next_hop
        self.local_pref = local_pref
        self.med = med
        self.communities = communities
        self.permitted = permitted
        self.__setattr__ = self._disable_mutations

    def _disable_mutations(self, key, value):
        assert hasattr(self, key), "Cannot assign new attributes"
        val = str(getattr(self, key))
        err = "Cannot assigned value to %s, existing value is %s" % (key, val)
        assert val == VALUENOTSET, err
        super(Announcement, self).__setattr__(key, value)

    def __str__(self):
        return "Announcement<%s, %s, %s, %s, %s, %s, %s>" % (
            self.prefix, self.peer, self.origin,
            self.as_path, self.next_hop, self.local_pref, self.communities
        )

    def copy(self):
        comms = {}
        for comm, fun in self.communities.iteritems():
            comms[comm] = fun
        return Announcement(
            prefix=self.prefix, peer=self.peer, origin=self.origin,
            as_path=self.as_path, next_hop=self.next_hop,
            as_path_len=self.as_path_len, local_pref=self.local_pref,
            med=self.med, communities=comms, permitted=self.permitted)


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
        if self.is_new_format:
            return self.get_new_format()
        return self._value

    def get_value(self):
        """Get the actual integer value"""
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
        bin = '{0:032b}'.format(self._value)
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

    def __hash__(self):
        return hash(self.value)

    def __eq__(self, other):
        return self.value == getattr(other, 'value', other)

    def __ne__(self, other):
        return not self.__eq__(other)

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


class MatchAsPath(Match):
    def __init__(self, as_path):
        assert as_path == VALUENOTSET or isinstance(as_path, Iterable)
        self._match = as_path

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        self._match = value


class MatchPermitted(Match):
    def __init__(self, access):
        assert access == VALUENOTSET or isinstance(access, Access)
        self._match = access

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        self._match = value


class MatchAsPathLen(Match):
    def __init__(self, as_path_len):
        assert as_path_len == VALUENOTSET or isinstance(as_path_len, int)
        self._match = as_path_len

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        self._match = value


class MatchMED(Match):
    def __init__(self, med):
        assert med == VALUENOTSET or isinstance(med, int)
        self._match = med

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        assert isinstance(value, int)
        self._match = value


class MatchSelectOne(Match):
    """Allow multiple matches"""
    def __init__(self, matches):
        assert isinstance(matches, Iterable)
        assert matches
        for match in matches:
            assert isinstance(match, Match)
        self._match = matches

    @property
    def match(self):
        return self._match

    @match.setter
    def match(self, value):
        if self._match != VALUENOTSET:
            raise ValueError("Match already set to %s" % self._match)
        assert isinstance(value, int)
        self._match = value


class ActionPermitted(Action):
    def __init__(self, access):
        assert access == VALUENOTSET or isinstance(access, Access)
        self._value = access

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


class ActionSetNextHop(Action):
    def __init__(self, next_hop):
        assert is_empty(next_hop) or isinstance(next_hop, basestring)
        self._value = next_hop

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
        return "SetNextHop(%s)" % self.value

    def __repr__(self):
        return self.__str__()


class ActionSetPrefix(Action):
    def __init__(self, prefix):
        assert is_empty(prefix) or isinstance(prefix, basestring)
        self._value = prefix

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
        return "SetPrefix(%s)" % self.value

    def __repr__(self):
        return self.__str__()


class ActionASPathPrepend(Action):
    """Prepend list of AS Paths"""

    def __init__(self, as_paths):
        assert isinstance(as_paths, Iterable)
        self._value = as_paths

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
        return "ASPathPrepend(%s)" % self.value

    def __repr__(self):
        return self.__str__()


class ActionSetASPath(Action):
    """Prepend list of AS Paths"""

    def __init__(self, as_path):
        assert isinstance(as_path, Iterable)
        self._value = as_path

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
        return "SetASPath(%s)" % self.value

    def __repr__(self):
        return self.__str__()


class ActionSetASPathLen(Action):
    def __init__(self, as_path_len):
        assert is_empty(as_path_len) or isinstance(as_path_len, int)
        self._value = as_path_len

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
        return "SetASPathLen(%s)" % self.value

    def __repr__(self):
        return self.__str__()


class ActionSetPeer(Action):
    def __init__(self, peer):
        assert is_empty(peer) or isinstance(peer, basestring)
        self._value = peer

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
        return "SetPeer(%s)" % self.value

    def __repr__(self):
        return self.__str__()


class ActionSetMED(Action):
    def __init__(self, med):
        assert is_empty(med) or isinstance(med, int)
        self._value = med

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
        return "SetMED(%s)" % self.value

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
            assert is_empty(community) or isinstance(community, Community)
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
            assert isinstance(match, Match), "Expected a match but found %s" % match
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
