#!/usr/bin/env python
"""
Synthesize policies .. aka route maps for the moment

Match Semantics from
https://www.cisco.com/c/en/us/support/docs/ip/border-gateway-protocol-bgp/49111-route-map-bestp.html

A match or set command in each clause can be missed or repeated several times,
    if one of these conditions exist:

If several match commands are present in a clause, all must succeed for
    a given route in order for that route to match the clause
    (in other words, the logical AND algorithm is applied for multiple
    match commands).

If a match command refers to several objects in one command, either of
    them should match (the logical OR algorithm is applied).
    For example, in the match ip address 101 121 command,
    a route is permitted if it is permitted by access list 101 or access list 121.

If a match command is not present, all routes match the clause.
    In the previous example, all routes that reach clause 30 match;
    therefore, the end of the route-map is never reached.

If a set command is not present in a route-map permit clause then
    the route is redistributed without modification of its current attributes.
"""


from collections import namedtuple
import z3

from synet.topo.bgp import VALUENOTSET
from synet.topo.bgp import Community
from synet.topo.bgp import CommunityList
from synet.topo.bgp import IpPrefixList
from synet.topo.bgp import MatchIpPrefixListList
from synet.topo.bgp import MatchCommunitiesList

__author__ = "Ahmed El-Hassany"
__email__ = "a.hassany@gmail.com"


AndOp = namedtuple('AndOp', ['values'])
OrOp = namedtuple('OrOp', ['values'])


class SMTContext(object):
    """
    Hold SMT Context needed for the policy synthesis
    """
    def __init__(self, announcements, announcements_vars, announcement_sort,
                 communities_fun, prefixes_vars, prefix_sort, prefix_fun):
        """
        :param announcements: dict of name -> Announcement
        :param announcements_vars: dict of name -> Z3 Announcement
        :param announcement_sort: Z3 announcement type
        :param communities_fun: Community -> (z3.function (Announcement->True or False))
        :param prefixes_vars: dict of name -> Z3 Prefix var
        :param prefix_sort: Z3 prefix type
        :param prefix_fun: prefix -> (z3.function (Announcement->True or False))
        """
        self._announcements = announcements
        self._announcements_vars = announcements_vars
        self._announcement_sort = announcement_sort
        self._communities_fun = communities_fun
        self._prefixes_vars = prefixes_vars
        self._prefix_sort = prefix_sort
        self._prefix_fun = prefix_fun

    @property
    def announcements(self):
        """Returns a dict of name -> Announcement"""
        return self._announcements

    @property
    def announcements_vars(self):
        """Returns a dict of name -> Z3 Announcement var"""
        return self._announcements_vars

    @property
    def announcement_sort(self):
        """Returns Z3 announcement type"""
        return self._announcement_sort

    @property
    def communities_fun(self):
        """Returns a dict of Community -> (z3.function (Announcement->True or False))"""
        return self._communities_fun

    @property
    def prefixes_vars(self):
        """Returns a dict of name -> z3 Prefix var"""
        return self._prefixes_vars

    @property
    def prefix_sort(self):
        """Returns prefix z3 sort"""
        return self._prefix_sort

    @property
    def prefix_fun(self):
        """Returns  a dict prefix -> (z3.function (Announcement->True or False))"""
        return self._prefix_fun


class SMTObject(object):
    """
    Parent object for SMT helper classes
    """
    def get_val(self, model):
        """
        Return the concrete or synthesized value
        :param model: Z3 model
        :return: dependent on the subclass
        """
        raise NotImplementedError()

    def get_config(self, model):
        """
        Return the concrete or synthesized configuration instance
        :param model: Z3 model
        :return: dependent on the subclass
        """
        raise NotImplementedError()


class SMTCommunity(SMTObject):
    """
    Synthesis one Community match
    """
    def __init__(self, name, community, context):
        """
        :param community: Community object or VALUENOTSET
        :param name: unique name to make the SMT variables more readable
        :param context: SMTContext
        """
        assert community == VALUENOTSET or isinstance(community, Community)
        self.name = name
        self._community = community
        self.ctx = context
        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}
        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized community for this match
        :param model: Z3 model
        :return: Community
        """
        if self.match_synthesized is None:
            return self._community
        index = model.eval(self.match_synthesized).as_long()
        ret = self.match_syn_map[index]
        return ret

    def is_concrete(self):
        """
        Return true if concrete Community object defined for all
        known announcements in self.announcements
        """
        if self._community == VALUENOTSET:
            return False
        concrete = True
        for _, ann in self.ctx.announcements.iteritems():
            if ann.COMMUNITIES[self._community] not in ['T', 'F']:
                return False
        return concrete

    def _gen_match_func(self):
        if self._community != VALUENOTSET:
            if self.is_concrete():
                func = lambda x: self.ctx.announcements[str(x)].COMMUNITIES[self._community] == 'T'
                return func
            return self.ctx.communities_fun[self._community]
        else:
            # This is a bit tricky to handle
            # In case the community match is EMPTY,
            #     the the synthesizer is free to choose any community
            # We create a dummy function such that it ranges and values maps exactly to
            # one or more assigned communities.
            # Then we enumerate the communities,
            # and the variable _Selected_Community tells us which one that successfully
            # mapped to our dummy match
            f_name = '%s_Synthesize_Comm_Match' % self.name
            dummy_match = z3.Function(f_name, self.ctx.announcement_sort, z3.BoolSort())
            c_name = '%s_Selected_Comm_Match' % self.name
            self.match_synthesized = z3.Const(c_name, z3.IntSort())
            self.match_syn_map = {}
            constrains = []
            for i, community in enumerate(sorted(self.ctx.communities_fun.keys())):
                # TODO: there are some room for partial eval
                tmp = z3.Const('%s_Tmp%d' % (self.name, i), self.ctx.announcement_sort)
                self.match_syn_map[i] = community
                constrains.append(
                    z3.And(self.match_synthesized == i,
                           z3.ForAll(
                               [tmp],
                               dummy_match(tmp) == self.ctx.communities_fun[community](tmp)
                           ))
                )
            self.constraints = [z3.Or(*constrains)]
            # self.solver.append(constrains)
            match_fun = dummy_match
        return match_fun

    def get_config(self, model):
        """
        Get the synthesized Community
        :param model: Z3 model
        :return: Community
       """
        return self.get_val(model)


class SMTCommunityList(SMTObject):
    """
    Synthesis list of Communities (AND)
    """
    def __init__(self, name, community_list, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param communities: CommunityList object
        :param context: SMTContext
        """
        assert isinstance(community_list, CommunityList)
        self.name = name
        self._community_list = community_list
        self.ctx = context
        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}
        self._smt_matches = []
        for i, comm in enumerate(self._community_list.communities):
            name = '%s_%d' % (self.name, i)
            smt = SMTCommunity(name=name, community=comm, context=self.ctx)
            self._smt_matches.append(smt)
        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized list of Communities for this match
        :param model: Z3 model
        :return: list of Community
        """
        return [smt.get_val(model) for smt in self._smt_matches]

    def is_concrete(self):
        """
        Return true if concrete Community object defined for all
        known announcements in self.announcements
        :return:
        """
        for smt in self._smt_matches:
            if not smt.is_concrete():
                return False
        return True

    def _gen_match_func(self):
        # Add constraints
        for smt in self._smt_matches:
            self.constraints.extend(smt.constraints)
        dist = [smt.match_synthesized for smt in
                self._smt_matches if smt.match_synthesized is not None]
        if len(dist) > 1:
            unique_c = z3.Distinct(dist)
            self.constraints.append(unique_c)
        fun = lambda x: z3.And(*[smt.match_fun(x) for smt in self._smt_matches])
        return fun

    def get_config(self, model):
        """
        Get the synthesized CommunityList
        :param model: Z3 model
        :return: CommunityList
        """
        communities = self.get_val(model)
        return CommunityList(list_id=self._community_list.list_id,
                             access=self._community_list.access,
                             communities=communities)


class SMTIpPrefix(SMTObject):
    """
    Synthesis one IPPrefix
    TODO: Support longest prefix matching
    """
    def __init__(self, name, prefix, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param prefix: Prefix or VALUENOTSET
        :param context: SMTContext
        """
        assert prefix == VALUENOTSET or isinstance(prefix, basestring)
        self.name = name
        self._prefix = prefix
        self.ctx = context

        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}

        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized prefix for this match
        :param model: Z3 model
        :return: prefix
        """
        if self.match_synthesized is None:
            return self._prefix
        index = model.eval(self.match_synthesized)
        index = index.as_long()
        ret = self.match_syn_map[index]
        return ret

    def is_concrete(self):
        """
        Return true if concrete Prefix object
        :return: boolean
        """
        return self._prefix != VALUENOTSET

    def _gen_match_func(self):

        if self._prefix != VALUENOTSET:
            match_fun = lambda x: self.ctx.prefix_fun(x) == self.ctx.prefixes_vars[self._prefix]
        else:
            dummy_match = z3.Function(
                '%s_Synthesize_Prefix_Match' % self.name,
                self.ctx.announcement_sort, z3.BoolSort())
            self.match_synthesized = z3.Const(
                '%s_Selected_Prefix_Match' % self.name, z3.IntSort())
            self.match_syn_map = {}
            constraints = []
            for i, prefix in enumerate(sorted(self.ctx.prefixes_vars.keys())):
                prefix_var = self.ctx.prefixes_vars[prefix]
                tmp = z3.Const('%s_Tmp%d' % (self.name, i), self.ctx.announcement_sort)
                self.match_syn_map[i] = prefix
                constraints.append(
                    z3.And(self.match_synthesized == i,
                           z3.ForAll(
                               [tmp],
                               dummy_match(tmp) == z3.If(
                                   self.ctx.prefix_fun(tmp) == prefix_var,
                                   True,
                                   False))))
            self.constraints = [z3.Or(*constraints)]
            match_fun = dummy_match
        return match_fun

    def get_config(self, model):
        """
        Get the synthesized Prefix
        :param model: Z3 model
        :return: Prefix
       """
        return self.get_val(model)


class SMTIpPrefixList(SMTObject):
    """
    Synthesis list of IP Prefixes (AND)
    """
    def __init__(self, name, prefix_list, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param prefix_list: IpPrefixlist object
        :param context: SMTContext
        """
        assert isinstance(prefix_list, IpPrefixList)
        self.name = name
        self.prefix_list = prefix_list
        self.ctx = context

        self.constraints = []
        self.match_synthesized = None
        self.match_syn_map = {}

        self._smt_matches = []
        for i, prefix in enumerate(self.prefix_list.networks):
            name = '%s_%d' % (self.name, i)
            smt = SMTIpPrefix(name=name, prefix=prefix, context=self.ctx)
            self._smt_matches.append(smt)
        self.match_fun = self._gen_match_func()

    def get_val(self, model):
        """
        Return the synthesized list of Prefixes for this match
        :param model: Z3 model
        :return: list of Community
        """
        return [smt.get_val(model) for smt in self._smt_matches]

    def is_concrete(self):
        """
        Return true if concrete Prefix object defined
        :return:
        """
        for smt in self._smt_matches:
            if not smt.is_concrete():
                return False
        return True

    def _gen_match_func(self):
        # Add constraints
        for smt in self._smt_matches:
            self.constraints.extend(smt.constraints)
        dist = [smt.match_synthesized for smt in
                self._smt_matches if smt.match_synthesized is not None]
        if len(dist) > 1:
            unique_c = z3.Distinct(dist)
            self.constraints.append(unique_c)
        fun = lambda x: z3.And(*[smt.match_fun(x) for smt in self._smt_matches])
        return fun

    def get_config(self, model):
        """
        Get the synthesized CommunityList
        :param model: Z3 model
        :return: CommunityList
        """
        prefixes = self.get_val(model)
        return IpPrefixList(name=self.prefix_list.name,
                            access=self.prefix_list.access,
                            networks=prefixes)


class SMTMatch(SMTObject):
    """
    A single match is OR between a list of the same object type
    """
    def __init__(self, name, match, context):
        self.name = name
        self.match = match
        self.ctx = context
        self.constraints = []
        self.smts = []
        self.match_dispatch = {
            MatchCommunitiesList: self._match_comm,
            MatchIpPrefixListList: self._match_ip,
            OrOp: self._match_or
        }
        self.match_fun = self.match_dispatch[type(match)](match)

    def _match_comm(self, match):
        name = "%s_comm_list" % self.name
        self.smts = [SMTCommunityList(name, match.match, self.ctx)]
        self.constraints.extend(self.smts[0].constraints)
        return self.smts[0].match_fun

    def _match_ip(self, match):
        name = "%s_ip_list" % self.name
        self.smts = [SMTIpPrefixList(name, match.match, self.ctx)]
        self.constraints.extend(self.smts[0].constraints)
        return self.smts[0].match_fun

    def _match_or(self, match):
        matches = []
        for i, value in enumerate(match.values):
            name = "%s_or_%d_" % (self.name, i)
            new_match = SMTMatch(name, value, self.ctx)
            match_func = new_match.match_fun
            constraints = new_match.constraints
            matches.append(match_func)
            self.constraints.extend(constraints)
            self.smts.append(new_match)
        match_func = lambda x: z3.Or(*[m(x) for m in matches])
        return match_func

    def get_val(self, model):
        if len(self.smts) == 1:
            return self.smts[0].get_val(model)
        return [smt.get_val(model) for smt in self.smts]

    def _get_single_config(self, smt, model):
        config = smt.get_config(model)
        if isinstance(self.match, MatchCommunitiesList):
            return MatchCommunitiesList(config)
        elif isinstance(self.match, MatchIpPrefixListList):
            return MatchIpPrefixListList(config)
        return config

    def get_config(self, model):
        if isinstance(self.match, OrOp):
            return [smt.get_config(model) for smt in self.smts]
        return self._get_single_config(self.smts[0], model)


class SMTMatches(SMTObject):
    """
    A multiple matches with AND operator
    """
    def __init__(self, name, matches, context):
        """
        :param name: unique name to make the SMT variables more readable
        :param matches: List of Match objects
        :param context: SMTContext
        """
        self.name = name
        self.matches = matches
        self.ctx = context
        self.constraints = []
        self.boxes = []
        self.match_fun = self._load_matches()

    def _load_matches(self):
        match_funs = []
        for i, match in enumerate(self.matches):
            name = "%s_and_%d_" % (self.name, i)
            box = SMTMatch(name=name, match=match, context=self.ctx)
            self.constraints.extend(box.constraints)
            self.boxes.append(box)
            match_funs.append(box.match_fun)
        return lambda x: z3.And([m(x) for m in match_funs])

    def get_val(self, model):
        return [m.get_val(model) for m in self.boxes]

    def get_config(self, model):
        return [m.get_config(model) for m in self.boxes]
