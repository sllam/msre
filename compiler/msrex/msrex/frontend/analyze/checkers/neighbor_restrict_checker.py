
'''
This file is part of MSR Ensemble (MSRE-X).

MSRE-X is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

MSRE-X is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with MSRE-X. If not, see <http://www.gnu.org/licenses/>.

MSR Ensemble (MSRE-X) Version 0.5, Prototype Alpha

Authors:
Edmund S. L. Lam      sllam@qatar.cmu.edu
Iliano Cervesato      iliano@cmu.edu

* This implementation was made possible by an NPRP grant (NPRP 09-667-1-100, Effective Programming 
for Large Distributed Ensembles) from the Qatar National Research Fund (a member of the Qatar 
Foundation). The statements made herein are solely the responsibility of the authors.
'''

import msrex.frontend.lex_parse.ast as ast
import msrex.misc.visit as visit

from msrex.misc.aggregators import subseteq
from msrex.frontend.analyze.inspectors import Inspector
from msrex.frontend.analyze.checkers.base_checker import Checker

def extend(match_obligations, v, fact, is_simp, role):
	if v.name in match_obligations:
		heads = match_obligations[v.name]
		if is_simp:
			extendRoleDict(heads['simp'], fact, role)
		else:
			extendRoleDict(heads['prop'], fact, role)
	else:
		stds = []
		trgs = []
		acts = []
		if role == ast.MATCH_FACT:
			stds = [fact]
		elif role == ast.TRIGGER_FACT:
			trgs = [fact]
		elif role == ast.ACTUATOR_FACT:
			acts = [fact]	
		if is_simp:
			match_obligations[v.name] = { 'term':v
                                                    , 'simp':{ 'triggers':trgs, 'actuators':acts, 'facts':stds }
                                                    , 'prop':{ 'triggers':[], 'actuators':[], 'facts':[] } }
		else:
			match_obligations[v.name] = { 'term':v
                                                    , 'prop':{ 'triggers':trgs, 'actuators':acts, 'facts':stds }
                                                    , 'simp':{ 'triggers':[], 'actuators':[], 'facts':[] } }

def mkNewRoleDict(trgs=[],acts=[],stds=[],mix=[]):
	for fact,role in mix:
		if role == ast.MATCH_FACT:
			stds += [fact]
		elif role == ast.TRIGGER_FACT:
			trgs += [fact]
		elif role == ast.ACTUATOR_FACT:
			acts += [fact]		
	return { 'triggers':trgs, 'actuators':acts, 'facts':stds }

def extendRoleDict(role_dict, fact, role):
	if role == ast.MATCH_FACT:
		role_dict['facts'].append(fact)
	elif role == ast.TRIGGER_FACT:
		role_dict['triggers'].append(fact)
	elif role == ast.ACTUATOR_FACT:
		role_dict['actuators'].append(fact)

def retrieveFacts(role_dict, simps=False, props=False, triggers=False, actuators=False, facts=False):
	outputs = []
	if simps:
		if triggers:
			outputs += role_dict['simp']['triggers']
		if actuators:
			outputs += role_dict['simp']['actuators']
		if facts:
			outputs += role_dict['simp']['facts']
	if props:
		if triggers:
			outputs += role_dict['prop']['triggers']
		if actuators:
			outputs += role_dict['prop']['actuators']
		if facts:
			outputs += role_dict['prop']['facts']
	return outputs

def retrieveAll(role_dict):
	return retrieveFacts(role_dict, simps=True, props=True, triggers=True, actuators=True, facts=True)

def getHeads(match_obligations, var_name):
	heads = match_obligations[var_name]
	return heads['simp'] + heads['prop']

class NeighborRestrictChecker(Checker):

	def __init__(self, decs, source_text, builtin_preds=[]):
		self.initialize(decs, source_text, builtin_preds=builtin_preds)
		self.inspect = Inspector()
		self.fact_dict = {}

	def check(self):
		for ensem_dec in self.inspect.filter_decs(self.decs, ensem=True):
			self.checkEnsem(ensem_dec)

	def checkEnsem(self, ensem_dec):
		self.fact_dict = {}

		for fact_dec in self.inspect.filter_decs(ensem_dec.decs, fact=True):
			self.fact_dict[fact_dec.name] = fact_dec

		max_nbr_level = -1
		some_requires_sync = False
		for rule_dec in self.inspect.filter_decs(ensem_dec.decs, rule=True):
			nbr_level,requires_sync = self.checkRule(rule_dec)
			if max_nbr_level < nbr_level:
				max_nbr_level = nbr_level
			if requires_sync:
				some_requires_sync = True

		ensem_dec.max_nbr_level = max_nbr_level 
		ensem_dec.requires_sync = some_requires_sync

	def checkRule(self, rule_dec):
		match_obligations = {}
		for fact in rule_dec.slhs:
			self.checkFact(fact, match_obligations, True)
		for fact in rule_dec.plhs:
			self.checkFact(fact, match_obligations, False)
		if len(match_obligations.keys()) > 1:
			rule_dec.is_system_centric = True
			rule_dec.match_obligations = match_obligations
			# TODO: Check neighbor relation and determine viable primary location
			
			nbr_options = []
			for primary_loc in match_obligations:
				my_facts = retrieveAll( match_obligations[primary_loc] )
				other_locs = []
				other_facts = []
				for loc in match_obligations:
					if primary_loc != loc:
						other_locs  += [ loc ]
						other_facts += retrieveAll( match_obligations[loc] )
				my_args = []
				for fact in my_facts:
					my_args += map(lambda v: v.name, self.inspect.free_vars( fact, loc=False, args=True ))

				if subseteq(other_locs, my_args):
					other_fact_dict = {}
					for loc in other_locs:
						other_fact_dict[loc] = match_obligations[loc]
					has_trigger = False
					for fact in my_facts:
						if ast.TRIGGER_FACT == self.getFactRole( fact ):
							has_trigger = True

					primary_grds = []
					other_grds   = {}
					for loc in other_fact_dict:
						other_grds[loc] = []
					non_iso_grds  = []
					for grd in rule_dec.grd:
						if subseteq(self.inspect.free_vars( grd ), my_args):
							primary_grds.append( grd )
						else:
							grd_added = False
							for loc in other_fact_dict:
								other_facts = other_fact_dict[loc]
								other_args = map(lambda v: v.name, self.inspect.free_vars( other_facts, loc=False, args=True ))
								if subseteq(self.inspect.free_vars( grd ), my_args+other_args):
									other_grds[loc].append( grd )
									grd_added = True
							if not grd_added:
								non_iso_grds.append( grd )

					nbr_option = { 'primary_loc'         : primary_loc
                                                     , 'primary_obligation'  : match_obligations[primary_loc]
                                                     , 'primary_guards'      : primary_grds
                                                     , 'other_obligations'   : other_fact_dict
                                                     , 'other_guards'        : other_grds
                                                     , 'non_iso_guards'      : non_iso_grds
                                                     , 'primary_has_trigger' : has_trigger }
					if len(non_iso_grds) == 0:
						if has_trigger:
							nbr_options = [ nbr_option ] + nbr_options
						else:
							nbr_options.append( nbr_option )
			if len(nbr_options) < 1:
				error_idx = self.declare_error( "System-centric rule is not neighbor-restricted.")
				self.extend_error( error_idx, rule_dec )

			rule_dec.nbr_options = nbr_options
			rule_dec.nbr_level = len( other_locs )

			# Currently always requires sync
			# TODO: Check LHS patterns and programmer pragmas
			rule_dec.requires_sync = True

			return (rule_dec.nbr_level,rule_dec.requires_sync)
		else:
			rule_dec.primary_loc = match_obligations.keys()[0]
			rule_dec.is_system_centric = False
			rule_dec.requires_sync = False
			return (0,False)

	@visit.on( 'fact' )
	def checkFact(self, fact, match_obligations, is_simp):
		pass

	@visit.when( ast.FactLoc )
	def checkFact(self, fact, match_obligations, is_simp):
		vs = self.inspect.free_vars( fact.loc )
		role = self.getFactRole( fact )
		extend(match_obligations, vs[0], fact, is_simp, role)

	@visit.when( ast.FactCompre )
	def checkFact(self, fact, match_obligations, is_simp):
		vs = self.inspect.free_vars( fact.facts[0].loc )
		role = self.getFactRole( fact )
		extend(match_obligations, vs[0], fact, is_simp, role)

	@visit.on( 'fact' )
	def getFactRole(self, fact):
		pass

	@visit.when( ast.FactLoc )
	def getFactRole(self, fact):
		return self.fact_dict[fact.fact.name].fact_role

	@visit.when( ast.FactCompre )
	def getFactRole(self, fact):
		return self.fact_dict[fact.facts[0].fact.name].fact_role

