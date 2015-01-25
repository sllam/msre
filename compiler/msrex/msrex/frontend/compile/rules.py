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

from msrex.frontend.analyze.inspectors import Inspector

from msrex.frontend.compile.rule_facts import FactDirectory, SIMP_HEAD, PROP_HEAD, FactAtomHead, FactCompreHead, FactAtomBody, FactCompreBody
from msrex.frontend.compile.rule_guards import process_guard

# Rules

RULE_INDEX = 0
def get_next_rule_index():
	global RULE_INDEX
	new_id = RULE_INDEX
	RULE_INDEX += 1
	return new_id

class Rule:
	def __init__(self, rule_dec, fact_dir):
		self.rule = rule_dec

		'''
		# Count and index rule variables
		inspect = Inspector()
		var_idx = 0
		self.vars = {}
		# Annotate Rule heads and body with variable indices
		for tvar in inspect.free_vars( rule_dec.slhs + rule_dec.plhs + rule_dec.rhs, compre_binders=True ):
			if tvar.name not in self.vars:
				self.vars[tvar.name] = var_idx
				var_idx += 1
			tvar.rule_idx = self.vars[tvar.name]
		# Annotate Rule Guards with variable indices
		for tvar in inspect.free_vars( rule_dec.grd, compre_binders=True ):
			if tvar.name not in self.vars:
				self.vars[tvar.name] = var_idx
				var_idx += 1
			tvar.rule_idx = self.vars[tvar.name]
		# Annotate Exist variables with variable indices
		for tvar in rule_dec.exists:
			if tvar.name not in self.vars:
				self.vars[tvar.name] = var_idx
				var_idx += 1
			tvar.rule_idx = self.vars[tvar.name]
		# Annotate Where stmts with variable indices
		for tassign in rule_dec.where:
			for tvar in inspect.free_vars( [tassign.term_pat, tassign.builtin_exp], compre_binders=True ):
				if tvar.name not in self.vars:
					self.vars[tvar.name] = var_idx
					var_idx += 1
				tvar.rule_idx = self.vars[tvar.name]
		'''

		# Variable index
		self.next_var_idx = rule_dec.next_rule_idx

		# Rule heads
		self.atom_heads   = []
		self.compre_heads = []
		self.has_simplify = False
		self.has_propagate = False

		inspect = Inspector()

		'''
		rule_head_var_dicts = {}
		for rule_head_var in inspect.free_vars(rule_dec.slhs+rule_dec.plhs, loc=True, args=True, compre_binders=False):
			rule_head_var_dicts[rule_head_var.name] = rule_head_var
		self.rule_head_vars = rule_head_var_dicts.values()

		rule_head_binder_dicts = {}
		for rule_head_binder in inspect.free_vars(rule_dec.slhs+rule_dec.plhs, loc=False, args=False, compre_binders=True):
			rule_head_binder_dicts[rule_head_binder.name] = rule_head_binder
		self.rule_head_binders = rule_head_binder_dicts.values()
		'''

		rule_head_pat_vars,rule_head_binders,rule_head_all_vars = inspect.get_all_free_vars(rule_dec.slhs+rule_dec.plhs)
		self.rule_head_vars     = rule_head_pat_vars
		self.rule_head_binders  = rule_head_binders
		self.rule_head_all_vars = rule_head_all_vars

		body_pat_vars,body_binders,body_all_vars = inspect.get_all_free_vars(rule_dec.rhs)
		self.body_vars     = body_pat_vars
		self.body_binders  = body_binders
		self.body_all_vars = body_all_vars

		where_pat_vars,where_binders,where_all_vars = inspect.get_all_free_vars(rule_dec.where)
		self.where_vars     = where_pat_vars
		self.where_binders  = where_binders
		self.where_all_vars = where_all_vars

		self.all_vars = inspect.set_vars( inspect.free_vars(rule_dec.slhs+rule_dec.plhs+rule_dec.rhs+rule_dec.where
                                                                   ,loc=True, args=True, compre_binders=True) )

		for head in rule_dec.slhs:
			self.has_simplify = True
			if head.fact_type == ast.FACT_LOC:
				self.atom_heads.append( FactAtomHead(head, SIMP_HEAD, fact_dir) )
			elif head.fact_type == ast.FACT_COMPRE:
				self.compre_heads.append( FactCompreHead(head, SIMP_HEAD, fact_dir) )
			else:
				print "Error: unknown head type"
		for head in rule_dec.plhs:
			self.has_propagate = True
			if head.fact_type == ast.FACT_LOC:
				self.atom_heads.append( FactAtomHead(head, PROP_HEAD, fact_dir) )
			elif head.fact_type == ast.FACT_COMPRE:
				self.compre_heads.append( FactCompreHead(head, PROP_HEAD, fact_dir) )
			else:
				print "Error: unknown head type"


		# Assign rule heads an occurrence number, based on atom first, simplify first
		self.occ_heads = {}
		occ_idx = 0
		for head in self.atom_heads + self.compre_heads:
			self.occ_heads[occ_idx] = head
			occ_idx += 1

		# Rule Guards
		self.idx_grds  = []
		self.non_idx_grds = []

		for grd in rule_dec.grd:
			rulegrd = process_guard( grd )
			if rulegrd.indexable():
				self.idx_grds.append( rulegrd )
			else:
				self.non_idx_grds.append( rulegrd )

		# Exists Variable
		self.exist_dests = []
		self.exist_locs  = []
		for exist_var in rule_dec.exists:
			if exist_var.type.name == ast.DEST:
				self.exist_dests.append( exist_var )
			if exist_var.type.name == ast.LOC:
				self.exist_locs.append( exist_var )

		# Where Bindings
		self.where = rule_dec.where

		# Rule Body
		self.rule_body = []
		self.has_non_local     = False
		self.has_non_monotonic = False
		self.has_prioritized   = False
		for f in rule_dec.rhs:
			if f.fact_type == ast.FACT_LOC:
				local = f.fact.local
				monotone = f.fact.monotone
				priority = f.fact.priority
				rbody = FactAtomBody( f, fact_dir )
			elif f.fact_type == ast.FACT_COMPRE:
				local = f.facts[0].fact.local
				monotone = f.facts[0].fact.monotone
				priority = f.facts[0].fact.priority
				rbody = FactCompreBody( f, fact_dir )
			if not local:
				self.has_non_local = True
			if not monotone:
				self.has_non_monotonic = True
			if priority != None:
				self.has_prioritized = True
			self.rule_body.append( rbody )

	def get_name(self):
		return self.rule.name

	def get_next_var_idx(self):
		new_var_idx = self.next_var_idx
		self.next_var_idx += 1
		return new_var_idx

	def __repr__(self):
		strs = "===== Rule: %s =====\n" % self.rule.name
		strs += "Has Simplify Heads :- %s\n" % ("Yes" if self.has_simplify else "No")
		strs += "Has Propagate Heads :- %s\n" % ("Yes" if self.has_propagate else "No")
		strs += "Has Non-Local Body:- %s\n" % ("Yes" if self.has_non_local else "No")
		strs += "Has Non-Monotonic Body:- %s\n" % ("Yes" if self.has_non_monotonic else "No")
		strs += "Has Prioritized Body:- %s\n" % ("Yes" if self.has_prioritized else "No")
		if len(self.atom_heads) > 0:
			strs += "Atom Heads :-\n"
			for atom in self.atom_heads:
				strs += atom.__repr__() + "\n"
		if len(self.compre_heads) > 0:
			strs += "Compre Heads :-\n"
			for comp in self.compre_heads:
				strs += comp.__repr__() + "\n"
		if len(self.idx_grds) > 0:
			strs += "Indexible Guards :-\n"
			for grd in self.idx_grds:
				strs += grd.__repr__() + "\n"
		if len(self.non_idx_grds) > 0:
			strs += "Non-indexible Guards :-\n"
			for grd in self.non_idx_grds:
				strs += grd.__repr__() + "\n"
		if len(self.exist_locs) > 0:
			strs += "Exist Locs :- %s\n" % (' '.join(map( lambda e: e.__str__(), self.exist_locs )))
		if len(self.exist_dests) > 0:
			strs += "Exist Dests :- %s\n" % (' '.join(map( lambda e: e.__str__(), self.exist_dests )))
		if len(self.where) > 0:
			strs += "Where Declarations :-\n"
			for tassign in self.where:
				strs += "%s := %s\n" % (tassign.term_pat,tassign.builtin_exp)
		if len(self.rule_body) > 0:
			strs += "Rule Body :-\n"
			for fact in self.rule_body:
				strs += fact.__repr__() + "\n"
		return strs



# Currently assumes exactly 1 ensem dec in the program
def process_rules(ensem_dec):
	inspect = Inspector()

	facts   = inspect.filter_decs(ensem_dec, fact=True)
	rules   = inspect.filter_decs(ensem_dec, rule=True)

	fact_dir = FactDirectory( facts )

	return (fact_dir, map(lambda r: Rule(r, fact_dir),rules))

