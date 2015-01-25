
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

# This extractor inspects each fact F for several specific properties based on the given rules. Currently:
#     (i)   - Persistent: Fact F is never deleted.
#             Current implementation checks that predicate name of F never appear in a simplified rule head.
#     (ii)  - Local: Fact F is never sent to another MSR node.
#             Current implementation checks that predicate name of F (a) never appears in a rule with multiple
#             locations in rule head, (b) in rules with single location x in rule head, it appears in the rule
#             body at the same location x. 
#     (iii) - Not-LHS-Comprehended: Fact F never participates in a LHS comprehension pattern.
#             Current implementation checks that predicate name of F never appears in a LHS comprehension pattern
#             of a rule.
#     (iv)  - Is-Prioritized: Fact F is prioritized by a rule that introduces it.

# For each rule, we will also do the following:
#     (A) - Identify the predicate names that appear in different rule heads
#     (B) - Identify the predicate names that it prioritized (related to iv)

import msrex.frontend.lex_parse.ast as ast
import msrex.misc.visit as visit

from msrex.frontend.analyze.inspectors import Inspector
from msrex.frontend.analyze.checkers.base_checker import Checker

class FactPropertyExtractor(Checker):

	def __init__(self, decs, source_text, builtin_preds=[]):
		self.initialize(decs, source_text, builtin_preds=builtin_preds)
		self.rule_unique_heads = {}
		self.rule_priority_body = {}

	def check(self):
		for dec in self.decs:
			self.int_check(dec)

	@visit.on('ast_node')
	def int_check(self, ast_node):
		pass

	@visit.when(ast.EnsemDec)
	def int_check(self, ast_node):

		inspect = Inspector()

		decs = ast_node.decs

		simplified_pred_names = {}
		non_local_pred_names  = {}
		lhs_compre_pred_names = {}
		prioritized_pred_names = {}

		for rule_dec in inspect.filter_decs(decs, rule=True):
			rule_head_locs = {}
			simp_heads = rule_dec.slhs
			prop_heads = rule_dec.plhs
			rule_body  = rule_dec.rhs

			# Scan for simplified predicate names
			for fact in inspect.get_base_facts( simp_heads ):
				simplified_pred_names[ fact.name ] = ()

			# Scan for non local predicate names
			# Annotates non local rule body facts as well.
			loc_var_terms = inspect.free_vars( simp_heads+prop_heads, args=False, compre_binders=True )
			loc_vars = map(lambda t: t.name, loc_var_terms)
			if len(set(loc_vars)) > 1:
				# Flag all body predicates as non local
				for fact in inspect.get_base_facts( rule_body ):
					non_local_pred_names[ fact.name ] = ()
					fact.local = False
			else:
				loc_var = loc_vars[0]
				(bfs,lfs,lfcs,comps) = inspect.partition_rule_heads( rule_body )
				for lf in lfs:
					if isinstance(lf.loc, ast.TermVar):
						if lf.loc.name != loc_var:
							non_local_pred_names[ lf.fact.name ] = ()
							lf.fact.local = False
					else:
						# Location is not variable, hence treat as non-local
						non_local_pred_names[ lf.fact.name ] = ()
						lf.fact.local = False
				for lfc in lfcs:
					if isinstance(lfc.loc, ast.TermVar):
						if lfc.loc.name != loc_var:
							for f in lfc.facts:
								non_local_pred_names[ f.name ] = ()
								f.local = False
					else:
						# Location is not variable, hence treat as non-local
						for f in lfc.facts:
							non_local_pred_names[ f.name ] = ()
							f.local = False
				for comp in comps:
					# Assumes that comprehension fact patterns are solo
					loc_fact = comp.facts[0]
					if isinstance(loc_fact, ast.FactLoc):
						if loc_fact.loc.name != loc_var:
							non_local_pred_names[ loc_fact.fact.name ] = ()
							loc_fact.fact.local = False
						else:
							if loc_var in map(lambda tv: tv.name, inspect.free_vars( comp.comp_ranges[0].term_vars )):
								non_local_pred_name[ loc_fact.fact.name ] = ()
								loc_fact.fact.local = False

			# Scan for LHS comprehension predicate names
			(bfs,lfs,lfcs,comps) = inspect.partition_rule_heads( simp_heads + prop_heads )
			for comp in comps:
				loc_fact = comp.facts[0]
				if isinstance(loc_fact, ast.FactLoc):
					lhs_compre_pred_names[ loc_fact.fact.name ] = ()
				else:
					lhs_compre_pred_names[ loc_fact.name ] = ()

			# Scan for non-unique rule heads
			rule_head_pred_names = {}
			for fact in inspect.get_base_facts( simp_heads + prop_heads ):
				if fact.name not in rule_head_pred_names:
					rule_head_pred_names[fact.name] = [fact]
				else:
					rule_head_pred_names[fact.name].append( fact )

			self.rule_unique_heads[ rule_dec.name ] = []
			collision_idx = 0
			for name in rule_head_pred_names:
				facts = rule_head_pred_names[name]
				unique_head = len(facts) == 1
				for fact in facts:
					fact.unique_head  = unique_head
					fact.collision_idx = collision_idx
				collision_idx += 1
				if unique_head:
					self.rule_unique_heads[rule_dec.name].append( name )

			# Scan for priorities
			self.rule_priority_body[ rule_dec.name ] = {}
			(bfs,lfs,lfcs,comps) = inspect.partition_rule_heads( rule_body )
			for bf in bfs:
				if bf.priority != None:
					prioritized_pred_names[ bf.name ] = ()
					self.rule_priority_body[ rule_dec.name ][ bf.name ] = ()
			for lf in lfs:
				if lf.priority != None:
					prioritized_pred_names[ lf.fact.name ] = ()
					self.rule_priority_body[ rule_dec.name ][ lf.fact.name ] = ()
			for lfc in lfcs:
				if lfc.priority != None:
					for f in lfc.facts:
						prioritized_pred_names[ f.name ] = ()
						self.rule_priority_body[ rule_dec.name ][ f.name ] = ()
			for comp in comps:
				if comp.priority != None:
					for f in comp.facts:
						prioritized_pred_names[ f.name ] = ()
						self.rule_priority_body[ rule_dec.name ][ f.name ] = ()

		# Annotate fact declaration nodes with relevant information	
		fact_decs = inspect.filter_decs(decs, fact=True)
		for fact_dec in fact_decs:
			fact_dec.persistent = fact_dec.name not in simplified_pred_names
			fact_dec.local      = fact_dec.name not in non_local_pred_names
			fact_dec.monotone   = fact_dec.name not in lhs_compre_pred_names
			fact_dec.uses_priority = fact_dec.name in prioritized_pred_names
		self.fact_decs = fact_decs

		# Annotate rule declaration nodes with relevant information
		rule_decs = inspect.filter_decs(decs, rule=True)
		for rule_dec in rule_decs:
			rule_dec.unique_head_names        = self.rule_unique_heads[ rule_dec.name ]
			rule_dec.rule_priority_body_names = self.rule_priority_body[ rule_dec.name ].keys()

		# Annotate RHS constraints with monotonicity information
		for rule_dec in rule_decs:
			rule_body = rule_dec.rhs
			for fact in inspect.get_base_facts( rule_body ):
				fact.monotone = fact.name not in lhs_compre_pred_names

		# Annotate fact declaration nodes with export declaration information
		export_decs = inspect.filter_decs(decs, export=True)
		for export_dec in export_decs:
			if export_dec.export_sort == ast.QUERY_EXPORT:
				fact = export_dec.arg
				for fact_dec in fact_decs:
					if fact_dec.name == fact.name:
						fact_dec.exported_queries.append( fact )
						break

	def get_analysis(self):
		strs = "Analysis from Fact Property Extractor:\n"
		for fact_dec in self.fact_decs:
			strs += "Fact %s: %s %s %s\n" % (fact_dec.name, "Persist" if fact_dec.persistent else "Non-persist" 
                                                                 , "Local" if fact_dec.local else "Non-local"
                                                                 , "Monotonic" if fact_dec.monotone else "Non-monotonic")
		for rule_name in self.rule_unique_heads:
			unique_heads = self.rule_unique_heads[rule_name]
			if len(unique_heads) > 0:
				strs += "Rule %s has unique heads: %s\n" % (rule_name,', '.join(unique_heads))
		for rule_name in self.rule_priority_body:
			priority_body = self.rule_priority_body[rule_name]
			if len(priority_body) > 0:
				strs += "Rule %s has prioritized facts: %s" % (rule_name,', '.join(priority_body))
		return strs

