
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

from msrex.frontend.analyze.inspectors import Inspector

from msrex.frontend.compile.join_ordering import JoinOrdering
from msrex.frontend.compile.lookup_context import ORD_LEQ, ORD_GEQ, ORD_LT, ORD_GT, LookupContext, LookupTables, LinearLookup, HashLookup, MemLookup, OrdLookup

from collections import defaultdict

class ProgCompilation:

	def __init__(self, ensem_dec, rules, fact_dir, extern_decs, exec_dec, prog_name):
		self.ensem_dec = ensem_dec
		self.prog_name  = prog_name
		self.ensem_name = ensem_dec.name
		self.fact_dir = fact_dir
		self.lookup_tables = LookupTables( fact_dir )
		rule_compilations = []
		for rule in rules:
			rule_compilations.append( RuleCompilation(rule, fact_dir, self.lookup_tables) )
		self.rule_compilations = rule_compilations
		self.lookup_tables.padWithLinearLookup()
		self.rules = rules
		self.fact_dir = fact_dir

		self.pred_rule_compilations = defaultdict(list)
		for rule_comp in self.rule_compilations:
			for join_ordering in rule_comp.join_orderings:
				self.pred_rule_compilations[join_ordering.fact_idx].append( join_ordering )

		self.extern_decs = extern_decs
		self.exec_dec    = exec_dec

	def getRuleNames(self):
		inspect = Inspector()
		rules = inspect.filter_decs( self.ensem_dec.decs, rule=True )
		return map(lambda r: r.name, rules)

	def __repr__(self):
		prog_str = "" ## "======== Lookup Tables ========\n"
		prog_str += "%s\n" % self.lookup_tables
		for (fact_idx,join_orderings) in self.pred_rule_compilations.items():
			fact_dec = self.fact_dir.getFactFromIdx(fact_idx)
			fact_name = fact_dec.name
			jo_strs = []
			for join_ordering in join_orderings:
				jo_strs.append( "%s" % join_ordering )
			prog_str += "\n======== Rule Compilations for %s ========\n" % fact_name
			prog_str += "\n".join( jo_strs )
		return prog_str

class RuleCompilation:

	def __init__(self, rule, fact_dir, lookup_tables):
		self.rule = rule
		self.join_orderings = []
		for occ_idx in rule.occ_heads:
			self.join_orderings.append( JoinOrdering(rule, occ_idx, fact_dir, lookup_tables) )



