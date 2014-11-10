
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
from msrex.frontend.analyze.checkers.base_checker import Checker

class LHSRestrictChecker(Checker):

	def __init__(self, decs, source_text):
		self.initialize(decs, source_text)

	def check(self):
		inspect = Inspector()
		for ensem_dec in inspect.filter_decs(self.decs, ensem=True):
			self.check_int(ensem_dec)

	@visit.on('ast_node')
	def check_int(self, ast_node):
		pass

	@visit.when(ast.EnsemDec)
	def check_int(self, ast_node):
		inspect = Inspector()
		for dec in inspect.filter_decs(ast_node.decs, rule=True):
			self.check_int(dec)		

	@visit.when(ast.RuleDec)
	def check_int(self, ast_node):
		inspect = Inspector()
		self.rule_free_vars = inspect.free_vars( ast_node.plhs + ast_node.slhs )
		for fact in ast_node.plhs + ast_node.slhs:
			self.check_int(fact)
		self.rule_free_vars = []	

	@visit.when(ast.FactBase)
	def check_int(self, ast_node):
		# error_idx = self.declare_error("Unsupported LHS Pattern: Atomic fact pattern with no location.")
		# self.extend_error(error_idx, ast_node)
		# Note: now allowed. DefaultLocation transformer will insert the appropriate default location ast node.
		pass

	@visit.when(ast.FactLoc)
	def check_int(self, ast_node):
		pass

	@visit.when(ast.FactLocCluster)
	def check_int(self, ast_node):
		pass

	@visit.when(ast.FactCompre)
	def check_int(self, ast_node):
		comp_ranges = ast_node.comp_ranges
		if len(comp_ranges) > 1:
			error_idx = self.declare_error("Unsupported LHS Pattern: Comprehension pattern with multiple comprehension range.")
			for comp_range in comp_ranges:
				self.extend_error(error_idx, comp_range)
		else:
			for comp_range in comp_ranges:
				self.check_int(comp_range)
		inspect = Inspector()
		fact_bases = inspect.get_base_facts( ast_node.facts )
		if len(fact_bases) != 1:
			error_idx = self.declare_error("Unsupported LHS Pattern: Comprehension pattern with multiple fact patterns.")
			for f in ast_node.facts:
				self.extend_error(error_idx, f)

	@visit.when(ast.CompRange)
	def check_int(self, ast_node):
		term_vars  = ast_node.term_vars
		term_range = ast_node.term_range
		
		if term_range.term_type != ast.TERM_VAR:
			error_idx = self.declare_error("Unsupported LHS Pattern: Comprehension pattern with non-variable comprehension range.")
			self.extend_error(error_idx, term_range)
		else:
			match_comp_range = []
			for free_var in self.rule_free_vars:
				if free_var.name == term_range.name:
					match_comp_range.append(free_var)
			if len(match_comp_range) > 1:
				error_idx = self.declare_error("Unsupported LHS Pattern: Comprehension pattern with non-linear comprehension range.")
				map(lambda m: self.extend_error(error_idx, m), match_comp_range)

		non_var_binders = False
		if term_vars.term_type == ast.TERM_VAR:
			pass
		elif term_vars.term_type == ast.TERM_TUPLE:
			for term_var in term_vars.terms:
				if term_var.term_type != ast.TERM_VAR:
					non_var_binders = True
		else:
			non_var_binders = True
		if non_var_binders:
			error_idx = self.declare_error("Unsupported LHS Pattern: Comprehension pattern with non-variable binders.")
			self.extend_error(error_idx, term_vars)

		
