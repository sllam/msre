
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

from msrex.frontend.transform.base_transformer import Transformer

import msrex.frontend.lex_parse.ast as ast
import msrex.misc.visit as visit
from msrex.misc.framed_ctxt import FramedCtxt

from msrex.frontend.analyze.inspectors import Inspector

class AlphaIndexer(Transformer):

	def __init__(self, decs):
		self.initialize(decs)
		self.inspect = Inspector()

	def transform(self):
		self.int_transform( self.decs )

	@visit.on( 'ast_node' )
	def int_transform(self, ast_node, ctxt=None):
		pass

	@visit.when( list )
	def int_transform(self, ast_node, ctxt=None):
		for node in ast_node:
			self.int_transform( node, ctxt )

	@visit.when( ast.EnsemDec )
	def int_transform(self, ast_node, ctxt=None):
		rules = self.inspect.filter_decs( ast_node.decs, rule=True )
		for rule in rules:
			self. int_transform( rule )

	@visit.when( ast.RuleDec )
	def int_transform(self, ast_node, ctxt=None):
		ctxt = FramedCtxt()
		self.int_transform(ast_node.plhs, ctxt)
		self.int_transform(ast_node.slhs, ctxt)
		self.int_transform(ast_node.grd, ctxt)
		self.int_transform(ast_node.exists, ctxt)
		self.int_transform(ast_node.where, ctxt)
		self.int_transform(ast_node.rhs, ctxt)
		ast_node.next_rule_idx = ctxt.var_idx

	@visit.when( ast.AssignDec )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform( ast_node.term_pat, ctxt )
		self.int_transform( ast_node.builtin_exp, ctxt )

	@visit.when( ast.FactBase )
	def int_transform(self, ast_node, ctxt=None):
		for term in ast_node.terms:
			self.int_transform( term, ctxt )

	@visit.when( ast.FactLoc )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform(ast_node.loc, ctxt)
		self.int_transform(ast_node.fact, ctxt)

	@visit.when( ast.FactLocCluster )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform(ast_node.loc, ctxt)
		for fact in ast_node.facts:
			self.int_transform(fact, ctxt)

	@visit.when( ast.FactCompre )
	def int_transform(self, ast_node, ctxt=None):
		for cr in ast_node.comp_ranges:
			self.int_transform(cr.term_range, ctxt)

		comp_binders = self.inspect.free_vars( map(lambda cr: cr.term_vars, ast_node.comp_ranges) )
		ctxt.push_frame( keys = set(map(lambda cb: cb.name, comp_binders)) )

		self.int_transform(comp_binders, ctxt)
		self.int_transform(ast_node.facts, ctxt)
		self.int_transform(ast_node.guards, ctxt)

		ctxt.pop_frame()

	@visit.when( ast.TermVar )
	def int_transform(self, ast_node, ctxt=None):
		ast_node.rule_idx = ctxt.get_index( ast_node.name )
		
	@visit.when( ast.TermApp )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform(ast_node.term1, ctxt) 
		self.int_transform(ast_node.term2, ctxt)

	@visit.when( ast.TermTuple )
	def int_transform(self, ast_node, ctxt=None):
		for term in ast_node.terms:
			self.int_transform(term, ctxt)

	@visit.when( ast.TermList )
	def int_transform(self, ast_node, ctxt=None):
		for term in ast_node.terms:
			self.int_transform(term, ctxt)
	
	@visit.when( ast.TermListCons )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform(ast_node.term1, ctxt) 
		self.int_transform(ast_node.term2, ctxt)

	@visit.when( ast.TermMSet )
	def int_transform(self, ast_node, ctxt=None):
		for term in ast_node.terms:
			self.int_transform(term, ctxt)

	@visit.when( ast.TermEnumMSet )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform(ast_node.texp1, ctxt)
		self.int_transform(ast_node.texp2, ctxt)

	@visit.when( ast.TermCompre )
	def int_transform(self, ast_node, ctxt=None):
		for cr in ast_node.comp_ranges:
			self.int_transform(cr.term_range, ctxt)

		comp_binders = self.inspect.free_vars( map(lambda cr: cr.term_vars, ast_node.comp_ranges) )
		ctxt.push_frame( keys = set(map(lambda cb: cb.name, comp_binders)) )

		self.int_transform(comp_binders, ctxt)
		self.int_transform(ast_node.term, ctxt)
		self.int_transform(ast_node.guards, ctxt)

		ctxt.pop_frame()

	@visit.when( ast.TermBinOp )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform(ast_node.term1, ctxt) 
		self.int_transform(ast_node.term2, ctxt)

	@visit.when( ast.TermUnaryOp )
	def int_transform(self, ast_node, ctxt=None):
		self.int_transform(ast_node.term, ctxt) 

