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

from msrex.frontend.analyze.inspectors import Inspector

from msrex.frontend.analyze.smt_solver import tyLoc

class DefaultLocation(Transformer):

	def __init__(self, decs):
		self.initialize(decs)
		self.loc_idx = 0
		self.loc_ctxt = {}
		self.has_defaulted = False

	def get_fresh_loc(self):
		loc_name = "Here" # "l%s" % self.loc_idx
		self.loc_idx += 1
		loc_var = ast.TermVar(loc_name)
		loc_var.smt_type = tyLoc
		loc_var.type     = ast.TypeCons( ast.LOC )
		return loc_var

	def transform(self):
		self.int_transform(self.decs)

	@visit.on( 'ast_node' )
	def int_transform(self, ast_node):
		pass

	@visit.when( list )
	def int_transform(self, ast_node):
		for node in ast_node:
			self.int_transform( node )

	@visit.when( ast.EnsemDec )
	def int_transform(self, ast_node):
		rules = self.inspect.filter_decs( ast_node.decs, rule=True )
		for rule in rules:
			self. int_transform( rule )

	@visit.when( ast.ExecDec )
	def int_transform(self, ast_node):
		default_loc_var = self.get_fresh_loc()
		self.has_defaulted = False
		fact_decs = self.inspect.filter_decs( ast_node.decs, loc_facts=True )
		for fact_dec in fact_decs:
			 self.int_transform_fact_dec( fact_dec, default_loc_var )
		if self.has_defaulted:
			ast_node.decs = [ast.ExistDec([default_loc_var])] + ast_node.decs

	def int_transform_fact_dec(self, fact_dec, default_loc_var ):
		tr_loc_facts = []
		for fact in fact_dec.loc_facts:
			tr_loc_facts += self.int_transform_fact( fact, default_loc_var )
		fact_dec.loc_facts = tr_loc_facts

	@visit.when( ast.RuleDec )
	def int_transform(self, ast_node):
		default_loc_var = self.get_fresh_loc()
		self.has_defaulted = False
		tr_slhs = []
		for simp_head in ast_node.slhs:
			tr_slhs += self.int_transform_fact( simp_head, default_loc_var )
		tr_plhs = []
		for prop_head in ast_node.plhs:
			tr_plhs += self.int_transform_fact( prop_head, default_loc_var ) 
		tr_rhs = []
		for body in ast_node.rhs:
			tr_rhs += self.int_transform_fact( body, default_loc_var ) 
		ast_node.slhs = tr_slhs
		ast_node.plhs = tr_plhs
		ast_node.rhs  = tr_rhs

	@visit.on( 'fact_node' )
	def int_transform_fact( self, fact_node, default_loc_var ):
		pass

	@visit.when( ast.FactLoc )
	def int_transform_fact( self, fact_node, default_loc_var ):
		return [fact_node]

	@visit.when( ast.FactBase )
	def int_transform_fact( self, fact_node, default_loc_var ):
		self.has_defaulted = True
		print "Adding default location %s\n" % default_loc_var
		return [ast.FactLoc(default_loc_var, fact_node, priority=fact_node.priority)]
		
	@visit.when( ast.FactLocCluster )
	def int_transform_fact( self, fact_node, default_loc_var ):
		fact_locs = []
		for fact in fact_node.facts:
			fact_locs.append( ast.FactLoc(fact_node.loc, fact, priority=fact_node.priority) )
		return fact_locs

	@visit.when( ast.FactCompre )
	def int_transform_fact( self, fact_node, default_loc_var ):
		tr_facts = []
		for fact in fact_node.facts:
			tr_facts += self.int_transform_fact( fact, default_loc_var )
		fact_node.facts = tr_facts
		return [fact_node]


