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

class RuleLinearizer(Transformer):

	def __init__(self, decs):
		self.initialize(decs)
		self.var_idx = 0
		self.var_ctxt = {}

	def get_fresh_var_name(self):
		var_name = "lvar%s" % self.var_idx
		self.var_idx += 1
		return var_name

	def transform(self):
		self.int_transform( self.decs )

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

	@visit.when( ast.RuleDec )
	def int_transform(self, ast_node):
		tr_grds = []
		for simp_head in ast_node.slhs:
			self.var_ctxt = {}			
			tr_grds += self.int_transform_fact( simp_head )
		for prop_head in ast_node.plhs:
			self.var_ctxt = {}
			tr_grds += self.int_transform_fact( prop_head )
		ast_node.grd += tr_grds

		tr_where = []
		for body in ast_node.rhs:
			tr_where += self.int_transform_fact( body, is_lhs=False )
		ast_node.where += tr_where

	@visit.on( 'fact' )
	def int_transform_fact(self, fact, is_lhs=True):
		pass

	@visit.when( ast.FactBase )
	def int_transform_fact(self, fact, is_lhs=True):
		tterms = []
		tgrds  = []		
		for term in fact.terms:
			(tterm,cons) = self.int_transform_term(term, is_lhs=is_lhs)
			tterms.append( tterm )
			tgrds += cons
		fact.terms = tterms
		return tgrds

	@visit.when( ast.FactLoc )
	def int_transform_fact(self, fact, is_lhs=True):
		(tloc,loc_grds) = self.int_transform_term( fact.loc, is_lhs=is_lhs )
		fact.loc = tloc
		f_grds = self.int_transform_fact( fact.fact, is_lhs=is_lhs )
		return loc_grds + f_grds

	@visit.when( ast.FactLocCluster )
	def int_transform_fact(self, fact, is_lhs=True):
		(tloc,loc_grds) = self.int_transform_term( fact.loc, is_lhs=is_lhs )
		fact.loc = tloc
		f_grds = []
		for f in fact.facts:
			f_grds += self.int_transform_fact( f, is_lhs=is_lhs )
		return loc_grds + f_grds

	@visit.when( ast.FactCompre )
	def int_transform_fact(self, fact, is_lhs=True):
		f_grds = []
		for f in fact.facts:
			f_grds += self.int_transform_fact( f, is_lhs=is_lhs )
		fact.guards += f_grds
		return []

	def mk_eq_cons(self, term, is_lhs=True):
		other = ast.TermVar( self.get_fresh_var_name() )
		other.type = term.type
		if is_lhs:
			# print "Linearized: %s == %s" % (other, term)
			return (other, [ast.TermBinOp(other,ast.EQ,term)])
		else:
			# print "Linearized: %s := %s" % (other, term)
			return (other, [ast.AssignDec(other, term)])

	@visit.on( 'term' )
	def int_transform_term(self, term, is_lhs=True):
		pass

	@visit.when( ast.TermVar )
	def int_transform_term(self, term, is_lhs=True):
		'''
		if term.name in self.var_ctxt:
			return self.mk_eq_cons(term)
		else:
			self.var_ctxt[term.name] = ()
			return (term,[])
		'''
		return (term, [])

	@visit.when( ast.TermApp )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermLit )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermCompre )
	def int_transform_term(self, term, is_lhs=True):
		if is_lhs:
			return self.mk_eq_cons(term, is_lhs=is_lhs)
		else:
			cp_wheres = []
			for comp_range in term.comp_ranges:
				other,where = self.int_transform_term( comp_range.term_range, is_lhs=False )
				comp_range.term_range = other
				cp_wheres += where
			tterm,cm_wheres = self.mk_eq_cons(term, is_lhs=False)
			return (tterm, cp_wheres + cm_wheres)

	@visit.when( ast.TermTuple )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermMSet )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermEnumMSet )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermList )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermListCons )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermBinOp )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermUnaryOp )
	def int_transform_term(self, term, is_lhs=True):
		return self.mk_eq_cons(term, is_lhs=is_lhs)

	@visit.when( ast.TermUnderscore )
	def int_transform_term(self, term, is_lhs=True):
		return (term,[])

