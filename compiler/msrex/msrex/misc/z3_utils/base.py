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

import z3 as z3
import pysetcomp.setcomp_z3 as z3sc
import msrex.misc.z3_utils.types as types
import msrex.misc.z3_utils.data as data

import msrex.misc.visit as visit
# from msrex.misc.smt_utils import SMTSolver, SMTConstraint, SAT, UNSAT, UNKNOWN, SMTTypeTerm, get_new_var
import msrex.misc.smt_utils as smt

import msrex.frontend.lex_parse.ast as ast

def type_to_data_sort(ty):
	dt_name = datatype_name(ty) 
	if dt_name == types.TY_LOC:
		return data.Loc
	elif dt_name == types.TY_INT:
		return z3.IntSort()
	elif dt_name == types.TY_BOOL:
		return z3.BoolSort()
	elif dt_name == types.TY_FLOAT:
		return z3.RealSort()
	elif dt_name == types.TY_DEST:
		return data.Dest
	elif dt_name == types.TY_CHAR:
		return data.Char
	elif dt_name == types.TY_STR: 
		return data.String
	elif dt_name == types.TY_LIST:
		elem_sort = type_to_data_sort(ty.arg(0))
		return z3sc.listInfo( elem_sort )['sort']
 	elif dt_name == types.TY_TUPLE:
		sorts = []
		while dt_name != types.TY_UNIT:
			sorts.append( type_to_data_sort( ty.arg(0) ) )
			ty = ty.arg(1)
			dt_name = datatype_name(ty)
		return z3sc.tupleInfo( *sorts )['sort']
	elif dt_name == types.TY_MSET:
		elem_sort = type_to_data_sort(ty.arg(0))
		return z3sc.setInfo( elem_sort )['sort']
	elif dt_name == types.TY_ARROW:
		return None
	else:
		return data.Unknown

class TermTranslator:

	def __init__(self):
		self.ctxt = {}
		self.var_idx = 0

	def lookupVar(self, termvar):
		name = termvar.name
		if name in self.ctxt:
			return self.ctxt[name]
		else:
			data_sort = type_to_data_sort( termvar.type )
			data_var  = z3.Const(name, data_sort)
			self.ctxt[name] = data_var
			return data_var

	def mkVar(self, ty):
		name = "var_%s" % self.var_idx
		self.var_idx += 1
		data_sort = type_to_data_sort( ty )
		data_var  = z3.Const(name, data_sort)
		self.ctxt[name] = data_var
		return data_var

	def translate(self, term):
		if hasattr(term, 'term_type') or isinstance(term, list):
			return self.trans(term)
		else:
			return term

	@visit.on( 'term' )
	def trans(self, term):
		pass

	@visit.when( list )
	def trans(self, term):
		ts = []
		for t in term:
			ts.append( self.trans( term ) )
		return ts

	@visit.when( ast.TermCons )
	def trans(self, term):
		# TODO: Fix this..
		return None

	@visit.when( ast.TermVar )
	def trans(self, term):
		return self.lookupVar( term )

	@visit.when( ast.TermApp )
	def trans(self, term):
		# TODO: Currently does not support application types, we simply represent this with a fresh variable
		return self.mkVar( term.type )

	@visit.when( ast.TermList )
	def trans(self, term):
		list_sort = type_to_data_sort( term.type )
		elem_sort = z3sc.listInfoFromList( list_sort )['elem']
		targs = []
		for t in term.terms:
			targs.append( self.trans( t ) )
		return z3sc.VList(elem_sort, *targs)

	@visit.when( ast.TermTuple )
	def trans(self, term):
		tup_sort = type_to_data_sort( term.type )
		targs = []
		for t in term.terms:
			targs.append( self.trans( t ) )
		return tup_sort.tup(*targs)

	@visit.when( ast.TermBinOp )
	def trans(self, term):
		# TODO: Implement this!
		pass

	@visit.when( ast.TermUnaryOp )
	def trans(self, term):
		# TODO: Implement this!
		pass

	@visit.when( ast.TermLit )
	def trans(self, term):
		sort = type_to_data_sort( term.type )
		if isinstance(sort, z3.ArithSortRef):
			if sort.is_real():
				return z3.RealVal(term.literal)
			else:
				return z3.IntVal(term.literal)
		elif isinstance(sort, z3.BoolSortRef):
			return z3.BoolVal(term.literal)
		else:
			# TODO: Unsupported literal terms, just create fresh variable
			return self.mkVar(term.type)

	@visit.when( ast.TermUnderscore )
	def trans(self, term):
		return self.mkVar(term.type)

	@visit.when( ast.TermMSet )
	def trans(self, term):
		mset_sort = type_to_data_sort( term.type )
		elem_sort = z3sc.setInfoFromSet( set_sort )['elem']
		targs = []
		for t in term.terms:
			targs.append( self.trans( t ) )
		return z3sc.VSet(elem_sort, *targs)

	@visit.when( ast.TermCompre )
	def trans(self, term):
		pass

class Z3Solver(smt.SMTSolver):

	def __init__(self, axioms=[]):
		self.initialize(axioms=axioms)

	def internalize(self, constraint):
		ctok = constraint.token
		if ctok == smt.EQ_CONS:
			if constraint.is_set:
				return constraint.t1 |z3sc.Eq| constraint.t2
			else:
				return constraint.t1 == constraint.t2
		elif ctok == smt.NEQ_CONS:			
			if constraint.is_set:
				return z3sc.Not( constraint.t1 |z3sc.Eq| constraint.t2 )
			else:
				return z3sc.Not( constraint.t1 == constraint.t2 )
		elif ctok == smt.LEQ_CONS:
			if constraint.is_set:
				return constraint.t1 |z3sc.subseteq| constraint.t2
			else:
				return constraint.t1 <= constraint.t2
		elif ctok == smt.GEQ_CONS:
			if constraint.is_set:
				return constraint.t2 |z3sc.subseteq| constraint.t1
			else:
				return constraint.t1 >= constraint.t2
		elif ctok == smt.LT_CONS:
			return constraint.t1 < constraint.t2
		elif ctok == smt.GT_CONS:
			return constraint.t1 > constraint.t2
		elif ctok == smt.OR_CONS:
			ic1 = self.internalize(constraint.c1)
			ic2 = self.internalize(constraint.c2)
			return ic1 |z3sc.Or| ic2
		elif ctok == smt.AND_CONS:
			ic1 = self.internalize(constraint.c1)
			ic2 = self.internalize(constraint.c2)
			return ic1 |z3sc.And| ic2
		elif ctok == smt.IFF_CONS:
			ic1 = self.internalize(constraint.c1)
			ic2 = self.internalize(constraint.c2)
			return ic1 |z3sc.iff| ic2
		elif ctok == smt.IMP_CONS:
			ic1 = self.internalize(constraint.c1)
			ic2 = self.internalize(constraint.c2)
			return ic1 |z3sc.implies| ic2
		elif ctok == smt.EXISTS_CONS:
			ic = self.internalize(constraint.c)
			return z3sc.Exists(constraint.vars, ic)
		elif ctok == smt.FORALL_CONS:
			ic = self.internalize(constraint.c)
			return z3sc.Forall(constraint.vars, ic)
		
	def satisfiable(self, constraints):
		s = z3.Solver()
		trans_pref = { 'use_set_eq':False }
		# print self.axioms + constraints
		for cons in map(lambda c: self.internalize(c), self.axioms + constraints):
			(tform, tcons, sig) = z3sc.transForm(cons, trans_pref)
			z3constr = [tform] + tcons
			s.add(*z3constr)
		res = s.check()
		if res == z3.sat:
			return smt.SAT
		elif res == z3.unsat:
			return smt.UNSAT
		else:
			return smt.UNKNOWN

	def solve(self, constraints):
		s = z3.Solver()
		trans_pref = { 'use_set_eq':False }
		for cons in map(lambda c: self.internalize(c), self.axioms + constraints):
			(tform, tcons, sig) = z3sc.transForm(cons, trans_pref)
			z3constr = [tform] + tcons
			s.add(*z3constr)
		res = s.check()
		if res == z3.sat:
			m = s.model()
			# print m
			return m
		else:
			return None

def datatype_name(d):
	return d.decl().name()


