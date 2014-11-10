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
import msrex.misc.terminal_color as terminal

'''
from msrex.misc.z3_utils.base import Z3Solver
from msrex.misc.z3_utils.types import tyVar, tyLoc, tyInt, tyBool, tyFloat, tyChar, tyStr, tyDest, tyList, tyMSet, tyTuple, tyUnit, tyArrow
from msrex.misc.z3_utils.coerce import type_to_data_sort
'''
from msrex.misc.smt_utils import Eq, Or, just, min_unsat_subset
from msrex.frontend.analyze.smt_solver import Solver, tyVar, tyLoc, tyInt, tyBool, tyFloat, tyChar, tyStr, tyDest, tyList, tyMSet, tyTuple, tyUnit, tyArrow, type_to_data_sort, coerce_type

from msrex.frontend.analyze.inspectors import Inspector
from msrex.frontend.analyze.checkers.base_checker import Checker

from msrex.misc.aggregators import foldl

'''
BASE_TYPES = ["loc","int","float","char","string","dest"]

BOOL_OPS_1 = ["==","!=",">","<",">=","<="]
BOOL_OPS_2 = ["in","notin"]
NUM_OPS  = ["+","-","*","/"]
'''
BASE_TYPES = ast.BASE_TYPES

BOOL_OPS_1 = ast.BOOL_OPS_1
BOOL_OPS_2 = ast.BOOL_OPS_2
BOOL_OPS_3 = ast.BOOL_OPS_3
NUM_OPS    = ast.NUM_OPS

def smt_base_type(name):
	if name == "loc":
		return tyLoc
	elif name == "int":
		return tyInt
	elif name == "float":
		return tyFloat
	elif name == "char":
		return tyChar
	elif name == "string":
		return tyStr
	elif name == "bool":
		return tyBool
	else:
		return tyDest

def new_ctxt():
	return { 'vars':{}, 'cons':{}, 'pred':{}, 'rule':{}, 'type_vars':{}, 'ensem':{} }

def copy_ctxt(ctxt):
	n_ctxt = new_ctxt()
	for kind in ctxt:
		n_ctxt[kind] = {}
		for (name,entry) in ctxt[kind].items():
			n_ctxt[kind][name] = entry
	return n_ctxt

class TypeChecker(Checker):

	def __init__(self, decs, source_text):
		self.inspect = Inspector()
		self.initialize(decs, source_text)	
		self.solver = Solver()
		self.infer_goals = {}

	def check(self):
		ctxt = new_ctxt()
		for ensem_dec in self.inspect.filter_decs(self.decs, ensem=True):
			self.int_check_dec(ensem_dec, ctxt)
		for exec_dec in self.inspect.filter_decs(self.decs, execute=True):
			self.int_check_dec(exec_dec, ctxt)

	# Check Declarations

	@visit.on( 'ast_node' )
	def int_check_dec(self, ast_node, ctxt):
		pass

	@visit.when( ast.EnsemDec )
	def int_check_dec(self, ast_node, ctxt):
		inspect = self.inspect
		s0 = True
		extern_cons = []
		for extern_dec in inspect.filter_decs(ast_node.decs, extern=True):
			(s,cons) = self.int_check_dec(extern_dec, ctxt)
			s0 = s0 and s
			extern_cons += cons
		fact_dec_cons = []
		for fact_dec in inspect.filter_decs(ast_node.decs, fact=True):
			(s,cons) = self.int_check_dec(fact_dec, ctxt)
			s0 = s0 and s
			fact_dec_cons += cons
		rule_dec_cons = []
		this_s = True
		for rule_dec in inspect.filter_decs(ast_node.decs, rule=True):
			(s,cons) = self.int_check_dec(rule_dec, ctxt)
			s0 = s0 and s
			if self.check_type_sat( cons + extern_cons + fact_dec_cons ):	
				rule_dec_cons += cons
			else:
				this_s = False
		ctxt['ensem'][ast_node.name] = { 'succ':s0 and this_s, 'cons':extern_cons + fact_dec_cons }
		return (s0 and this_s, extern_cons + fact_dec_cons + rule_dec_cons)

	@visit.when( ast.ExternDec )
	def int_check_dec(self, ast_node, ctxt):
		s0 = True
		type_sig_cons = []		
		for ty_sig in ast_node.type_sigs:
			(s,t,cs) = self.int_check_type(ty_sig.type_sig, ctxt)
			s0 = s0 and s
			t0 = tyVar()
			type_sig_cons += [t0 |Eq| t |just| [ty_sig]] + cs
			ctxt['cons'][ty_sig.name] = t0
		return (s0, type_sig_cons)

	@visit.when( ast.FactDec )
	def int_check_dec(self, ast_node, ctxt):
		local_ctxt  = copy_ctxt(ctxt)
		tvar1 = tyVar()
		ctxt['pred'][ast_node.name] = tvar1
		if ast_node.type == None:
			return (True,[tvar1 |Eq| tyUnit |just| [ast_node]])
		else:
			(s,tvar2,cons) = self.int_check_type(ast_node.type, local_ctxt)
			return (s,[tvar1 |Eq| tvar2 |just| [ast_node]] + cons)

	@visit.when( ast.RuleDec )
	def int_check_dec(self, ast_node, ctxt):
		local_ctxt = copy_ctxt(ctxt)
		head_cons = []
		s0 = True
		for lhs in ast_node.slhs + ast_node.plhs:
			(s,cons) = self.int_check_fact(lhs, local_ctxt)
			s0 = s0 and s
			head_cons += cons
		guard_cons = []
		for guard in ast_node.grd:
			(s,tg,cons) = self.int_check_term(guard, local_ctxt)
			s0 = s0 and s
			guard_cons += [tg |Eq| tyBool |just| [ast_node]] + cons
		exist_cons = []
		for exist in ast_node.exists:
			(s,te,cons) = self.int_check_term(exist, local_ctxt)
			s0 = s0 and s
			exist_cons += [(te |Eq| tyLoc |just| [exist])|Or|(te |Eq| tyDest |just| [exist])] + cons 
		where_cons = []
		for wh in ast_node.where:
			(s,cons) = self.int_check_dec(wh, local_ctxt)
			s0 = s0 and s
			where_cons += cons
		body_cons = []
		for rhs in ast_node.rhs:
			(s,cons) = self.int_check_fact(rhs, local_ctxt)
			s0 = s0 and s
			body_cons += cons
		return (s0, head_cons + guard_cons + exist_cons + where_cons + body_cons)

	@visit.when( ast.ExecDec )
	def int_check_dec(self, ast_node, ctxt):
		local_ctxt = copy_ctxt( ctxt )
		ensem_ty_data = ctxt['ensem'][ast_node.name]
		s0 = True
		exec_cons = []
		for dec in ast_node.decs:
			(s,cons) = self.int_check_dec(dec, local_ctxt)
			s0 = s0 and s
			exec_cons += cons
		if not self.check_type_sat( ensem_ty_data['cons'] + exec_cons ):
			s0 = False
		return (s0, ensem_ty_data['cons'] + exec_cons)

	@visit.when( ast.ExistDec )
	def int_check_dec(self, ast_node, ctxt):
		s0   = True
		cons = []		
		for exist in ast_node.exist_vars:
			(s,t,cs) = self.int_check_term(exist, ctxt)
			s0 = s0 and s
			cons += [(t |Eq| tyLoc |just| [exist])|Or|(t |Eq| tyDest |just| [exist])] + cs
		return (s0, cons)

	@visit.when( ast.AssignDec )
	def int_check_dec(self, ast_node, ctxt):
		(s0,t0,cs0) = self.int_check_term(ast_node.term_pat, ctxt)
		(s1,t1,cs1) = self.int_check_term(ast_node.builtin_exp, ctxt)
		return (s0 and s1,[t0 |Eq| t1 |just| [ast_node]] + cs0 + cs1)

	@visit.when( ast.LocFactDec )
	def int_check_dec(self, ast_node, ctxt):
		s0   = True
		cons = []		
		for loc_fact in ast_node.loc_facts:
			(s,cs) = self.int_check_fact(loc_fact, ctxt)
			s0 = s0 and s
			cons += cs
		return (s0, cons)

	# Check Facts

	@visit.on( 'ast_node' )
	def int_check_fact(self, ast_node, ctxt):
		pass


	@visit.when( ast.FactBase )
	def int_check_fact(self, ast_node, ctxt):
		t0 = ctxt['pred'][ast_node.name]
		(s1,ts,term_cons) = self.int_check_term(ast_node.terms, ctxt)
		if len(ts) == 1:
			return (s1, [t0 |Eq| ts[0] |just| [ast_node]] + term_cons)
		else:
			curr = len(ts)-1
			t1 = tyUnit
			while curr >= 0:
				t1 = tyTuple(ts[curr],t1)
				curr -= 1
			return (s1, [t0 |Eq| t1 |just| [ast_node]] + term_cons)

	@visit.when( ast.FactLoc )
	def int_check_fact(self, ast_node, ctxt):
		(s0, tl, loc_cons) = self.int_check_term(ast_node.loc, ctxt)
		(s1, fact_cons)    = self.int_check_fact(ast_node.fact, ctxt)
		return (s0 and s1, [tl |Eq| tyLoc |just| [ast_node]] + loc_cons + fact_cons)

	@visit.when( ast.FactLocCluster )
	def int_check_fact(self, ast_node, ctxt):
		(s0, tl, loc_cons) = self.int_check_term(ast_node.loc, ctxt)
		fact_cons = []
		for fact in ast_node.facts:
			(s1, c) = self.int_check_fact(fact, ctxt)
			s0 = s0 and s1
			fact_cons += c
		return (s0, [tl |Eq| tyLoc |just| [ast_node]] + loc_cons + fact_cons)
		
	@visit.when( ast.FactCompre )
	def int_check_fact(self, ast_node, ctxt):
		local_ctxt = copy_ctxt( ctxt )
		s0 = True
		all_cons = []
		for comp_range in ast_node.comp_ranges:
			(s,cs) = self.int_check_comp_range( comp_range, ctxt, local_ctxt )
			s0 = s0 and s
			all_cons += cs
		for fact in ast_node.facts:
			(s,cs) = self.int_check_fact( fact, local_ctxt )
			s0 = s0 and s
			all_cons += cs
		for guard in ast_node.guards:
			(s,tg,cs) = self.int_check_term( guard, local_ctxt )
			s0 = s0 and s
			all_cons += [tg |Eq| tyBool |just| [ast_node]] + cs		
		return (s0, all_cons)

	def int_check_comp_range(self, comp_range, ctxt, local_ctxt):
		(s0,t0,cs0) = self.int_check_term(comp_range.term_vars, local_ctxt)
		(s1,t1,cs1) = self.int_check_term(comp_range.term_range, ctxt)
		return (s0 and s1, [(t1 |Eq| tyMSet(t0) |just| [comp_range])|Or|(t1 |Eq| tyList(t0) |just| [comp_range])] + cs0 + cs1)

	# Check Terms

	@visit.on( 'ast_node' )
	def int_check_term(self, ast_node, ctxt):
		pass

	@visit.when( list )
	def int_check_term(self, ast_node, ctxt):
		ts = []
		cons = []
		s0 = True
		for node in ast_node:
			(s,t,c) = self.int_check_term(node, ctxt)
			s0 = s0 and s
			ts   += [t]
			cons += c
		return (s0,ts,cons)

	@visit.when( ast.TermVar )
	def int_check_term(self, ast_node, ctxt):
		tvar1 = tyVar()
		if ast_node.name in ctxt['vars']:
			tvar2 = ctxt['vars'][ast_node.name]
		else:
			tvar2 = tyVar()
			ctxt['vars'][ast_node.name] = tvar2
		self.mark_for_infer(ast_node, tvar1)
		return (True, tvar1, [tvar1 |Eq| tvar2 |just| [ast_node]])
		
	@visit.when( ast.TermCons )
	def int_check_term(self, ast_node, ctxt):
		tvar1 = tyVar()
		tvar2 = ctxt['cons'][ast_node.name] 
		self.mark_for_infer(ast_node, tvar1)
		return (True, tvar1, [tvar1 |Eq| tvar2 |just| [ast_node]])

	@visit.when( ast.TermLit )
	def int_check_term(self, ast_node, ctxt):
		tvar1 = tyVar()
		(s,tvar2,cons) = self.int_check_type( ast_node.type, ctxt)
		# print map(lambda c: str(c),cons)
		self.mark_for_infer(ast_node, tvar1)
		return (s,tvar1,[tvar1 |Eq| tvar2 |just| [ast_node]] + cons)

	@visit.when( ast.TermApp )
	def int_check_term(self, ast_node, ctxt):
		(s0,t0,cs0) = self.int_check_term(ast_node.term1, ctxt)
		(s1,t1,cs1) = self.int_check_term(ast_node.term2, ctxt)
		t2  = tyVar()
		t3  = tyVar()
		cs2 = [t0 |Eq| tyArrow(t2,t3) |just| [ast_node], t1 |Eq| t2 |just| [ast_node]]
		self.mark_for_infer(ast_node, t3)
		return (s0 and s1, t3, cs2 + cs0 + cs1)

	@visit.when( ast.TermTuple )
	def int_check_term(self, ast_node, ctxt):
		(s0, ts, cs0) = self.int_check_term(ast_node.terms, ctxt)
		curr = len(ts) - 1
		t1   = tyUnit
		while curr >= 0:
			t1 = tyTuple(ts[curr],t1)
			curr -= 1
		t0 = tyVar()
		self.mark_for_infer(ast_node, t0)
		return (s0, t0, [t0 |Eq| t1 |just| [ast_node]] + cs0)

	@visit.when( ast.TermList )
	def int_check_term(self, ast_node, ctxt):
		(s0, ts, cs0) = self.int_check_term(ast_node.terms, ctxt)
		cs1 = []
		t1  = tyVar()
		for t0 in ts:
			cs1.append(t1 |Eq| tyList(t0) |just| [ast_node])
		self.mark_for_infer(ast_node, t1)
		return (s0, t1, cs1 + cs0)

	@visit.when( ast.TermListCons )
	def int_check_term(self, ast_node, ctxt):
		(s0,t0,cs0) = self.int_check_term(ast_node.term1, ctxt)
		(s1,t1,cs1) = self.int_check_term(ast_node.term2, ctxt)
		t2  = tyVar()
		cs2 = [t1 |Eq| tyList(t0) |just| [ast_node], t2 |Eq| t1]
		self.mark_for_infer(ast_node, t2)
		return (s0 and s1, t2, cs2 + cs0 + cs1)

	@visit.when( ast.TermMSet )
	def int_check_term(self, ast_node, ctxt):
		(s0, ts, cs0) = self.int_check_term(ast_node.terms, ctxt)
		cs1 = []
		t1  = tyVar()
		for t0 in ts:
			cs1.append(t1 |Eq| tyMSet(t0) |just| [ast_node])
		self.mark_for_infer(ast_node, t1)
		return (s0, t1, cs1 + cs0)

	@visit.when( ast.TermEnumMSet )
	def int_check_term(self, ast_node, ctxt):
		(s0, t0, cs0) = self.int_check_term(ast_node.texp1, ctxt)
		(s1, t1, cs1) = self.int_check_term(ast_node.texp2, ctxt)
		t2  = tyVar()
		cs2 = [t2 |Eq| tyMSet(t0) |just| [ast_node], t2 |Eq| tyMSet(t1) |just| [ast_node]]
		self.mark_for_infer(ast_node, t2)
		return (s0 and s1, t2, cs0 + cs1 + cs2)

	@visit.when( ast.TermCompre )
	def int_check_term(self, ast_node, ctxt):
		local_ctxt = copy_ctxt( ctxt )
		s0 = True
		all_cons = []
		for comp_range in ast_node.comp_ranges:
			(s,cs) = self.int_check_comp_range( comp_range, ctxt, local_ctxt )
			s0 = s0 and s
			all_cons += cs
		(s,t0,cs) = self.int_check_term(ast_node.term, local_ctxt)
		t1 = tyVar()
		s0 = s0 and s
		all_cons += [t1 |Eq| tyMSet(t0) |just| [ast_node]] + cs
		for guard in ast_node.guards:
			(s,tg,cs) = self.int_check_term( guard, local_ctxt )
			s0 = s0 and s
			all_cons += [tg |Eq| tyBool |just| [ast_node]] + cs		
		self.mark_for_infer(ast_node, t1)
		return (s0, t1, all_cons)

	@visit.when( ast.TermBinOp )
	def int_check_term(self, ast_node, ctxt):
		(s0,t0,cs0) = self.int_check_term(ast_node.term1, ctxt)
		(s1,t1,cs1) = self.int_check_term(ast_node.term2, ctxt)
		t3 = tyVar()
		if ast_node.op in BOOL_OPS_1:
			cs3 = [t0 |Eq| t1 |just| [ast_node], t3 |Eq| tyBool |just| [ast_node]]
		elif ast_node.op in BOOL_OPS_2:
			cs3 = [tyMSet(t0) |Eq| t1 |just| [ast_node], t3 |Eq| tyBool |just| [ast_node]]
		elif ast_node.op in NUM_OPS:
			cs3 = [t0 |Eq| t1 |just| [ast_node], t0 |Eq| t3 |just| [ast_node]]
		self.mark_for_infer(ast_node, t3)
		return (s0 and s1, t3, cs3 + cs0 + cs1)

	@visit.when( ast.TermUnaryOp )
	def int_check_term(self, ast_node, ctxt):
		(s0,t0,cs0) = self.int_check_term(ast_node.term, ctxt)
		t1 = tyVar()
		self.mark_for_infer(ast_node, t1)
		return (s0, t1, [t1 |Eq| tyBool |just| [ast_node], t0 |Eq| tyBool |just| [ast_node]] + cs0)

	@visit.when( ast.TermUnderscore )
	def int_check_term(self, ast_node, ctxt):
		t = tyVar()
		self.mark_for_infer(ast_node, t)
		return (True, t, [])

	# Check Types

	@visit.on( 'ast_node' )
	def int_check_type(self, ast_node, ctxt):
		pass

	@visit.when( ast.TypeVar )
	def int_check_type(self, ast_node, ctxt):
		tvar1 = tyVar()
		if ast_node.name in ctxt['type_vars']:
			tvar2 = ctxt['type_vars'][ast_node.name]
		else:
			tvar2 = tyVar()
			ctxt['type_vars'][ast_node.name] = tvar2
		return (True, tvar1, [tvar1 |Eq| tvar2 |just| [ast_node]])

	@visit.when(ast.TypeCons)
	def int_check_type(self, ast_node, ctxt):
		tvar = tyVar()
		if ast_node.name not in BASE_TYPES:
			error_idx = self.declare_error("Unknown data type \'%s\'" % ast_node.name)
			self.extend_error(error_idx,ast_node)
			return (False,tvar,[])
		else:
			return (True,tvar,[tvar |Eq| smt_base_type(ast_node.name) |just| [ast_node]])

	@visit.when(ast.TypeApp)
	def int_check_type(self, ast_node, ctxt):
		(s1,t1,cons1) = self.int_check_type(ast_node.type1, ctxt)
		(s2,t2,cons2) = self.int_check_type(ast_node.type2, ctxt)
		t3 = tyVar()
		t4 = tyVar()
		return (s1 and s2, t4, [t1 |Eq| tyArrow(t3,t4) |just| [ast_node], t2 |eq| t3 |just| [ast_node]] + cons1 + cons2)

	@visit.when(ast.TypeArrow)
	def int_check_type(self, ast_node, ctxt):
		(s1,t1,cons1) = self.int_check_type(ast_node.type1, ctxt)
		(s2,t2,cons2) = self.int_check_type(ast_node.type2, ctxt)
		t3 = tyVar()
		return (s1 and s2,t3,[t3 |Eq| tyArrow(t1,t2) |just| [ast_node]] + cons1 + cons2)

	@visit.when(ast.TypeTuple)
	def int_check_type(self, ast_node, ctxt):
		types = ast_node.types
		curr  = len(types)-1
		all_cons = []
		t1 = tyUnit
		s0 = True
		while curr >= 0:
			(s,t2,cons) = self.int_check_type(types[curr], ctxt)
			s0 = s0 and s
			all_cons += cons
			t1 = tyTuple(t2,t1)
			curr -= 1
		t0 = tyVar()
		return (s0,t0,[t0 |Eq| t1 |just| [ast_node]] + all_cons)

	@visit.when(ast.TypeMSet)
	def int_check_type(self, ast_node, ctxt):
		(s,t1,cons) = self.int_check_type(ast_node.type, ctxt)
		t0 = tyVar()
		return (s,t0,[t0 |Eq| tyMSet(t1) |just| [ast_node]] + cons)

	@visit.when(ast.TypeList)
	def int_check_type(self, ast_node, ctxt):
		(s,t1,cons) = self.int_check_type(ast_node.type, ctxt)
		t0 = tyVar()
		return (s,t0,[t0 |Eq| tyList(t1) |just| [ast_node]] + cons)

	# Check Type constraint satisfiability
	
	def check_type_sat(self, cons):
		# print (map(lambda c: str(c),cons))
		mus = min_unsat_subset(self.solver, cons)
		if len(mus) == 0:
			model = self.solver.solve(cons)
			for d in model:
				key = str(d)
				if key in self.infer_goals:
					smt_type = model[d]
					self.infer_goals[key].smt_type = smt_type
					self.infer_goals[key].type = coerce_type( smt_type )
					# print "%s -> %s::%s" % (self.infer_goals[key], type_to_data_sort( model[d] ), self.infer_goals[key].type )
					del self.infer_goals[key]
			return True
		else:
			error_idx = self.declare_error("Type Error in the following sites")
			for error_site in foldl( map(lambda c: c.get_just(),mus), []):
				self.extend_error(error_idx, error_site)
			return False

	# Type inference operations

	def mark_for_infer(self, ast_node, ty_var):
		self.infer_goals[str(ty_var)] = ast_node


