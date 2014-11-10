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



# Guards
# TODO: schedulable method return with output variables, only when
# all term arguments are of normal form (e.g., variable, constants, constructors). 
# For non-normal terms, we simply assume all variables are input variables. 

NON_IDX_GRD = 'non_idx'
EQ_GRD      = 'eq'
MEM_GRD     = 'mem'
ORD_GRD     = 'ord'

GUARD_INDEX = 0
def get_next_guard_index():
	global GUARD_INDEX
	new_id = GUARD_INDEX
	GUARD_INDEX += 1
	return new_id

class RuleGuard:
	def initialize(self, term, guard_type):
		self.type = guard_type
		self.term = term
		self.id   = get_next_guard_index()
		self.inspect = Inspector()
	def indexable(self):
		return False
	def scheduleAsGuard(self, var_ctxt):
		return False
	def scheduleAsIndex(self, var_ctxt):
		return None
	def extendCtxt(self, ctxt):
		pass
	def __eq__(self, other):
		return self.id == other.id
	def __repr__(self):
		return "%s" % (self.term)

class NonIndexGuard(RuleGuard):
	def __init__(self, term):
		self.initialize(term, NON_IDX_GRD)
	def indexable(self):
		return False
	def scheduleAsGuard(self, var_ctxt):
		input_vars = self.inspect.free_var_idxs(self.term)
		return input_vars <= var_ctxt
	def scheduleAsIndex(self, var_ctxt):
		return None
	def extendCtxt(self, ctxt):
		pass

class EqGuard(RuleGuard):
	def __init__(self, term):
		self.initialize(term, EQ_GRD)
		self.term1 = term.term1
		self.term2 = term.term2
	def indexable(self):
		# return self.inspect.is_normal_form(self.term1) and self.inspect.is_normal_form(self.term2)
		return self.term1.term_type == ast.TERM_VAR and self.term2.term_type == ast.TERM_VAR
	def scheduleAsGuard(self, var_ctxt):
		inspect = self.inspect
		input_vars = inspect.free_var_idxs(self.term1) | inspect.free_var_idxs(self.term2)
		return input_vars <= var_ctxt
	def scheduleAsIndex(self, var_ctxt):
		if not self.indexable():
			return None
		inspect = self.inspect
		vars1   = inspect.free_var_idxs(self.term1)
		vars2   = inspect.free_var_idxs(self.term2)
		if vars1 <= var_ctxt and (not vars2 <= var_ctxt):
			return (vars1, vars2, True)
		elif (vars2 <= var_ctxt) and (not vars1 <= var_ctxt):
			return (vars2, vars1, False)
		else:
			return None
	def extendCtxt(self, ctxt):
		if self.indexable():
			output_vars = set(map(lambda t: t.name, inspect.free_vars(self.term1) + inspect.free_vars(self.term2)))
			ctxt.addEq(output_vars)

class MemGuard(RuleGuard):
	def __init__(self, term):
		self.initialize(term, MEM_GRD)
		self.term1 = term.term1
		self.term2 = term.term2
	def indexable(self):
		return self.inspect.is_normal_form(self.term1) and self.term2.term_type in [ast.TERM_VAR,ast.TERM_MSET]
	def scheduleAsGuard(self, var_ctxt):
		input_vars = self.inspect.free_var_idxs(self.term1) | self.inspect.free_var_idxs(self.term2)
		return input_vars <= var_ctxt
	def scheduleAsIndex(self, var_ctxt):
		if self.indexable():
			vars1 = self.inspect.free_var_idxs(self.term1)
			vars2 = self.inspect.free_var_idxs(self.term2)
			output_vars = vars1 - var_ctxt
			input_vars  = vars2
			if (len(output_vars) > 0) and (input_vars <= var_ctxt):
				return (input_vars, output_vars, False) 
			else:
				return None
		else:
			return None
	def extendCtxt(self, ctxt):
		if self.indexable():
			output_vars = set( map(lambda t: t.name, self.inspect.free_vars(self.term1)) )
			ctxt.addMem(output_vars, self.term1, self.term2, self)

class OrdGuard(RuleGuard):
	def __init__(self, term):
		self.initialize(term, ORD_GRD)
		if term.op in [ast.LEQ,ast.LT]: 
			self.term1 = term.term1
			self.term2 = term.term2
		else: # term.op in [ast.GEQ,ast.GT]
			self.term1 = term.term2
			self.term2 = term.term1
		if term.op in [ast.GEQ,ast.LEQ]:
			self.include_eq = True
		else: # term.op in [ast.GT,ast.LT]
			self.include_eq = False
	def indexable(self):
		return self.term1.term_type in [ast.TERM_VAR,ast.TERM_LIT] and self.term2.term_type in [ast.TERM_VAR,ast.TERM_LIT] and (self.term1.term_type == ast.TERM_VAR or self.term2.term_type == ast.TERM_VAR)
	def scheduleAsGuard(self, var_ctxt):
		input_vars = self.inspect.free_var_idxs(self.term1) | self.inspect.free_var_idxs(self.term2)
		return input_vars <= var_ctxt
	def scheduleAsIndex(self, var_ctxt):
		if not self.indexable():
			return None
		inspect = self.inspect
		vars1 = inspect.free_var_idxs(self.term1)
		vars2 = inspect.free_var_idxs(self.term2)
		if vars1 <= var_ctxt and (not vars2 <= var_ctxt) and len(vars2) > 0:
			return (vars1, vars2, True)
		elif (vars2 <= var_ctxt) and (not vars1 <= var_ctxt) and len(vars1) > 0:
			return (vars2, vars1, False)
		else:
			return None
	
	def extendCtxt(self, ctxt):
		if self.indexable():
			if self.term1.term_type == ast.TERM_VAR:
				vars2 = set(map(lambda t: t.name, inspect.free_vars(self.term2)))
				if vars2 <= ctxt.eq_ctxt:
					ctxt.addOrd(self.term1, ORD_LEQ if self.include_eq else ORD_LT, self.term2, self)
			if self.term2.term_type == ast.TERM_VAR:
				vars1 = set(map(lambda t: t.name, inspect.free_vars(self.term1)))
				if vars1 <= ctxt.eq_ctxt:
					ctxt.addOrd(self.term2, ORD_GEQ if self.include_eq else ORD_GT, self.term1, self)

def process_guard(grd):
	if grd.term_type == ast.TERM_BINOP:
		if grd.op == ast.EQ:
			rulegrd = EqGuard( grd )
		elif grd.op == ast.IN:
			rulegrd = MemGuard( grd )
		elif grd.op in [ast.LEQ,ast.GEQ,ast.LT,ast.GT]:
			rulegrd = OrdGuard( grd )
		else:
			rulegrd = NonIndexGuard( grd )
		return rulegrd
	else:
		return NonIndexGuard( grd )

