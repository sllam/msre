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

from msrex.misc.infix import Infix

SMTCONS_COUNT = 0

class SMTConstraint:

	'''
	def __init__(self, cons, justify=[]):
		self.cons = cons
		self.justify = justify
		global SMTCONS_COUNT
		self.id = SMTCONS_COUNT
		SMTCONS_COUNT += 1
	'''

	def initialize(self, my_token):
		self.token = my_token
		global SMTCONS_COUNT
		self.id = SMTCONS_COUNT
		SMTCONS_COUNT += 1
		self.justify = []

	def get_just(self):
		return self.justify

	def __eq__(self, other):
		return self.id == other.id

EQ_CONS  = 1
NEQ_CONS = 2
LEQ_CONS = 3
GEQ_CONS = 4
LT_CONS  = 5
GT_CONS  = 6
IN_CONS  = 14

OR_CONS  = 7
AND_CONS = 8
NOT_CONS = 9
EXISTS_CONS = 10
FORALL_CONS = 11
IFF_CONS = 12
IMP_CONS = 13

class EqCons(SMTConstraint):
	def __init__(self, t1, t2, is_set=False):
		self.initialize(EQ_CONS)
		self.t1 = t1
		self.t2 = t2
		self.is_set = is_set
	def __repr__(self):
		return "%s == %s" % (self.t1,self.t2)
@Infix
def Eq(x1, x2):
	return EqCons(x1, x2)
@Infix
def MEq(x1, x2):
	return EqCons(x1, x2, is_set=True)

class NeqCons(SMTConstraint):
	def __init__(self, t1, t2, is_set=False):
		self.initialize(NEQ_CONS)
		self.t1 = t1
		self.t2 = t2
		self.is_set = is_set
	def __repr__(self):
		return "%s != %s" % (self.t1,self.t2)
@Infix
def Neq(x1, x2):
	return NeqCons(x1, x2)
@Infix
def MNeq(x1, x2):
	return NeqCons(x1, x2, is_set=True)

class LeqCons(SMTConstraint):
	def __init__(self, t1, t2, is_set=False):
		self.initialize(LEQ_CONS)
		self.t1 = t1
		self.t2 = t2
		self.is_set = is_set
	def __repr__(self):
		return "%s <= %s" % (self.t1,self.t2)
@Infix
def Leq(x1, x2):
	return LeqCons(x1, x2)
@Infix
def Subseteq(x1, x2):
	return LeqCons(x1, x2, is_set=True)

class GeqCons(SMTConstraint):
	def __init__(self, t1, t2, is_set=False):
		self.initialize(GEQ_CONS)
		self.t1 = t1
		self.t2 = t2
		self.is_set = is_set
	def __repr__(self):
		return "%s >= %s" % (self.t1,self.t2)
@Infix
def Geq(x1, x2):
	return GeqCons(x1,x2)
@Infix
def Supseteq(x1, x2):
	return GeqCons(x1, x2, is_set=True)

class LtCons(SMTConstraint):
	def __init__(self, t1, t2):
		self.initialize(LT_CONS)
		self.t1 = t1
		self.t2 = t2
	def __repr__(self):
		return "%s < %s" % (self.t1,self.t2)
@Infix
def Lt(x1, x2):
	return LtCons(x1,x2)

class GtCons(SMTConstraint):
	def __init__(self, t1, t2):
		self.initialize(LT_CONS)
		self.t1 = t1
		self.t2 = t2
	def __repr__(self):
		return "%s > %s" % (self.t1,self.t2)
@Infix
def Gt(x1, x2):
	return GtCons(x1,x2)

class InCons(SMTConstraint):
	def __init__(self, t1, t2):
		self.initialize(IN_CONS)
		self.t1 = t1
		self.t2 = t2
	def __repr__(self):
		return "%s in %s" % (self.t1,self.t2)
@Infix
def In(x1, x2):
	return InCons(x1, x2)

class OrCons(SMTConstraint):
	def __init__(self, c1, c2):
		self.initialize(OR_CONS)
		self.c1 = c1
		self.c2 = c2
	def get_just(self):
		return self.c1.get_just() + self.c2.get_just() + self.justify
	def __repr__(self):
		return "%s \/ %s" % (self.c1,self.c2)		
@Infix
def Or(c1, c2):
	return OrCons(c1, c2)
def Ors(*args):
	cs = args[0]
	index = 1
	while index < len(cs):
		cs = OrCons(cs, args[index])
		index += 1
	return cs

class AndCons(SMTConstraint):
	def __init__(self, c1, c2):
		self.initialize(AND_CONS)
		self.c1 = c1
		self.c2 = c2
	def get_just(self):
		return self.c1.get_just() + self.c2.get_just() + self.justify
	def __repr__(self):
		return "%s /\ %s" % (self.c1,self.c2)		
@Infix
def And(c1, c2):
	return AndCons(c1, c2)
def Ands(*args):
	cs = args[0]
	index = 1
	while index < len(cs):
		cs = AndCons(cs, args[index])
		index += 1
	return cs


class NotCons(SMTConstraint):
	def __init__(self, c):
		self.initialize(NOT_CONS)
		self.c = c
	def get_just(self):
		return self.c.get_just() + self.justify
	def __repr__(self):
		return "-%s" % (self.c)		
@Infix
def Not(c):
	return NotCons(c)

class ExistsCons(SMTConstraint):
	def __init__(self, xs, c):
		self.initialize(EXISTS_CONS)
		self.vars = xs
		self.c = c
	def get_just(self):
		return self.c.get_just() + self.justify
	def __repr__(self):
		return "exists %s. %s" % (','.join(map(lambda v: str(v),self.vars)),self.c)		
def Exists(xs, c):
	return ExistsCons(xs, c)

class ForallCons(SMTConstraint):
	def __init__(self, xs, c):
		self.initialize(FORALL_CONS)
		self.vars = xs
		self.c = c
	def get_just(self):
		return self.c.get_just() + self.justify
	def __repr__(self):
		return "forall %s. %s" % (','.join(map(lambda v: str(v),self.vars)),self.c)		
def Forall(xs, c):
	return ForallCons(xs, c)

class IffCons(SMTConstraint):
	def __init__(self, c1, c2):
		self.initialize(IFF_CONS)
		self.c1 = c1
		self.c2 = c2
	def get_just(self):
		return self.c1.get_just() + self.c2.get_just() + self.justify
	def __repr__(self):
		return "%s <--> %s" % (self.c1,self.c2)		
@Infix
def Iff(c1, c2):
	return IffCons(c1, c2)

class ImpliesCons(SMTConstraint):
	def __init__(self, c1, c2):
		self.initialize(IMP_CONS)
		self.c1 = c1
		self.c2 = c2
	def get_just(self):
		return self.c1.get_just() + self.c2.get_just() + self.justify
	def __repr__(self):
		return "%s --> %s" % (self.c1,self.c2)		
@Infix
def Implies(c1, c2):
	return ImpliesCons(c1, c2)

@Infix
def just(cons, js):
	cons.justify += js
	return cons

SAT     = 'sat'
UNSAT   = 'unsat'
UNKNOWN = 'unknown'

class SMTSolver:

	def initialize(self, axioms=[]):
		self.axioms = axioms

	def add(self, axiom):
		self.axioms.append( axiom )
		
	def internalize(self, constraint):
		return constraint

	def satisfiable(self, constraints):
		return SAT

def min_unsat_subset(smt_solver, constraints):
	d = constraints
	m = []
	if smt_solver.satisfiable(d) == SAT:
		return []
	while smt_solver.satisfiable(m) == SAT:
		c = m
		curr_e = None
		while smt_solver.satisfiable(c) == SAT:
			# print "inner"
			# print map(lambda x: str(x),m)
			dmc = diff(d, c)
			if len(dmc) > 0:
				e = dmc[0]
				c = c + [e]
				curr_e = e
			else:
				return []
		d = c
		if curr_e != None:
			if curr_e not in m:
				m += [curr_e]
		else:
			return []
	return m

# auxiliary functions

def diff(ls1, ls2):
	ls3 = []
	for l1 in ls1:
		if l1 not in ls2:
			ls3.append(l1)
	return ls3

# Type Term

SMTVAR_COUNT = 0

def get_new_var(prefix="v"):
	global SMTVAR_COUNT
	new_id = SMTVAR_COUNT
	SMTVAR_COUNT += 1
	return "%s%s" % (prefix,new_id)

class SMTTypeTerm:
	def initialize(self):
		pass
	def to_smt(self):
		pass

	

