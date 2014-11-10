
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

from msrex.misc.infix import Infix

from msrex.misc.smt_utils import SMTSolver, SMTConstraint, SAT, UNSAT, UNKNOWN, SMTTypeTerm, get_new_var

# MSRE Data representation in z3

smt_data  = None

def init_default_data():
	Data  = z3.Datatype('Data')

	Data.declare( 'int', ('data',z3.IntSort()) )
	Data.declare( 'others', ('data',Data) )
	Data.declare( 'tuple', ('left',Data), ('right',Data) )
	Data.declare( 'mset', ('body',Data), ('elem',Data) )
	Data.declare( 'list', ('head',Data), ('tail',Data) )
	Data.declare( 'unit' )

	Data  = Data.create()
	global smt_data
	smt_data  = Data

init_default_data()

def datVar(id=None):
	if id == None:
		id = get_new_var("t")
	return z3.Const(id, smt_data)


# Logic Connectives

mem_f = z3.Function('member', smt_data, smt_data, z3.BoolSort())

@Infix
def mem(x ,xs):
	return SMTConstraint(mem_f(x,xs))

empty_f = z3.Function('empty', smt_data, z3.BoolSort())

@Infix
def empty(xs):
	return SMTConstraint(empty_f(xs))

@Infix
def implies(ps, cs):
	i = SMTConstraint(z3.Implies(ps.cons, cs.cons))
	i.justify += ps.justify + cs.justify
	return i

def And(*args):
	size = len(args)
	clause  = args[size-1].cons
	justify = args[size-1].justify
	curr = size-2
	while curr >= 0:
		clause  = z3.And(args[curr].cons,clause)
		justify += args[curr].justify
		curr -= 1
	a = SMTConstraint(clause)
	a.justify = justify
	return a

def Or(*args):
	size = len(args)
	clause  = args[size-1].cons
	justify = args[size-1].justify
	curr = size-2
	while curr >= 0:
		clause  = z3.Or(args[curr].cons,clause)
		justify += args[curr].justify
		curr -= 1
	a = SMTConstraint(clause)
	a.justify = justify
	return a

def Not(cs):
	n = SMTConstraint( z3.Not(cs.cons) )
	n.justify = cs.justify
	return n

def forall(vs, cs):
	f = SMTConstraint( z3.ForAll(vs, cs.cons) )
	f.justify = cs.justify
	return f

def exists(vs, cs):
	f = SMTConstraint( z3.Exists(vs, cs.cons) )
	f.justify = cs.justify
	return f

