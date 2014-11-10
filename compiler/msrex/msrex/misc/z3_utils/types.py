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

# MSRE type representation in z3

smt_type = None

TY_LOC   = 'loc'
TY_INT   = 'int'
TY_CHAR  = 'char'
TY_FLOAT = 'float'
TY_BOOL  = 'bool'
TY_STR   = 'string'
TY_DEST  = 'dest'
TY_LIST  = 'list'
TY_MSET  = 'mset'
TY_TUPLE = 'tuple'
TY_UNIT  = 'unit'
TY_ARROW = 'arrow'

def init_default_type():
	Type = z3.Datatype('Type')
	Type.declare(TY_LOC)
	Type.declare(TY_INT)
	Type.declare(TY_CHAR)
	Type.declare(TY_FLOAT)
	Type.declare(TY_BOOL)
	Type.declare(TY_STR)
	Type.declare(TY_DEST)
	Type.declare(TY_LIST, ('type',Type))
	Type.declare(TY_MSET, ('type',Type))
	Type.declare(TY_TUPLE, ('left',Type), ('right',Type))
	Type.declare(TY_UNIT)
	Type.declare(TY_ARROW, ('in',Type), ('out',Type))

	# Insert new types

	Type = Type.create()
	
	global smt_type
	smt_type = Type

init_default_type()

'''
@Infix
def or_cons(c1, c2):
	c = SMTConstraint(z3.Or(c1.cons,c2.cons))
	c.justify = c1.justify + c2.justify
	return c
'''

def tyVar(id=None):
	if id == None:
		id = get_new_var("t")
	return z3.Const(id, smt_type)

tyLoc  = smt_type.loc
tyInt  = smt_type.int
tyFloat = smt_type.float
tyBool = smt_type.bool
tyChar = smt_type.char
tyStr  = smt_type.string
tyDest = smt_type.dest

def tyList(ty_term):
	return smt_type.list(ty_term)

def tyMSet(ty_term):
	return smt_type.mset(ty_term)

def tyTuple(left, right):
	return smt_type.tuple(left, right)

tyUnit = smt_type.unit

def tyArrow(inpt, outpt):
	return smt_type.arrow(inpt, outpt)



