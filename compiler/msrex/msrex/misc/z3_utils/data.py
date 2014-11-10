

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

from msrex.misc.smt_utils import SMTSolver, SMTConstraint, SAT, UNSAT, UNKNOWN

SMTVAR_COUNT = 0

def get_new_var(prefix="v"):
	global SMTVAR_COUNT
	new_id = SMTVAR_COUNT
	SMTVAR_COUNT += 1
	return "%s%s" % (prefix,new_id)

# Integers

def newInt():
	iname = get_new_var(prefix="i")
	return z3.Int(iname)

def newInts(quantity):
	inames = " ".join( map(lambda _: get_new_var(prefix="i") ,range(0,quantity)) )
	return z3.Ints(inames)

# Booleans

def newBool():
	bname = get_new_var(prefix="b")
	return z3.Bool(bname)

def newBools(quantity):
	bnames = " ".join( map(lambda _: get_new_var(prefix="b") ,range(0,quantity)) )
	return z3.Bools(bnames)

# Locations

Loc = z3.DeclareSort('Loc')

def newLoc():
	lname = get_new_var(prefix="l")
	return z3.Const(lname, Loc)

def newLocs(quantity):
	lnames = " ".join( map(lambda _: get_new_var(prefix="l") ,range(0,quantity)) )
	return z3.Consts(lnames, Loc)

# Destinations

Dest = z3.DeclareSort('Dest')

def newDest():
	dname = get_new_var(prefix="d")
	return z3.Const(dname, Dest)

def newDests(quantity):
	dnames = " ".join( map(lambda _: get_new_var(prefix="d") ,range(0,quantity)) )
	return z3.Consts(dnames, Dest)

# Char

Char = z3.DeclareSort('Char')

def newChar():
	cname = get_new_var(prefix="c")
	return z3.Const(cname, Char)

def newChars(quantity):
	cnames = " ".join( map(lambda _: get_new_var(prefix="c") ,range(0,quantity)) )
	return z3.Consts(cnames, Char)

# String

String = z3.DeclareSort('String')

def newString():
	sname = get_new_var(prefix="str")
	return z3.Const(sname, String)

def newStrings(quantity):
	snames = " ".join( map(lambda _: get_new_var(prefix="str") ,range(0,quantity)) )
	return z3.Consts(snames, String)

# Unknowns

Unknown = z3.DeclareSort('Unknown')

def newUnknown():
	uname = get_new_var(prefix="uk")
	return z3.Const(uname, Unknown)

def newUnknowns(quantity):
	unames = " ".join( map(lambda _: get_new_var(prefix="str") ,range(0,quantity)) )
	return z3.Consts(unames, Unknown)


