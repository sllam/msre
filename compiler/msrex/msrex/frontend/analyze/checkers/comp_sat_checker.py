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

import msrex.misc.smt_utils as smt
from msrex.misc.smt_solver import Solver

from msrex.frontend.analyze.inspectors import Inspector
from msrex.frontend.analyze.checkers.base_checker import Checker


class CompSatChecker(Checker):

	def __init__(self, decs, source_text, builtin_preds=[]):
		self.inspect = Inspector()
		self.initialize(decs, source_text, builtin_preds=builtin_preds)

	# Main checking routine does nothing for now
	def check(self):
		pass

	# Assumes that guards is a list of terms of the type bool
	def guards_sat(self, guards):
		pass

	# Guard Translation: Translates a list of guards into a list of SMT constraints
	
	@visit.on( 'guard' )
	def guardTrans(self, guard):
		pass

	@visit.when( list )
	def guardTrans(self, guard):
		css = []
		for grd in guard:
			cs   = self.guardTrans(grd)
			css += cs
		return css 

	@visit.when( ast.TermBinOp )
	def guardTrans(self, guard):
		t1 = guard.term1
		t2 = guard.term2
		if guard.op == ast.EQ:
			op_cons = t1 |smt.Eq| t2 |smt.just| [guard]
		elif guard.op == ast.NEQ:
			op_cons = t1 |smt.Neq| t2 |smt.just| [guard]
		elif guard.op == ast.GT:
			op_cons = t1 |smt.Gt| t2 |smt.just| [guard]
		elif guard.op == ast.LT:
			op_cons = t1 |smt.Lt| t2 |smt.just| [guard]
		elif guard.op == ast.GEQ:
			op_cons = t1 |smt.Geq| t2 |smt.just| [guard]
		elif guard.op == ast.LEQ:
			op_cons = t1 |smt.Leq| t2 |smt.just| [guard]
		elif guard.op == ast.IN:
			op_cons = t1 |smt.In| t2 |smt.just| [guard]
		return op_cons

	@visit.when( ast.TermUnaryOp )
	def guardTrans(self, guard):
		c = self.guardTrans(guard.term)
		return smt.Not(c)

	# Term Translation

	@visit.on( 'term' )
	def termTrans(self, term):
		pass

	@visit.when( ast.TermVar )
	def termTrans(self, term):
		if term.name in self.ctxt:
			return (self.ctxt[term.name],[], )

