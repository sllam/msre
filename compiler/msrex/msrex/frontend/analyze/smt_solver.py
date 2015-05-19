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

USE_Z3 = True

if USE_Z3:
	import z3
	import msrex.misc.z3_utils.base as base
	import msrex.misc.z3_utils.types as types
	'''
	from msrex.misc.z3_utils.types import tyVar, tyLoc, tyInt, tyBool, tyFloat, tyChar, tyStr, tyDest, tyList, tyMSet, tyTuple, tyUnit, tyArrow
	from msrex.misc.z3_utils.coerce import type_to_data_sort
	'''
	Solver = base.Z3Solver
	tyVar  = types.tyVar
	tyLoc  = types.tyLoc
	tyInt  = types.tyInt
	tyBool = types.tyBool
	tyFloat = types.tyFloat
	tyChar = types.tyChar
	tyStr  = types.tyStr
	tyDest = types.tyDest
	tyList = types.tyList
	tyMSet = types.tyMSet
	tyTuple = types.tyTuple
	tyUnit  = types.tyUnit
	tyArrow = types.tyArrow

	tyTime = types.tyTime

	type_to_data_sort = base.type_to_data_sort

	# Convert a z3 SMT type to MSRE ast type
	def coerce_type(smt_type):
		dt_name = base.datatype_name(smt_type) 
		if dt_name == types.TY_LOC:
			return ast.TypeCons( ast.LOC )
		elif dt_name ==	types.TY_INT:
			return ast.TypeCons( ast.INT )
		elif dt_name == types.TY_FLOAT:
			return ast.TypeCons( ast.FLOAT )
		elif dt_name == types.TY_DEST:
			return ast.TypeCons( ast.DEST )
		elif dt_name == types.TY_CHAR:
			return ast.TypeCons( ast.CHAR )
		elif dt_name == types.TY_STR:
			return ast.TypeCons( ast.STRING )
		elif dt_name == types.TY_BOOL:
			return ast.TypeCons( ast.BOOL )
		elif dt_name == types.TY_TIME:
			return ast.TypeCons( ast.TIME )
		elif dt_name == types.TY_LIST:
			ast_type = coerce_type(smt_type.arg(0))
			return ast.TypeList( ast_type )
	 	elif dt_name == types.TY_TUPLE:
			ast_types = []
			while dt_name != types.TY_UNIT:
				ast_types.append( coerce_type( smt_type.arg(0) ) )
				smt_type = smt_type.arg(1)
				dt_name = base.datatype_name(smt_type)
			return ast.TypeTuple( ast_types )
		elif dt_name == types.TY_MSET:
			ast_type = coerce_type(smt_type.arg(0))
			return ast.TypeMSet( ast_type )
		elif dt_name == types.TY_ARROW:
			ast_in_type  = coerce_type( smt_type.arg(0) )
			ast_out_type = coerce_type( smt_type.arg(1) )
			return ast.TypeArrow(ast_in_type, ast_out_type)
		else:
			return None

	

