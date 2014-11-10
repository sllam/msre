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

from msrex.misc.infix import Infix

from msrex.misc.z3_utils.base import datatype_name

import msrex.misc.z3_utils.types as types
import msrex.misc.z3_utils.data  as data

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


