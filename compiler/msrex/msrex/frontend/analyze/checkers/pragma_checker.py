
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
from msrex.frontend.analyze.checkers.base_checker import Checker

PRAGMA_TEXT_SOLO_EXEC = "solo"

class PragmaChecker(Checker):

	def __init__(self, decs, source_text):
		self.initialize(decs, source_text)
		self.pragma_dict = { 'solo' : False }

	def check(self):
		inspect = Inspector()
		for pragma_dec in inspect.filter_decs(self.decs, pragmas=True):
			self.check_pragma(pragma_dec)
		
	def check_pragma(self, pragma_dec):
		pragma_text = pragma_dec.pragma_text
		if not pragma_text in [PRAGMA_TEXT_SOLO_EXEC]:
			error_idx = self.declare_error("Unknown pragma \'%s\'" % pragma_dec.pragma_text)
			self.extend_error(error_idx, pragma_dec)
		else:
			if pragma_text == PRAGMA_TEXT_SOLO_EXEC:
				self.pragma_dict['solo'] = True

	def get_analysis_name(self):
		return "pragmas"

	def get_analysis_data(self):
		return self.pragma_dict

	def get_analysis(self):
		strs = "Analysis from PragmaChecker:\n"
		for pragma,arg in self.pragma_dict.items():
			strs += "   %s : %s\n" % (pragma,arg)
		return strs



