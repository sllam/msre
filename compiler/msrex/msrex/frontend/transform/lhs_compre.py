
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

from msrex.frontend.transform.base_transformer import Transformer

from msrex.misc.aggregators import foldl

import msrex.frontend.lex_parse.ast as ast
import msrex.misc.visit as visit

from msrex.frontend.analyze.inspectors import Inspector

from msrex.frontend.analyze.smt_solver import tyInt, tyMSet

class LHSCompre(Transformer):

	def __init__(self, decs):
		self.initialize(decs)
		self.inspect = Inspector()

	def transform(self):
		ensem_dec = self.inspect.filter_decs(self.decs, ensem=True)[0]
		rule_decs = self.inspect.filter_decs(ensem_dec.decs, rule=True)
		map( lambda rule_dec: self.transformRule(rule_dec), rule_decs)

	def transformRule(self, rule_dec):
		_,atoms,_,compres = self.inspect.partition_rule_heads( rule_dec.plhs + rule_dec.slhs )
		# scope_vars = self.getVarsFilterByRuleIdx(atoms)
		map(lambda c: self.transformCompre(c, rule_dec), compres)

	def transformCompre(self, compre, rule_dec):
		if len(compre.comp_ranges) == 0 and compre.compre_mod in [ast.COMP_NONE_EXISTS,ast.COMP_ONE_OR_MORE]:			
			term_vars  = ast.TermLit(1,"int")
			next_rule_idx = rule_dec.next_rule_idx
			rule_dec.next_rule_idx += 1
			term_range = ast.TermVar( "comp_mod_%s" % next_rule_idx )
			term_range.rule_idx = next_rule_idx
			term_range.type     = ast.TypeMSet( term_vars.type )
			term_range.smt_type = tyMSet( tyInt )
			compre.comp_ranges  = [ ast.CompRange(term_vars, term_range) ]
		if compre.compre_mod == ast.COMP_NONE_EXISTS:
			term_range = compre.comp_ranges[0].term_range
			comp_none_exist_grd = ast.TermBinOp( ast.TermApp(ast.TermCons("size"), term_range), "==", ast.TermLit(0, "int"))
			rule_dec.grd += [comp_none_exist_grd]
		elif compre.compre_mod == ast.COMP_ONE_OR_MORE:
			term_range = compre.comp_ranges[0].term_range
			comp_one_or_more_grd = ast.TermBinOp( ast.TermApp(ast.TermCons("size"), term_range), ">", ast.TermLit(0, "int"))
			rule_dec.grd += [comp_one_or_more_grd]
				

	def getVarsFilterByRuleIdx(self, facts):
		fact_vars = self.getVars(facts)
		uniq_vars = []
		idx_dict  = {}
		for fact_var in fact_vars:
			if fact_var.rule_idx not in idx_dict:
				idx_dict[fact_var.rule_idx] = ()
				uniq_vars.append( fact_var )
		return uniq_vars

	@visit.on( 'fact' )
	def getVars(self, fact):
		pass

	@visit.when( list )
	def getVars(self, fact):
		return foldl(map(lambda f: self.getVars(f), fact), [])

	@visit.when( ast.FactLoc )
	def getVars(self, fact):
		return self.inspect.free_vars(fact)


