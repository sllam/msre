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

from msrex.misc.aggregators import foldl

ERROR_IDX = 1

class Checker:

	# Front End Interfaces

	def __init__(self, decs, source_text, default_highlight=terminal.T_RED_BACK, builtin_preds=[]):
		self.initialize(decs, source_text, default_highlight=default_highlight, builtin_preds=builtin_preds)

	def initialize(self, decs, source_text, default_highlight=terminal.T_RED_BACK, builtin_preds=[]):
		self.errors   = {}
		self.decs     = decs
		self.source_text = source_text
		self.default_highlight = default_highlight
		self.builtin_preds = builtin_preds

		# idx = self.declare_error("Test Error")
		
	def get_builtin_fact_decs(self):
		return map(lambda bp: bp.getFactDec(), self.builtin_preds)

	def get_next_error_idx(self):
		global ERROR_IDX
		new_idx = ERROR_IDX
		ERROR_IDX += 1
		return new_idx

	def declare_error(self, error_report, legend=""):
		new_idx = self.get_next_error_idx()
		self.errors[new_idx] = { 'error_regions':[], 'display_regions':[], 'error_report':error_report, 'legend':legend }
		return new_idx

	def extend_error(self, error_idx, ast_node):
		if ast_node.has_source_info:
			if hasattr(ast_node,'type_kind') and (ast_node.type_kind in [ast.TYPE_TUP,ast.TYPE_LIST,ast.TYPE_MSET]):
				self.errors[error_idx]['error_regions'].append((self.default_highlight,ast_node.hl_start,ast_node.hl_start+1))
				self.errors[error_idx]['error_regions'].append((self.default_highlight,ast_node.hl_end-1,ast_node.hl_end))
			elif hasattr(ast_node,'fact_type') and ast_node.fact_type == ast.FACT_BASE:
				self.errors[error_idx]['error_regions'].append((self.default_highlight,ast_node.hl_start,ast_node.hl_start+len(ast_node.name)))
				self.errors[error_idx]['error_regions'].append((self.default_highlight,ast_node.hl_end-1,ast_node.hl_end))
			else:
				self.errors[error_idx]['error_regions'].append((self.default_highlight,ast_node.hl_start,ast_node.hl_end))
			ast_node.extend_error(error_idx)

	def extend_info(self, error_idx, ast_node, highlight_color=terminal.T_GREEN_BACK):
		if ast_node.has_source_info:
			self.errors[error_idx]['error_regions'].append((highlight_color,ast_node.hl_start,ast_node.hl_end))
			ast_node.extend_error(error_idx)
		

	def extend_error_region(self, error_idx, error_region, ast_node):
		(es,ee) = error_region
		self.errors[error_idx]['error_regions'].append((self.default_highlight,es,ee))
		ast_node.extend_error(error_idx)

	def extend_display_regions(self, error_idxs, display_regions):
		for error_idx in error_idxs:
			if error_idx in self.errors:
				self.errors[error_idx]['display_regions'] += display_regions

	# Building display regions from error regions

	def init_build_display_regions(self):
		for dec in self.decs:
			self.build_display_regions(dec)

	@visit.on('ast_node')
	def build_display_regions(self, ast_node):
		pass

	@visit.when(ast.EnsemDec)
	def build_display_regions(self, ast_node):
		(hs,he),(fs,fe) = get_source_header_footer_regions(self.source_text, ast_node)
		for dec in ast_node.decs:
			error_idxs = self.build_display_regions(dec)
			self.extend_display_regions(error_idxs,[(hs,he),(fs,fe)])
		return []

	@visit.when(ast.ExternDec)
	def build_display_regions(self, ast_node):
		(hs,he),(fs,fe) = get_source_header_footer_regions(self.source_text, ast_node)
		for type_sig in ast_node.type_sigs:
			error_idxs = self.build_display_regions(type_sig)
			self.extend_display_regions(error_idxs,[(hs,he),(fs,fe)])
		return []

	@visit.when(ast.ExternTypeSig)
	def build_display_regions(self, ast_node):
		error_idxs = self.build_display_regions(ast_node.type_sig)
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs 

	@visit.when(ast.ExecDec)
	def build_display_regions(self, ast_node):
		(hs,he),(fs,fe) = get_source_header_footer_regions(self.source_text, ast_node)
		for dec in ast_node.decs:
			error_idxs = self.build_display_regions(dec)
			self.extend_display_regions(error_idxs,[(hs,he),(fs,fe)])
		return []

	@visit.when(ast.ExistDec)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs + foldl(map(lambda v: self.build_display_regions(v),ast_node.exist_vars),[])
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs

	@visit.when(ast.LocFactDec)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs + foldl(map(lambda lf: self.build_display_regions(lf),ast_node.loc_facts),[])
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs

	@visit.when(ast.FactDec)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs + self.build_display_regions(ast_node.type)
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs

	@visit.when(ast.ExportDec)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs + self.build_display_regions(ast_node.arg)
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs

	@visit.when(ast.RuleDec)
	def build_display_regions(self, ast_node):
		error_idxs = []
		for fact in ast_node.slhs + ast_node.plhs:
			error_idxs += self.build_display_regions(fact)
		for grd_term in ast_node.grd:
			error_idxs += self.build_display_regions(grd_term)
		for exist_var in ast_node.exists:
			error_idxs += self.build_display_regions(exist_var)
		for fact in ast_node.rhs:
			error_idxs += self.build_display_regions(fact)
		for assign in ast_node.where:
			error_idxs += self.build_display_regions(assign)
		error_idxs = set_interp(error_idxs)
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs

	@visit.when(ast.InitDec)
	def build_display_regions(self, ast_node):
		error_idxs = []
		for fact in ast_node.facts:
			error_idxs += self.build_display_regions(fact)
		error_idxs = set_interp( error_idxs )
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs

	@visit.when(ast.AssignDec)
	def build_display_regions(self, ast_node):
		error_idxs = set_interp( self.build_display_regions( ast_node.term_pat ) + self.build_display_regions( ast_node.builtin_exp ) )
		self.extend_display_regions(error_idxs,[(ast_node.lex_start,ast_node.lex_end)])
		return error_idxs

	@visit.when(ast.TypeVar)
	def build_display_regions(self, ast_node):
		# self.extend_error_region(0, (ast_node.lex_start,ast_node.lex_end), ast_node)
		return ast_node.error_idxs

	@visit.when(ast.TypeCons)
	def build_display_regions(self, ast_node):
		# self.extend_error_region(0, (ast_node.lex_start,ast_node.lex_end), ast_node)
		return ast_node.error_idxs

	@visit.when(ast.TypeApp)
	def build_display_regions(self, ast_node):
		return set_interp(ast_node.error_idxs + self.build_display_regions(ast_node.type1) + self.build_display_regions(ast_node.type2))

	@visit.when(ast.TypeArrow)
	def build_display_regions(self, ast_node):
		return set_interp(ast_node.error_idxs + self.build_display_regions(ast_node.type1) + self.build_display_regions(ast_node.type2))

	@visit.when(ast.TypeTuple)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		for ty in ast_node.types:
			error_idxs += self.build_display_regions(ty)
		return set_interp(error_idxs)

	@visit.when(ast.TypeList)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		error_idxs += self.build_display_regions(ast_node.type)
		return set_interp(error_idxs)

	@visit.when(ast.TypeMSet)
	def build_display_regions(self, ast_node):
		# TODO
		error_idxs = ast_node.error_idxs
		error_idxs += self.build_display_regions(ast_node.type)
		return set_interp(error_idxs)

	@visit.when(ast.FactType)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		for ty in ast_node.types:
			error_idxs += self.build_display_regions(ty)
		return set_interp(error_idxs)

	@visit.when(ast.ExternType)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		for ty in ast_node.types:
			error_idxs += self.build_display_regions(ty)
		return set_interp(error_idxs)

	@visit.when(ast.FactLoc)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		error_idxs += self.build_display_regions( ast_node.loc )
		error_idxs += self.build_display_regions( ast_node.fact )
		return set_interp(error_idxs)
		
	@visit.when(ast.FactBase)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		for term in ast_node.terms:
			error_idxs += self.build_display_regions( term )
		return set_interp(error_idxs)

	@visit.when(ast.CompRange)
	def build_display_regions(self, ast_node):
		# TODO
		error_idxs = ast_node.error_idxs
		error_idxs += self.build_display_regions( ast_node.term_vars )
		error_idxs += self.build_display_regions( ast_node.term_range )
		return set_interp(error_idxs)

	@visit.when(ast.FactCompre)
	def build_display_regions(self, ast_node):
		# TODO
		error_idxs = ast_node.error_idxs
		for fact in ast_node.facts:
			error_idxs += self.build_display_regions( fact )
		for comp_range in ast_node.comp_ranges:
			error_idxs += self.build_display_regions( comp_range )
		for guard in ast_node.guards:
			error_idxs += self.build_display_regions( guard )
		return set_interp( error_idxs )

	'''
	@visit.when(ast.SetComprehension)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs + self.build_display_regions(ast_node.term_pat) + self.build_display_regions(ast_node.term_subj)
		for fact in ast_node.facts:
			error_idxs += self.build_display_regions(fact)
		return set_interp(error_idxs)
	'''

	'''
	@visit.when(ast.RHSFact)
	def build_display_regions(self, ast_node):
		return self.build_display_regions(ast_node.elem)

	@visit.when(ast.RHSSetComp)
	def build_display_regions(self, ast_node):
		return self.build_display_regions(ast_node.elem)
	'''

	@visit.when(ast.TermCons)
	def build_display_regions(self, ast_node):
		# self.extend_error_region(0, (ast_node.lex_start,ast_node.lex_end), ast_node)
		return ast_node.error_idxs

	@visit.when(ast.TermVar)
	def build_display_regions(self, ast_node):
		# self.extend_error_region(0, (ast_node.lex_start,ast_node.lex_end), ast_node)
		return ast_node.error_idxs

	@visit.when(ast.TermApp)
	def build_display_regions(self, ast_node):
		return set_interp( ast_node.error_idxs + self.build_display_regions(ast_node.term1) + self.build_display_regions(ast_node.term2) )	

	@visit.when(ast.TermTuple)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		for term in ast_node.terms:
			error_idxs += self.build_display_regions(term)
		return set_interp(error_idxs)

	@visit.when(ast.TermList)
	def build_display_regions(self, ast_node):
		error_idxs = ast_node.error_idxs
		for term in ast_node.terms:
			error_idxs += self.build_display_regions(term)
		return set_interp(error_idxs)

	@visit.when(ast.TermMSet)
	def build_display_regions(self, ast_node):
		# TODO
		error_idxs = ast_node.error_idxs
		for term in ast_node.terms:
			error_idxs += self.build_display_regions(term)
		return set_interp(error_idxs)

	@visit.when(ast.TermCompre)
	def build_display_regions(self, ast_node):
		# TODO
		error_idxs = ast_node.error_idxs
		error_idxs += self.build_display_regions( ast_node.term )
		for comp_range in ast_node.comp_ranges:
			error_idxs += self.build_display_regions( comp_range )
		for guard in ast_node.guards:
			error_idxs += self.build_display_regions( guard )
		return set_interp(error_idxs)

	@visit.when(ast.TermBinOp)
	def build_display_regions(self, ast_node):
		return set_interp( ast_node.error_idxs + self.build_display_regions(ast_node.term1) + self.build_display_regions(ast_node.term2) )	
	
	@visit.when(ast.TermUnaryOp)
	def build_display_regions(self, ast_node):
		return set_interp( ast_node.error_idxs + self.build_display_regions(ast_node.term) )	

	@visit.when(ast.TermLit)
	def build_display_regions(self, ast_node):
		return ast_node.error_idxs

	@visit.when(ast.TermUnderscore)
	def build_display_regions(self, ast_node):
		return ast_node.error_idxs

	# formatting error reports

	def get_error_reports(self):
		error_outputs = []
		for idx in self.errors:
			error = self.errors[idx]
			error_output = ("Error %s: " % idx) + error['error_report'] + "\n" 
			error_output += "Code snippet:\n" + terminal.format_str(self.source_text, set_interp(error['error_regions']), set_interp(error['display_regions']))
			if len(error['legend']) > 0:
				error_output += "\n" + error['legend'] 
			error_outputs.append( error_output )
		return error_outputs

	# Analysis

	def get_analysis_name(self):
		return "None"

	def get_analysis_data(self):
		return None

	def get_analysis(self):
		return None

# Auxiliary Functions

def get_source_header_footer_regions(source_text, ast_node):

	header_start = ast_node.lex_start
	header_end   = header_start
	for idx in range(ast_node.lex_start,ast_node.lex_end):
		if source_text[idx] == '{':
			header_end = idx + 1
			break

	footer_end   = ast_node.lex_end
	footer_start = footer_end
	rev_idxs = range(ast_node.lex_start,ast_node.lex_end)
	rev_idxs.reverse()
	for idx in rev_idxs:
		if source_text[idx] == '}':
			footer_start = idx
			break

	return (header_start,header_end),(footer_start,footer_end)
	

def set_interp(ls):
	return list(set(ls))
