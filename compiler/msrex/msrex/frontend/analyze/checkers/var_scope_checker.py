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
import msrex.frontend.lex_parse.constants as constants
import msrex.misc.visit as visit
import msrex.misc.terminal_color as terminal
from msrex.frontend.analyze.inspectors import Inspector

from msrex.frontend.analyze.checkers.base_checker import Checker

class VarScopeChecker(Checker):

	def __init__(self, decs, source_text, builtin_preds=[]):
		self.inspect = Inspector()
		self.initialize(decs, source_text, builtin_preds=builtin_preds)
		self.curr_out_scopes = new_ctxt()
		self.curr_duplicates = { 'vars':{} }
		self.ensems = {}

	# Main checking operation

	def check(self):

		inspect = self.inspect

		ctxt = new_ctxt()

		# Check scoping of extern name declarations
		for extern in inspect.filter_decs(self.decs, extern=True):
			self.check_scope(extern, ctxt)

		for ensem_dec in inspect.filter_decs(self.decs, ensem=True):
			self.check_scope(ensem_dec, ctxt)

		for exec_dec in inspect.filter_decs(self.decs, execute=True):
			self.check_scope(exec_dec, ctxt)

	@visit.on('ast_node')
	def check_scope(self, ast_node, ctxt, lhs=False):
		pass

	@visit.when(ast.EnsemDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		old_ctxt = ctxt
		ctxt = copy_ctxt(ctxt)
		decs = ast_node.decs
		inspect = Inspector()
	
		dec_preds = {}

		# Check scoping of extern name declarations
		for extern in inspect.filter_decs(decs, extern=True):
			self.check_scope(extern, ctxt)

		# Check scoping of predicate declarations
		for dec in inspect.filter_decs(decs, fact=True) + self.get_builtin_fact_decs():
			local_ctxt = self.check_scope(dec, ctxt)
			for pred in local_ctxt['preds']:
				if pred.name in dec_preds:
					dec_preds[pred.name].append(pred)
				else:
					dec_preds[pred.name] = [pred]
			extend_ctxt(ctxt, local_ctxt)

		self.compose_duplicate_error_reports("predicate", dec_preds)

		# Check scoping of export declarations
		for dec in inspect.filter_decs(decs, export=True):
			self.check_scope(dec, ctxt)

		# Check scoping of rule declarations
		for dec in inspect.filter_decs(decs, rule=True):
			self.check_scope(dec, ctxt)

		ctxt['vars'] = []
		self.ensems[ast_node.name] = ctxt

		return old_ctxt

	@visit.when(ast.ExecDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		if ast_node.name not in self.ensems:
			self.curr_out_scopes['ensem'].append( ast_node )
			self.compose_out_scope_error_report(ctxt)
		else:
			ctxt = self.ensems[ast_node.name]
			for dec in ast_node.decs:
				self.check_scope(dec, ctxt)
			self.compose_duplicate_error_reports("variables", self.curr_duplicates['vars'])
			self.curr_duplicates['vars'] = {}
			self.compose_out_scope_error_report(ctxt)

	@visit.when(ast.ExistDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		for tvar in ast_node.exist_vars:
			if not lookup_var(ctxt, tvar):
				ctxt['vars'] += [tvar]
			else:
				self.record_duplicates(tvar, ctxt)

	@visit.when(ast.AssignDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_scope(ast_node.builtin_exp, ctxt)
		inspect = Inspector()
		for new_var in inspect.free_vars( ast_node.term_pat ):
			if not lookup_var(ctxt, new_var):
				ctxt['vars'] += [new_var]
			else:
				self.record_duplicates(new_var, ctxt)

	@visit.when(ast.LocFactDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		for loc_fact in ast_node.loc_facts:
			self.check_scope(loc_fact, ctxt)

	@visit.when(ast.ExternDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		for type_sig in ast_node.type_sigs:
			self.check_scope(type_sig, ctxt)

	@visit.when(ast.ExternTypeSig)
	def check_scope(self, ast_node, ctxt, lhs=False):
		ctxt['cons'].append( ast_node )

	@visit.when(ast.FactDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		ctxt = new_ctxt()
		ctxt['preds'].append( ast_node )
		# TODO: check types
		return ctxt

	@visit.when(ast.ExportDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		ctxt = copy_ctxt(ctxt)
		if ast_node.export_sort == ast.QUERY_EXPORT:
			self.check_scope(ast_node.arg, ctxt)

	@visit.when(ast.RuleDec)
	def check_scope(self, ast_node, ctxt, lhs=False):
		ctxt = copy_ctxt(ctxt)
		heads   = ast_node.slhs + ast_node.plhs
		inspect = self.inspect

		# Extend location context with all rule head variables
		'''
		for fact in map(inspect.get_fact, heads):
			terms = inspect.get_atoms( [inspect.get_loc(fact)] + inspect.get_args(fact) )
			ctxt['vars'] += inspect.filter_atoms(terms, var=True)
		'''
		ctxt['vars'] += self.get_rule_scope( heads, compre=False )
	
		# Check scope of rule heads. This step checks consistency of constant names and
		# scoping of comprehension patterns.
		map(lambda h: self.check_scope(h, ctxt, lhs=True) , heads)
		map(lambda g: self.check_scope(g, ctxt, lhs=True) , ast_node.grd)

		ctxt['vars'] += self.get_rule_scope( heads, atoms=False)

		# Include exist variables scopes and check for overlaps with existing variables.
		# (We currently disallow them.)
		dup_vars = {}
		for v in ctxt['vars']:
			dup_vars[v.name] = [v]

		for ex_var in ast_node.exists:
			if ex_var.name in dup_vars:
				dup_vars[ex_var.name].append( ex_var )
			else:
				dup_vars[ex_var.name] = [ex_var]

		ctxt['vars'] += ast_node.exists

		# Incremental include where assign statements
		for ass_stmt in ast_node.where:
			self.check_scope(ass_stmt.builtin_exp, ctxt)
			self.compose_out_scope_error_report(ctxt)
			a_vars = inspect.filter_atoms( inspect.get_atoms(ass_stmt.term_pat), var=True)
			for a_var in a_vars:
				if a_var.name in dup_vars:
					dup_vars[a_var.name].append( a_var )
				else:
					dup_vars[a_var.name] = [a_var]
			ctxt['vars'] += a_vars

		self.compose_duplicate_error_reports("variables", dup_vars)

		map(lambda b: self.check_scope(b, ctxt) , ast_node.rhs)

		'''
		for fact in map(inspect.get_fact, ast_node.rhs), fact_atoms=True ):
			loc = inspect.get_loc(fact)
			loc_key = loc.compare_value()
			args = inspect.get_args(fact)
			atoms = inspect.get_atoms(args)
			arg_map[loc_key] += map(lambda t: t.name,inspect.filter_atoms(atoms, var=True))
		'''

		self.compose_out_scope_error_report(ctxt)

	'''
	@visit.when(ast.SetComprehension)
	def check_scope(self, ast_node, ctxt):
		inspect = Inspector()
		ctxt = copy_ctxt(ctxt)
		self.check_scope(ast_node.term_subj, ctxt)
		pat_vars = inspect.filter_atoms( inspect.get_atoms(ast_node.term_pat), var=True)
		ctxt['vars'] += pat_vars
		map(lambda fact: self.check_scope(fact, ctxt), ast_node.facts)
		self.compose_out_scope_error_report(ctxt)
		return ctxt
	'''

	@visit.when(ast.FactBase)
	def check_scope(self, ast_node, ctxt, lhs=False):
		ctxt = copy_ctxt(ctxt)
		self.check_pred(ctxt, ast_node)
		# print ast_node
		map(lambda t: self.check_scope(t, ctxt), ast_node.terms)
		return ctxt

	@visit.when(ast.FactLoc)
	def check_scope(self, ast_node, ctxt, lhs=False):
		ctxt = copy_ctxt(ctxt)
		self.check_scope(ast_node.loc, ctxt)
		self.check_scope(ast_node.fact, ctxt)
		return ctxt

	@visit.when(ast.FactLocCluster)
	def check_scope(self, ast_node, ctxt, lhs=False):
		ctxt = copy_ctxt(ctxt)
		self.check_scope(ast_node.loc, ctxt)
		for fact in ast_node.facts:
			self.check_scope(fact, ctxt)
		return ctxt

	@visit.when(ast.FactCompre)
	def check_scope(self, ast_node, old_ctxt, lhs=False):
		ctxt = copy_ctxt(old_ctxt)
		comp_ranges = ast_node.comp_ranges

		# Check scope of comprehension ranges
		if not lhs:
			map(lambda comp_range: self.check_scope(comp_range, ctxt), comp_ranges)

		self.compose_out_scope_error_report(ctxt)
		
		# Extend variable context with comprehension binders
		ctxt['vars'] += self.inspect.free_vars( map(lambda cr: cr.term_vars, comp_ranges) )

		# With extended variable context, check scopes of the fact pattern and guards
		for fact in ast_node.facts:
			self.check_scope( fact, ctxt )
		for guard in ast_node.guards:
			self.check_scope( guard, ctxt )

		self.compose_out_scope_error_report(ctxt)

		if lhs:
			old_ctxt['vars'] += self.inspect.free_vars( map(lambda cr: cr.term_range, comp_ranges) )

	@visit.when(ast.CompRange)	
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_scope( ast_node.term_range, ctxt )

	@visit.when(ast.TermCons)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_cons(ctxt, ast_node)
		return ctxt

	@visit.when(ast.TermVar)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_var(ctxt, ast_node)
		return ctxt

	@visit.when(ast.TermApp)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_scope(ast_node.term1, ctxt)
		self.check_scope(ast_node.term2, ctxt)
		return ctxt

	@visit.when(ast.TermTuple)
	def check_scope(self, ast_node, ctxt, lhs=False):
		map(lambda t: self.check_scope(t, ctxt), ast_node.terms)
		return ctxt

	@visit.when(ast.TermList)
	def check_scope(self, ast_node, ctxt, lhs=False):
		map(lambda t: self.check_scope(t, ctxt), ast_node.terms)
		return ctxt

	@visit.when(ast.TermListCons)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_scope(ast_node.term1, ctxt)
		self.check_scope(ast_node.term2, ctxt)
		return ctxt

	@visit.when(ast.TermMSet)
	def check_scope(self, ast_node, ctxt, lhs=False):
		map(lambda t: self.check_scope(t, ctxt), ast_node.terms)
		return ctxt

	@visit.when(ast.TermCompre)
	def check_scope(self, ast_node, old_ctxt, lhs=False):
		ctxt = copy_ctxt(old_ctxt)
		comp_ranges = ast_node.comp_ranges

		# Check scope of comprehension ranges
		map(lambda comp_range: self.check_scope(comp_range, ctxt), comp_ranges)

		# Extend variable context with comprehension binders
		ctxt['vars'] += self.inspect.free_vars( map(lambda cr: cr.term_vars, comp_ranges) )

		# With extended variable context, check scopes of the term pattern and guards
		self.check_scope(ast_node.term, ctxt)
		map(lambda guard: self.check_scope(guard, ctxt), ast_node.guards)

		self.compose_out_scope_error_report(ctxt)
		return old_ctxt

	@visit.when(ast.TermEnumMSet)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_scope(ast_node.texp1, ctxt)
		self.check_scope(ast_node.texp2, ctxt)
		return ctxt

	@visit.when(ast.TermBinOp)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_scope(ast_node.term1, ctxt)
		self.check_scope(ast_node.term2, ctxt)
		return ctxt

	@visit.when(ast.TermUnaryOp)
	def check_scope(self, ast_node, ctxt, lhs=False):
		self.check_scope(ast_node.term, ctxt)
		return ctxt

	@visit.when(ast.TermLit)
	def check_scope(self, ast_node, ctxt, lhs=False):
		return ctxt

	@visit.when(ast.TermUnderscore)
	def check_scope(self, ast_node, ctxt, lhs=False):
		return ctxt

	# Error state operations
	def flush_error_ctxt(self):
		self.curr_out_scopes = new_ctxt()
		self.curr_duplicates = { 'vars':{} }

	def check_var(self, ctxt, var):
		if not lookup_var(ctxt, var):
			self.curr_out_scopes['vars'].append( var )
			return False
		else:
			return True

	def check_pred(self, ctxt, pred):
		if not lookup_pred(ctxt, pred):
			self.curr_out_scopes['preds'].append( pred )
			return False
		else:
			return True

	def check_cons(self, ctxt, cons):
		if not lookup_cons(ctxt, cons):
			if cons.name in constants.BUILTIN_CONSTANTS:
				return True
			self.curr_out_scopes['cons'].append( cons )
			return False
		else:
			return True

	# Get rule scope

	@visit.on('ast_node')
	def get_rule_scope(self, ast_node, atoms=True, compre=True):
		pass

	@visit.when(list)
	def get_rule_scope(self, ast_node, atoms=True, compre=True):
		this_free_vars = []
		for obj in ast_node:
			this_free_vars += self.get_rule_scope(obj, atoms=atoms, compre=compre)
		return this_free_vars	

	@visit.when(ast.FactBase)
	def get_rule_scope(self, ast_node, atoms=True, compre=True):
		if atoms:
			return self.inspect.free_vars(ast_node)
		else:
			return []

	@visit.when(ast.FactLoc)
	def get_rule_scope(self, ast_node, atoms=True, compre=True):
		if atoms:
			return self.inspect.free_vars(ast_node)
		else:
			return []

	@visit.when(ast.FactLocCluster)
	def get_rule_scope(self, ast_node, atoms=True, compre=True):
		if atoms:
			return self.inspect.free_vars(ast_node)
		else:
			return []

	@visit.when(ast.FactCompre)
	def get_rule_scope(self, ast_node, atoms=True, compre=True):
		if compre:
			comp_ranges = ast_node.comp_ranges
			if len(comp_ranges) == 1:
				return [comp_ranges[0].term_range]
			else:
				return []
		else:
			return []

	# Reporting

	def record_duplicates(self, tvar, ctxt):
		if tvar.name not in self.curr_duplicates['vars']:
			dups = []
			for t in ctxt['vars']:
				if tvar.name == t.name:
					dups.append( t )
			dups.append( tvar )
			self.curr_duplicates['vars'][tvar.name] = dups
		else:
			self.curr_duplicates['vars'][tvar.name].append( tvar )

	def compose_out_scope_error_report(self, ctxt):
		err = self.curr_out_scopes
		if len(err['vars']) > 0:
			legend = ("%s %s: Scope context variable(s).\n" % (terminal.T_GREEN_BACK,terminal.T_NORM)) + ("%s %s: Out of scope variable(s)." % (terminal.T_RED_BACK,terminal.T_NORM))
			error_idx = self.declare_error("Variable(s) %s not in scope." % (','.join(set(map(lambda t: t.name,err['vars'])))), legend)
			map(lambda t: self.extend_error(error_idx,t), err['vars'])
			map(lambda t: self.extend_info(error_idx,t), ctxt['vars'])
		if len(err['preds']) > 0:
			legend = ("%s %s: Scope context predicate(s).\n" % (terminal.T_GREEN_BACK,terminal.T_NORM)) + ("%s %s: Out of scope predicate(s)." % (terminal.T_RED_BACK,terminal.T_NORM))
			error_idx = self.declare_error("Predicate(s) %s not in scope." % (','.join(set(map(lambda t: t.name,err['preds'])))), legend)
			map(lambda t: self.extend_error(error_idx,t), err['preds'])
			map(lambda t: self.extend_info(error_idx,t), ctxt['preds'])
		if len(err['cons']) > 0:
			legend = ("%s %s: Scope context name(s).\n" % (terminal.T_GREEN_BACK,terminal.T_NORM)) + ("%s %s: Out of scope name(s)." % (terminal.T_RED_BACK,terminal.T_NORM))
			error_idx = self.declare_error("Name(s) %s not in scope." % (','.join(set(map(lambda t: t.name,err['cons'])))), legend)
			map(lambda t: self.extend_error(error_idx,t), err['cons'])
			map(lambda t: self.extend_info(error_idx,t), ctxt['cons'])
		if len(err['ensem']) > 0:
			for exec_node in err['ensem']:
				error_idx = self.declare_error("Ensemble %s not in scope." % exec_node.name)
				self.extend_error(error_idx, exec_node)
		self.curr_out_scopes = new_ctxt()

	def compose_duplicate_error_reports(self, kind, dups):
		for name in dups:
			elems = dups[name]
			if len(elems) > 1:
				error_idx = self.declare_error("Duplicated declaration of %s %s." % (kind,name))
				map(lambda p: self.extend_error(error_idx,p), elems)

def new_ctxt():
	return { 'vars':[], 'preds':[], 'cons':[], 'ensem':[] }

def lookup_var(ctxt, v):
	return v.name in map(lambda t: t.name,ctxt['vars'])

def lookup_pred(ctxt, p):
	return p.name in map(lambda t: t.name,ctxt['preds'])

def lookup_cons(ctxt, c):
	return c.name in map(lambda t: t.name,ctxt['cons'])

def copy_ctxt(c):
	output = new_ctxt()
	extend_ctxt(output, c)
	return output

def extend_ctxt(c1, c2):
	map(lambda v: remove_ctxt(c1,'vars',v), c2['vars'])
	map(lambda p: remove_ctxt(c1,'preds',p), c2['preds'])
	map(lambda c: remove_ctxt(c1,'cons',c), c2['cons'])
	c1['vars']  += c2['vars']
	c1['preds'] += c2['preds']
	c1['cons']  += c2['cons']

def union_ctxt(c1, c2):
	output = new_ctxt()
	extend_ctxt(output,c1)	
	extend_ctxt(output,c2)
	return output

def remove_ctxt(c, ty, e):
	ls = c[ty]
	for idx in range(0,len(ls)):
		if e.name == ls[idx].name:
			del ls[idx]
			break



