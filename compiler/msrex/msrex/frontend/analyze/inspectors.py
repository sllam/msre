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

from msrex.misc.aggregators import tmerge, foldl


DEFAULT_ACCEPT_NODES = [ast.TERM_VAR, ast.TERM_LIT]
DEFAULT_EXPAND_NODES = [ast.TERM_TUPLE, ast.TERM_BINOP]

class Inspector:

	# Filter Facts from FactBase, FactLoc, FactLocCluster or FactCompre

	@visit.on('fact')
	def filter_rule_facts(self, fact, fact_bases=False, fact_atoms=False, fact_clusters=False, comprehensions=False):
		pass

	@visit.when(list)
	def filter_rule_facts(self, fact, fact_bases=False, fact_atoms=False, fact_clusters=False, comprehensions=False):
		facts = []
		for f in fact:
			facts += self.filter_rule_facts(f, fact_bases=fact_bases, fact_atoms=fact_atoms, fact_clusters=fact_clusters, comprehensions=comprehensions)
		return facts
	
	@visit.when(ast.FactBase)
	def filter_rule_facts(self, fact, fact_bases=False, fact_atoms=False, fact_clusters=False, comprehensions=False):
		return [fact] if fact_bases else []

	@visit.when(ast.FactLoc)
	def filter_rule_facts(self, fact, fact_bases=False, fact_atoms=False, fact_clusters=False, comprehensions=False):
		return [fact] if fact_atoms else []

	@visit.when(ast.FactLocCluster)
	def filter_rule_facts(self, fact, fact_bases=False, fact_atoms=False, fact_clusters=False, comprehensions=False):
		return [fact] if fact_clusters else []

	@visit.when(ast.FactCompre)
	def filter_rule_facts(self, fact, fact_bases=False, fact_atoms=False, fact_clusters=False, comprehensions=False):
		return [fact] if comprehensions else []

	# Get Location from FactLoc

	def get_loc(self, loc_fact):
		return loc_fact.loc

	# Get Term arguments from FactLoc

	@visit.on('ast_node')
	def get_args(self, ast_node):
		pass

	@visit.when(list)
	def get_args(self, ast_node):
		args = []
		for node in ast_node:
			args += self.get_args(node)
		return args

	@visit.when(ast.FactLoc)
	def get_args(self, ast_node):
		return self.get_args(ast_node.fact)
	
	@visit.when(ast.FactBase)
	def get_args(self, ast_node):
		args = []
		for term in ast_node.terms:
			args.append(term)
		return args
		
	# Get Term Atoms from Terms
	
	@visit.on('term')
	def get_atoms(self, term):
		pass

	@visit.when(list)
	def get_atoms(self, term):
		atoms = []
		for t in term:
			atoms += self.get_atoms(t)
		return atoms

	@visit.when(ast.TermVar)
	def get_atoms(self, term):
		return [term]

	@visit.when(ast.TermCons)
	def get_atoms(self, term):
		return [term]

	@visit.when(ast.TermApp)
	def get_atoms(self, term):
		return self.get_atoms(term.term1) + self.get_atoms(term.term2)

	@visit.when(ast.TermTuple)
	def get_atoms(self, term):
		atoms = []
		for t in term.terms:
			atoms += self.get_atoms(t)
		return atoms

	@visit.when(ast.TermList)
	def get_atoms(self, term):
		atoms = []
		for t in term.terms:
			atoms += self.get_atoms(t)
		return atoms

	@visit.when(ast.TermListCons)
	def get_atoms(self, term):
		return self.get_atoms(term.term1) + self.get_atoms(term.term2)

	@visit.when(ast.TermMSet)
	def get_atoms(self, term):
		atoms = []
		for t in term.terms:
			atoms += self.get_atoms(t)
		return atoms

	@visit.when(ast.TermEnumMSet)
	def get_atoms(self, term):
		return self.get_atoms(term.texp1) + self.get_atoms(term.texp2)
		

	@visit.when(ast.TermBinOp)
	def get_atoms(self, term):
		return self.get_atoms(term.term1) + self.get_atoms(term.term2)
		
	@visit.when(ast.TermUnaryOp)
	def get_atoms(self, term):
		return self.get_atoms(term.term)

	@visit.when(ast.TermLit)
	def get_atoms(self, term):
		return [term]

	@visit.when(ast.TermUnderscore)
	def get_atoms(self, term):
		return []

	# Filtering from Term Atoms
	
	@visit.on('term')
	def filter_atoms(self, term, var=False, lit=False, cons=False):
		pass

	@visit.when(list)
	def filter_atoms(self, term, var=False, lit=False, cons=False):
		atoms = []
		for t in term:
			atoms += self.filter_atoms(t, var=var, lit=lit, cons=cons)
		return atoms

	@visit.when(ast.TermVar)
	def filter_atoms(self, term, var=False, lit=False, cons=False):
		return [term] if var else []

	@visit.when(ast.TermLit)
	def filter_atoms(self, term, var=False, lit=False, cons=False):
		return [term] if lit else []

	@visit.when(ast.TermCons)
	def filter_atoms(self, term, var=False, lit=False, cons=False):
		return [term] if cons else []

	# Filtering from Decs

	@visit.on('dec')
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		pass

	@visit.when(list)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		decs = []
		for d in dec:
			decs += self.filter_decs(d, ensem=ensem, extern=extern, execute=execute, fact=fact, rule=rule, assign=assign, init=init
                                                ,exist=exist, loc_facts=loc_facts, pragmas=pragmas, export=export, rolesig=rolesig, roledef=roledef)
		return decs

	@visit.when(ast.PragmaDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if pragmas else []

	@visit.when(ast.EnsemDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if ensem else []

	@visit.when(ast.ExternDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if extern else []

	@visit.when(ast.ExecDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if execute else []

	@visit.when(ast.ExistDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if exist else []

	@visit.when(ast.LocFactDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if loc_facts else []

	@visit.when(ast.FactDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if fact else []

	@visit.when(ast.RuleDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if rule else []

	@visit.when(ast.AssignDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if assign else []

	@visit.when(ast.RoleSigDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if rolesig else []

	@visit.when(ast.RoleDefDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if roledef else []

	@visit.when(ast.InitDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if init else []

	@visit.when(ast.ExportDec)
	def filter_decs(self, dec, ensem=False, extern=False, execute=False, fact=False, rule=False, assign=False, init=False, exist=False, loc_facts=False, pragmas=False, export=False, rolesig=False, roledef=False):
		return [dec] if export else []

	# Filtering Facts from FactLoc

	@visit.on('loc_fact')
	def filter_facts(self, loc_fact, loc_var):
		pass

	@visit.when(list)
	def filter_facts(self, loc_fact, loc_var):
		facts = []
		for lf in loc_fact:
			facts += self.filter_facts(lf, loc_var)
		return facts	

	@visit.when(ast.FactLoc)
	def filter_facts(self, loc_fact, loc_var):
		locs = self.filter_atoms( self.get_loc(loc_fact) , var=True)
		if len(locs) == 1:
			if locs[0].name == loc_var:
				return loc_fact.facts
			else:
				return []
		else:
			return []


	# Counting the number of term arguments for given fact declaration

	@visit.on('ast_node')
	def count_terms(self, ast_node):
		pass

	@visit.when(ast.FactDec)
	def count_terms(self, ast_node):
		if ast_node.type == None:
			return 0
		c = self.count_terms(ast_node.type)
		if isinstance(c, list):
			return c[0]
		else:
			return c

	@visit.when(ast.TypeTuple)
	def count_terms(self, ast_node):
		return len(ast_node.types)

	@visit.when(ast.ASTNode)
	def count_terms(self, ast_node):
		return 1

	# Tuple terms to list number of term arguments for given fact declaration

	@visit.on('ast_node')
	def tuple_term_to_list(self, ast_node):
		pass

	@visit.when(ast.FactDec)
	def tuple_term_to_list(self, ast_node):
		if ast_node.type == None:
			return []
		c = self.tuple_term_to_list(ast_node.type)
		if isinstance(c, list):
			return [c[0]]
		else:
			# print c['types']
			return c['types']

	@visit.when(ast.TypeTuple)
	def tuple_term_to_list(self, ast_node):
		# print ast_node.types
		return { 'types' : ast_node.types }

	@visit.when(ast.TypeList)
	def tuple_term_to_list(self, ast_node):
		return { 'types' : [ast_node] }

	@visit.when(ast.TypeCons)
	def tuple_term_to_list(self, ast_node):
		return { 'types': [ast_node] }

	@visit.when(ast.ASTNode)
	def tuple_term_to_list(self, ast_node):
		# print "Here: %s" % ast_node
		return { 'types' : [ast_node] }

	# Free Variables

	@visit.on('ast_node')
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		pass

	@visit.when(list)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		this_free_vars = []
		for obj in ast_node:
			this_free_vars += self.free_vars( obj, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores )
		return this_free_vars

	@visit.when(ast.FactBase)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return self.free_vars(ast_node.terms, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores)

	@visit.when(ast.FactLoc)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		fvs = []
		if loc:
			fvs += self.free_vars(ast_node.loc, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores)
		if args:
			fvs += self.free_vars(ast_node.fact, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores)
		return fvs

	@visit.when(ast.FactLocCluster)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		fvs = []
		if loc:
			fvs += self.free_vars(ast_node.loc, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores)
		if args:
			fvs += self.free_vars(ast_node.facts, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores)
		return fvs

	@visit.when(ast.FactCompre)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		comp_term_vars   = map(lambda comp_range: comp_range.term_vars, ast_node.comp_ranges)
		comp_term_ranges = map(lambda comp_range: comp_range.term_range, ast_node.comp_ranges)	

		binders    = self.free_vars( comp_term_vars )
		scope_vars = self.free_vars( ast_node.facts, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores ) 

		if args:
			scope_vars += self.free_vars( ast_node.guards, compre_binders=compre_binders, uscores=uscores ) 
			scope_vars += self.free_vars( comp_term_ranges, compre_binders=compre_binders, uscores=uscores )

		if compre_binders:
			this_free_vars = scope_vars + binders
		else:
			this_free_vars = []
			for scope_var in scope_vars:
				if not contains_var(scope_var, binders):
					this_free_vars.append( scope_var )
		return this_free_vars

	@visit.when(ast.TermCons)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return []

	@visit.when(ast.TermVar)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return [ast_node]

	@visit.when(ast.TermApp)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return self.free_vars( ast_node.term1, compre_binders=compre_binders, uscores=uscores ) + self.free_vars( ast_node.term2, compre_binders=compre_binders, uscores=uscores )

	@visit.when(ast.TermTuple)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		this_free_vars = []
		for term in ast_node.terms:
			this_free_vars += self.free_vars( term, compre_binders=compre_binders, uscores=uscores )
		return this_free_vars

	@visit.when(ast.TermList)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		this_free_vars = []
		for term in ast_node.terms:
			this_free_vars += self.free_vars( term, compre_binders=compre_binders, uscores=uscores )
		return this_free_vars

	@visit.when(ast.TermListCons)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return self.free_vars( ast_node.term1, compre_binders=compre_binders, uscores=uscores ) + self.free_vars( ast_node.term2, compre_binders=compre_binders, uscores=uscores )

	@visit.when(ast.TermMSet)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		this_free_vars = []
		for term in ast_node.terms:
			this_free_vars += self.free_vars( term, compre_binders=compre_binders, uscores=uscores )
		return this_free_vars

	@visit.when(ast.TermEnumMSet)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		fvs1 = self.free_vars(ast_node.texp1,loc=loc,args=args,compre_binders=compre_binders,uscores=uscores)
		fvs2 = self.free_vars(ast_node.texp2,loc=loc,args=args,compre_binders=compre_binders,uscores=uscores)
		return fvs1 + fvs2

	@visit.when(ast.TermCompre)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		comp_term_vars   = map(lambda comp_range: comp_range.term_vars, ast_node.comp_ranges)
		comp_term_ranges = map(lambda comp_range: comp_range.term_range, ast_node.comp_ranges)	

		binders    = self.free_vars( comp_term_vars )
		scope_vars = self.free_vars( ast_node.term ) + self.free_vars( ast_node.guards ) + self.free_vars( comp_term_ranges )

		if not compre_binders:
			this_free_vars = []
			for scope_var in scope_vars:
				if not contains_var(scope_var, binders):
					this_free_vars.append( scope_var )
		else:
			this_free_vars = scope_vars + binders
		return this_free_vars

	@visit.when(ast.TermBinOp)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return self.free_vars( ast_node.term1, compre_binders=compre_binders, uscores=uscores ) + self.free_vars( ast_node.term2, compre_binders=compre_binders,uscores=uscores )

	@visit.when(ast.TermUnaryOp)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return self.free_vars( ast_node.term, compre_binders=compre_binders,uscores=uscores )

	@visit.when(ast.TermLit)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		return []

	@visit.when(ast.TermUnderscore)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		if not uscores:
			return []
		else:
			return [ast_node]

	@visit.when(ast.AssignDec)
	def free_vars(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		pat_vars = self.free_vars(ast_node.term_pat, uscores=uscores)
		exp_vars = self.free_vars(ast_node.builtin_exp, compre_binders=compre_binders, uscores=uscores)

		if not compre_binders:
			return exp_vars
		else:
			return pat_vars + exp_vars

	def free_var_idxs(self, ast_node, loc=True, args=True, compre_binders=False, uscores=False):
		free_vars = self.free_vars(ast_node, loc=loc, args=args, compre_binders=compre_binders, uscores=uscores)
		return set(map(lambda fv: fv.rule_idx, free_vars))

	def set_vars(self, vs, comp=lambda v: v.rule_idx):
		vs_dict = {}
		for v in vs:
			if comp(v) not in vs_dict:
				vs_dict[comp(v)] = v
		return vs_dict.values()

	def get_all_free_vars(self, ast_node):
		pat_vars = self.set_vars( self.free_vars(ast_node, loc=True, args=True, compre_binders=False) )
		binders  = self.set_vars( self.free_vars(ast_node, loc=False, args=False, compre_binders=True) )
		all_vars = self.set_vars( self.free_vars(ast_node, loc=True, args=True, compre_binders=True) )
		return pat_vars,binders,all_vars

	# Pretty Printer

	@visit.on('ast_node')
	def pretty(self, ast_node, verbose=0):
		pass

	@visit.when(list)
	def pretty(self, ast_node, verbose=0):
		strs = []
		for elem in ast_node:
			strs.append( self.pretty(elem, verbose=verbose) )
		return ','.join(strs)

	@visit.when(ast.TermCons)
	def pretty(self, ast_node, verbose=0):
		if ast_node.inferred_type != None:
			return "<%s::%s>" % (ast_node.name, self.pretty(ast_node.inferred_type, verbose=verbose))
		else:
			return "<%s::??>" % ast_node.name

	@visit.when(ast.TermVar)
	def pretty(self, ast_node, verbose=0):
		if ast_node.inferred_type != None:
			return "<%s::%s>" % (ast_node.name, self.pretty(ast_node.inferred_type, verbose=verbose))
		else:
			return "<%s::??>" % ast_node.name

	@visit.when(ast.TermApp)
	def pretty(self, ast_node, verbose=0):
		p1 = self.pretty(ast_node.term1,verbose=verbose)
		p2 = self.pretty(ast_node.term2,verbose=verbose)
		return "%s %s" % (p1,p2)

	@visit.when(ast.TermTuple)
	def pretty(self, ast_node, verbose=0):
		ps = map(lambda t: self.pretty(t,verbose=verbose), ast_node.terms)
		return "(%s)" % (','.join(ps))

	@visit.when(ast.TermList)
	def pretty(self, ast_node, verbose=0):
		ps = map(lambda t: self.pretty(t,verbose=verbose), ast_node.terms)
		return "[%s]" % (','.join(ps))

	@visit.when(ast.TermListCons)
	def pretty(self, ast_node, verbose=0):
		p1 = self.pretty(ast_node.term1,verbose=verbose)
		p2 = self.pretty(ast_node.term2,verbose=verbose)
		return "[%s|%s]" % (p1,p2)

	@visit.when(ast.TermMSet)
	def pretty(self, ast_node, verbose=0):
		ps = map(lambda t: self.pretty(t,verbose=verbose), ast_node.terms)
		return "{%s}" % (','.join(ps))

	@visit.when(ast.TermEnumMSet)
	def pretty(self, ast_node, verbose=0):
		p1 = self.pretty(ast_node.texp1, verbose=verbose)
		p2 = self.pretty(ast_node.texp2, verbose=verbose)
		return "{%s..%s}" % (p1,p2)

	@visit.when(ast.CompRange)
	def pretty(self, ast_node, verbose=0):
		p1 = self.pretty(ast_node.term_vars,verbose=verbose)
		p2 = self.pretty(ast_node.term_range,verbose=verbose)
		return "%s <- %s" % (p1,p2)

	@visit.when(ast.TermCompre)
	def pretty(self, ast_node, verbose=0):
		p = self.pretty(ast_node.term, verbose=verbose)
		ps2 = ','.join( map(lambda c: self.pretty(c,verbose=verbose), ast_node.comp_ranges) )
		ps3 = ','.join( map(lambda g: self.pretty(g,verbose=verbose), ast_node.guards) )
		if len(ast_node.comp_ranges) > 0 and len(ast_node.guards) > 0:
			return "{%s|%s.%s}" % (p,ps2,ps3)
		elif len(ast_node.comp_ranges) > 0 and len(ast_node.guards) == 0:
			return "{%s|%s}" % (p,ps2)
		elif len(ast_node.comp_ranges) == 0 and len(ast_node.guards) > 0:
			return "{%s|%s}" % (p,ps3)
		else:
			return "{%s}" % p

	@visit.when(ast.FactCompre)
	def pretty(self, ast_node, verbose=0):
		ps1 = ','.join( map(lambda f: self.pretty(f,verbose=verbose), ast_node.facts) )
		ps2 = ','.join( map(lambda c: self.pretty(c,verbose=verbose), ast_node.comp_ranges) )
		ps3 = ','.join( map(lambda g: self.pretty(g,verbose=verbose), ast_node.guards) )
		if len(ast_node.comp_ranges) > 0 and len(ast_node.guards) > 0:
			return "{%s|%s.%s}" % (ps1,ps2,ps3)
		elif len(ast_node.comp_ranges) > 0 and len(ast_node.guards) == 0:
			return "{%s|%s}" % (ps1,ps2)
		elif len(ast_node.comp_ranges) == 0 and len(ast_node.guards) > 0:
			return "{%s|%s}" % (ps1,ps3)
		else:
			return "{%s}" % ps1

	@visit.when(ast.TermBinOp)
	def pretty(self, ast_node, verbose=0):
		p1 = self.pretty(ast_node.term1,verbose=verbose)
		p2 = self.pretty(ast_node.term2,verbose=verbose)
		return "%s%s%s" % (p1,ast_node.op,p2)
		
	@visit.when(ast.TermUnaryOp)
	def pretty(self, ast_node, verbose=0):
		p = self.pretty(ast_node.term,verbose=verbose)
		return "%s%s" % (ast_node.op,p)

	@visit.when(ast.TermLit)
	def pretty(self, ast_node, verbose=0):
		return str(ast_node.literal)

	@visit.when(ast.TermUnderscore)
	def pretty(self, ast_node, verbose=0):
		return "_"

	@visit.when(ast.FactBase)
	def pretty(self, ast_node, verbose=0):
		ps = map(lambda t: self.pretty(t,verbose=verbose),ast_node.terms)
		return "%s(%s)" % (ast_node.name,','.join(ps))

	@visit.when(ast.TypeVar)
	def pretty(self, ast_node, verbose=0):
		return ast_node.name

	@visit.when(ast.TypeCons)
	def pretty(self, ast_node, verbose=0):
		return ast_node.name

	@visit.when(ast.TypeApp)
	def pretty(self, ast_node, verbose=0):
		return "%s %s" % (self.pretty(ast_node.type1, verbose=verbose),self.pretty(ast_node.type2, verbose=verbose))

	@visit.when(ast.TypeArrow)
	def pretty(self, ast_node, verbose=0):
		return "%s -> %s" % (self.pretty(ast_node.type1, verbose=verbose),self.pretty(ast_node.type2, verbose=verbose))

	@visit.when(ast.TypeTuple)
	def pretty(self, ast_node, verbose=0):
		return "(%s)" % ( ','.join(map(lambda t: self.pretty(t, verbose=verbose),ast_node.types)) )

	@visit.when(ast.TypeList)
	def pretty(self, ast_node, verbose=0):
		return "[%s]" % (self.pretty(ast_node.type, verbose=verbose))

	@visit.when(ast.TypeMSet)
	def pretty(self, ast_node, verbose=0):
		return "{%s}" % (self.pretty(ast_node.type, verbose=verbose))

	@visit.on( 'head' )
	def partition_rule_heads(self, head):
		pass

	@visit.when( list )
	def partition_rule_heads(self, head):
		if len(head) == 0:
			return ([],[],[],[])
		ts1 = None
		for h in head:
			ts2 = self.partition_rule_heads( h )
			if ts1 == None:
				ts1 = ts2
			else:
				ts1 = tmerge(ts1, ts2)
		return ts1

	@visit.when( ast.FactBase )
	def partition_rule_heads(self, head):
		return ([head],[],[],[])

	@visit.when( ast.FactLoc )
	def partition_rule_heads(self, head):
		return ([],[head],[],[])

	@visit.when( ast.FactLocCluster )
	def partition_rule_heads(self, head):
		return ([],[],[head],[])

	@visit.when( ast.FactCompre )
	def partition_rule_heads(self, head):
		return ([],[],[],[head])

	@visit.on( 'fact' )
	def get_base_facts(self, fact):
		pass

	@visit.when( list )
	def get_base_facts(self, fact):
		bfs = []
		for f in fact:
			bfs += self.get_base_facts(f)
		return bfs

	@visit.when( ast.FactBase )
	def get_base_facts(self, fact):
		return [fact]

	@visit.when( ast.FactLoc )
	def get_base_facts(self, fact):
		return [fact.fact]

	@visit.when( ast.FactLocCluster )
	def get_base_facts(self, fact):
		return foldl(map(lambda f: self.get_base_facts(f), fact.facts), [])

	@visit.when( ast.FactCompre )
	def get_base_facts(self, fact):
		return foldl(map(lambda f: self.get_base_facts(f), fact.facts), [])

	@visit.on( 'fact' )
	def get_fact_name(self, fact):
		pass

	@visit.when( ast.FactBase )
	def get_fact_name(self, fact):
		return fact.name

	@visit.when( ast.FactLoc )
	def get_fact_name(self, fact):
		return fact.fact.name

	# Recursively check a term if it contains any sub-terms of the given term types.
	@visit.on( 'term' )
	def has_sub_terms_of(self, term, term_types):
		pass

	@visit.when( ast.TermCons )
	def has_sub_terms_of(self, term, term_types):
		return term.term_type in term_types

	@visit.when( ast.TermVar )
	def has_sub_terms_of(self, term, term_types):
		return term.term_type in term_types

	@visit.when( ast.TermApp )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			return self.has_sub_terms_of(term.term1, term_types) or self.has_sub_terms_of(term.term2, term_types)

	@visit.when( ast.TermTuple )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			for t in term.terms:
				if self.has_sub_terms_of(t, term_types):
					return True
			return False

	@visit.when( ast.TermList )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			for t in term.terms:
				if self.has_sub_terms_of(t, term_types):
					return True
			return False

	@visit.when( ast.TermListCons )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			return self.has_sub_terms_of(term.term1, term_types) or self.has_sub_terms_of(term.term2, term_types)

	@visit.when( ast.TermMSet )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			for t in term.terms:
				if self.has_sub_terms_of(t, term_types):
					return True
			return False

	@visit.when( ast.TermEnumMSet )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			return self.has_sub_terms_of(term.texp1, term_types) or self.has_sub_terms_of(term.texp2, term_types)

	@visit.when( ast.TermCompre )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			if self.has_sub_terms_of(term.term, term_types):
				return True
			for g in term.guards:
				if self.has_sub_terms_of(g, term_types):
					return True
			for crange in term.comp_ranges:
				if self.has_sub_terms_of(crange.term_range, term_types):
					return True
			return False

	@visit.when( ast.TermBinOp )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			return self.has_sub_terms_of(term.term1, term_types) or self.has_sub_terms_of(term.term2, term_types)

	@visit.when( ast.TermUnaryOp )
	def has_sub_terms_of(self, term, term_types):
		if term.term_type in term_types:
			return True
		else:
			return self.has_sub_terms_of(term.term, term_types)

	@visit.when( ast.TermLit )
	def has_sub_terms_of(self, term, term_types):
		return term.term_type in term_types

	@visit.when( ast.TermUnderscore )
	def has_sub_terms_of(self, term, term_types):
		return term.term_type in term_types

	def is_normal_form(self, term):
		non_normal_forms = [ast.TERM_CONS, ast.TERM_APP, ast.TERM_COMPRE, ast.TERM_BINOP, ast.TERM_UNAOP]
		return not self.has_sub_terms_of(term, non_normal_forms)

	@visit.on( 'ast_node' )
	def flatten_term(self, ast_node, accept_nodes=DEFAULT_ACCEPT_NODES, expand_nodes=DEFAULT_EXPAND_NODES):
		pass

	@visit.when( list )
	def flatten_term(self, ast_node, accept_nodes=DEFAULT_ACCEPT_NODES, expand_nodes=DEFAULT_EXPAND_NODES):
		terms = []
		for node in ast_node:
			terms += self.flatten_term(node, accept_nodes=accept_nodes, expand_nodes=expand_nodes)
		return terms

	@visit.when( ast.TermVar )
	def flatten_term(self, ast_node, accept_nodes=DEFAULT_ACCEPT_NODES, expand_nodes=DEFAULT_EXPAND_NODES):
		if ast.TERM_VAR in accept_nodes:
			return [ast_node]
		else:
			return []

	@visit.when( ast.TermLit )
	def flatten_term(self, ast_node, accept_nodes=DEFAULT_ACCEPT_NODES, expand_nodes=DEFAULT_EXPAND_NODES):
		if ast.TERM_LIT in accept_nodes:
			return [ast_node]
		else:
			return []

	@visit.when( ast.TermTuple )
	def flatten_term(self, ast_node, accept_nodes=DEFAULT_ACCEPT_NODES, expand_nodes=DEFAULT_EXPAND_NODES):
		if ast.TERM_TUPLE in accept_nodes:
			return [ast_node]
		elif ast.TERM_TUPLE in expand_nodes:
			return self.flatten_term(ast_node.terms, accept_nodes=accept_nodes, expand_nodes=expand_nodes)
		else:
			return []

	@visit.when( ast.TermBinOp )
	def flatten_term(self, ast_node, accept_nodes=DEFAULT_ACCEPT_NODES, expand_nodes=DEFAULT_EXPAND_NODES):
		if ast.TERM_BINOP in accept_nodes:
			return [ast_node]
		elif ast.TERM_BINOP in expand_nodes:
			return self.flatten_term([ast_node.term1,ast_node.term2], accept_nodes=accept_nodes, expand_nodes=expand_nodes)
		else:
			return []

	@visit.on( 'term' )
	def unfold_term_seq(self, term):
		pass

	@visit.when( list )
	def unfold_term_seq(self, term):
		ts = []
		for t in term:
			ts = ts + self.unfold_term_seq(t)
		return ts

	@visit.when( ast.TermLit )
	def unfold_term_seq(self, term):
		return [term]

	@visit.when( ast.TermVar )
	def unfold_term_seq(self, term):
		return [term]

	@visit.when( ast.TermUnderscore )
	def unfold_term_seq(self, term):
		return [term]

	@visit.when( ast.TermTuple )
	def unfold_term_seq(self, term):
		ts = []
		for t in term.terms:
			ts = ts + self.unfold_term_seq(t) 
		return ts

# Auxiliary operations

def contains_var(term_var, context):
	for elem in context:
		if term_var.name == elem.name:
			return True
	return False


