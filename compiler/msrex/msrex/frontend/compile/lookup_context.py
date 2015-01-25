
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
from msrex.misc.aggregators import foldl

from msrex.frontend.analyze.inspectors import Inspector

from msrex.frontend.compile.rule_facts import FactDirectory, SIMP_HEAD, PROP_HEAD, FactAtomHead, FactCompreHead, FactAtomBody, FactCompreBody
from msrex.frontend.compile.rule_guards import process_guard, NON_IDX_GRD, EQ_GRD, MEM_GRD, ORD_GRD, EqGuard

# Lookup Context

def emptyset():
	return set([])

ORD_LEQ = 'leq'
ORD_GEQ = 'geq'
ORD_LT  = 'lt'
ORD_GT  = 'gt'

INPUT  = '+'
OUTPUT = '-'

class LookupTables:

	def __init__(self, fact_dir):
		self.fact_dir = fact_dir
		self.lookup_tables = {}
		self.linear_table_indices = {}
		for fact_idx in fact_dir.getIndices():
			self.lookup_tables[ fact_idx ] = []
		
	def registerLookup(self, new_lookup):
		table_idx = 0
		for curr_lookup in self.lookup_tables[ new_lookup.pred_idx ]:
			if new_lookup == curr_lookup:
				new_lookup.setLookupIdx( table_idx )
				if new_lookup.type == LINEAR_LK:
					self.linear_table_indices[new_lookup.pred_idx] = table_idx
				return table_idx
			table_idx += 1
		new_lookup.setLookupIdx( table_idx )
		self.lookup_tables[new_lookup.pred_idx].append( new_lookup )
		if new_lookup.type == LINEAR_LK:
			self.linear_table_indices[new_lookup.pred_idx] = table_idx
		return table_idx

	def linear_lookup_index(self, fact_idx):
		# print self.linear_table_indices
		return self.linear_table_indices[fact_idx]

	def padWithLinearLookup(self):
		for fact_idx in self.lookup_tables:
			if fact_idx not in self.linear_table_indices:
				name = self.fact_dir.getFactFromIdx( fact_idx ).name
				linear_lookup = LinearLookup(self.fact_dir, name)
				table_idx = len(self.lookup_tables[fact_idx])
				linear_lookup.setLookupIdx(table_idx)
				self.lookup_tables[fact_idx].append( linear_lookup )
				self.linear_table_indices[fact_idx] = table_idx				

			'''
			if len(self.lookup_tables[fact_idx]) == 0:
				name = self.fact_dir.getFactFromIdx( fact_idx ).name
				linear_lookup = LinearLookup(self.fact_dir, name)
				linear_lookup.setLookupIdx(0)
				self.lookup_tables[fact_idx].append( linear_lookup )
			'''

	def padWithExportedLookup(self):
		for fact_idx,fact_dec in self.fact_dir.fact_name_dict.values():
			name = fact_dec.name
			for fact in fact_dec.exported_queries:
				linear_lookup = LinearLookup(self.fact_dir, name, exported=True)
				table_idx = len(self.lookup_tables[fact_idx])
				linear_lookup.setLookupIdx(table_idx)
				self.lookup_tables[fact_idx].append( linear_lookup )
				self.linear_table_indices[fact_idx] = table_idx	

	def __repr__(self):
		strs = "========== Lookup Tables ==========\n"
		for pred_idx,lookups in self.lookup_tables.items():
			fact_dec = self.fact_dir.getFactFromIdx(pred_idx)
			strs += "%s : %s\n" % (pred_idx,fact_dec.name)
			for lookup in lookups:
				strs += "  %s : %s\n" % (lookup.lookup_idx, lookup.__repr__())
		strs += "==================================="
		return strs

class LookupContext:

	def __init__(self, fact_dir):
		self.bs_eq_ctxt = emptyset()
		self.eq_ctxt  = emptyset()
		self.mem_grds = []
		self.ord_grds = []
		self.eq_grds  = []
		self.non_idx_grds = []
		self.inspect  = Inspector()
		self.fact_dir = fact_dir

	def __repr__(self):
		strs  = "======== Lookup Context ========\n"
		strs += "BootStrap Eqs: %s\n" % self.bs_eq_ctxt
		strs += "Eqs: %s\n" % self.eq_ctxt
		all_grds = self.mem_grds + self.ord_grds + self.eq_grds + self.non_idx_grds
		if len(all_grds) > 0:
			strs += "Guards: %s\n" % (','.join(map(lambda g: g.__repr__(), all_grds)))
		strs += "================================"
		return strs

	def varCtxt(self):
		return self.eq_ctxt | self.bs_eq_ctxt

	def removeBootStrapped(self):
		self.bs_eq_ctxt = emptyset()

	def addFactHead(self, head, boot_strap=False):
		if head.is_atom:
			free_vars = self.inspect.free_var_idxs( head.fact )
		else:
			free_vars  =  self.inspect.free_var_idxs( head.fact.facts[0] ) 
			if not boot_strap:
				free_vars |= self.inspect.free_var_idxs( map(lambda cr: cr.term_range, head.fact.comp_ranges) )
		if not boot_strap:
			self.eq_ctxt = self.eq_ctxt | free_vars
		else:
			self.bs_eq_ctxt = self.bs_eq_ctxt | free_vars

	def addVars(self, term_vars, boot_strap=False):
		free_vars = self.inspect.free_var_idxs( term_vars )
		if not boot_strap:
			self.eq_ctxt = self.eq_ctxt | free_vars
		else:
			self.bs_eq_ctxt = self.bs_eq_ctxt | free_vars

	def addGuard(self, guard):
		if guard.indexable():
			if guard.type == MEM_GRD:
				self.mem_grds.append( guard )
			elif guard.type == ORD_GRD:
				self.ord_grds.append( guard )
			elif guard.type == EQ_GRD:
				self.eq_grds.append( guard )
			else:
				self.non_idx_grds.append( guard )
		else:
			self.non_idx_grds.append( guard )

	def scheduleGuards(self):
		sch_grds = []

		new_eq_grds = []
		for eq_grd in self.eq_grds:
			if eq_grd.scheduleAsGuard( self.varCtxt() ):
				sch_grds.append( eq_grd )
			else:
				new_eq_grds.append( eq_grd )
		self.eq_grds = new_eq_grds

		new_ord_grds = []
		for ord_grd in self.ord_grds:
			if ord_grd.scheduleAsGuard( self.varCtxt() ):
				sch_grds.append( ord_grd )
			else:
				new_ord_grds.append( ord_grd )
		self.ord_grds = new_ord_grds

		new_mem_grds = []
		for mem_grd in self.mem_grds:
			if mem_grd.scheduleAsGuard( self.varCtxt() ):
				sch_grds.append( mem_grd )
			else:
				new_mem_grds.append( mem_grd )
		self.mem_grds = new_mem_grds

		new_non_idx_grds = []
		for non_idx_grd in self.non_idx_grds:
			if non_idx_grd.scheduleAsGuard( self.varCtxt() ):
				sch_grds.append( non_idx_grd )
			else:
				new_non_idx_grds.append( non_idx_grd )
		self.non_idx_grds = new_non_idx_grds

		return sch_grds

	def bestLookupOption(self, new_head_info):
		curr_best_head_idx = -1
		curr_best_lookup   = None
		curr_best_cost     = (10000,0,0)
		curr_best_head     = None
		for head_idx,new_head in new_head_info.items():
			lookups = self.lookupOptions(new_head)
			if lookups[0].cost() < curr_best_cost:
				curr_best_head_idx = head_idx
				curr_best_lookup = lookups[0]
				curr_best_cost   = lookups[0].cost()
				curr_best_head   = new_head
	
		return (curr_best_head_idx, curr_best_lookup)

	def remove_guards(self, rm_grds):
		self.eq_grds  = filter(lambda g: g not in rm_grds, self.eq_grds)
		self.mem_grds = filter(lambda g: g not in rm_grds, self.mem_grds)
		self.ord_grds = filter(lambda g: g not in rm_grds, self.ord_grds)
		self.non_idx_grds = filter(lambda g: g not in rm_grds, self.non_idx_grds)

	# Current implementation ignores Eq guards.
	def lookupOptions(self, new_head):
		if new_head.is_atom:
			loc_fact = new_head.fact
			head_eq_grds  = []
			head_mem_grds = []
			head_ord_grds = [] 
		else:
			loc_fact = new_head.fact.facts[0]
			head_eq_grds  = new_head.eq_grds
			head_mem_grds = new_head.mem_grds
			head_ord_grds = new_head.ord_grds
		pred_idx,_ = self.fact_dir.getFactFromName( loc_fact.fact.name )

		lookup_opts = [ LinearLookup(self.fact_dir, loc_fact.fact.name) ]
		free_vars = self.inspect.free_var_idxs( loc_fact )
		join_vars = self.varCtxt() & free_vars
		new_vars  = free_vars - self.varCtxt()
		
		# Add a hash lookup if the new head has overlapping variables with the current
		# variable context.
		if len(join_vars) > 0:
			hash_lookup = HashLookup(self.fact_dir, loc_fact, join_vars)
			lookup_opts.append( hash_lookup )

		# TODO: Mem guard lookup and ord guard lookup omitted for now.
		'''
		# Add member lookup if the head has overlapping variables with a member guard
		for mem_guard in self.mem_grds + head_mem_grds:
			index_info = mem_guard.scheduleAsIndex( self.varCtxt() )
			if index_info != None:
				input_vars,output_vars,_ = index_info
				if len(new_vars & output_vars) > 0:
					mem_lookup = MemLookup(self.fact_dir, loc_fact, mem_guard, self.varCtxt())
					lookup_opts.append( mem_lookup )

		# Add order lookup
		for ord_guard in self.ord_grds + head_ord_grds:
			index_info = ord_guard.scheduleAsIndex( self.varCtxt() )
			if index_info != None:
				input_vars,output_vars,is_left_input = index_info
				if len(new_vars & output_vars) > 0:
					ord_lookup = OrdLookup(self.fact_dir, loc_fact, ord_guard, is_left_input, self.varCtxt())
					lookup_opts.append( ord_lookup )
		'''
	
		return sorted(lookup_opts, key=lambda lk: lk.cost())

def show_pat(p,alt='_'):
	return '%s' % p if p != None else alt


# Currently implementation only allows pure variables for arguments
class LookupTechnique:

	def initialize(self, lookup_type, pred_idx, fact_dir, lookup_name, pred_args, guard_args
                      ,guard_str='.', assoc_guards=[], exported=False):
		self.type = lookup_type
		self.pred_idx    = pred_idx
		self.pred_name   = fact_dir.getFactFromIdx( pred_idx ).name
		self.lookup_name = lookup_name
		# var_ctxt = {}
		# var_idx  = 0
		'''
		for x in range(0,len(pred_args)):
			pred_arg = pred_args[x]
			if pred_arg != None:
				var = '#i%s' % var_idx
				var_ctxt[pred_arg.name] = var
				var_idx += 1
				pred_args[x] = var 
				pass
			else:
				pred_args[x] = OUTPUT
		'''
		self.pred_args   = pred_args
		self.guard_args = guard_args
		self.guard_str  = guard_str
		self.assoc_guards = assoc_guards
		self.exported = exported

	def signature(self):
		var_ctxt = {}
		var_idx  = 0
		sign_args = []
		for arg in self.pred_args + self.guard_args:
			if isinstance(arg, str):
				sign_args.append( arg )
			elif hasattr(arg, 'rule_idx'):
				if arg.rule_idx in var_ctxt:
					sign_args.append( var_ctxt[arg.rule_idx] )
				else:
					new_idx = var_idx
					var_ctxt[arg.rule_idx] = new_idx
					var_idx += 1
					sign_args.append( new_idx )
			else:
				sign_args.append( arg.term_type )
		return sign_args

	def __eq__(self, other):
		if self.type == other.type and self.pred_idx == other.pred_idx and self.lookup_name == other.lookup_name:
			return self.signature() == other.signature()
		else:
			return False

	def setLookupIdx(self, lookup_idx):
		self.lookup_idx = lookup_idx

	def outputVars(self, head):
		if head.is_atom:
			head_atom = head.fact
		else:
			head_atom = head.fact.facts[0]
		head_args = [head_atom.loc] + head_atom.fact.terms
		output_vars = []
		seen = {}
		for i in range(0,len(self.pred_args)):
			pred_arg = self.pred_args[i]
			if isinstance(pred_arg, str) and pred_arg == INPUT:
				pass 
			elif isinstance(pred_arg, str) and pred_arg == OUTPUT:
				output_vars.append( head_args[i] )
			else:
				if pred_arg.rule_idx not in seen:
					output_vars.append( head_args[i] )
					seen[pred_arg.rule_idx] = ()

		inspect = Inspector()
		this_args = []
		for assoc_guard in self.assoc_guards:
			this_args += inspect.free_vars( assoc_guard.term1 ) + inspect.free_vars( assoc_guard.term2 )
		for i in range(0,len(self.guard_args)):
			guard_arg = self.guard_args[i]
			if isinstance(guard_arg, str) and guard_arg == INPUT:
				pass 
			elif isinstance(guard_arg, str) and guard_arg == OUTPUT:
				output_vars.append( this_args[i] )
			elif guard_arg.rule_idx not in seen:
				output_vars.append( this_args[i] )
				seen[guard_arg.rule_idx] = ()

		return output_vars

	def outputVarsModuloDependencies(self, head, var_gen):
		output_vars = self.outputVars( head )
		dep_grds = []
		alpha_output_vars = []
		for output_var in output_vars:
			if output_var.rule_idx in self.var_dependencies:
				alpha_output_var = ast.TermVar( output_var.name )
				alpha_output_var.rule_idx = var_gen.get_next_var_idx()
				alpha_output_vars.append( alpha_output_var )
				dep_grds.append( EqGuard(ast.TermBinOp(output_var, ast.EQ, alpha_output_var)) )
			else:
				alpha_output_vars.append( output_var )
		return (alpha_output_vars, dep_grds)

	def inputVars(self, head):
		if head.is_atom:
			head_atom = head.fact
		else:
			head_atom = head.fact.facts[0]
		head_args = [head_atom.loc] + head_atom.fact.terms
		input_vars = []
		for i in range(0,len(self.pred_args)):
			pred_arg = self.pred_args[i]
			if isinstance(pred_arg, str) and pred_arg == INPUT:
				input_vars.append( head_args[i] )
	
		inspect = Inspector()
		this_args = []
		for assoc_guard in self.assoc_guards:
			# this_args += inspect.free_vars( assoc_guard.term1 ) + inspect.free_vars( assoc_guard.term2 )
			this_args += inspect.flatten_term( assoc_guard.term1 ) + inspect.flatten_term( assoc_guard.term2 )
			# this_args += inspect.flatten_term( assoc_guard )
		for i in range(0,len(self.guard_args)):
			guard_arg = self.guard_args[i]
			if isinstance(guard_arg, str) and guard_arg == INPUT:
				input_vars.append( this_args[i] )

		return input_vars

	def cost(self):
		return (self.type,0,0)

	def __repr__(self):
		arg_str = ','.join(map(lambda a: show_pat(a,alt=OUTPUT),self.pred_args[1:]))
		extern = "" if not self.exported else "is external view"
		return "%s:%s:%s<[%s]%s(%s)|%s> %s" % (self.pred_idx,self.lookup_idx,self.lookup_name,
                                                       show_pat(self.pred_args[0],alt=OUTPUT),
                                                       self.pred_name,arg_str,self.guard_str % tuple(self.guard_args),extern)	

	def lookupArgIndices(self):
		idxs = []
		for i in range(0,len(self.pred_args)):
			pred_arg = self.pred_args[i]
			# TODO: Handle mem and ord
			if isinstance(pred_arg, str):
				if pred_arg == INPUT:
					idxs.append(i)
		return idxs



HASH_LK = 1
MEM_LK  = 2
ORD_LK  = 3
LOC_HASH_LK = 4
LINEAR_LK = 5


# linear(pid:[_]p(_)|.)
class LinearLookup(LookupTechnique):
	def __init__(self, fact_dir, name, exported=False):
		pred_idx,_ = fact_dir.getFactFromName( name )
		num_args = fact_dir.getCardinality( pred_idx )
		pred_args = []
		for i in range(0,num_args+1):
			pred_args.append( OUTPUT )
		self.var_dependencies = emptyset()
		self.initialize(LINEAR_LK, pred_idx, fact_dir, "linear", pred_args, [], exported=exported)		

# hash(pid:[loc]p(args)|.)
class HashLookup(LookupTechnique):
	def __init__(self, fact_dir, loc_fact, join_vars):
		pred_idx,_ = fact_dir.getFactFromName( loc_fact.fact.name )
		degree_freedom = 0
		degree_join    = 0
		ppred_args = []
		non_loc_hash_index = False
		curr_index = 0
		for pred_arg in [loc_fact.loc] + loc_fact.fact.terms:
			if pred_arg.rule_idx in join_vars:
				ppred_args.append( INPUT )
				degree_join += 1
				if curr_index > 0:
					non_loc_hash_index = True				
			else:
				ppred_args.append( OUTPUT )
				degree_freedom += 1
			curr_index += 1
		self.degree_join    = degree_join
		self.degree_freedom = degree_freedom
		self.var_dependencies = emptyset()
		if non_loc_hash_index:
			hash_type = HASH_LK
		else:
			hash_type = LOC_HASH_LK
		self.initialize(hash_type, pred_idx, fact_dir, "hash", pred_args=ppred_args, guard_args=[], assoc_guards=[])
	def cost(self):
		return (self.type,self.degree_freedom,-self.degree_join)

# mem(pid:[loc]p(args)| (mem_args) in <->)
class MemLookup(LookupTechnique):
	def __init__(self, fact_dir, loc_fact, mem_guard, var_ctxt):
		pred_idx,_ = fact_dir.getFactFromName( loc_fact.fact.name )
		inspect = Inspector()
		fact_vars = inspect.free_var_idxs(loc_fact.loc) | inspect.free_var_idxs(loc_fact.fact) 
		mem_vars  = inspect.free_var_idxs(mem_guard.term1)
		common_vars = fact_vars & mem_vars
		self.degree_join = len(common_vars)
		degree_freedom = 0

		# Existing dependencies from variable context
		self.var_dependencies = (fact_vars | mem_vars) & var_ctxt
		
		has_hash_index = False
		ppred_args = []
		for pred_arg in [loc_fact.loc] + loc_fact.fact.terms:
			if pred_arg.rule_idx in self.var_dependencies:
				ppred_args.append( INPUT )
				has_hash_index = True
			elif pred_arg.rule_idx in common_vars:
				ppred_args.append( pred_arg )
			else:
				ppred_args.append( OUTPUT )
				degree_freedom += 1
		guard_args = []
		for mem_arg in inspect.free_vars(mem_guard.term1):
			if pred_arg.rule_idx in self.var_dependencies:
				ppred_args.append( INPUT )
				has_hash_index = True
			elif mem_arg.rule_idx in common_vars:
				guard_args.append( mem_arg )
			else:
				guard_args.append( OUTPUT )
				degree_freedom += 1
		guard_args.append( INPUT )
		guard_str =  '(%s) in %s' % (','.join( map(lambda _: '%s',range(0,len(guard_args)-1)) ),'%s')
		self.degree_freedom = degree_freedom
		if has_hash_index:
			lk_name = "hash+mem"
		else:
			lk_name = "mem"
		self.initialize(MEM_LK, pred_idx, fact_dir, lk_name, pred_args=ppred_args, guard_args=guard_args, guard_str=guard_str
                               ,assoc_guards=[mem_guard])
	def cost(self):
		return (self.type,self.degree_freedom,-self.degree_join)

# ord(pid:[loc]p(args)| larg <op> garg)
# op is either < or <=
class OrdLookup(LookupTechnique):
	def __init__(self, fact_dir, loc_fact, ord_guard, is_left_input, var_ctxt):
		pred_idx,_ = fact_dir.getFactFromName( loc_fact.fact.name )
		inspect = Inspector()
		fact_vars = inspect.free_var_idxs(loc_fact.loc) | inspect.free_var_idxs(loc_fact.fact)
		self.degree_freedom = len(fact_vars) - 1
		self.degree_join    = 1
		ord_vars = inspect.free_var_idxs( ord_guard.term1 ) | inspect.free_var_idxs( ord_guard.term2 )
		self.var_dependencies = (fact_vars | ord_vars) & var_ctxt
		has_hash_index = False
		pred_args = []
		for pred_arg in [loc_fact.loc] + loc_fact.fact.terms:
			if pred_arg.rule_idx in self.var_dependencies:
				pred_args.append( INPUT )
				has_hash_index = True
			elif pred_arg.rule_idx in ord_vars:
				pred_args.append( pred_arg ) 
			else:
				pred_args.append( OUTPUT )
		if is_left_input:
			guard_args = [INPUT, ord_guard.term2]
		else:
			guard_args = [ord_guard.term1, INPUT]
		op = '<=' if ord_guard.include_eq else '<'
		guard_str = '%s %s %s' % ('%s',op,'%s')
		if has_hash_index:
			lk_name = "hash+ord"
		else:
			lk_name = "ord"
		self.initialize(ORD_LK, pred_idx, fact_dir, lk_name, pred_args=pred_args, guard_args=guard_args, guard_str=guard_str
                               ,assoc_guards=[ord_guard])
	def cost(self):
		return (self.type,self.degree_freedom,-self.degree_join)


