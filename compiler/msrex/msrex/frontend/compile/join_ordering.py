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

from msrex.frontend.compile.rule_facts import FactDirectory, SIMP_HEAD, PROP_HEAD, FactAtomHead, FactCompreHead, FactAtomBody, FactCompreBody
from msrex.frontend.compile.rule_guards import process_guard
from msrex.frontend.compile.rules import Rule
from msrex.frontend.compile.lookup_context import ORD_LEQ, ORD_GEQ, ORD_LT, ORD_GT, LookupContext, LookupTables, LinearLookup, HashLookup, MemLookup, OrdLookup

from collections import defaultdict

def head_idx_str(idx):
	return "#H%s" % idx

# Match Tasks

MT_INDEX = 0
def get_next_matchtask_index():
	global MT_INDEX
	new_id = MT_INDEX
	MT_INDEX += 1
	return new_id

class MatchTask:
	def initialize(self, ast_node=None):
		self.id = get_next_matchtask_index()
		if ast_node != None:
			inspect = Inspector()
			self.free_vars = inspect.free_vars( ast_node )

class ActiveAtom(MatchTask):
	def __init__(self, head, head_idx):
		self.initialize(head.fact)
		self.head_idx = head_idx
		self.output_vars = self.free_vars
		self.head = head
		self.fact = head.fact
	def __repr__(self):
		return "Active %s %s" % (head_idx_str(self.head_idx),self.fact)

class ActiveCompre(MatchTask):
	def __init__(self, head, head_idx):
		self.initialize(head.fact)
		self.head_idx = head_idx
		self.fact = head.fact.facts[0]
		self.fact_pat = head.fact_pat
		self.head = head
		self.compre = head.fact
		inspect = Inspector()
		self.output_vars =  inspect.free_vars( self.fact )
		self.compre_binders = inspect.free_vars( head.fact, loc=False, args=False, compre_binders=True )
	def __repr__(self):
		return "Active %s %s" % (head_idx_str(self.head_idx),self.fact)

class CheckGuard(MatchTask):
	def __init__(self, guard):
		self.initialize()
		self.guard = guard
	def __repr__(self):
		return "CheckGuard %s" % (self.guard)

class FilterGuard(MatchTask):
	def __init__(self, term_vars, compre_dom, head_idx, guards, init_binders=False):
		self.initialize()
		self.term_vars  = term_vars
		# print "HG HG: %s" % term_vars
		self.compre_dom = compre_dom
		self.head_idx = head_idx
		self.guards = guards
		self.init_binders=init_binders
	def __repr__(self):
		return "FilterGuard %s %s" % (head_idx_str(self.head_idx), ','.join(map(lambda g: "%s" % g,self.guards)) )

class LookupAtom(MatchTask):
	def __init__(self, head, head_idx, lookup, var_gen):
		self.initialize()
		self.head_idx = head_idx
		self.head = head
		self.fact = head.fact
		self.lookup = lookup
		self.input_vars  = lookup.inputVars(head)
		# output_vars,dep_grds = lookup.outputVarsModuloDependencies(head, var_gen)
		self.output_vars = lookup.outputVars(head)
		# self.dep_grds = dep_grds
	def __repr__(self):
		ivs = ','.join( map(lambda v:'%s'%v, self.input_vars) )
		return "LookupAtom %s %s %s %s" % (head_idx_str(self.head_idx), self.lookup, ivs, self.head.fact_pat)

class LookupAll(MatchTask):
	def __init__(self, head, head_idx, lookup, var_gen):
		self.initialize()
		inspect = Inspector()
		self.term_vars  = inspect.free_vars(head.fact.comp_ranges[0].term_vars)
		self.compre_dom = head.fact.comp_ranges[0].term_range
		self.lookup = lookup
		self.input_vars  = lookup.inputVars(head)
		# output_vars,dep_grds = lookup.outputVarsModuloDependencies(head, var_gen)
		self.output_vars = lookup.outputVars(head)
		# self.dep_grds = dep_grds
		self.head_idx = head_idx
		self.head = head
		self.fact = head.fact
		self.fact_pat = head.fact_pat
	def __repr__(self):
		# tvs = ','.join( map(lambda v:'%s'%v, self.term_vars) )
		ivs = ','.join( map(lambda v:'%s'%v, self.input_vars) )
		return "LookupAll %s %s %s %s" % (head_idx_str(self.head_idx), self.lookup, ivs, self.head.fact_pat)

class CompreDomain(MatchTask):
	def __init__(self, head, head_idx, init_binders=False):
		inspect = Inspector()
		self.head = head
		self.head_idx = head_idx
		self.term_vars  = inspect.free_vars(head.fact.comp_ranges[0].term_vars)
		self.compre_dom = head.fact.comp_ranges[0].term_range
		self.init_binders = init_binders
	def __repr__(self):
		tvs = ','.join( map(lambda v:'%s'%v, self.term_vars) )
		return "CompreDomain %s %s %s %s" % (head_idx_str(self.head_idx), tvs, self.compre_dom, self.head.fact_pat)

class NeqHead(MatchTask):
	def __init__(self, head_idx1, head_idx2):
		self.initialize()
		self.head_idx1 = head_idx1
		self.head_idx2 = head_idx2
	def __repr__(self):
		return "NeqHead %s %s" % (head_idx_str(self.head_idx1), head_idx_str(self.head_idx2))

class ExcludeAtom(MatchTask):
	def __init__(self, head_idx1, head_idx2):
		self.initialize()
		self.head_idx1 = head_idx1
		self.head_idx2 = head_idx2
	def __repr__(self):
		return "ExcludeAtom %s %s" % (head_idx_str(self.head_idx1), head_idx_str(self.head_idx2))

class FilterHead(MatchTask):
	def __init__(self, head_idx1, head_idx2):
		self.initialize()
		self.head_idx1 = head_idx1
		self.head_idx2 = head_idx2
	def __repr__(self):
		return "FilterHead %s %s" % (head_idx_str(self.head_idx1), head_idx_str(self.head_idx2))

class ExistDest(MatchTask):
	def __init__(self, exist_var):
		self.initialize()
		self.exist_var = exist_var
	def __repr__(self):
		return "ExistDest %s" % self.exist_var

class ExistLoc(MatchTask):
	def __init__(self, exist_var):
		self.initialize()
		self.exist_var = exist_var
	def __repr__(self):
		return "ExistLoc %s" % self.exist_var

class LetBind(MatchTask):
	def __init__(self, assign_dec):
		self.initialize()
		self.assign_dec = assign_dec
	def __repr__(self):
		return "LetBind %s %s" % (self.assign_dec.term_pat, self.assign_dec.builtin_exp)

class IntroAtom(MatchTask):
	def __init__(self, atom_body, body_idx):
		self.body = atom_body
		self.fact = atom_body.fact
		self.local    = atom_body.local
		self.priority = atom_body.priority
		self.monotone = atom_body.monotone
		self.body_idx   = body_idx
	def is_local(self, name=True):
		if name:
			return "Local" if self.local else "Remote"
		else:
			return 1 if self.local else 0
	def is_priority(self, name=True):
		if name:
			return "Prior(%s)" % self.priority if self.priority != None else "NoPrior"
		else:
			return self.priority if self.priority !=None else 0
	def is_monotone(self, name=True):
		if name:
			return "Mono" if self.monotone else "NonMono"
		else:
			return 1 if self.local else 0
	def __repr__(self):
		return "IntroAtom %s %s %s %s" % (self.is_local(),self.is_priority(),self.is_monotone(),self.fact)

class IntroCompre(MatchTask):
	def __init__(self, compre_body, body_idx, compre_idx):
		inspect = Inspector()
		self.body = compre_body
		self.fact = compre_body.fact
		self.local    = compre_body.local
		self.priority = compre_body.priority
		self.monotone = compre_body.monotone
		self.term_vars  = inspect.free_vars(compre_body.fact.comp_ranges[0].term_vars)
		self.compre_dom = compre_body.fact.comp_ranges[0].term_range
		self.body_idx   = body_idx
		self.compre_idx = compre_idx
	def is_local(self, name=True):
		if name:
			return "Local" if self.local else "Remote"
		else:
			return 1 if self.local else 0
	def is_priority(self, name=True):
		if name:
			return "Prior(%s)" % self.priority if self.priority != None else "NoPrior"
		else:
			return self.priority if self.priority !=None else 0
	def is_monotone(self, name=True):
		if name:
			return "Mono" if self.monotone else "NonMono"
		else:
			return 1 if self.local else 0
	def __repr__(self):
		return "IntroCompre %s %s %s %s %s %s" % (self.is_local(), self.is_priority(), self.is_monotone()
                                                         ,','.join(map(lambda v: str(v),self.term_vars))
                                                         ,self.compre_dom, self.body.fact_pat)

class DeleteHead(MatchTask):
	def __init__(self, head_idx):
		self.head_idx = head_idx
	def __repr__(self):
		return "DeleteHead %s" % head_idx_str(self.head_idx)

# Generating Join Ordering

class JoinOrdering:

	def __init__(self, rule, occ_idx, fact_dir, lookup_tables):

		inspect = Inspector()

		self.rule_head_vars    = rule.rule_head_vars
		self.rule_head_binders = rule.rule_head_binders
		self.rule_all_vars     = rule.all_vars

		occ_head = rule.occ_heads[occ_idx]
		atom_partner_heads   = {}
		compre_partner_heads = {}
		for partner_idx,partner_head in rule.occ_heads.items():
			if partner_idx != occ_idx:
				if partner_head.is_atom:
					atom_partner_heads[partner_idx] = partner_head
				else:
					compre_partner_heads[partner_idx] = partner_head

		self.occ_head = occ_head
		self.fact_idx = occ_head.fact_idx
		self.rule = rule
		self.occ_idx = occ_idx
		self.is_active_prop = False
		self.is_propagated = True

		simp_head_idx = []
		prop_head_idx = []

		# Build Active Match task and Initialize guard pool.
		guard_pool = map(lambda a: a, rule.idx_grds + rule.non_idx_grds)
		if occ_head.is_atom:
			active_task = ActiveAtom(occ_head, 0)
			boot_strap  = False
			collision_map = defaultdict(list)
			collision_map[occ_head.collision_idx].append( (occ_head.is_atom,0) )
			if occ_head.head_type == SIMP_HEAD:
				simp_head_idx.append( 0 )
				self.is_propagated  = False
			else:
				prop_head_idx.append( 0 )
				self.is_active_prop = True
		else:
			# We bootstrap active comprehensions. Specifically, we execute the comprehension
			# pattern as though it is an atom. This atom is treated as a 'phantom' head. 
			# Bootstrapping is completed below at (*)
			active_task = ActiveCompre(occ_head, 0)
			boot_strap  = True
			guard_pool += occ_head.eq_grds + occ_head.mem_grds + occ_head.ord_grds + occ_head.non_idx_grds
			collision_map = defaultdict(list)
			if occ_head.head_type == SIMP_HEAD:
				self.is_propagated  = False
			else:
				self.is_active_prop = True

		# Initiate Matching Context
		lctxt = LookupContext( fact_dir )
		lctxt.addFactHead(occ_head, boot_strap=boot_strap)
		map(lambda g: lctxt.addGuard(g), guard_pool)

		# Initiate Head Match Tasks
		head_match_tasks = {}
		head_match_tasks[0] = [active_task] + map(lambda g: CheckGuard(g) ,lctxt.scheduleGuards())

		# Build Partner Match task
		head_idx = 1	
		while len(atom_partner_heads.items()) > 0:
		
			# Find best lookup leap to next partner
			(best_idx,best_lookup) = lctxt.bestLookupOption( atom_partner_heads )
			partner_head = atom_partner_heads[best_idx]
			del atom_partner_heads[best_idx]
		
			# Register head type
			if partner_head.head_type == SIMP_HEAD:
				simp_head_idx.append( head_idx )
				self.is_propagated  = False
			else:
				prop_head_idx.append( head_idx )

			# Build lookup match task for best lookup partner option
			lookup_task = LookupAtom(partner_head, head_idx, best_lookup, rule)

			lookup_tables.registerLookup( best_lookup )

			# Update lookup context
			# lctxt.addFactHead( partner_head )
			lctxt.addVars( lookup_task.input_vars + lookup_task.output_vars )
			# map(lambda g: lctxt.addGuard(g), lookup_task.dep_grds)
			lctxt.remove_guards( best_lookup.assoc_guards )

			# Append new match tasks
			partner_match_tasks  = [lookup_task] + collision_guard_task(True, head_idx, collision_map[partner_head.collision_idx])
			partner_match_tasks += map(lambda g: CheckGuard(g) ,lctxt.scheduleGuards())
			head_match_tasks[ head_idx ] = partner_match_tasks

			# Register partner collision index in collision map
			collision_map[partner_head.collision_idx].append( (True,head_idx) )
	
			head_idx += 1

		# (*) Complete active comprehension bootstrapping:
		#    i.   Add comprehension guards to end of lookup atom tasks
		#    ii.  Add active comprehension tasks to the head of the lookup compre tasks.
		#    iii. (ii) is followed by adding an 'exclude atom' task 
		if occ_head.is_compre:

			if occ_head.head_type == SIMP_HEAD:
				simp_head_idx.append( head_idx )
				self.is_propagated  = False
			else:
				prop_head_idx.append( head_idx )

			lctxt.removeBootStrapped()
			lookup = lctxt.lookupOptions(occ_head)[0]
			lookup_task = LookupAll(occ_head, head_idx, lookup, rule)
	
			lookup_tables.registerLookup( lookup )

			# lctxt.addFactHead( occ_head )
			lctxt.addVars( lookup_task.output_vars + [occ_head.compre_dom] ) 
			# map(lambda g: lctxt.addGuard(g), lookup_task.dep_grds)

			# lctxt.addVars( lookup.outputVars( occ_head ) + [occ_head.compre_dom] )
			lctxt.remove_guards( lookup.assoc_guards )

			compre_guards = []
			for guard in occ_head.eq_grds + occ_head.mem_grds + occ_head.ord_grds + occ_head.non_idx_grds:
				if guard not in lookup.assoc_guards:
					compre_guards.append( guard )

			boot_match_tasks  = [lookup_task] + collision_guard_task(False, head_idx, collision_map[occ_head.collision_idx]) 
			# boot_match_tasks += map(lambda g: FilterGuard(lookup_task.term_vars, lookup_task.compre_dom, head_idx, g), compre_guards)
			if len(compre_guards) > 0:
				boot_match_tasks += [FilterGuard(lookup_task.term_vars, lookup_task.compre_dom, head_idx, compre_guards, init_binders=False)]
			boot_match_tasks += [CompreDomain(occ_head, head_idx, init_binders=False)]
			boot_match_tasks += map(lambda g: CheckGuard(g), lctxt.scheduleGuards())
			head_match_tasks[ head_idx ] = boot_match_tasks

			collision_map[occ_head.collision_idx].append( (False,head_idx) )

			head_idx += 1

		while len(compre_partner_heads.items()) > 0:

			# Find best lookup leap to next partner
			(best_idx,best_lookup) = lctxt.bestLookupOption( compre_partner_heads )
			partner_head = compre_partner_heads[best_idx]
			del compre_partner_heads[best_idx]
		
			# Register head type
			if partner_head.head_type == SIMP_HEAD:
				simp_head_idx.append( head_idx )
				self.is_propagated  = False
			else:
				prop_head_idx.append( head_idx )

			# Build lookup match task for best lookup partner option
			lookup_task = LookupAll(partner_head, head_idx, best_lookup, rule)
		
			lookup_tables.registerLookup( best_lookup )

			# Update lookup context
			# lctxt.addFactHead( partner_head )
			lctxt.addVars( lookup_task.output_vars + [partner_head.compre_dom] )
			# map(lambda g: lctxt.addGuard(g), lookup_task.dep_grds)
			# lctxt.addVars( best_lookup.outputVars( partner_head ) + [partner_head.compre_dom] )
			lctxt.remove_guards( best_lookup.assoc_guards )
	
			compre_guards = []
			for guard in partner_head.eq_grds + partner_head.mem_grds + partner_head.ord_grds + partner_head.non_idx_grds:
				if guard not in best_lookup.assoc_guards:
					compre_guards.append( guard )

			# Append new match tasks
			partner_match_tasks  = [lookup_task] + collision_guard_task(False, head_idx, collision_map[partner_head.collision_idx])
			# partner_match_tasks += map(lambda g: FilterGuard(lookup_task.term_vars, lookup_task.compre_dom, head_idx, g)
                        #                           ,compre_guards)
			if len(compre_guards) > 0:
				partner_match_tasks += [FilterGuard(lookup_task.term_vars, lookup_task.compre_dom, head_idx, compre_guards, init_binders=True)]
			partner_match_tasks += [CompreDomain(partner_head, head_idx, init_binders=True)] 
			partner_match_tasks += map(lambda g: CheckGuard(g), lctxt.scheduleGuards())
			head_match_tasks[ head_idx ] = partner_match_tasks	

			collision_map[partner_head.collision_idx].append( (False,head_idx) )
	
			head_idx += 1

		self.head_indices = range(0,head_idx)
		self.head_match_tasks = head_match_tasks

		self.delete_head_tasks = map(lambda hidx: DeleteHead(hidx), simp_head_idx)

		# Extract exist tasks
		exist_tasks = []
		for exist_dest in rule.exist_dests:
			exist_tasks.append( ExistDest( exist_dest ) )
		for exist_loc in rule.exist_locs:
			exist_tasks.append( ExistLoc( exist_loc ) )
		self.exist_tasks = exist_tasks

		# Extract let binding tasks
		letbind_tasks = []
		for where in rule.where:
			letbind_tasks.append( LetBind(where) )
		self.letbind_tasks = letbind_tasks

		# Extract rule body tasks
		atom_body_tasks   = []
		compre_body_tasks = []
		compre_idx = 0
		body_idx = 0
		for body in rule.rule_body:
			if body.is_atom:
				atom_body_tasks.append( IntroAtom(body, body_idx) )
			else:
				compre_body_tasks.append( IntroCompre(body, body_idx, compre_idx) )
				compre_idx += 1
			body_idx += 1
		self.atom_body_tasks = atom_body_tasks
		self.compre_body_tasks = compre_body_tasks

	def getName(self):
		return self.rule.get_name()

	def activeTask(self):
		return self.head_match_tasks[0][0]

	def getJoinTasks(self):
		return self.getMatchTasks()

	def getMatchTasks(self):
		head_match_tasks = []
		for head_idx in self.head_indices:
			head_match_tasks += self.head_match_tasks[ head_idx ]
		return head_match_tasks + self.delete_head_tasks + self.exist_tasks + self.letbind_tasks + self.atom_body_tasks + self.compre_body_tasks

	def __repr__(self):
		strs  = "**** %s Join Ordering of Rule %s ****\n" % (self.occ_idx,self.rule.rule.name)
		strs += "Rule Head Variables: %s\n" % (', '.join(map(lambda v: "%s" % v,self.rule_head_vars)))
		strs += "Rule Head Compre Binders: %s\n" % (', '.join(map(lambda v: "%s" % v,self.rule_head_binders)))
		strs += '\n'.join( map(lambda s: "%s" % s, self.getMatchTasks()) )
		return strs

def collision_guard_task(subj_is_atom, subj_idx, collision_list):
	col_tasks = []
	for col_is_atom,col_idx in collision_list:
		if subj_is_atom and col_is_atom:
			col_tasks.append( NeqHead(subj_idx, col_idx) )
		elif not subj_is_atom and col_is_atom:
			col_tasks.append( FilterHead(subj_idx, col_idx) )
		elif not subj_is_atom and not col_is_atom:
			col_tasks.append( FilterHead(subj_idx, col_idx) )
	return col_tasks


