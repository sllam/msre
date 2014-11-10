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

from msrex.frontend.compile.rule_guards import process_guard, NON_IDX_GRD, EQ_GRD, MEM_GRD, ORD_GRD

FACT_INDEX = 0
def get_next_fact_index():
	global FACT_INDEX
	new_id = FACT_INDEX
	FACT_INDEX += 1
	return new_id

class FactDirectory:

	def __init__(self, fact_decs):
		self.fact_decs = fact_decs
		self.fact_idx_dict  = {}
		self.fact_name_dict = {}
		self.initialize()

	def initialize(self):
		for fact_dec in self.fact_decs:
			new_idx = get_next_fact_index()
			self.fact_idx_dict[ new_idx ] = fact_dec
			self.fact_name_dict[ fact_dec.name ] = (new_idx,fact_dec)
	
	def getIndices(self):
		return self.fact_idx_dict.keys()

	def getFactFromIdx(self, idx):
		return self.fact_idx_dict[ idx ]

	def getFactFromName(self, name):
		return self.fact_name_dict[ name ]

	def getCardinality(self, idx):
		fact_dec = self.fact_idx_dict[idx]
		ty = fact_dec.type
		if ty == None:
			return 0
		elif ty.type_kind == ast.TYPE_TUP:
			return len(ty.types)
		else:
			return 1

	def uses_priority(self):
		for idx in self.fact_idx_dict:
			if self.fact_idx_dict[idx].uses_priority:
				return True
		return False

	def __repr__(self):
		strs = "============= Fact Directory ==============\n"
		for idx in self.fact_idx_dict:
			fact_dec = self.fact_idx_dict[ idx ]
			strs += "%s : %s\n" % (idx,fact_dec.name)
			strs += "  Type Sig: %s\n" % (fact_dec.type)
			strs += "  Is Persistent: %s\n" % ('Yes' if fact_dec.persistent else 'No') 
			strs += "  Is Local: %s\n" % ('Yes' if fact_dec.local else 'No')
			strs += "  Is Monotonic: %s\n" % ('Yes' if fact_dec.monotone else 'No')
			strs += "  Uses Priorities: %s\n" % ('Yes' if fact_dec.uses_priority else 'No')
		strs += "===========================================\n"
		return strs


# Fact Atoms

FACT_INDEX = 0
def get_next_fact_index():
	global FACT_INDEX
	new_id = FACT_INDEX
	FACT_INDEX += 1
	return new_id

class Fact:
	def initialize(self, fact, fact_name, fact_dir, is_compre):
		self.fact = fact
		self.id   = get_next_fact_index()
		self.inspect = Inspector()
		idx,_ = fact_dir.getFactFromName(fact_name)
		self.fact_idx = idx
		self.is_compre = is_compre
		self.is_atom   = not is_compre
	def getFactTerms(self):
		if self.is_atom:
			return [self.fact.loc] + self.fact.terms
		else:
			loc_fact = self.fact.facts[0]
			return [loc_fact.loc] + loc_fact.terms
	def __eq__(self, other):
		return self.id == other.id
	def __repr__(self):
		return "%s: %s#%s" % (self.id, self.fact, self.fact_idx)
	
SIMP_HEAD = 'simp'
PROP_HEAD = 'prop'

class FactAtomHead(Fact):
	def __init__(self, loc_fact, head_type, fact_dir):
		self.initialize(loc_fact, loc_fact.fact.name, fact_dir, False)
		self.head_type = head_type
		self.fact_pat  = loc_fact
		self.unique    = loc_fact.fact.unique_head
		self.collision_idx = loc_fact.fact.collision_idx
	def __repr__(self):
		return "%s %s: %s#%s %s" % (self.head_type,self.id,self.fact,self.fact_idx
                                           ,'unique' if self.unique else 'non-unique')

class FactCompreHead(Fact):
	def __init__(self, fact_compre, head_type, fact_dir):
		self.initialize(fact_compre, fact_compre.facts[0].fact.name, fact_dir, True)
		self.head_type = head_type
		self.fact_pat  = fact_compre.facts[0]
		self.unique = fact_compre.facts[0].fact.unique_head
		self.collision_idx = fact_compre.facts[0].fact.collision_idx
		self.eq_grds  = []
		self.mem_grds = []
		self.ord_grds = []
		self.non_idx_grds = []
		for grd in fact_compre.guards:
			rulegrd = process_guard( grd )
			if rulegrd.indexable():
				if rulegrd.type == EQ_GRD:
					self.eq_grds.append( rulegrd )
				elif rulegrd.type == MEM_GRD:
					self.mem_grds.append( rulegrd )
				elif rulegrd.type == ORD_GRD:
					self.ord_grds.append( rulegrd )
				else:
					self.non_idx_grds.append( rulegrd )
			else:
				self.non_idx_grds.append( rulegrd )
		self.compre_dom = fact_compre.comp_ranges[0].term_range
	def __repr__(self):
		if len( self.eq_grds + self.mem_grds + self.ord_grds ) > 0:
			idxgrdstr = "\nIndexible Guards :-\n" + '\n'.join(map(lambda g:g.__repr__(), self.eq_grds + self.mem_grds + self.ord_grds))
		else:
			idxgrdstr = ""
		if len( self.non_idx_grds ) > 0:
			nonidxgrdstr = "\nNon-Indexible Guards :-\n" + '\n'.join(map(lambda g:g.__repr__(), self.non_idx_grds))
		else:
			nonidxgrdstr = ""
		return "%s %s: %s#%s %s %s%s" % (self.head_type,self.id,self.fact,self.fact_idx
                                                ,'unique' if self.unique else 'non-unique',idxgrdstr,nonidxgrdstr)

class FactAtomBody(Fact):
	def __init__(self, loc_fact, fact_dir):
		self.initialize(loc_fact, loc_fact.fact.name, fact_dir, False)
		self.local    = loc_fact.fact.local
		self.priority = loc_fact.fact.priority
		self.monotone = loc_fact.fact.monotone
	def __repr__(self):
		return "%s: %s#%s %s %s %s" % (self.id, self.fact, self.fact_idx
                                              ,'local' if self.local else 'non-local'
                                              ,'priority(%s)' % self.priority if self.priority != None else 'non-prioritized'
                                              ,'monotonic' if self.monotone else 'non-monotonic')
		

class FactCompreBody(Fact):
	def __init__(self, fact_compre, fact_dir):
		self.initialize(fact_compre, fact_compre.facts[0].fact.name, fact_dir, True)
		self.local    = fact_compre.facts[0].fact.local
		self.priority = fact_compre.facts[0].fact.priority
		self.monotone = fact_compre.facts[0].fact.monotone
		self.fact_pat = fact_compre.facts[0]
		self.guards   = fact_compre.guards
	def __repr__(self):
		return "%s: %s#%s %s %s %s" % (self.id, self.fact, self.fact_idx
                                              ,'local' if self.local else 'non-local'
                                              ,'priority(%s)' % self.priority if self.priority != None else 'non-prioritized'
                                              ,'monotonic' if self.monotone else 'non-monotonic')

