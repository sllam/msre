
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

from string import split

import msrex.frontend.lex_parse.ast as ast
import msrex.frontend.lex_parse.parser as p

from msrex.frontend.analyze.inspectors import Inspector

import msrex.frontend.compile.join_ordering as join

from msrex.frontend.compile.lookup_context import HASH_LK, MEM_LK, ORD_LK, LOC_HASH_LK, LINEAR_LK, LookupTables
from msrex.frontend.compile.prog_compilation import ProgCompilation

import msrex.misc.visit as visit
from msrex.misc.template import compile_template, template, compact

BASE_IMPORT_LIST = template('''

	#include <iostream>
	#include <sstream>
	#include <string>
	#include <list>

	#include <boost/date_time/posix_time/posix_time.hpp>
	#include <boost/unordered_map.hpp>
	#include <boost/functional/hash/hash.hpp>
	#include <boost/serialization/string.hpp>
	#include <boost/serialization/list.hpp>
	#include <boost/mpi.hpp>
	#include <boost/mpi/status.hpp>
	#include <boost/format.hpp>
	#include <boost/tuple/tuple.hpp>

	#include \"msre/fact.h\"
	#include \"msre/comm.h\"
	#include \"msre/store.h\"
	#include \"msre/goals.h\"
	#include \"msre/rewrite.h\"
	#include \"msre/directory.h\"
	#include \"msre/logger.h\"			
	#include \"msre/hash.h\"

	using namespace std;
	using namespace boost;
	using namespace boost::tuples;

''')

BASE_MACRO_LIST = template('''

	#ifdef MSRE_CONFIG_FILE
	#include "msre_config.h"
	#endif

	#ifndef MSRE_NODE_INSTANCE
	#define MSRE_NODE_INSTANCE AdminExpoBackoffMSRENode
	#endif

	#ifndef MSRE_MPICOMM_INSTANCE
	#define MSRE_MPICOMM_INSTANCE MPICommBasic
	#endif

	#ifndef MSRE_GOAL_INSTANCE
	#define MSRE_GOAL_INSTANCE {| goal_instance_code |}
	#endif

	#ifndef MSRE_DIRECTORY_INSTANCE
	#define MSRE_DIRECTORY_INSTANCE NodeProxyDirectory
	#endif

''')

BOILER_PLATE_CODES = template('''
	private: bool rewrite() {
		bool done_something = false;
		while(goals->has_goals()) {
			Fact* fact = goals->next();
			fact->execute( this );
			done_something = true;
		}
		return done_something;
	}

	private: bool rewrite(int max_steps) {
		int count = 0;
		while(goals->has_goals() and count < max_steps) {
			Fact* fact = goals->next();
			fact->execute( this );
			count++;
		}
		return count > 0;
	}
''')

PRIME_NUMBERS = [7919,13259,31547,53173,72577,91099,103421,224737,350377,499979]

def mk_ensem_name( name ):
	ensem_name = ""
	for frag in split(name,'_'):
		ensem_name += frag[0].upper() + frag[1:]
	return ensem_name

def mk_pred_name( name ):
	pred_name = ""
	for frag in split(name,'_'):
		pred_name += frag[0].upper() + frag[1:]
	return pred_name

def mk_cpp_var_name( name ):
	return name.lower()

def mk_join_task_source_text( join_task ):
	return "// Join Task: %s" % join_task

def all_pat_vars(join_head_dict):
	pat_vars = set([])
	for idx in join_head_dict:
		pat_vars |= set(join_head_dict[idx]['pat_vars'])
	return pat_vars

def local_loc_var(join_head_dict):
	join_head_info = join_head_dict[0]
	return join_head_info['pat_vars'][0]

def req_collision_check(idx_var_eq):
	return len(idx_var_eq) > 1

class CPPCodeGenerator:

	def __init__(self, prog, fact_dir, extract_data):
		self.prog = prog
		self.rule_names = prog.getRuleNames()
		self.fact_dir = fact_dir
		self.lookup_tables = prog.lookup_tables
		self.init_fact_dict()
		self.init_store_dict()
		self.join_ordering_dict = {}
		self.var_idx = 0
		self.extract_data = extract_data

	def next_temp_var_name(self):
		var_name = "temp%s" % self.var_idx
		self.var_idx += 1
		return var_name;

	def init_fact_dict(self):
		self.fact_dict = {}
		cpp_type_coerce = CPPTypeCoercion()
		for fact_idx,fact_dec in self.fact_dir.fact_idx_dict.items():
			arg_names = []
			for i in range(1,len(fact_dec.arg_types())+1):
				arg_names.append( "arg%s" % i )
			info = { 'fact_idx'   : fact_idx
                               , 'src_name'   : fact_dec.name
                               , 'fact_name'  : mk_pred_name( fact_dec.name )
                               , 'var_name'   : mk_cpp_var_name( fact_dec.name )
                               , 'loc_name'   : 'loc'
                               , 'loc_type'   : 'int'
                               , 'arg_names'  : arg_names
                               , 'types'      : fact_dec.arg_types()
                               , 'type_codes' : map(lambda arg_type : cpp_type_coerce.coerce_cpp_type_codes(arg_type), fact_dec.arg_types())
                               , 'pretty_codes'   : ["%s"] + map(lambda arg_type : cpp_type_coerce.coerce_cpp_pretty_codes(arg_type), fact_dec.arg_types())
                               , 'markdown_codes' : ["print_markdown(aliases,%s)"] + map(lambda arg_type : cpp_type_coerce.coerce_cpp_markdown_codes(arg_type), fact_dec.arg_types())
                               , 'persistent' : fact_dec.persistent
                               , 'local'      : fact_dec.local
                               , 'monotone'   : fact_dec.monotone
                               , 'uses_priority' : fact_dec.uses_priority }
			self.fact_dict[fact_idx] = info
			# print "%s:%s:%s" % (fact_dec.name, map(str,fact_dec.arg_types()), info['pretty_codes'])

	def init_store_dict(self):
		self.store_dict = {}
		for fact_idx,fact_stores in self.lookup_tables.lookup_tables.items():
			fact_info = self.fact_dict[fact_idx]
			fact_name = fact_info['fact_name']
			for fact_store in fact_stores:
				store_idx = fact_store.lookup_idx
				store_name = "%s_store_%s" % ( mk_cpp_var_name(fact_name) ,store_idx)
				# print "Ho ho ho: %s" % fact_store.type
				if fact_store.type == LINEAR_LK:
					store_type = "ListStore<%s>" % fact_name
					iter_type  = "ListIter<%s>" % fact_name
					has_index  = False
				elif fact_store.type == HASH_LK or fact_store.type == LOC_HASH_LK:
					store_type = "MultimapStore<%s>" % fact_name
					iter_type  = "MultimapIter<%s>" % fact_name
					has_index  = True
				else:
					print "Hahah"
					# TODO
					pass
				fact_arg_names  = [fact_info['loc_name']] + fact_info['arg_names']
				fact_type_codes = [fact_info['loc_type']] + fact_info['type_codes']
				idx_func_name = "index%s%s" % (store_idx,fact_name)

				idx_codes = []
				for idx in fact_store.lookupArgIndices():
					idx_codes.append( { 'idx':idx, 'arg_name':fact_arg_names[idx], 'type_code':fact_type_codes[idx] } )			
	
				store_info = { 'name':store_name, 'type':store_type, 'iter':iter_type, 'idx_func':idx_func_name, 'sort':fact_store.type
		                             , 'idx':idx_codes, 'collision_free':len(idx_codes)<=1, 'has_index':has_index, 'store_idx':store_idx }

				if fact_idx in self.store_dict:
					self.store_dict[fact_idx].append( store_info )
				else:
					self.store_dict[fact_idx] = [store_info]

	def generate(self):
		prog        = self.prog
		prog_name   = self.prog.prog_name
		extern_decs = self.prog.extern_decs
		# specs = self.msre_specs['specs']
		exec_decs   = [self.prog.exec_dec]

		extern_import_list = map(lambda e: self.generate_extern_import( e ), extern_decs)
		ensem_classes = map(lambda p: self.generate_ensemble( p ), [prog])

		exec_codes = []
		count = 0
		for exec_dec in exec_decs:
			exec_codes.append( self.generate_exec(exec_dec, count) )
			count += 1

		use_ordered_goals = prog.fact_dir.uses_priority()
		'''
		for ensem_spec in specs:
			for (sym_id,fact_spec) in ensem_spec['fact_specs'].items():
				if fact_spec['uses_priority']:
					use_ordered_goals = True
		'''
		if use_ordered_goals:
			goal_instance_code = "OrderedGoals"
		else:
			goal_instance_code = "ListGoals"
		base_marco_list = compile_template(BASE_MACRO_LIST, goal_instance_code=goal_instance_code)

		main_codes = ""
		if len(exec_decs) > 0:
			exec_call_codes = []
			for idx in range(0,len(exec_decs)):
				exec_call_codes.append( "execute_%s(argv[1]);" % idx )
			main_codes = compile_template( template('''
			int main(int argc, char* argv[]) { 

				mpi::environment env(argc, argv);
				mpi::communicator world;

				if (world.rank() == 0) { print_log_pref(); }

				{| '\\n'.join( exec_call_codes ) |}
			}
			'''), exec_call_codes=exec_call_codes )
			

		ensem_code = template('''
			{| base_macro_list |}

			{| base_import_list |}

			{| '\\n'.join( extern_import_list ) |}

			{| '\\n'.join( ensem_classes ) |}

			{| '\\n'.join( exec_codes ) |}

			{| main_codes |}
		''')		
		
		file_name = "%s.cpp" % prog_name

		output = open(file_name, 'w')
		output.write( compile_template(ensem_code, base_import_list=BASE_IMPORT_LIST, base_macro_list=base_marco_list
                                              ,extern_import_list=extern_import_list, ensem_classes=ensem_classes, exec_codes=exec_codes
                                              ,main_codes=main_codes) )

	def generate_extern_import(self, extern_dec):
		extern_import_codes = template('''
			#include {| extern_module_name |}
		''')
		return compile_template( extern_import_codes, extern_module_name=extern_dec.name )

	def generate_fact_atom(self, fact_idx, loc_fact):
		fact_name = self.fact_dict[fact_idx]['fact_name']

		fact_args = []
		arg_contexts = []
		for fact_arg in [loc_fact.loc] + loc_fact.fact.terms:
			context_codes,f_arg_codes = self.generate_term( fact_arg )
			fact_args.append( f_arg_codes )
			arg_contexts += context_codes

		if loc_fact.priority != None:
			fact_args.append( str(loc_fact.priority) )

		return arg_contexts,fact_args

	def generate_exec(self, exec_dec, idx):

		ensem_name = mk_ensem_name( exec_dec.name )
		inspect = Inspector()
		cpp_type_coerce = CPPTypeCoercion()
		exist_decs = inspect.filter_decs(exec_dec.decs, exist=True)
		rest_decs  = inspect.filter_decs(exec_dec.decs, loc_facts=True, assign=True)

		idx_dict = { 'loc':0, 'compre':0 }

		# Generate exist codes
		exist_codes = []
		for exist_dec in exist_decs:
			exist_codes.append( self.generate_exec_stmt(exist_dec, inspect, cpp_type_coerce, idx_dict) )

		# Generate all other supported declaration codes
		rest_codes = []
		for rest_dec in rest_decs:
			rest_codes.append( self.generate_exec_stmt(rest_dec, inspect, cpp_type_coerce, idx_dict) )				

		exec_codes = template('''
			void execute_{| idx |}(string filename) {
				{| ensem_name |} en = {| ensem_name |}();

				{| '\\n'.join( exist_codes ) |}

				en.init();

				{| '\\n'.join( rest_codes ) |}

				en.run_stat(filename);
				en.close();
			}
		''')

		return compact( compile_template( exec_codes, idx=idx, ensem_name=ensem_name, exist_codes=exist_codes
                                                , rest_codes=rest_codes ) )

	@visit.on( 'dec' )
	def generate_exec_stmt(self, dec, inspect, cpp_type_coerce, idx_dict):
		pass

	@visit.when( ast.ExistDec )
	def generate_exec_stmt(self, dec, inspect, cpp_type_coerce, idx_dict):
		exist_codes = []
		for exist_var in dec.exist_vars:
			exist_type = cpp_type_coerce.coerce_cpp_type_codes( exist_var.type )
			exist_name = mk_cpp_var_name( exist_var.name )
			exist_value = ""
			if exist_var.type.name == ast.LOC:
				exist_value = "%s" % idx_dict['loc']
				idx_dict['loc'] += 1

				exist_code = template('''
					{| exist_type |} {| exist_cpp_name |} = en.reg_node_alias({| exist_value |},\"{| exist_src_name |}\");
					en.add_node({| exist_cpp_name |});
				''')
				exist_codes.append( compile_template(exist_code, exist_type=exist_type, exist_cpp_name=exist_name
                                                                    ,exist_src_name=exist_var.name, exist_value=exist_value) )

			elif exist_var.type.name == ast.DEST:
				exist_value = "en.next_exist_id(\"%s\",-1)" % exist_var.name
				exist_codes.append( "%s %s = %s;" % (exist_type,exist_name,exist_value) )

		all_exist_codes = template('''
			{| '\\n'.join( exist_codes ) |}		
		''')
		return compile_template(all_exist_codes, exist_codes=exist_codes)
		
	@visit.when( ast.AssignDec )
	def generate_exec_stmt(self, dec, inspect, cpp_type_coerce, idx_dict):
		# left_pat_context,left_pat_codes = self.generate_left_pattern(dec.term_pat, dec.term_pat.type)
		left_pat_context,left_pat_codes,left_post_codes = self.generate_left_pattern( dec.term_pat )
		context_codes,assign_exp_codes = self.generate_term(dec.builtin_exp)
		
		assign_template = template('''
			{| left_pat_context |}
			{| '\\n'.join( context_codes ) |}
			{| left_pat_codes |} = {| assign_exp_codes |};
			{| left_post_codes |}
		''')

		return compile_template(assign_template, left_pat_context=left_pat_context, left_pat_codes=left_pat_codes
                                       ,context_codes=context_codes, assign_exp_codes=assign_exp_codes
                                       ,left_post_codes=left_post_codes)

	@visit.when( ast.LocFactDec )
	def generate_exec_stmt(self, dec, inspect, cpp_type_coerce, idx_dict):
		
		init_fact_codes = []
		for loc_fact in dec.loc_facts:
			if loc_fact.fact_type == ast.FACT_LOC:
				fact_idx,_ = self.fact_dir.getFactFromName( loc_fact.fact.name )
				arg_contexts,fact_args = self.generate_fact_atom(fact_idx, loc_fact)
				fact_name = self.fact_dict[fact_idx]['var_name']						
				init_fact_codes += arg_contexts
				init_fact_codes.append( "en.add_%s(%s);" % (fact_name,','.join(fact_args)) )
			else: # body_fact['type'] == FACT_COMPRE
				# TODO: Currently supports only one compre range
				main_comp_range = loc_fact.comp_ranges[0]
				term_pat  = main_comp_range.term_vars  # body_fact['term_pat']
				term_subj = main_comp_range.term_range 
				facts     = loc_fact.facts

				subj_type    = cpp_type_coerce.coerce_cpp_type_codes( term_subj.type )
				subj_varname = "comp_%s" % idx_dict['compre']
				idx_dict['compre'] += 1
				subj_context_codes,subj_exp   = self.generate_term( term_subj )
				# term_pat_context,term_pat_var = self.generate_left_pattern(term_pat, term_pat.type)
				term_pat_context,term_pat_var,term_pat_post = self.generate_left_pattern( term_pat )

				fact_atom_codes = []
				for f in facts:
					fact_idx,_ = self.fact_dir.getFactFromName( f.fact.name )
					arg_contexts,fact_args = self.generate_fact_atom(fact_idx, f)
					fact_atom_codes += arg_contexts
					fact_atom_codes.append( "en.add_%s(%s);" % (f.fact.name,','.join(fact_args)) )

				compre_codes = template('''
				{| '\\n'.join( subj_context_codes ) |}
				{| subj_type |} {| subj_varname |} = {| subj_exp |};
				for({| subj_type |}::iterator it={| subj_varname |}.begin(); it!={| subj_varname |}.end(); it++) {
					{| term_pat_context |}
					{| term_pat_var |} = *it;
					{| term_pat_post |}
					{| '\\n'.join( fact_atom_codes ) |}
				}
				''')
				init_fact_codes.append( compile_template( compre_codes, subj_context_codes=subj_context_codes
                                                      , subj_type=subj_type, subj_varname=subj_varname, subj_exp=subj_exp
                                                      , term_pat_context=term_pat_context, term_pat_var=term_pat_var
                                                      , term_pat_post=term_pat_post, fact_atom_codes=fact_atom_codes ) )
				
		all_fact_codes = template('''
			{|  '\\n'.join( init_fact_codes ) |}
		''')
		return compile_template(all_fact_codes, init_fact_codes=init_fact_codes)
		

	def generate_ensemble(self, prog):

		ensem_name = mk_ensem_name( prog.ensem_name )

		# Setup info

		# self.fact_decs  = { }
		# self.store_decs = { }
		# self.occ_decs   = { }

		'''
		rule_names = []
		for (sym_id,rule_specs) in ensem_spec['rule_specs'].items():
			for rule_spec in rule_specs:
				rule_name = rule_spec['rule_name']
				if rule_name not in rule_names:
					rule_names.append( rule_name )
		self.rule_names = rule_names
		'''

		'''
		for (sym_id,fact_spec) in ensem_spec['fact_specs'].items():
			self.register_fact(sym_id, mk_pred_name( fact_spec['pred_name'] ), fact_spec['arg_types']
                                          ,fact_spec['persistent'], fact_spec['local'], fact_spec['uses_priority'])
		'''

		# self.ensem_info[ensem_spec['ensem_name']] = self.fact_decs

		# Generate codes

		extern_imports = "" # map(lambda e: self.generate_extern_import( e ), ensem_spec['extern_specs'])

		fact_dec_codes = map(lambda fact_idx: self.generate_fact_decs(ensem_name, fact_idx), self.fact_dict)

		index_dec_codes = self.generate_store_index_decs(ensem_name)
		const_pred_id_decs = map(lambda (fact_idx,fact_info): "const static int %s_pred_id = %s;" % (fact_info['var_name'],fact_idx) 
                                        ,self.fact_dict.items() )
		fact_comm_decs = map(lambda (fact_idx,fact_info): "MSRE_MPICOMM_INSTANCE<%s> %s_comm;" % (fact_info['fact_name'],fact_info['var_name'])
                                   ,filter(lambda (fact_idx,fact_info): not fact_info['local'], self.fact_dict.items()) )
		rule_app_counter_decs = map(lambda rule_name: "int %s_rule_count;" % rule_name, self.rule_names)
		store_dec_codes = []
		for (fact_idx,store_infos) in self.store_dict.items():
			for store_info in store_infos:
				store_dec_codes.append( "%s %s;" % (store_info['type'],store_info['name']) )
		constructor_codes    = self.generate_constructor( ensem_name )
		fact_member_codes    = self.generate_fact_members( ensem_name )
		receive_member_codes = self.generate_receive_member( ensem_name )

		join_exec_member_codes = []
		for fact_idx,join_orderings in self.prog.pred_rule_compilations.items():
			for i in range(0,len(join_orderings)):
				join_ordering = join_orderings[i]
				join_exec_member_codes.append( self.generate_join_ordering_member( ensem_name, join_ordering, i+1 ) )

		fact_exec_member_codes = map(lambda fact_idx: self.generate_fact_member(fact_idx), self.fact_dict.keys())

		spec_code = template('''
			{| '\\n'.join( extern_imports ) |}

			class {| ensem_name |} : public MSRE_NODE_INSTANCE {

				struct Fact : public Pretty, public HTML {
					virtual void execute({| ensem_name |}* node) = 0;
					virtual int priority() = 0;
				};

				{| '\\n'.join( fact_dec_codes ) |}

				{| index_dec_codes |}

				{| '\\n'.join( const_pred_id_decs ) |}
				
				const mpi::communicator world;
				const int rank;

				{| '\\n'.join( fact_comm_decs ) |}

				Goals<Fact>* goals;

				{| '\\n'.join( store_dec_codes ) |}

				COUNTER(
				{| '\\n'.join( rule_app_counter_decs ) |}
				int rule_app_misses;
				)

				{| constructor_codes |}

				{| boiler_plate_codes |}

				{| receive_member_codes |}

				{| fact_member_codes |}

				{| '\\n'.join( join_exec_member_codes ) |}

				{| '\\n'.join( fact_exec_member_codes ) |}

			};
		''')
		
		return compile_template( spec_code, ensem_name=ensem_name, extern_imports=extern_imports, fact_dec_codes=fact_dec_codes, index_dec_codes=index_dec_codes 
                                       , const_pred_id_decs=const_pred_id_decs, fact_comm_decs=fact_comm_decs, rule_app_counter_decs=rule_app_counter_decs
                                       , store_dec_codes=store_dec_codes, constructor_codes=constructor_codes, boiler_plate_codes=BOILER_PLATE_CODES 
                                       , receive_member_codes=receive_member_codes, fact_member_codes=fact_member_codes
                                       , join_exec_member_codes=join_exec_member_codes, fact_exec_member_codes=fact_exec_member_codes)

	def generate_fact_decs(self, ensem_name, fact_idx):

		fact_info = self.fact_dict[fact_idx]
		fact_name = fact_info['fact_name']
		arg_types = fact_info['types']
		num_of_args = len( arg_types )
		# kill_code   = ""
		# archive_alive_code = ""

		arg_dec_codes = [ "%s %s;" % (fact_info['loc_type'],fact_info['loc_name']) ]
		for (arg_name,type_code) in zip(fact_info['arg_names'],fact_info['type_codes']):
			arg_dec_codes.append( "%s %s;" % (type_code,arg_name) )	
		arg_dec_codes.append( "bool alive;" )
		# arg_dec_codes.append( "bool monotone;" )

		# if not fact_info['persistent']:
			# kill_code = "alive = false;"
			# archive_alive_code = "ar & alive;"

		constructor_args = [ "%s %s" % (fact_info['loc_type'],'l')  ]
		init_codes = [ "%s(%s)" % (fact_info['loc_name'],'l') ]
		for (arg_name,type_code,i) in zip(fact_info['arg_names'],fact_info['type_codes'],range(1,num_of_args+1)):
			constructor_args.append( "%s a%s" % (type_code,i) )
			init_codes.append( "%s(a%s)" % (arg_name,i) )
		# if not fact_info['persistent']:
		init_codes.append( "alive(true)" )

		# constructor_args.append( "bool mono" )
		# init_codes.append( "monotone(mono)" )
				

		type_codes     = [ fact_info['loc_type'] ] + fact_info['type_codes']
		arg_name_codes = [ fact_info['loc_name'] ] + fact_info['arg_names']

		str_subs = [ "%s" for i in range(num_of_args) ]
		

		if fact_info['uses_priority']:
			arg_dec_codes.append( "int prior;" )
			constructor_args.append("int p=1")
			init_codes.append( "prior(p)" )
			arg_name_plus_codes = []
			for arg_name in arg_name_codes:
				arg_name_plus_codes.append( arg_name )
			# arg_name_plus_codes.append( "monotone" )
			arg_name_plus_codes.append( "prior" )
			prior_member_codes = "int priority() { return prior; }"
		else:
			arg_name_plus_codes = arg_name_codes # + ["monotone"]
			prior_member_codes = "int priority() { return 1; }"

		arg_name_pretty_codes = map(lambda (pretty,name): pretty % name, zip(fact_info['pretty_codes'],arg_name_codes))

		arg_name_markdown_codes = map(lambda (markdown,name): markdown % name, zip(fact_info['markdown_codes'],arg_name_codes))   
		# [("print_markdown(aliases,%s)" % arg_name_codes[0])] + arg_name_pretty_codes[1:]

		# TODO: TDMONO

		fact_dec_code = template('''
			struct {| fact_name |} : Fact {
				{| '\\n'.join( arg_dec_codes ) |}

				{| fact_name |}() {}
				{| fact_name |}({| ', '.join( constructor_args ) |}) : {| ', '.join( init_codes ) |} {}
	
				{| join_ext_cond(',',type_codes,'tuple<','>') |} args() { return {| join_ext_cond(',',arg_name_codes,'make_tuple(',')') |}; }

				int node_id() { return {| loc_name |}; }

				string pretty() {
					return (format("{| loc_sub |}{| src_name |}({| ','.join( str_subs ) |})") % {| ' % '.join( arg_name_pretty_codes ) |} ).str();
				}

				string markdown() {
					bcont::map<int,string> aliases;
					return markdown(aliases);
				}

				string markdown(bcont::map<int,string> aliases) {
					return (format("{| loc_sub |}{| src_name |}({| ','.join( str_subs ) |})") % {| ' % '.join( arg_name_markdown_codes ) |} ).str();
				}

				void set_dead() { alive = false; }

				bool is_alive() { return alive; }

				void execute({| ensem_name |}* ensem) { ensem->execute( this ); }

				{| fact_name |}* identity() { return this; }

				{| fact_name |}* clone() { return new {| fact_name |}({| ','.join( map(lambda a: \"dcopy(%s)\" % a,arg_name_plus_codes) ) |}); }

				{| prior_member_codes |}

				friend class boost::serialization::access;
	
				template<class Archive>
				void serialize(Archive & ar, const unsigned int version) {
					{| '\\n'.join( map(lambda a: \"ar & %s;\" % a ,arg_name_plus_codes) ) |}
					ar & alive;
				}
			};
		''')

		if self.extract_data['pragmas']['solo']:
			loc_sub = ""
			arg_name_pretty_codes   = arg_name_pretty_codes[1:]
			arg_name_markdown_codes = arg_name_markdown_codes[1:]
		else:
			loc_sub = "[%s]"

		return compile_template(fact_dec_code, fact_name=fact_name, ensem_name=ensem_name, arg_dec_codes=arg_dec_codes, constructor_args=constructor_args
                                       ,init_codes=init_codes, type_codes=type_codes, arg_name_codes=arg_name_codes, arg_name_pretty_codes=arg_name_pretty_codes
                                       ,loc_name=fact_info['loc_name'], str_subs=str_subs, arg_name_plus_codes=arg_name_plus_codes, prior_member_codes=prior_member_codes
                                       ,src_name=fact_info['src_name'], arg_name_markdown_codes=arg_name_markdown_codes, loc_sub=loc_sub)

	def generate_store_index_decs(self, ensem_name):
		
		index_func_codes = []
		for fact_idx,store_infos in self.store_dict.items():
			fact_info = self.fact_dict[fact_idx]
			for idx in range(1,len(store_infos)+1):
				store_info = store_infos[idx-1]
				if store_info['sort'] == HASH_LK or store_info['sort'] == LOC_HASH_LK:
					if len( store_info['idx'] ) > 1:
						hash_values = map(lambda i: "(msre::hash(%s)*%s)" % (i['arg_name'],PRIME_NUMBERS[i['idx']]) , store_info['idx'])
					else:
						hash_values = [ store_info['idx'][0]['arg_name'] ]
					index_func_code = template('''
						size_t {| idx_func_name |}({| ', '.join( constr_args ) |}) {
							return {| ' + '.join( hash_values ) |};
						}
					''')
					constr_args = map(lambda i: "%s %s" % (i['type_code'],i['arg_name']) ,store_info['idx'])
					index_func_codes.append(
						compile_template(index_func_code, idx_func_name=store_info['idx_func'], constr_args=constr_args
                                                                ,hash_values=hash_values)
					)
		store_codes = template('''
			{| '\\n'.join( index_func_codes ) |}
		''')

		return compact( compile_template(store_codes, index_func_codes=index_func_codes) )

	def generate_constructor(self, ensem_name):
				
		rule_app_counter_codes = map(lambda rule_name: "%s_rule_count = 0;" % rule_name, self.rule_names)

		store_init_codes = []
		store_logger_codes = []
		repr_init_codes = []
		for fact_idx in self.store_dict:
			fact_name = self.fact_dict[fact_idx]['fact_name']
			src_name  = self.fact_dict[fact_idx]['src_name']
			has_repr = False
			for store_info in self.store_dict[fact_idx]:
				store_init_code = template('''
					{| store_name |}.set_name(\"{| fact_name |} Store\");
					set_store_component( &{| store_name |} );
				''')
				store_init_codes.append( compile_template(store_init_code, store_name=store_info['name'], fact_name=src_name) )
				store_logger_codes.append( "set_logger_child( &%s,\"%s Store\" );" % (store_info['name'], fact_name) )	
				if not has_repr:
					repr_init_code = template("set_repr_component( &{| store_name |} );")
					repr_init_codes.append( compile_template(repr_init_code, store_name=store_info['name']) )
					has_repr = True

		fact_comm_init_codes_1 = []
		fact_comm_init_codes_2 = []
		fact_comm_logger_codes = []
		fact_comm_counter_codes = []
		for fact_idx in self.fact_dict:
			fact_info = self.fact_dict[fact_idx]
			if not fact_info['local']:
				var_name  = fact_info['var_name']
				fact_name = fact_info['fact_name']
				fact_comm_init_codes_1.append( "%s_comm = MSRE_MPICOMM_INSTANCE<%s>(%s_pred_id);" % (var_name,fact_name,var_name) )
				fact_comm_init_code_2 = template('''
					{| var_name |}_comm.init_send();
					{| var_name |}_comm.init_receive();
				''')
				fact_comm_init_codes_2.append( compile_template(fact_comm_init_code_2, var_name=var_name) )
				fact_comm_logger_codes.append( "set_logger_child( &%s_comm,\"%s Comm\");" % (var_name,fact_name) )
				fact_comm_counter_code = template('''
					set_pretty_counter("{| fact_name |} MPI messages sent", {| var_name |}_comm.get_send_counter());
					set_pretty_counter("{| fact_name |} MPI messages received", {| var_name |}_comm.get_recv_counter());
				''')
				fact_comm_counter_codes.append( compile_template(fact_comm_counter_code, fact_name=fact_name, var_name=var_name) )

		rule_counter_codes = []
		for rule_name in self.rule_names:
			rule_counter_codes.append( "set_pretty_counter(\"%s rule applications\", &%s_rule_count);" % (rule_name,rule_name) )		

		constructor_code = template('''
			public: {| ensem_name |}() : rank(world.rank()) {

				exist_counter = 0;

				COUNTER(
				{| '\\n'.join( rule_app_counter_codes ) |}
				rule_app_misses = 0;
				);

				dir   = new MSRE_DIRECTORY_INSTANCE(world.size());
				goals = new MSRE_GOAL_INSTANCE<Fact>();
	
				set_pretty_component( goals );

				{| '\\n'.join( store_init_codes ) |}

				{| '\\n'.join( repr_init_codes ) |}

				{| '\\n'.join( fact_comm_init_codes_1 ) |}

				LOG(
				string logger_name = (format("node%s") % rank).str();
				init_logger(logger_name, logger_name, "Main");
				set_logger_child( goals, "Goals" );
				{| '\\n'.join( store_logger_codes ) |}
				{| '\\n'.join( fact_comm_logger_codes ) |}
				);

				{| '\\n'.join( fact_comm_init_codes_2 ) |}

				COUNTER(
				{| '\\n'.join( rule_counter_codes ) |}
				set_pretty_counter("Store iteration misses", &rule_app_misses);
				{| '\\n'.join( fact_comm_counter_codes ) |}
				);

			}
		''')

		return compile_template(constructor_code, ensem_name=ensem_name, rule_app_counter_codes=rule_app_counter_codes
                                       ,store_init_codes=store_init_codes, fact_comm_init_codes_1=fact_comm_init_codes_1, store_logger_codes=store_logger_codes
                                       ,fact_comm_init_codes_2=fact_comm_init_codes_2 , fact_comm_logger_codes=fact_comm_logger_codes 
                                       ,fact_comm_counter_codes=fact_comm_counter_codes, rule_counter_codes=rule_counter_codes
                                       ,repr_init_codes=repr_init_codes )

	def generate_fact_members(self, ensem_name):

		# TODO: TDMONO
	
		store_member_codes = []
		add_member_codes   = []
		send_member_codes  = []
		for fact_idx in self.fact_dict:
			fact_info = self.fact_dict[fact_idx]
			fact_name = fact_info['fact_name']
			var_name  = fact_info['var_name']
			add_to_store_codes = []
			for store_info in self.store_dict[fact_idx]:
				if store_info['has_index']:
					xs = (store_info['name'],var_name,store_info['idx_func']
                                             ,','.join(map(lambda idx: "(*%s).%s" % (var_name,idx['arg_name']) ,store_info['idx'])) )
					add_to_store_codes.append( "%s.add( %s, %s(%s) );" % xs )
				else:
					xs = (store_info['name'], var_name)
					add_to_store_codes.append( "%s.add( %s );" % xs )
			store_member_code = template('''
				private: void store({| fact_name |}* {| var_name |}) {
					{| '\\n'.join( add_to_store_codes ) |}
				} 				
			''')			
			store_member_codes.append( compile_template(store_member_code, fact_name=fact_name, var_name=var_name
                                                                   ,add_to_store_codes=add_to_store_codes) )
			arg_decs  = map(lambda (t,n): "%s %s" % (t,n) ,zip(fact_info['type_codes'],fact_info['arg_names']))

			# monotone = "true"
			arg_calls = fact_info['arg_names'] # + [monotone]

			if fact_info['monotone']:
				add_cons_codes = compile_template(template('''
							goals->add( new {| fact_name |}(loc{| join_ext(',', arg_calls, prefix=',') |}) );
					         '''), fact_name=fact_name, arg_calls=arg_calls)
			else:
				template_args = { 'fact_name' : fact_name
                                                , 'arg_calls' : arg_calls }
				add_cons_codes = compile_template(template('''
							{| fact_name |}* temp = new {| fact_name |}(loc{| join_ext(',', arg_calls, prefix=',') |});
							goals->add( temp );
							store( temp );
                                                 '''), **template_args)

			add_member_code = template('''
				public: void add_{| var_name |}(int loc{| join_ext(',', arg_decs, prefix=',') |}) {
					int dest = lookup_dir( loc );
					if (dest == rank) {
						{| add_cons_codes |}
					}
				}
			''')
			add_member_codes.append( compile_template(add_member_code, var_name=var_name
                                                                 ,arg_decs=arg_decs, add_cons_codes=add_cons_codes) )
			if not self.fact_dict[fact_idx]['local']:
				# TODO: Send accounts for non-monotone constraints, but not receive! Fix soon.
				if fact_info['monotone']:
					send_member_code = template('''
						private: void send({| fact_name |} {| var_name |}) {
							int dest = lookup_dir( {| var_name |}.node_id() );
							if (dest != rank) {
								{| var_name |}_comm.send( dest, {| var_name |}); 
							} else {
								goals->add( {| var_name |}.clone() );
							}
						}
					''')
				else:
					send_member_code = template('''
						private: void send({| fact_name |} {| var_name |}) {
							int dest = lookup_dir( {| var_name |}.node_id() );
							if (dest != rank) {
								{| var_name |}_comm.send( dest, {| var_name |}); 
							} else {
								{| fact_name |}* temp = {| var_name |}.clone();
								goals->add( temp );
								store( temp );
							}
						}
					''')
				send_member_codes.append( compile_template(send_member_code, fact_name=fact_name, var_name=var_name) )

		fact_member_codes = template('''
			{| '\\n'.join( store_member_codes ) |}
			{| '\\n'.join( add_member_codes ) |}
			{| '\\n'.join( send_member_codes ) |}
		''')

		return compile_template( fact_member_codes, store_member_codes=store_member_codes, add_member_codes=add_member_codes
                                       , send_member_codes=send_member_codes )

	def generate_receive_member(self, ensem_name):
		receive_comm_codes = []
		send_codes = []
		recv_codes = []
		idx = 1
		for fact_idx in self.fact_dict:
			fact_info = self.fact_dict[fact_idx]
			var_name  = fact_info['var_name']
			fact_name = fact_info['fact_name']
			if not fact_info['local']:
				receive_comm_code = template('''
					optional<list<{| fact_name |}*> > opt_{| idx |} = {| var_name |}_comm.receive();
					if (opt_{| idx |}) {
						for (list<{| fact_name |}*>::iterator st = opt_{| idx |}->begin(); st != opt_{| idx |}->end(); st++) {
							goals->add( *st );
							received = true;
						}
					}				
				''')
				receive_comm_codes.append( compile_template(receive_comm_code, fact_name=fact_name, var_name=var_name, idx=idx) )
				idx += 1
				send_codes.append( "*(%s_comm.get_send_counter())" % var_name );
				recv_codes.append( "*(%s_comm.get_recv_counter())" % var_name );

		num_of_comm = idx - 1;

		receive_member_codes = template('''
			private: bool receive() {
				bool received = false;
				{| '\\n'.join( receive_comm_codes ) |}
				return received;
			}

			protected: bool globally_quiescence() {
				int ns1 [{| num_of_comm |}] = { {| ', '.join( send_codes ) |} };
				int ns2 [{| num_of_comm |}] = { {| ', '.join( recv_codes ) |} };
				return all_eq_sum<{| num_of_comm |}>(ns1, ns2);
			}
		''')
		return compile_template(receive_member_codes, receive_comm_codes=receive_comm_codes, num_of_comm=num_of_comm
                                       ,send_codes=send_codes, recv_codes=recv_codes)

	def generate_fact_lhs(self, fact_idx, loc_fact, fact_var_name, head_idx, var_ctxt):
		fact_info = self.fact_dict[fact_idx]
		orig_pat_vars  = [mk_cpp_var_name(loc_fact.loc.name)] + map(lambda t: mk_cpp_var_name(t.name), loc_fact.fact.terms)

		idx_var_eq = []
		mod_pat_vars = []
		for i in range(0,len(orig_pat_vars)):
			if orig_pat_vars[i] in var_ctxt:
				idx_var_eq.append( "is_eq(%s,%s%s)" % (orig_pat_vars[i],orig_pat_vars[i],head_idx) )
				mod_pat_vars.append( "%s%s" % (orig_pat_vars[i],head_idx) )
			else:
				mod_pat_vars.append( orig_pat_vars[i])

		arg_decs   = map(lambda (t,v): "%s %s;" % (t,v) , zip([fact_info['loc_type']]+fact_info['type_codes'],mod_pat_vars)) 
		if len(mod_pat_vars) > 1:
			arg_unpack = "tie(%s) = (*%s).args();" % (','.join(mod_pat_vars),fact_var_name)
		else:
			arg_unpack = "%s = (*%s).args();" % (mod_pat_vars[0],fact_var_name)
		fact_lhs_codes = template('''
			{| ' '.join( arg_decs ) |}
			{| arg_unpack |}
		''')
		return orig_pat_vars,compile_template(fact_lhs_codes, arg_decs=arg_decs, arg_unpack=arg_unpack),idx_var_eq

	def generate_join_ordering_member(self, ensem_name, join_ordering, join_idx):

		fact_idx  = join_ordering.fact_idx
		fact_info = self.fact_dict[fact_idx]
		fact_type = fact_info['fact_name']
		fact_var  = fact_info['var_name']
		arg_types = fact_info['type_codes']

		join_member_name = "execute_%s_join_ordering_%s" % (fact_var, join_idx)

		l_args = (join_member_name,"%s","%")
		logging_code = "LOG_RULE_APP( record((format(\"Attempting occurrence %s on %s\") %s act->pretty()).str(), THIS_SRC) ); " % l_args
		
		if fact_idx in self.join_ordering_dict:
			self.join_ordering_dict[fact_idx].append( { 'member_name':join_member_name, 'always_continue':join_ordering.is_active_prop } )
		else:
			self.join_ordering_dict[fact_idx] = [{ 'member_name':join_member_name, 'always_continue':join_ordering.is_active_prop }]

		source_text = join_ordering.__repr__()

		# entry_pat = rule_spec['entry']
		# pat_vars,fact_lhs_codes = self.generate_fact_lhs( entry_pat, "act" )
		# active_task = join_ordering.activeTask()
		# pat_vars,fact_lhs_codes = self.generate_fact_lhs( active_task, "act" )

		# loc_var      = pat_vars[0]
		# delete_infos = []

		# rest_match_step_codes = self.generate_match_step(rule_spec['match_steps'] ,pat_vars, loc_var, 1, delete_infos, rule_spec)
		join_ordering_codes = self.generate_join_ordering(join_ordering, join_ordering.getJoinTasks(), {})

		join_member_codes = template('''
			/*
			{| source_text |}
			*/
			private: bool {| join_member_name |}({| fact_type |}* act) {
				{| logging_code |}
				{| join_ordering_codes |}
				return true;
			}
		''')

		return compile_template( join_member_codes, join_member_name=join_member_name, fact_type=fact_type, source_text=source_text
                                       , logging_code=logging_code, join_ordering_codes=join_ordering_codes)

	def generate_fact_member(self, fact_idx, join_ordering_info=None):
		if join_ordering_info == None:
			fact_info = self.fact_dict[fact_idx]
			fact_name = fact_info['fact_name']
			var_name  = fact_info['var_name']
			if fact_idx in self.join_ordering_dict:
				rest_exec_codes = compact( self.generate_fact_member(fact_idx, self.join_ordering_dict[fact_idx]) )
			else:
				rest_exec_codes = compact( self.generate_fact_member(fact_idx, []) )
			fact_exec_codes = template('''
				private: void execute({| fact_name |}* {| var_name |}) {
					{| rest_exec_codes |}
				}
			''')
			return compile_template(fact_exec_codes, fact_name=fact_name, var_name=var_name, rest_exec_codes=rest_exec_codes)
		else:
			if len(join_ordering_info) == 0:				
				fact_info = self.fact_dict[fact_idx]
				if fact_info['monotone']:
					store_codes = template("store( {| var_name |} );")
				else:
					store_codes = ""
				return compact( compile_template(store_codes, var_name=self.fact_dict[fact_idx]['var_name']) )
			else:
				this_join_ordering_info = join_ordering_info[0]
				rest_join_ordering_info = join_ordering_info[1:]
				if this_join_ordering_info['always_continue']:
					fact_exec_codes = template('''
						{| member_name |}( {| var_name |} );
						{| rest_exec_codes |}
					''')
				else:
					fact_exec_codes = template('''
						if( {| member_name |}({| var_name |}) ) {
							{| rest_exec_codes |}
						}
					''')

				rest_exec_codes = compact( self.generate_fact_member(fact_idx, rest_join_ordering_info) )
				return compile_template(fact_exec_codes, member_name=this_join_ordering_info['member_name']
                                                       ,var_name=self.fact_dict[fact_idx]['var_name']
                                                       ,rest_exec_codes=rest_exec_codes )

	# ==========================
	# Generating Join Orderings
	# ==========================

	def generate_join_ordering(self, join_ordering, join_tasks, join_head_dict):
		if len(join_tasks) > 0:
			curr_task  = join_tasks[0]
			rest_tasks = join_tasks[1:]
			template_args,join_ordering_template = self.generate_join_task(curr_task, join_head_dict)
			rest_tasks_code = self.generate_join_ordering(join_ordering, rest_tasks, join_head_dict)
			template_args['rest_tasks_code'] = rest_tasks_code
			return compact( compile_template(join_ordering_template, **template_args) )
		else:
			if join_ordering.is_active_prop: # join_ordering.is_propagated:
				escape_code = ""
			else:
				escape_code = "return false;"

			counter_code = "COUNTER(%s_rule_count++);" % join_ordering.getName()
			'''
			pat_var_list = []
			for pat_var in pat_vars:
				if pat_var not in pat_var_list:
					pat_var_list.append( pat_var )
			'''
			pat_var_list = all_pat_vars(join_head_dict)
			ls = (join_ordering.getName(), ','.join( map(lambda _: "%s",pat_var_list) )
                             ,"" if len(pat_var_list)==0 else ('% ' + ' % '.join( map(lambda v: "to_str(%s)" % v,pat_var_list) ) ))
			log_code = "LOG_RULE_APP( record((format(\"Applying %s(%s)\") %s).str(), THIS_SRC) ); " % ls

			end_rule_codes = template('''
				{| counter_code |}
				{| log_code |}
				{| escape_code |}
			''')

			return compile_template( end_rule_codes, counter_code=counter_code, log_code=log_code, escape_code=escape_code)


	@visit.on('join_task')
	def generate_join_task(self, join_task, join_head_dict):
		pass

	@visit.when(join.ActiveAtom)
	def generate_join_task(self, join_task, join_head_dict):
		pat_vars,fact_head_codes,_ = self.generate_fact_lhs(join_task.head.fact_idx, join_task.head.fact, "act"
                                                                   ,join_task.head_idx, all_pat_vars(join_head_dict))
		join_head_dict[join_task.head_idx] = { 'fact_idx' : join_task.head.fact_idx
                                                     , 'pat_vars' : pat_vars
                                                     , 'fact_var' : "act"
                                                     , 'head'     : join_task.head
                                                     , 'is_atom'  : True }

		if self.fact_dict[join_task.head.fact_idx]['monotone']:
			join_ordering_template = template('''
				{| source_text |}
				{| curr_task_code |}
				{| rest_tasks_code |}
			''')
		else:
			join_ordering_template = template('''
				{| source_text |}
				if (act->is_alive()) {
					{| curr_task_code |}			
					{| rest_tasks_code |}
				}
			''')
		template_args = { 'curr_task_code' : fact_head_codes
                                , 'source_text'    : mk_join_task_source_text( join_task ) }
		return template_args,join_ordering_template

	@visit.when(join.ActiveCompre)
	def generate_join_task(self, join_task, join_head_dict):
		pat_vars,fact_head_codes,_ = self.generate_fact_lhs(join_task.head.fact_idx, join_task.fact_pat, "act"
                                                                   ,join_task.head_idx, all_pat_vars(join_head_dict))
		join_head_dict[join_task.head_idx] = { 'fact_idx' : join_task.head.fact_idx
                                                     , 'pat_vars' : pat_vars
                                                     , 'fact_var' : "act"
                                                     , 'head'     : join_task.head
                                                     , 'is_atom'  : False }
		if self.fact_dict[join_task.head.fact_idx]['monotone']:
			join_ordering_template = template('''
				{| source_text |}
				{| curr_task_code |}
				{| rest_tasks_code |}
			''')
		else:
			join_ordering_template = template('''
				{| source_text |}
				if (act->is_alive()) {
					{| curr_task_code |}			
					{| rest_tasks_code |}
				}
			''')
		template_args = { 'curr_task_code' : fact_head_codes
                                , 'source_text'    : mk_join_task_source_text( join_task ) }
		return template_args,join_ordering_template

	@visit.when(join.CheckGuard)
	def generate_join_task(self, join_task, join_head_dict):
		context_codes,cond_codes = self.generate_term( join_task.guard.term )
		join_ordering_template = template('''
			{| source_text |}
			{| '\\n'.join( context_codes ) |}
			if ({| cond_codes |}) {
				{| rest_tasks_code |}
			}
		''')
		template_args = { 'context_codes' : context_codes
		                , 'cond_codes'    : cond_codes
                                , 'source_text'   : mk_join_task_source_text( join_task ) }
		return template_args,join_ordering_template

	@visit.when(join.LookupAtom)
	def generate_join_task(self, join_task, join_head_dict):

		# fact_pat = this_match_step['fact_pat']
		# sym_id   = fact_pat['sym_id']
		# store_info = self.store_decs[sym_id][this_match_step['lookup_index']]
		fact_pat = join_task.fact
		fact_idx = join_task.head.fact_idx
		lookup   = join_task.lookup
		store_info = self.store_dict[fact_idx][lookup.lookup_idx]
		cand_idx = join_task.head_idx

		# idx_vars   = map(mk_cpp_var_name,this_match_step['idx_vars'])
		idx_vars   = map(lambda iv: mk_cpp_var_name(iv.name), lookup.inputVars(join_task.head))

		if store_info['has_index']:
			index_func_app = "%s(%s)" % (store_info['idx_func'],','.join(idx_vars))
		else:
			index_func_app = ""

		fact_name  = self.fact_dict[fact_idx]['fact_name']
		cand_name  = "cand_%s" % cand_idx

		if self.fact_dict[fact_idx]['persistent']:
			get_next_code = "get_next()"
		else:
			get_next_code = "get_next_alive()"

		this_pat_vars,fact_lhs_codes,idx_var_eq = self.generate_fact_lhs(fact_idx, fact_pat, "*%s" % cand_name, cand_idx, all_pat_vars(join_head_dict))
		join_head_dict[join_task.head_idx] = { 'fact_idx' : fact_idx
                                                     , 'pat_vars' : this_pat_vars
                                                     , 'fact_var' : cand_name
                                                     , 'head'     : join_task.head
                                                     , 'is_atom'  : True }

		# TODO: Might not be always collision free.
		if store_info['collision_free']:
			report_collision_code = ""
		else:
			msg_str = "\"Collision on %s found: %s is not a compatiable candidate.\"" % ("%s","%s")
			l_args = "cand_%s %s (**%s).pretty()" % (cand_idx," % ",cand_name)
			report_collision_code = "LOG_RULE_APP( record((format(%s) %s %s).str(), THIS_SRC) );" % (msg_str,"%",l_args)

		l_args = (cand_name,"%s","%","(**%s).pretty()" % cand_name)
		logging_codes = "LOG_RULE_APP( record((format(\"Candidate for %s found -> %s\") %s %s).str(), THIS_SRC) ); " % l_args

		if not store_info['collision_free']: # len(idx_var_eq) > 0:
			join_ordering_template = template('''
				{| source_text |}
				{| iter_type |} candidates_{| cand_idx |} = {| store_name |}.lookup_candidates({| index_func_app |});
				optional<{| fact_name |}*> {| cand_name |} = candidates_{| cand_idx |}.{| get_next_code |};
				while({| cand_name |}) {
					{| fact_lhs_codes |}
					{| logging_codes |}
					#ifdef MSRE_HASH_COLLISION_CHECK
					if ({| ' && '.join( idx_var_eq ) |}) {
						{| rest_tasks_code |}
					} else {
						{| report_collision_code |}
					}
					#else
					{| rest_tasks_code |}
					#endif
					{| cand_name |} = candidates_{| cand_idx |}.{| get_next_code |};
				}
			''') 
		else:
			join_ordering_template = template('''
				{| source_text |}
				{| iter_type |} candidates_{| cand_idx |} = {| store_name |}.lookup_candidates({| index_func_app |});
				optional<{| fact_name |}*> {| cand_name |} = candidates_{| cand_idx |}.{| get_next_code |};
				while({| cand_name |}) {
					{| fact_lhs_codes |}
					{| logging_codes |}
					{| rest_tasks_code |}
					{| cand_name |} = candidates_{| cand_idx |}.{| get_next_code |};
				}
			''')

		template_args = { 'iter_type'      : store_info['iter']
		                , 'cand_idx'       : cand_idx 
		                , 'store_name'     : store_info['name']
		                , 'index_func_app' : index_func_app
		                , 'fact_name'      : fact_name
		                , 'cand_name'      : cand_name
		                , 'fact_lhs_codes' : fact_lhs_codes 
		                , 'idx_var_eq'     : idx_var_eq
		                , 'get_next_code'  : get_next_code
		                , 'logging_codes'  : logging_codes
		                , 'report_collision_code' : report_collision_code
		                , 'source_text'    : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	@visit.when(join.LookupAll)
	def generate_join_task(self, join_task, join_head_dict):
		
		fact_pat = join_task.fact_pat
		fact_idx = join_task.head.fact_idx
		lookup   = join_task.lookup
		store_info = self.store_dict[fact_idx][lookup.lookup_idx]
		cand_idx = join_task.head_idx
		idx_vars   = map(lambda iv: mk_cpp_var_name(iv.name), lookup.inputVars(join_task.head))

		if store_info['has_index']:
			index_func_app = "%s(%s)" % (store_info['idx_func'],','.join(idx_vars))
		else:
			index_func_app = ""

		fact_name  = self.fact_dict[fact_idx]['fact_name']
		cand_name  = "cand_%s" % cand_idx

		if self.fact_dict[fact_idx]['persistent']:
			get_next_code = "get_next()"
		else:
			get_next_code = "get_next_alive()"

		this_pat_vars,fact_lhs_codes,idx_var_eq = self.generate_fact_lhs(fact_idx, fact_pat, "*%s" % cand_name, cand_idx, all_pat_vars(join_head_dict))
		iter_name = "candidates_%s" % cand_idx
		iter_mod  = 0

		compre_vars = map(lambda iv: mk_cpp_var_name(iv.name), join_task.term_vars)
		extern_pat_vars = []
		for pat_var in this_pat_vars:
			if pat_var not in compre_vars:
				extern_pat_vars.append( pat_var )

		join_head_dict[join_task.head_idx] = { 'fact_idx' : fact_idx
                                                     , 'pat_vars' : extern_pat_vars
                                                     , 'fact_var' : iter_name
                                                     , 'head'     : join_task.head
                                                     , 'is_atom'  : False
                                                     , 'fact_pat' : fact_pat
                                                     , 'iter_mod' : iter_mod }

		# TODO: Might not be always collision free.
		msg_str = "\"Collision on %s found: %s is not a compatiable candidate.\"" % ("%s","%s")
		l_args = "cand_%s %s (**%s).pretty()" % (cand_idx," % ",cand_name)
		report_collision_code = "LOG_RULE_APP( record((format(%s) %s %s).str(), THIS_SRC) );" % (msg_str,"%",l_args)

		template_args = { 'old_iter_type'  : store_info['iter']
                                , 'old_iter_name'  : iter_name
                                , 'store_name'     : store_info['name']
                                , 'index_func_app' : index_func_app 
		                , 'source_text'    : mk_join_task_source_text( join_task ) }

		if store_info['collision_free']: # len(idx_var_eq) == 0:
			join_ordering_template = template('''
				{| source_text |}
				{| old_iter_type |} {| old_iter_name |} = {| store_name |}.lookup_candidates({| index_func_app |});
				{| rest_tasks_code |}
			''')
			# join_head_dict[join_task.head_idx]['idx_var_eq'] = idx_var_eq
		else:
			new_iter_name = "%s_%s" % (iter_name,iter_mod)
			new_iter_type = "CompreIter<%s>" % fact_name
			join_head_dict[join_task.head_idx]['fact_var'] = new_iter_name
			join_head_dict[join_task.head_idx]['iter_mod'] = iter_mod + 1

			template_args['new_iter_type'] = new_iter_type
			template_args['new_iter_name'] = new_iter_name
			template_args['fact_name']  = fact_name
			template_args['cand_name']  = cand_name
			template_args['fact_lhs_codes'] = fact_lhs_codes 
			template_args['idx_var_eq']     = idx_var_eq
			template_args['get_next_code']  = get_next_code
			# template_args['logging_codes']  = logging_codes
			# template_args['report_collision_code'] = report_collision_code

			join_ordering_template = template('''
				{| source_text |}
				{| old_iter_type |} {| old_iter_name |} = {| store_name |}.lookup_candidates({| index_func_app |});
				{| new_iter_type |} {| new_iter_name |};
				optional<{| fact_name |}*> {| cand_name |} = {| old_iter_name |}.{| get_next_code |};
				while({| cand_name |}) {
					{| fact_lhs_codes |}
					if ({| ' && '.join( idx_var_eq ) |}) {
						{| new_iter_name |}.add( *{| cand_name |} );
					}
					{| cand_name |} = {| old_iter_name |}.{| get_next_code |};
				}
				{| new_iter_name |}.init_iter();
				{| rest_tasks_code |}
			''')
			
		return template_args,join_ordering_template

	@visit.when(join.FilterHead)
	def generate_join_task(self, join_task, join_head_dict):

		head_idx1  = join_task.head_idx1
		head_idx2  = join_task.head_idx2
		head_info1 = join_head_dict[head_idx1]
		head_info2 = join_head_dict[head_idx2]
		
		cand_idx  = join_task.head_idx1
		iter_mod  = head_info1['iter_mod']
		cand_name = "cand_%s_%s" % (cand_idx,iter_mod)
		old_iter_name = head_info1['fact_var']
		fact_idx  = head_info1['fact_idx']
		fact_name = self.fact_dict[fact_idx]['fact_name']
		fact_pat  = head_info1['fact_pat']

		head_info1['iter_mod'] = iter_mod + 1

		if self.fact_dict[fact_idx]['persistent']:
			get_next_code = "get_next()"
		else:
			get_next_code = "get_next_alive()"

		_,fact_lhs_codes,_ = self.generate_fact_lhs(fact_idx, fact_pat, "*%s" % cand_name, cand_idx, set([]))

		new_iter_name = "%s_%s" % (old_iter_name,iter_mod)
		new_iter_type = "CompreIter<%s>" % fact_name
		join_head_dict[cand_idx]['fact_var'] = new_iter_name
		join_head_dict[cand_idx]['iter_mod'] = iter_mod + 1

		template_args = { 'new_iter_type' : new_iter_type
                                , 'new_iter_name' : new_iter_name
                                , 'fact_name'     : fact_name
                                , 'cand_name'     : cand_name
                                , 'fact_lhs_codes': fact_lhs_codes
                                , 'old_iter_name' : old_iter_name
                                , 'get_next_code' : get_next_code
                                , 'source_text'   : mk_join_task_source_text( join_task ) }

		if head_info2['is_atom']:

			if head_idx2 != 0:
				head2_name = "**%s" % head_info2['fact_var']
			else:
				head2_name = "*%s" % head_info2['fact_var']

			join_ordering_template = template('''
				{| source_text |}
				{| new_iter_type |} {| new_iter_name |};
				optional<{| fact_name |}*> {| cand_name |} = {| old_iter_name |}.{| get_next_code |};
				while({| cand_name |}) {
					{| fact_lhs_codes |}
					if ((**{| cand_name |}).identity() != ({| head2_name |}).identity() ) {
						{| new_iter_name |}.add( *{| cand_name |} );
					}
					{| cand_name |} = {| old_iter_name |}.{| get_next_code |};
				}
				{| new_iter_name |}.init_iter();
				{| rest_tasks_code |}
			''')

			template_args['head2_name'] = head2_name

		else:

			join_ordering_template = template('''
				{| source_text |}
				{| new_iter_type |} {| new_iter_name |};
				optional<{| fact_name |}*> {| cand_name |} = {| old_iter_name |}.{| get_next_code |};
				while({| cand_name |}) {
					{| fact_lhs_codes |}
					if ( !{| iter2_name |}.contains( *{| cand_name |} ) ) {
						{| new_iter_name |}.add( *{| cand_name |} );
					}
					{| cand_name |} = {| old_iter_name |}.{| get_next_code |};
				}
				{| new_iter_name |}.init_iter();
				{| rest_tasks_code |}
			''')

			template_args['iter2_name'] = head_info2['fact_var']

		return template_args,join_ordering_template

	@visit.when(join.FilterGuard)
	def generate_join_task(self, join_task, join_head_dict):

		cand_idx = join_task.head_idx
		head_info = join_head_dict[join_task.head_idx]
		iter_mod  = head_info['iter_mod']
		cand_name = "cand_%s_%s" % (cand_idx,iter_mod)
		old_iter_name = head_info['fact_var']
		fact_idx  = head_info['fact_idx']
		fact_name = self.fact_dict[fact_idx]['fact_name']
		fact_pat  = head_info['fact_pat']

		head_info['iter_mod'] = iter_mod + 1

		if self.fact_dict[fact_idx]['persistent']:
			get_next_code = "get_next()"
		else:
			get_next_code = "get_next_alive()"

		_,fact_lhs_codes,_ = self.generate_fact_lhs(fact_idx, fact_pat, "*%s" % cand_name, cand_idx, set([]))

		new_iter_name = "%s_%s" % (old_iter_name,iter_mod)
		new_iter_type = "CompreIter<%s>" % fact_name
		join_head_dict[cand_idx]['fact_var'] = new_iter_name
		join_head_dict[cand_idx]['iter_mod'] = iter_mod + 1

		guard_context_codes = []
		guard_cond_codes    = [] # join_head_dict[cand_idx]['idx_var_eq']
		for guard in join_task.guards:
			guard_context_code,guard_cond_code = self.generate_term( guard.term )
			guard_context_codes += guard_context_code
			guard_cond_codes += [guard_cond_code]

		join_ordering_template = template('''
			{| source_text |}
			{| new_iter_type |} {| new_iter_name |};
			optional<{| fact_name |}*> {| cand_name |} = {| old_iter_name |}.{| get_next_code |};
			while({| cand_name |}) {
				{| fact_lhs_codes |}
				{| '\\n'.join( guard_context_codes ) |}
				if ({| ' && '.join( guard_cond_codes ) |}) {
					{| new_iter_name |}.add( *{| cand_name |} );
				}
				{| cand_name |} = {| old_iter_name |}.{| get_next_code |};
			}
			{| new_iter_name |}.init_iter();
			{| rest_tasks_code |}
		''')

		template_args = { 'new_iter_type'  : new_iter_type
                                , 'new_iter_name'  : new_iter_name
                                , 'fact_name'      : fact_name
                                , 'cand_name'      : cand_name
                                , 'old_iter_name'  : old_iter_name
                                , 'get_next_code'  : get_next_code
                                , 'fact_lhs_codes' : fact_lhs_codes
                                , 'guard_context_codes' : guard_context_codes
                                , 'guard_cond_codes'    : guard_cond_codes
		                , 'source_text'    : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	@visit.when(join.CompreDomain)
	def generate_join_task(self, join_task, join_head_dict):

		cand_idx = join_task.head_idx
		head_info = join_head_dict[join_task.head_idx]
		iter_mod  = head_info['iter_mod']
		cand_name = "cand_%s_%s" % (cand_idx,iter_mod)
		iter_name = head_info['fact_var']
		fact_idx  = head_info['fact_idx']
		fact_name = self.fact_dict[fact_idx]['fact_name']
		fact_pat  = head_info['fact_pat']

		term_vars  = join_task.term_vars
		compre_dom = join_task.compre_dom

		cpp_type_corece = CPPTypeCoercion()
		# print "Hurry! %s" % compre_dom.type
		compre_dom_type = cpp_type_corece.coerce_cpp_type_codes( compre_dom.type )
		# print compre_dom_type
		compre_dom_name = mk_cpp_var_name( compre_dom.name )
		if len(term_vars) > 1:
			compre_dom_elem = "make_tuple(%s)" % (','.join(map(lambda tv: mk_cpp_var_name(tv.name),term_vars))) 
		else:
			compre_dom_elem = mk_cpp_var_name(term_vars[0].name)

		if self.fact_dict[fact_idx]['persistent']:
			get_next_code = "get_next()"
		else:
			get_next_code = "get_next_alive()"

		_,fact_lhs_codes,_ = self.generate_fact_lhs(fact_idx, fact_pat, "*%s" % cand_name, cand_idx, set([]))

		head_info['iter_mod'] = iter_mod + 1

		head_info['pat_vars'].append( compre_dom_name )

		join_ordering_template = template('''
			{| source_text |}
			{| compre_dom_type |} {| compre_dom_name |};
			optional<{| fact_name |}*> {| cand_name |} = {| iter_name |}.{| get_next_code |};
			while({| cand_name |}) {
				{| fact_lhs_codes |}
				{| compre_dom_name |}.push_back( {| compre_dom_elem |} );
				{| cand_name |} = {| iter_name |}.{| get_next_code |};
			}
			{| iter_name |}.init_iter();
			{| rest_tasks_code |}
		''')

		template_args = { 'compre_dom_type' : compre_dom_type
                                , 'compre_dom_name' : compre_dom_name
                                , 'compre_dom_elem' : compre_dom_elem
                                , 'fact_name'       : fact_name
                                , 'cand_name'       : cand_name
                                , 'iter_name'       : iter_name
                                , 'get_next_code'   : get_next_code
                                , 'fact_lhs_codes'  : fact_lhs_codes
		                , 'source_text'     : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	@visit.when(join.NeqHead)
	def generate_join_task(self, join_task, join_head_dict):
		head_idx1  = join_task.head_idx1
		head_idx2  = join_task.head_idx2 
		head_info1 = join_head_dict[head_idx1]
		head_info2 = join_head_dict[head_idx2]
		monotone1 = self.fact_dict[head_info1['fact_idx']]['monotone']
		monotone2 = self.fact_dict[head_info2['fact_idx']]['monotone']
		if (head_idx1 != 0 or (head_idx1 == 0 and not monotone1)) and (head_idx2 != 0 or (head_idx2 == 0 and not monotone2)):
			fact_var1 = ("**%s" if head_idx1 != 0 else "*%s") % join_head_dict[head_idx1]['fact_var']
			fact_var2 = ("**%s" if head_idx2 != 0 else "*%s") % join_head_dict[head_idx2]['fact_var']
			neq_head_cond =	"(%s).identity() != (%s).identity()" % (fact_var1,fact_var2)
			# msg_str = "\"Collision on %s found: %s is not a compatiable candidate.\"" % ("%s","%s")
			# l_args = "cand_%s %s (**%s).pretty()" % (cand_idx," % ",cand_name)
			# report_collision_code = "LOG_RULE_APP( record((format(%s) %s %s).str(), THIS_SRC) );" % (msg_str,"%",l_args)
			join_ordering_template = template('''
				{| source_text |}
				if ({| neq_head_cond |}) {
					{| rest_tasks_code |}
				}
			''')
			template_args = { 'neq_head_cond' : neq_head_cond
                                        , 'source_text'   : mk_join_task_source_text( join_task ) }
			return template_args,join_ordering_template
		else:
			join_ordering_template = template('''
				{| source_text |}
				{| rest_tasks_code |}
			''')
			return { 'source_text' : mk_join_task_source_text( join_task ) },join_ordering_template

	@visit.when(join.DeleteHead)
	def generate_join_task(self, join_task, join_head_dict):
		head_info = join_head_dict[join_task.head_idx]
		monotone = self.fact_dict[head_info['fact_idx']]['monotone']
		if (join_task.head_idx != 0) or (join_task.head_idx == 0 and not monotone):
			head      = head_info['head']
			store_name = self.store_dict[head.fact_idx][0]['name']
			if head_info['is_atom']:
				cand_name  = join_head_dict[join_task.head_idx]['fact_var']
				join_ordering_template = template('''
					{| source_text |}
					{| store_name |}.remove( {| cand_name |} );
					{| rest_tasks_code |}
				''')
				template_args = { 'store_name'  : store_name
		                                , 'source_text' : mk_join_task_source_text( join_task ) }
				if join_task.head_idx == 0:
					template_args['cand_name'] = cand_name
				else:
					template_args['cand_name'] = "*%s" % cand_name
				return template_args,join_ordering_template
			else:
				
				cand_idx = join_task.head_idx
				head_info = join_head_dict[join_task.head_idx]
				iter_mod  = head_info['iter_mod']
				cand_name = "cand_%s_%s" % (cand_idx,iter_mod)
				iter_name = head_info['fact_var']
				fact_idx  = head_info['fact_idx']
				fact_name = self.fact_dict[fact_idx]['fact_name']
				fact_pat  = head_info['fact_pat']

				if self.fact_dict[fact_idx]['persistent']:
					get_next_code = "get_next()"
				else:
					get_next_code = "get_next_alive()"

				_,fact_lhs_codes,_ = self.generate_fact_lhs(fact_idx, fact_pat, "*%s" % cand_name, cand_idx, set([]))

				join_ordering_template = template('''
					{| source_text |}
					optional<{| fact_name |}*> {| cand_name |} = {| iter_name |}.{| get_next_code |};
					while({| cand_name |}) {
						{| store_name |}.remove( *{| cand_name |} );
						{| cand_name |} = {| iter_name |}.{| get_next_code |};
					}
					{| rest_tasks_code |}
				''')
				template_args = { 'fact_name'     : fact_name
                                                , 'cand_name'     : cand_name
                                                , 'iter_name'     : iter_name
                                                , 'get_next_code' : get_next_code
                                                , 'store_name'    : store_name
		                                , 'source_text'   : mk_join_task_source_text( join_task ) }

				return template_args,join_ordering_template
		else:
			join_ordering_template = template('''
				{| source_text |}
				// H0 is active and monotone, no delete required
				{| rest_tasks_code |}
			''')
			return { 'source_text' : mk_join_task_source_text( join_task ) },join_ordering_template

	@visit.when(join.ExistDest)
	def generate_join_task(self, join_task, join_head_dict):
		cpp_type_coerce = CPPTypeCoercion()
		exist_term = join_task.exist_var
		exist_type = cpp_type_coerce.coerce_cpp_type_codes( exist_term.type )
		exist_name = mk_cpp_var_name(exist_term.name)
		loc_var = mk_cpp_var_name( local_loc_var(join_head_dict) )

		join_ordering_template = template('''
			{| source_text |}
			{| exist_type |} {| exist_name |} = next_exist_id({| loc_var |});
			{| rest_tasks_code |}
		''')
		template_args = { 'exist_type'  : exist_type
		                , 'exist_name'  : exist_name
		                , 'loc_var'     : loc_var 
                                , 'source_text' : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	@visit.when(join.ExistLoc)
	def generate_join_task(self, join_task, join_head_dict):
		cpp_type_coerce = CPPTypeCoercion()
		exist_loc = join_task.exist_var
		exist_loc_type = cpp_type_coerce.coerce_cpp_type_codes( exist_loc.type )
		exist_loc_name = mk_cpp_var_name(exist_loc.name)
		
		join_ordering_template = template('''
			{| source_text |}
			{| exist_loc_type |} {| exist_loc_name |} = dir->new_node();
			{| rest_tasks_code |}
		''')
		template_args = { 'exist_loc_type' : exist_loc_type
		                , 'exist_loc_name' : exist_loc_name
	                        , 'source_text'    : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	@visit.when(join.LetBind)
	def generate_join_task(self, join_task, join_head_dict):
		assign_dec = join_task.assign_dec
		# left_pat_context,left_pat_codes = self.generate_left_pattern(assign_dec.term_pat, assign_dec.term_pat.type)
		left_pat_context,left_pat_codes,left_pat_post = self.generate_left_pattern(assign_dec.term_pat)
		context_codes,assign_exp_codes = self.generate_term(assign_dec.builtin_exp)
		
		join_ordering_template = template('''
			{| source_text |}
			{| left_pat_context |}
			{| '\\n'.join( context_codes ) |}
			{| left_pat_codes |} = {| assign_exp_codes |};
			{| left_pat_post |}
			{| rest_tasks_code |}
		''')

		template_args = { 'left_pat_context' : left_pat_context
		                , 'left_pat_codes'   : left_pat_codes
                                , 'left_pat_post'    : left_pat_post
		                , 'context_codes'    : context_codes
		                , 'assign_exp_codes' : assign_exp_codes
		                , 'source_text'      : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	@visit.when(join.IntroAtom)
	def generate_join_task(self, join_task, join_head_dict):

		loc_fact = join_task.fact
		fact_idx = join_task.body.fact_idx
		body_idx = join_task.body_idx

		atom_body = self.generate_rhs_atom(loc_fact, fact_idx, join_task.priority, join_task.monotone, body_idx, join_head_dict)

		join_ordering_template = template('''
			{| source_text |}
			{| atom_body |}
			{| rest_tasks_code |}
		''')		

		template_args = { 'atom_body'   : atom_body
		                , 'source_text' : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	@visit.when(join.IntroCompre)
	def generate_join_task(self, join_task, join_head_dict):

		# TODO: Currently supports only one compre range

		compre_body = join_task.body.fact
		main_comp_range = compre_body.comp_ranges[0]
		compre_idx = join_task.compre_idx
		body_idx   = join_task.body_idx

		term_pat  = main_comp_range.term_vars  # body_fact['term_pat']
		term_subj = main_comp_range.term_range # body_fact['term_subj']
		facts     = compre_body.facts          # body_fact['facts']

		cpp_type_corece = CPPTypeCoercion()

		subj_type    = cpp_type_corece.coerce_cpp_type_codes( term_subj.type )
		subj_varname = "comp_%s" % compre_idx
		subj_context_codes,subj_exp   = self.generate_term( term_subj )
		# term_pat_context,term_pat_var = self.generate_left_pattern(term_pat, term_pat.type)
		term_pat_context,term_pat_var,term_pat_post = self.generate_left_pattern(term_pat)

		fact_atom_codes = []
		for loc_fact in facts:
			fact_idx,_ = self.fact_dir.getFactFromName( loc_fact.fact.name )
			fact_atom_codes.append( self.generate_rhs_atom(loc_fact, fact_idx, loc_fact.fact.priority, loc_fact.fact.monotone
                                                                      ,body_idx, join_head_dict) )

		join_ordering_template = template('''
			{| source_text |}
			{| '\\n'.join( subj_context_codes ) |}
			{| subj_type |} {| subj_varname |} = {| subj_exp |};
			for({| subj_type |}::iterator it={| subj_varname |}.begin(); it!={| subj_varname |}.end(); it++) {
				{| term_pat_context |}
				{| term_pat_var |} = *it;
				{| term_pat_post |}
				{| '\\n'.join( fact_atom_codes ) |}
			}
			{| rest_tasks_code |}
		''')

		template_args = { 'subj_type'    : subj_type
		                , 'subj_varname' : subj_varname
		                , 'subj_exp'     : subj_exp
		                , 'subj_context_codes' : subj_context_codes
		                , 'term_pat_context'   : term_pat_context
		                , 'term_pat_var'       : term_pat_var
                                , 'term_pat_post'      : term_pat_post
                                , 'fact_atom_codes'    : fact_atom_codes 
		                , 'source_text'        : mk_join_task_source_text( join_task ) }

		return template_args,join_ordering_template

	def generate_rhs_atom(self, loc_fact, fact_idx, priority, monotone, body_idx, join_head_dict):

		fact_info = self.fact_dict[fact_idx]
		fact_name = fact_info['fact_name']
		loc_var = mk_cpp_var_name( local_loc_var(join_head_dict) )

		fact_args = []
		arg_contexts = []
		for fact_arg in [loc_fact.loc] + loc_fact.fact.terms:
			context_codes,f_arg_codes = self.generate_term( fact_arg )
			fact_args.append( f_arg_codes )
			arg_contexts += context_codes

		# TODO: TDMONO

		# monotone = "true"
		# fact_args.append( monotone )
		# print ("Loc Vars: %s %s" % (body_fact['loc'].name,loc_var))
		if priority != None:
			fact_args.append( priority )

		if fact_args[0] == loc_var:
			xs = (fact_name,','.join(fact_args))
			if monotone:
				body_codes = "goals->add( new %s(%s) );" % xs 
			else:
				template_args = { 'fact_name' : fact_name
						, 'fact_args' : ','.join(fact_args)
                                                , 'body_name' : "body_%s" % body_idx }
				non_monotone_template = template('''	
{| fact_name |}* {| body_name |} = new {| fact_name |}({| fact_args |});
goals->add( {| body_name |} );
store( {| body_name |} );
				''')
				body_codes = compile_template(non_monotone_template, **template_args)
		else:
			xs = (fact_name,','.join(fact_args))
			body_codes = "send( %s(%s) );" % xs
		atom_template = template('''
			{| '\\n'.join( arg_contexts ) |}
			{| body_codes |}
		''')

		return compile_template(atom_template, arg_contexts=arg_contexts, body_codes=body_codes)

	'''
	# Let binding left patterns
	def generate_left_pattern(self, term_pat, type_sig):
		# print term_pat
		# print type_sig
		cpp_type_coerce = CPPTypeCoercion()

		if type_sig.type_kind == ast.TYPE_CONS:
			var_name = mk_cpp_var_name( term_pat.name )
			return "%s %s;" % (cpp_type_coerce.coerce_cpp_type_codes( term_pat.type ), var_name),var_name
		elif type_sig.type_kind == ast.TYPE_TUP:
			left_pat_contexts = []
			left_pat_codes    = []
			# Err: What if term_pat is not a tuple, but a variable of tuple type!!
			for (term,ty_sig) in zip(term_pat.terms,type_sig.types):
				left_pat_context,left_pat_code = self.generate_left_pattern(term, ty_sig)
				left_pat_contexts.append( left_pat_context )
				left_pat_codes.append( left_pat_code )
			lp_contexts = compile_template( template("{| '\\n'.join( left_pat_contexts ) |}"), left_pat_contexts=left_pat_contexts )
			lp_codes    = compile_template( template("tie({| ','.join( left_pat_codes ) |})"), left_pat_codes=left_pat_codes )
			return lp_contexts,lp_codes
		elif type_sig.type_kind in [ast.TYPE_LIST,ast.TYPE_MSET]:
			if term_pat.term_type == ast.TERM_VAR:
				var_name = mk_cpp_var_name( term_pat.name )
				return "%s %s;" % (cpp_type_coerce.coerce_cpp_type_codes( term_pat.type ), var_name),var_name
			elif term_pat.term_type == ast.TERM_LISTCONS:
				pass
			else:
				# TODO
				pass
		else:
			# TODO
			pass
	'''

	def generate_left_pattern(self, t):
		cpp_type_coerce = CPPTypeCoercion()
		
		if t.term_type == ast.TERM_VAR:
			var_name = mk_cpp_var_name( t.name )
			left_context_codes = "%s %s;" % (cpp_type_coerce.coerce_cpp_type_codes( t.type ), var_name)
			left_pattern_codes = var_name
			left_postproc_codes = ""

		elif t.term_type == ast.TERM_TUPLE:
			lp_contexts = []
			lp_codes    = []
			lp_posts    = []
			for sub_term in t.terms:
				lp_context,lp_code,lp_post = self.generate_left_pattern(sub_term)
				lp_contexts.append( lp_context )
				lp_codes.append( lp_code )
				lp_posts.append( lp_post )
			left_context_codes = compile_template( template("{| '\\n'.join( lp_contexts ) |}"), lp_contexts=lp_contexts )
			left_pattern_codes = compile_template( template("tie({| ','.join( lp_codes ) |})"), lp_codes=lp_codes )
			left_postproc_codes = compile_template( template("{| '\\n'.join( lp_posts ) |}"), lp_posts=lp_posts )

		elif t.term_type in [ast.TERM_LIST,ast.TERM_MSET]:
			lp_contexts = []
			lp_codes    = []
			lp_posts    = []
			for sub_term in t.terms:
				lp_context,lp_code,lp_post = self.generate_left_pattern(sub_term)
				lp_contexts.append( lp_context )
				lp_codes.append( lp_code )
				lp_posts.append( lp_post )
			cont_type = cpp_type_coerce.coerce_cpp_type_codes( t.type )
			cont_name = self.next_temp_var_name()
			iter_name = self.next_temp_var_name()
			left_context_codes = compile_template( template('''
				{| '\\n'.join( lp_contexts ) |}
				{| cont_type |} {| cont_name |};
			'''), lp_contexts=lp_contexts, cont_type=cont_type, cont_name=cont_name)
			left_pattern_codes = cont_name
			cont_assign_codes = map(lambda elem_name: "%s = *%s; %s++;" % (elem_name,iter_name,iter_name), lp_codes)
			left_postproc_codes = compile_template( template('''
				{| '\\n'.join( lp_posts ) |}
				{| cont_type |}::iterator {| iter_name |}={| cont_name |}.begin();
				{| '\\n'.join( cont_assign_codes ) |}
			'''), lp_posts=lp_posts, cont_type=cont_type, iter_name=iter_name, cont_name=cont_name
                            , cont_assign_codes=cont_assign_codes )

		elif t.term_type == ast.TERM_LISTCONS:
			head_context,head_code,head_post = self.generate_left_pattern( t.term1 )
			tail_context,tail_code,tail_post = self.generate_left_pattern( t.term2 )
			cont_type = cpp_type_coerce.coerce_cpp_type_codes( t.type )
			cont_name = self.next_temp_var_name()
			iter_name = self.next_temp_var_name()
			left_context_codes = compile_template( template('''
				{| head_context |}
				{| tail_context |}
				{| cont_type |} {| cont_name |};
			'''), head_context=head_context, tail_context=tail_context, cont_type=cont_type, cont_name=cont_name)
			left_pattern_codes = cont_name
			left_postproc_codes = compile_template( template('''
				{| head_post |}
				{| tail_post |}
				{| cont_type |}::iterator {| iter_name |}={| cont_name |}.begin();
				{| head_code |} = *{| iter_name |};
				{| iter_name |}++;
				while({|iter_name|}!={| cont_name |}.end()) {
					{| tail_code |}.push_back(*{| iter_name |});
					{| iter_name |}++;
				}
			'''), head_post=head_post, tail_post=tail_post, cont_type=cont_type, iter_name=iter_name, cont_name=cont_name
                            , head_code=head_code, tail_code=tail_code)

		return left_context_codes,left_pattern_codes,left_postproc_codes


	# TODO: handle all types of terms
	def generate_term(self, t):
		cpp_type_coerce = CPPTypeCoercion()
		if t.term_type == ast.TERM_BINOP:
			cx1,t1_codes = self.generate_term( t.term1 )
			cx2,t2_codes = self.generate_term( t.term2 )
			context_codes = cx1 + cx2
			term_codes = "%s %s %s" % (t1_codes,t.op,t2_codes)
		elif t.term_type == ast.TERM_VAR:
			context_codes = []
			term_codes = mk_cpp_var_name( t.name )
		elif t.term_type == ast.TERM_LIT:
			context_codes = []
			term_codes = str(t.literal)
		elif t.term_type == ast.TERM_CONS:
			context_codes = []
			term_codes = t.name
		elif t.term_type == ast.TERM_APP:
			cx1,t1_codes = self.generate_term( t.term1 )
			cx2,t2_codes = self.generate_term( t.term2 )
			context_codes = cx1 + cx2
			if t.term2.term_type == ast.TERM_TUPLE:
				# TODO: ugly hack! Need to make uncurried function app first class!
				term_codes = "%s%s" % (t1_codes,t2_codes[10:])
			else:
				term_codes = "%s(%s)" % (t1_codes,t2_codes)
		elif t.term_type == ast.TERM_TUPLE:
			context_codes = []
			t_codes = []
			for t in t.terms:
				cx,t_code = self.generate_term( t )
				context_codes += cx
				t_codes.append( t_code )
			term_codes = "make_tuple(%s)" % ','.join(t_codes)
		elif t.term_type in [ast.TERM_LIST,ast.TERM_MSET]:
			context_codes = []
			t_codes = []
			for term in t.terms:
				cx,t_code = self.generate_term( term )
				context_codes += cx
				t_codes.append( t_code )
			term_var = self.next_temp_var_name()
			inspect = Inspector()
			# print "%s" % t.inferred_type
			context_codes.append( "%s %s[] = { %s };" % (cpp_type_coerce.coerce_cpp_type_codes(t.type.type),term_var,','.join(t_codes)) )
			term_codes = "tolist(%s,%s)" % (term_var,str(len(t.terms)))
		elif t.term_type == ast.TERM_LISTCONS:
			cx1,head_code = self.generate_term( t.term1 )
			cx2,tail_code = self.generate_term( t.term2 )
			cont_type = cpp_type_coerce.coerce_cpp_type_codes(t.type)
			cont_var  = self.next_temp_var_name()
			context_template = template('''
				{|cont_type|} {|cont_var|} = {|tail_code|};
				{|cont_var|}.push_front({|head_code|});
			''')

			context_codes  = cx1 + cx2
			context_codes += [ compile_template(context_template, cont_type=cont_type, cont_var=cont_var
                                                           ,head_code=head_code, tail_code=tail_code) ]
			term_codes = cont_var

		elif t.term_type == ast.TERM_ENUM_MSET:
			cx1,lower_val = self.generate_term( t.texp1 )
			cx2,upper_val = self.generate_term( t.texp2 )

			context_code = template('''
				{|cont_type|} {|cont_var|};
				for({|elem_type|} {|elem_var|}={|lower_val|}; {|elem_var|}<{|upper_val|}; {|elem_var|}++) {
					{|cont_var|}.push_back({|elem_var|});
				}
			''')

			cont_type = cpp_type_coerce.coerce_cpp_type_codes( t.type )
			elem_type = cpp_type_coerce.coerce_cpp_type_codes( t.type.type )
			cont_var = self.next_temp_var_name()
			elem_var = self.next_temp_var_name()

			context_codes  = cx1 + cx2 
			context_codes += [ compile_template(context_code, cont_type=cont_type, elem_type=elem_type, cont_var=cont_var
                                                           ,elem_var=elem_var, upper_val=upper_val, lower_val=lower_val) ]

			term_codes = cont_var
		elif t.term_type == ast.TERM_COMPRE:

			# TODO: Currently only handles single comprehension domain
			main_comp_range = t.comp_ranges[0]
			term_pat  = main_comp_range.term_vars  
			term_subj = main_comp_range.term_range           

			# Generate comprehension domain codes
			subj_type    = cpp_type_coerce.coerce_cpp_type_codes( term_subj.type )
			subj_varname = self.next_temp_var_name()
			subj_context_codes,subj_exp   = self.generate_term( term_subj )
			# term_pat_context,term_pat_var = self.generate_left_pattern(term_pat, term_pat.type)
			term_pat_context,term_pat_var,term_pat_post = self.generate_left_pattern(term_pat)

			# Generate guard codes
			guard_context_codes = []
			guard_cond_codes    = [] 
			has_guards = False
			for guard in t.guards:
				guard_context_code,guard_cond_code = self.generate_term( guard )
				guard_context_codes += guard_context_code
				guard_cond_codes += [guard_cond_code]
				has_guards = True

			# Generate term pattern codes
			term_out_context,term_out_var = self.generate_term( t.term )

			# Output term comprehension entities
			comp_out_type = cpp_type_coerce.coerce_cpp_type_codes( t.type )
			comp_out_var  = self.next_temp_var_name()

			if has_guards:
				tcomp_template = template('''
					{| '\\n'.join( subj_context_codes ) |}
					{| comp_out_type |} {| comp_out_var |};
					{| subj_type |} {| subj_varname |} = {| subj_exp |};
					for({| subj_type |}::iterator it={| subj_varname |}.begin(); it!={| subj_varname |}.end(); it++) {
						{| term_pat_context |}
						{| term_pat_var |} = *it;
						{| term_pat_post |}
						{| '\\n'.join( guard_context_codes ) |}
						if ({| ' && '.join( guard_cond_codes ) |}) {
							{| '\\n'.join(term_out_context) |}	
							{| comp_out_var |}.push_back( {| term_out_pat |} );
						}
					}
				''')
			else:
				tcomp_template = template('''
					{| '\\n'.join( subj_context_codes ) |}
					{| comp_out_type |} {| comp_out_var |};
					{| subj_type |} {| subj_varname |} = {| subj_exp |};
					for({| subj_type |}::iterator it={| subj_varname |}.begin(); it!={| subj_varname |}.end(); it++) {
						{| term_pat_context |}
						{| term_pat_var |} = *it;
						{| term_pat_post |}
						{| '\\n'.join(term_out_context) |}	
						{| comp_out_var |}.push_back( {| term_out_pat |} );
					}
				''')

			template_args = { 'subj_context_codes'  : subj_context_codes
                                        , 'subj_type'           : subj_type
                                        , 'subj_varname'        : subj_varname
                                        , 'subj_exp'            : subj_exp
                                        , 'term_pat_context'    : term_pat_context
                                        , 'term_pat_var'        : term_pat_var
                                        , 'term_pat_post'       : term_pat_post
                                        , 'guard_context_codes' : guard_context_codes
                                        , 'guard_cond_codes'    : guard_cond_codes
                                        , 'comp_out_type'       : comp_out_type
                                        , 'comp_out_var'        : comp_out_var
                                        , 'term_out_context'    : term_out_context
                                        , 'term_out_pat'        : term_out_var }

			context_codes = [ compile_template(tcomp_template, **template_args) ]

			term_codes = comp_out_var

		return context_codes,term_codes

class CPPTypeCoercion:

	def __init__(self):
		pass

	# Coercion from MSRE types to C++ types.
	# TODO: Currently works only for simple types.
	@visit.on('arg_type')
	def coerce_cpp_type_codes(self, arg_type):
		pass

	@visit.when(ast.TypeVar)
	def coerce_cpp_type_codes(self, arg_type):
		return "auto"

	@visit.when(ast.TypeCons)
	def coerce_cpp_type_codes(self, arg_type):
		const_name = arg_type.name
		if const_name == ast.LOC:
			return 'int'
		elif const_name == ast.INT:
			return 'int'
		elif const_name == ast.FLOAT:
			return 'float'
		elif const_name == ast.CHAR:
			return 'char'
		elif const_name == ast.STRING:
			return 'string'
		elif const_name == ast.BOOL:
			return 'bool'
		elif const_name == ast.DEST:
			return 'string'

	@visit.when(ast.TypeList)
	def coerce_cpp_type_codes(self, arg_type):
		cpp_type = self.coerce_cpp_type_codes( arg_type.type )
		return "list<%s> " % cpp_type

	@visit.when(ast.TypeMSet)
	def coerce_cpp_type_codes(self, arg_type):
		# print "Here! %s" % arg_type.type
		cpp_type = self.coerce_cpp_type_codes( arg_type.type )
		return "list<%s> " % cpp_type

	@visit.when(ast.TypeTuple)
	def coerce_cpp_type_codes(self, arg_type):
		cpp_types = map(lambda t: self.coerce_cpp_type_codes(t), arg_type.types) 
		return "tuple<%s> " % ','.join( cpp_types )

	# Coercion from MSRE type to required C++ pretty codes
	@visit.on( 'arg_type' )
	def coerce_cpp_pretty_codes(self, arg_type):
		pass

	@visit.when(ast.TypeCons)
	def coerce_cpp_pretty_codes(self, arg_type):
		const_name = arg_type.name
		if const_name in [ast.LOC,ast.INT,ast.FLOAT,ast.CHAR,ast.STRING,ast.BOOL,ast.DEST]:
			return "%s"
		else:
			# TODO: Support other pretty base types
			return "to_str(%s)"

	@visit.when(ast.TypeTuple)
	def coerce_cpp_pretty_codes(self, arg_type):
		return "to_str(%s)"
	
	@visit.when(ast.TypeList)
	def coerce_cpp_pretty_codes(self, arg_type):
		return "to_str(%s)"

	@visit.when(ast.TypeMSet)
	def coerce_cpp_pretty_codes(self, arg_type):
		return "to_str(%s)"

	# Coercion from MSRE type to required C++ markdown codes
	@visit.on( 'arg_type' )
	def coerce_cpp_markdown_codes(self, arg_type, alias_cont_name="aliases"):
		pass

	@visit.when(ast.TypeCons)
	def coerce_cpp_markdown_codes(self, arg_type, alias_cont_name="aliases"):
		const_name = arg_type.name
		if const_name in [ast.LOC]:
			return "print_markdown(" + alias_cont_name + ",%s)" 
		elif const_name in [ast.INT,ast.FLOAT,ast.CHAR,ast.STRING,ast.BOOL,ast.DEST]:
			return "%s"
		else:
			# TODO: Support other pretty base types
			return "to_str(%s)"

	@visit.when(ast.TypeTuple)
	def coerce_cpp_markdown_codes(self, arg_type, alias_cont_name="aliases"):
		return "to_str(%s)"
	
	@visit.when(ast.TypeList)
	def coerce_cpp_markdown_codes(self, arg_type, alias_cont_name="aliases"):
		return "to_str(%s)"

	@visit.when(ast.TypeMSet)
	def coerce_cpp_markdown_codes(self, arg_type, alias_cont_name="aliases"):
		return "to_str(%s)"

