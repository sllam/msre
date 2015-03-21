
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

from msrex.misc.aggregators import subseteq, diff, foldl

from msrex.frontend.transform.base_transformer import Transformer
from msrex.frontend.analyze.inspectors import Inspector

from msrex.frontend.analyze.checkers.neighbor_restrict_checker import retrieveFacts, retrieveAll

from msrex.misc.template import compile_template, template, compact

from msrex.frontend.analyze.smt_solver import tyDest

# This class executes a choreographic transformation of system-centric programs into
# node-centric ones.
class Choreographic(Transformer):

	def __init__(self, decs, source_text):
		self.initialize(decs)
		self.max_neighbor_restriction = -1
		self.source_text = source_text
		self.is_lhs = True
		self.sync_preds = []

	# Analyze the type of choreographic transformation needed for the program.
	# Returns True, iff choreographic transformation is required (exists at least one system-centric rule).
	def required(self):
		ensem_dec = self.inspect.filter_decs(self.decs, ensem=True)[0]
		return ensem_dec.requires_sync
		
	def transform(self):
		ensem_dec = self.inspect.filter_decs(self.decs, ensem=True)[0]
		execute_dec = self.inspect.filter_decs(self.decs, execute=True)[0]
		facts   = self.inspect.filter_decs(ensem_dec.decs, fact=True)

		monotone_facts = {}
		monotone_predlocks_codes = []
		for fact_dec in facts:
			# print "Here: %s %s" % (fact_dec.name,fact_dec.monotone)
			if not fact_dec.monotone:
				lock_name = "%sLock" % fact_dec.name
				monotone_facts[fact_dec.name] = { 'lock':ast.FactBase(lock_name, []) , 'dec':fact_dec }
				monotone_predlocks_code = "predicate %s :: fact." % lock_name
				monotone_predlocks_codes.append( monotone_predlocks_code )

		sync_pred_infos = []

		module_decs = self.inspect.filter_decs(ensem_dec.decs, extern=True)
		prog_mods_codes = map( lambda module_dec: self.generateModuleCode(module_dec), module_decs)

		pred_decs = self.inspect.filter_decs(ensem_dec.decs, fact=True)
		prog_preds_codes = map( lambda pred_dec: self.generatePredCode(pred_dec), pred_decs)

		export_decs = self.inspect.filter_decs(ensem_dec.decs, export=True)
		prog_exports_codes = map( lambda export_dec: self.generateExportCode(export_dec), export_decs)

		sync_template_args = { 'inTrans': ext('inTrans', '') }

		rule_decs = self.inspect.filter_decs(ensem_dec.decs, rule=True)
		prog_rules_codes = map( lambda rule_dec: self.generateRuleCode(rule_dec, self.required(), sync_pred_infos, monotone_facts, sync_template_args), rule_decs)
	
		sync_mods_codes, sync_preds_codes, sync_exports_codes = self.generateSyncPredCodes(sync_pred_infos, sync_template_args)

		role_decs = self.inspect.filter_decs(ensem_dec.decs, rolesig=True, roledef=True)
		role_codes = map(lambda r: self.generateRoleCode(r, monotone_facts), role_decs)

		node_centric_template = template('''
		ensem {| ensem_name |} {
			{| '\\n'.join( prog_mods_codes ) |}
			{| sync_mods_codes |}

			{| '\\n'.join( prog_preds_codes ) |}

			{| '\\n'.join( monotone_predlocks_codes ) |}

			{| sync_preds_codes |}

			{| '\\n'.join( role_codes ) |}

			{| '\\n'.join( prog_exports_codes ) |}
			{| '\\n'.join( sync_exports_codes ) |}

			{| '\\n\\n'.join( prog_rules_codes ) |}
		}

		execute {| ensem_name |} {
			{| '\\n'.join( prog_execute_codes ) |}
		}
		''')

		prog_execute_codes = self.generateExecuteCodes(execute_dec, monotone_facts)

		
		top_level_template_args = { 'ensem_name'       : ensem_dec.name
                                          , 'sync_mods_codes'  : sync_mods_codes
                                          , 'prog_mods_codes'  : prog_mods_codes
                                          , 'sync_preds_codes' : sync_preds_codes
                                          , 'monotone_predlocks_codes' : monotone_predlocks_codes
                                          , 'prog_preds_codes' : prog_preds_codes
                                          , 'role_codes' : role_codes
                                          , 'sync_exports_codes' : sync_exports_codes
                                          , 'prog_exports_codes' : prog_exports_codes
                                          , 'prog_rules_codes'   : prog_rules_codes
                                          , 'prog_execute_codes' : prog_execute_codes }

		self.node_centric_prog_codes = compile_template(node_centric_template, **top_level_template_args)

	def getGeneratedCodes(self):
		return self.node_centric_prog_codes

	def generateModuleCode(self, module_dec):
		return self.source_text[module_dec.lex_start:module_dec.lex_end]

	def generatePredCode(self, pred_dec):
		return self.source_text[pred_dec.lex_start:pred_dec.lex_end]

	def generateExportCode(self, export_dec):
		return self.source_text[export_dec.lex_start:export_dec.lex_end]

	@visit.on( 'role_dec' )
	def generateRoleCode(self, role_dec, monotone_facts):
		pass

	@visit.when( ast.RoleSigDec )
	def generateRoleCode(self, role_dec, monotone_facts):
		role_sig_codes = "role %s :: %s." % (role_dec.name, self.generateType( role_dec.type ) )
		return role_sig_codes

	@visit.when( ast.RoleDefDec )
	def generateRoleCode(self, role_dec, monotone_facts):
		if len(monotone_facts.keys()) > 0:
			mono_init_code = ", %s" % (','.join(map(lambda m: self.generateFact( ast.FactLoc(role_dec.loc, m['lock']) ),monotone_facts.values())))
		else:
			mono_init_code = ""
		role_def_codes = "role [%s]%s = %s%s" % (self.generateTerm(role_dec.loc), self.generateFact(role_dec.fact)
                                                        ,self.generateFact(role_dec.facts), mono_init_code)
		if len(role_dec.where) > 0:
			role_def_codes += " where %s." % (','.join(map(lambda w: self.generateAssignDec(w),role_dec.where)))
		else:
			role_def_codes += "."
		return role_def_codes

	def generateExecuteCodes(self, execute_dec, monotone_facts):
		return foldl( map(lambda d: self.generateExecuteCode(d, monotone_facts), execute_dec.decs), [] )

	@visit.on( 'exec_dec' )
	def generateExecuteCode(self, exec_dec, monotone_facts):
		pass

	@visit.when( ast.ExistDec )
	def generateExecuteCode(self, exec_dec, monotone_facts):
		exist_codes = "exists %s." % (','.join(map(lambda v: self.generateTerm(v),exec_dec.exist_vars)))
		'''
		mono_init_codes = []
		if len(monotone_facts.keys()) > 0:
			for exist_var in exec_dec.exist_vars:
				mono_init_code = "%s." % (','.join(map(lambda m: self.generateFact( ast.FactLoc(exist_var, m['lock']) ),monotone_facts.values())))
				mono_init_codes.append( mono_init_code )
		'''
		return [exist_codes] # + mono_init_codes

	@visit.when( ast.InitDec )
	def generateExecuteCode(self, init_dec, monotone_facts):
		init_codes = "init %s as %s." % (','.join(map(lambda l: self.generateTerm(l), init_dec.locs)),self.generateFact(init_dec.fact))
		return [init_codes]

	@visit.when( ast.LocFactDec )
	def generateExecuteCode(self, exec_dec, monotone_facts):
		return ["%s." % (','.join(map(lambda f: self.generateFact(f), exec_dec.loc_facts)))]

	@visit.when( ast.AssignDec )
	def generateExecuteCode(self, exec_dec, monotone_facts):
		return [self.generateAssignDec(exec_dec)]

	def generateRuleCode(self, rule_dec, sync_used, sync_pred_infos, monotone_facts, sync_template_args):
		# Program does not use sync, hence just return the original source rule
		if not rule_dec.requires_sync and not rule_dec.is_system_centric:
			return self.source_text[rule_dec.lex_start:rule_dec.lex_end]

		# This rule uses sync, hence decompose into node centric obligation matching.
		elif not rule_dec.requires_sync and rule_dec.is_system_centric:
			return self.generateNodeCentricSyncCompilationRuleCode( rule_dec, sync_pred_infos, monotone_facts, sync_template_args )

		else: # rule_dec.requires_sync and rule_dec.is_system_centric:
			# TODO: Implement
			return self.generateNodeCentricSyncCompilationRuleCode( rule_dec, sync_pred_infos, monotone_facts, sync_template_args )

	def generateNodeCentricSyncCompilationRuleCode( self, rule_dec, sync_pred_infos, monotone_facts, sync_template_args ):
		nbr_spec = rule_dec.nbr_options[0]
		primary_loc   = nbr_spec['primary_loc']
		primary_obligation   = nbr_spec['primary_obligation'] 
		primary_guards       = nbr_spec['primary_guards']
		other_obligations    = nbr_spec['other_obligations']
		other_guards         = nbr_spec['other_guards']
		primary_has_triggers = nbr_spec['primary_has_trigger']

		# Compute lock acquisition
		lock_pred_acq = {}
		lock_pred_acq[primary_loc] = self.generateLockFacts(retrieveAll(primary_obligation), monotone_facts, primary_loc)
		for other_loc in other_obligations:
			lock_pred_acq[other_loc] = self.generateLockFacts(retrieveAll(other_obligations[other_loc]), monotone_facts, other_loc)

		rule_name = rule_dec.name
		exist_var = ast.TermVar("T__")
		exist_var.type = ast.TypeCons("dest")
		exist_var.smt_type = tyDest
		sync_pred_info = self.generateSyncPreds(rule_name, exist_var, primary_loc, primary_obligation, other_obligations)

		sync_pred_infos.append( sync_pred_info )

		nc_comp_template = template('''
		rule {|rule_name|}Test :: -{ [{|p_loc|}]{|in_trans|}(_) }, {|all_pri_facts|} \ 1
				{|p_grds|} --o exists {|exist_var|}. [{|p_loc|}]{|in_trans|}({|exist_var|}), {|probe_facts|}.

		{| '\\n\\n'.join( probe_rule_codes ) |}
		rule {|rule_name|}Engage :: [{|p_loc|}]{|in_trans|}({|exist_var|}) \ {|ready_facts|} --o {|init_fact|}.

		rule {|rule_name|}Init :: {| p_prop_facts |}{|init_fact|}{| p_lk_facts |}{| p_simp_facts |}
				{|p_grds|} --o {|p_lhs_fact|}, {| req_facts |}.

		{| '\\n\\n'.join( req_succ_rule_codes ) |}
		rule {|rule_name|}Commit :: [{|p_loc|}]{|in_trans|}({|exist_var|}), {|all_lhs_facts|}
				--o {|rule_body|}
				    {|where_clauses|}

		{| '\\n\\n'.join( req_fail_rule_codes ) |}
		rule {|rule_name|}Abort{|p_loc|} :: {| p_abort_fact |} \ [{|p_loc|}]{|in_trans|}({|exist_var|}), {|p_lhs_fact|}
				--o {|p_lksimp_facts|}.

		{| '\\n\\n'.join( abort_rule_codes ) |}
		''')

		probe_facts = ', '.join( map(lambda (loc,info): self.generateSyncPredFact(loc, info['name'], info['args']), sync_pred_info['probe'].items()) )

		probe_rule_codes = []
		for other_loc in other_obligations:
			probe_rule_template = template('''
			rule {|rule_name|}Probe{|o_loc|} :: { [{|o_loc|}]{|in_trans|}(P__)|P__->Ps__ }, {|all_o_facts|} 
					\ {|probe_fact|} | {|o_grds|}strongest({|exist_var|},Ps__) --o {|ready_fact|}.
			''')
			probe_info = sync_pred_info['probe'][other_loc]
			ready_info = sync_pred_info['ready'][other_loc]
			probe_rule_args = { 'rule_name'  : rule_name
                                          , 'o_loc'      : other_loc
                                          , 'in_trans'   : sync_template_args['inTrans']
                                          , 'all_o_facts': self.generateFact( retrieveAll(other_obligations[other_loc]) )
                                          , 'o_grds' : "%s," % self.generateTerm( other_guards[other_loc] ) if len(other_guards[other_loc]) > 0 else ""
                                          , 'probe_fact' : self.generateSyncPredFact(other_loc, probe_info['name'], probe_info['args'])
                                          , 'exist_var'  : self.generateTerm(exist_var)
                                          , 'ready_fact' : self.generateSyncPredFact(primary_loc, ready_info['name'], ready_info['args']) }
                     
			probe_rule_codes.append( compile_template(probe_rule_template, **probe_rule_args) )

		req_succ_rule_codes = []
		for other_loc in other_obligations:
			req_succ_rule_template = template('''
			rule {|rule_name|}Req{|o_loc|}Succ :: {| o_prop_facts |}{| o_req_fact |}{| o_lk_facts |}{| o_simp_facts |}
					{|o_grds|} --o {|o_lhs_fact|}.
			''')
			req_info = sync_pred_info['req'][other_loc]
			if len(lock_pred_acq[other_loc].values()) > 0:
				o_lock_facts = ", %s" % self.generateFact( lock_pred_acq[other_loc].values() )
			else:
				o_lock_facts = ""			
			o_prop_fact_info = retrieveFacts(other_obligations[other_loc], props=True, triggers=True, facts=True)
			o_simp_fact_info = retrieveFacts(other_obligations[other_loc], simps=True, triggers=True, facts=True)
			if len(o_prop_fact_info) > 0:
				o_prop_facts = "%s \\" % self.generateFact( o_prop_fact_info )
			else:
				o_prop_facts = ""
			if len(o_simp_fact_info) > 0:
				o_simp_facts = ", %s" % self.generateFact( o_simp_fact_info )
			else:
				o_simp_facts = ""
			o_lhs_info = sync_pred_info['lhs'][other_loc]
			req_succ_rule_args = { 'rule_name'  : rule_name
                                             , 'o_loc'      : other_loc
                                             , 'o_req_fact' : self.generateSyncPredFact(other_loc, req_info['name'], req_info['args'])
                                             , 'o_lk_facts' : o_lock_facts
                                             , 'o_prop_facts' : o_prop_facts
                                             , 'o_simp_facts' : o_simp_facts
                                             , 'o_grds' : "%s," % self.generateTerm( other_guards[other_loc] ) if len(other_guards[other_loc]) > 0 else ""
                                             , 'o_lhs_fact' : self.generateSyncPredFact(primary_loc, o_lhs_info['name'], o_lhs_info['args']) }
			req_succ_rule_codes.append( compile_template(req_succ_rule_template, **req_succ_rule_args) )

		ready_facts = ', '.join( map(lambda (loc,info): self.generateSyncPredFact(primary_loc, info['name'], info['args']), sync_pred_info['ready'].items()) )

		if len(lock_pred_acq[primary_loc].values()) > 0:
			p_lock_facts = ", %s" % self.generateFact( lock_pred_acq[primary_loc].values() )
		else:
			p_lock_facts = ""

		p_prop_fact_info = retrieveFacts(primary_obligation, props=True, triggers=True, facts=True)
		p_simp_fact_info = retrieveFacts(primary_obligation, simps=True, triggers=True, facts=True)
		if len(p_prop_fact_info) > 0:
			p_prop_facts = "%s \\" % self.generateFact( p_prop_fact_info )
		else:
			p_prop_facts = ""
		if len(p_simp_fact_info) > 0:
			p_simp_facts = ", %s" % self.generateFact( p_simp_fact_info )
		else:
			p_simp_facts = ""

		req_facts = ', '.join( map(lambda (loc,info): self.generateSyncPredFact(loc, info['name'], info['args']), sync_pred_info['req'].items()) )

		all_lhs_facts  = [self.generateSyncPredFact(primary_loc, sync_pred_info['primary_lhs']['name'], sync_pred_info['primary_lhs']['args'])]
		all_lhs_facts += map(lambda info: self.generateSyncPredFact(primary_loc, info['name'], info['args']), sync_pred_info['lhs'].values())

		all_lk_facts = []
		for loc_lks in lock_pred_acq.values():
			all_lk_facts += loc_lks.values()
		
		rule_body = self.generateFact( rule_dec.rhs + all_lk_facts )

		if len( rule_dec.where ) > 0:
			where_clauses = "where %s." % (", ".join( map(lambda w: self.generateAssignDec(w), rule_dec.where) ))
		else:
			where_clauses = ""
			rule_body += "."

		req_fail_rule_codes = []
		for other_loc in other_obligations:
			req_fail_rule_template = template('''
			rule {|rule_name|}Req{|o_loc|}Fail :: {|req_fact|} --o {|abort_fact|}.
			''')
			req_info = sync_pred_info['req'][other_loc]
			req_fail_rule_args = { 'rule_name'  : rule_name
                                             , 'o_loc'      : other_loc
			                     , 'req_fact'   : self.generateSyncPredFact(other_loc, req_info['name'], req_info['args'])
                                             , 'abort_fact' : self.generateSyncPredFact(primary_loc, sync_pred_info['abort']['name'], sync_pred_info['abort']['args']) }
			req_fail_rule_codes.append( compile_template(req_fail_rule_template, **req_fail_rule_args) )

		p_simp_lk_facts = self.generateFact( lock_pred_acq[primary_loc].values() + p_simp_fact_info, rhs=True )
		if len(p_simp_lk_facts) == 0:
			p_simp_lk_facts = "1"

		abort_rule_codes = []
		for other_loc in other_obligations:
			abort_rule_template = template('''
			rule {|rule_name|}Abort{|o_loc|} :: {| o_abort_fact |} \ {| o_lhs_fact |}
					--o {| o_lksimp_facts |}.
			''')
			lhs_info = sync_pred_info['lhs'][other_loc]
			o_simp_fact_info = retrieveFacts(other_obligations[other_loc], simps=True, triggers=True, facts=True)
			o_lk_fact_info   = lock_pred_acq[other_loc].values()
			if len(o_simp_fact_info + o_lk_fact_info) > 0:
				o_lksimp_facts = self.generateFact( o_lk_fact_info + o_simp_fact_info, rhs=True )
			else:
				o_lksimp_facts = "1"
			abort_rule_args = { 'rule_name'      : rule_name
                                          , 'o_loc'          : other_loc
                                          , 'o_abort_fact'   : self.generateSyncPredFact(primary_loc, sync_pred_info['abort']['name'], sync_pred_info['abort']['args'])
                                          , 'o_lhs_fact'     : self.generateSyncPredFact(primary_loc, lhs_info['name'], lhs_info['args'])
                                          , 'o_lksimp_facts' : o_lksimp_facts }
			abort_rule_codes.append( compile_template( abort_rule_template, **abort_rule_args) )

		nc_comp_args = { 'rule_name' : rule_name
                               , 'p_loc'     : primary_loc
                               , 'in_trans'  : sync_template_args['inTrans']
                               , 'all_pri_facts' : self.generateFact( retrieveAll(primary_obligation) )
                               , 'p_grds' :  "| %s" % (','.join(map(lambda g: self.generateTerm(g),primary_guards))) if len(primary_guards) > 0 else ""
                               , 'exist_var' : self.generateTerm(exist_var)
                               , 'probe_facts' : probe_facts
                               , 'probe_rule_codes' : probe_rule_codes
                               , 'ready_facts' : ready_facts
                               , 'init_fact' : self.generateSyncPredFact(primary_loc, sync_pred_info['init']['name'], sync_pred_info['init']['args'])
                               , 'p_lk_facts': p_lock_facts
                               , 'p_prop_facts': p_prop_facts
                               , 'p_simp_facts': p_simp_facts
                               , 'p_lhs_fact' : self.generateSyncPredFact(primary_loc, sync_pred_info['primary_lhs']['name'], sync_pred_info['primary_lhs']['args']) 
                               , 'req_facts'  : req_facts
                               , 'req_succ_rule_codes' : req_succ_rule_codes
                               , 'all_lhs_facts' : ', '.join( all_lhs_facts )
                               , 'all_lk_facts'  : all_lk_facts
                               , 'rule_body' : rule_body
                               , 'where_clauses' : where_clauses
                               , 'req_fail_rule_codes' : req_fail_rule_codes
                               , 'p_lksimp_facts' : p_simp_lk_facts
                               , 'p_abort_fact' : self.generateSyncPredFact(primary_loc, sync_pred_info['abort']['name'], sync_pred_info['abort']['args'])
                               , 'abort_rule_codes' : abort_rule_codes }

		return compile_template(nc_comp_template, **nc_comp_args)
		

	def generateSyncPreds(self, rule_name, exist_var, primary_loc, primary_obligation, other_obligations):
		sync_pred_info = {}		

		other_locs     = other_obligations.keys()
		other_loc_vars = map( lambda o: o['term'], other_obligations.values() )

		primary_vars = diff(self.retrieveFreeVars(retrieveAll(primary_obligation)), [primary_loc], fx=lambda x: x.name)
		other_vars = {}
		for loc in other_locs:
			other_vars[loc] = diff(self.retrieveFreeVars(retrieveAll(other_obligations[loc])), map(lambda v: v.name,primary_vars)+[primary_loc,loc], fx=lambda x: x.name)

		sync_pred_info = { 'init'        : { 'name':'%sInit' % rule_name, 'args':[exist_var]+other_loc_vars }
                                 , 'abort'       : { 'name':'%sAbort' % rule_name, 'args':[exist_var] }
                                 , 'primary_lhs' : { 'name':'%sLHS%s' % (rule_name,primary_loc), 'args':[exist_var]+primary_vars }
                                 }

		probe_info = {}
		ready_info = {}
		req_info   = {}
		lhs_info   = {}
		for loc in other_locs:
			primary_vars_mloc = diff(primary_vars, loc, fx=lambda x: x.name)
			probe_info[loc] = { 'name':'%sProbe%s' % (rule_name,loc), 'args':[exist_var,primary_obligation['term']]+primary_vars_mloc }
			ready_info[loc] = { 'name':'%sReady%s' % (rule_name,loc), 'args':[exist_var,other_obligations[loc]['term']] }
			req_info[loc]   = { 'name':'%sReq%s' % (rule_name,loc), 'args':[exist_var,primary_obligation['term']]+diff(primary_vars, [loc], fx=lambda x:x.name) }
			lhs_info[loc]   = { 'name':'%sLHS%s' % (rule_name,loc), 'args':[exist_var,other_obligations[loc]['term']]+other_vars[loc] }

		sync_pred_info['probe'] = probe_info
		sync_pred_info['ready'] = ready_info
		sync_pred_info['req']   = req_info
		sync_pred_info['lhs']   = lhs_info

		return sync_pred_info

	def generateSyncPredDec(self, sync_pred_name, sync_pred_args):
		if len(sync_pred_args) == 0:
			return "predicate %s :: fact." % sync_pred_name
		elif len(sync_pred_args) == 1:
			return "predicate %s :: %s -> fact." % (sync_pred_name,self.generateType(sync_pred_args[0].type))
		else: # len(sync_pred_args) > 1:
			return "predicate %s :: (%s) -> fact." % (sync_pred_name,','.join(map(lambda a: self.generateType(a.type),sync_pred_args)))

	def generateSyncExportDec(self, sync_pred_name, sync_pred_args):
		return "export query %s(%s)." % (sync_pred_name,','.join(map(lambda _:"_",sync_pred_args)))

	def generateLockFacts(self, fact_list, monotone_facts, loc):
		lock_preds = {}
		for locfact in fact_list:
			if locfact.fact_type == ast.FACT_LOC:
				name = locfact.fact.name
			else:
				name = locfact.facts[0].fact.name
			if name in monotone_facts:
				lock_preds[name] = ast.FactLoc( ast.TermVar(loc), monotone_facts[name]['lock'] )
		return lock_preds

	def generateSyncPredFact(self, sync_pred_loc, sync_pred_name, sync_pred_args):
		return "[%s]%s(%s)" % (sync_pred_loc, sync_pred_name, ','.join(map(lambda a: self.generateTerm(a),sync_pred_args))) 

	def generateSyncPredCodes(self, sync_pred_infos, sync_template_args):
		sync_pred_template = template('''
			predicate {|inTrans|} :: dest -> fact.
			{| '\\n'.join( sync_pred_codes ) |}
		''')
		sync_pred_codes = []
		for sync_pred_info in sync_pred_infos:
			init_pred_dec   = self.generateSyncPredDec(sync_pred_info['init']['name'], sync_pred_info['init']['args'])
			abort_pred_dec  = self.generateSyncPredDec(sync_pred_info['abort']['name'], sync_pred_info['abort']['args'])
			prilhs_pred_dec = self.generateSyncPredDec(sync_pred_info['primary_lhs']['name'], sync_pred_info['primary_lhs']['args'])
			probe_pred_decs = map(lambda p: self.generateSyncPredDec(p['name'], p['args']), sync_pred_info['probe'].values())
			ready_pred_decs = map(lambda p: self.generateSyncPredDec(p['name'], p['args']), sync_pred_info['ready'].values())
			req_pred_decs   = map(lambda p: self.generateSyncPredDec(p['name'], p['args']), sync_pred_info['req'].values())
			lhs_pred_decs   = map(lambda p: self.generateSyncPredDec(p['name'], p['args']), sync_pred_info['lhs'].values())
			sync_pred_code  = compile_template(template('''
				{| '\\n'.join( probe_pred_decs ) |}
				{| '\\n'.join( ready_pred_decs ) |}
				{| init_pred_dec |}
				{| '\\n'.join( req_pred_decs ) |}
				{| prilhs_pred_dec |}
				{| '\\n'.join( lhs_pred_decs ) |}
				{| abort_pred_dec |}
			'''), probe_pred_decs=probe_pred_decs, ready_pred_decs=ready_pred_decs, init_pred_dec=init_pred_dec,
                              req_pred_decs=req_pred_decs, prilhs_pred_dec=prilhs_pred_dec, lhs_pred_decs=lhs_pred_decs, abort_pred_dec=abort_pred_dec)
			sync_pred_codes.append( sync_pred_code )		

		sync_export_codes = []
		for sync_pred_info in sync_pred_infos:
			init_export_dec   = self.generateSyncExportDec(sync_pred_info['init']['name'], sync_pred_info['init']['args'])
			abort_export_dec  = self.generateSyncExportDec(sync_pred_info['abort']['name'], sync_pred_info['abort']['args'])
			prilhs_export_dec = self.generateSyncExportDec(sync_pred_info['primary_lhs']['name'], sync_pred_info['primary_lhs']['args'])
			probe_export_decs = map(lambda p: self.generateSyncExportDec(p['name'], p['args']), sync_pred_info['probe'].values())
			ready_export_decs = map(lambda p: self.generateSyncExportDec(p['name'], p['args']), sync_pred_info['ready'].values())
			req_export_decs   = map(lambda p: self.generateSyncExportDec(p['name'], p['args']), sync_pred_info['req'].values())
			lhs_export_decs   = map(lambda p: self.generateSyncExportDec(p['name'], p['args']), sync_pred_info['lhs'].values())
			sync_export_code  = compile_template(template('''
				export query {|in_trans|}(_).
				{| '\\n'.join( probe_export_decs ) |}
				{| '\\n'.join( ready_export_decs ) |}
				{| init_export_dec |}
				{| '\\n'.join( req_export_decs ) |}
				{| prilhs_export_dec |}
				{| '\\n'.join( lhs_export_decs ) |}
				{| abort_export_dec |}
			'''), probe_export_decs=probe_export_decs, ready_export_decs=ready_export_decs, init_export_dec=init_export_dec,
                              req_export_decs=req_export_decs, prilhs_export_dec=prilhs_export_dec, lhs_export_decs=lhs_export_decs, 
                              abort_export_dec=abort_export_dec, in_trans=sync_template_args['inTrans'])
			sync_export_codes.append( sync_export_code )

		if len(sync_pred_infos) > 0:
			sync_mod_codes = template('''
			module comingle.lib.ExtLib import {
				strongest :: (dest,{dest}) -> bool.
			}
			''')
		else:
			sync_mod_codes = ""
			
		sync_pred_codes = compile_template(sync_pred_template, inTrans=sync_template_args['inTrans'], sync_pred_codes=sync_pred_codes)

		return sync_mod_codes, sync_pred_codes, sync_export_codes

	def retrieveFreeVars(self, fact_list):
		return self.inspect.set_vars( self.inspect.free_vars(fact_list, loc=True, args=True, compre_binders=False) 
                                            , comp=lambda v: v.name )

	
	@visit.on( 'term' )
	def generateTerm(self, term):
		pass

	@visit.when( list )
	def generateTerm(self, term):
		return ','.join(map(lambda t: self.generateTerm(t),term))

	@visit.when( ast.TermCons )
	def generateTerm(self, term):
		return "%s" % term.name

	@visit.when( ast.TermVar )
	def generateTerm(self, term):
		return term.name

	@visit.when( ast.TermApp )
	def generateTerm(self, term):
		return "(%s(%s))" % (self.generateTerm(term.term1),self.generateTerm(term.term2))

	@visit.when( ast.TermTuple )
	def generateTerm(self, term):
		return "(%s)" % (','.join(map(lambda t: self.generateTerm(t),term.terms)))

	@visit.when( ast.TermList )
	def generateTerm(self, term):
		return "[%s]" % (','.join(map(lambda t: self.generateTerm(t),term.terms)))

	@visit.when( ast.TermMSet )
	def generateTerm(self, term):
		return "{%s}" % (','.join(map(lambda t: self.generateTerm(t),term.terms)))

	@visit.when( ast.TermListCons )
	def generateTerm(self, term):
		return "[%s|%s]"  % (self.generateTerm(term.term1),self.generateTerm(term.term2))

	@visit.when( ast.TermEnumMSet )
	def generateTerm(self, term):
		return "{%s..%s}"  % (self.generateTerm(term.texp1),self.generateTerm(term.texp2))

	@visit.when( ast.TermBinOp )
	def generateTerm(self, term):
		return "%s %s %s" % (self.generateTerm(term.term1),term.op,self.generateTerm(term.term2))

	@visit.when( ast.TermUnaryOp )
	def generateTerm(self, term):
		return "%s %s" % (term.op,self.generateTerm(term.term))

	@visit.when( ast.TermLit )
	def generateTerm(self, term):
		return "%s" % term.literal

	@visit.when( ast.TermUnderscore )
	def generateTerm(self, term):
		return "_"

	@visit.when( ast.TermCompre )
	def generateTerm(self, term):
		term_code = self.generateTerm(term.term)

		comp_code = ','.join( map(lambda cr: self.generateCompRange(cr), term.comp_ranges) )
		grd_code  = ','.join( map(lambda g: self.generateTerm(g), term.guards) )

		if len(term.comp_ranges) > 0 and len(term.guards) > 0:
			quan_code = "|%s.%s" % (comp_code,gr_code)
		elif len(term.comp_ranges) > 0 and len(term.guards) == 0:
			quan_code = "|%s" % comp_code
		elif len(term.comp_ranges) == 0 and len(term.guards) > 0:
			quan_code = "|%s" % grd_code
		else:
			quan_code = ""

		return "{%s%s}" % (term_code,quan_code)

	@visit.on( 'typ' )
	def generateType(self, typ):
		pass

	@visit.when( ast.TypeVar )
	def generateType(self, typ):
		return typ.name

	@visit.when( ast.TypeCons )
	def generateType(self, typ):
		return typ.name

	@visit.when( ast.TypeApp )
	def generateType(self, typ):
		return "%s %s" % (self.generateType(typ.type1),self.generateType(typ.type2))

	@visit.when( ast.TypeArrow )
	def generateType(self, typ):
		return "%s -> %s" % (self.generateType(typ.type1),self.generateType(typ.type2))

	@visit.when( ast.TypeTuple )
	def generateType(self, typ):
		return "(%s)" % (','.join( map(lambda t: self.generateType(t), typ.types) ))

	@visit.when( ast.TypeMSet )
	def generateType(self, typ):
		return "{%s}" % self.generateType(typ.type)

	@visit.when( ast.TypeList )
	def generateType(self, typ):
		return "[%s]" % self.generateType(typ.type)

	def generateCompRange(self, comp_range, rhs=False):
		var_code = self.generateTerm( comp_range.term_vars )
		dom_code = self.generateTerm( comp_range.term_range )
		if not rhs:
			return "%s -> %s" % (var_code,dom_code)
		else:
			return "%s <- %s" % (var_code,dom_code)

	@visit.on( 'fact' )
	def generateFact(self, fact, rhs=False):
		pass

	@visit.when( list )
	def generateFact(self, fact, rhs=False):
		return ', '.join(map(lambda f: self.generateFact(f, rhs=rhs),fact))

	@visit.when( ast.FactBase )
	def generateFact(self, fact, rhs=False):
		term_code = ','.join( map(lambda t: self.generateTerm(t), fact.terms) )
		return "%s(%s)" % (fact.name,term_code)

	@visit.when( ast.FactLoc )
	def generateFact(self, fact, rhs=False):
		return "[%s]%s" % (self.generateTerm(fact.loc),self.generateFact(fact.fact))

	@visit.when( ast.FactCompre )
	def generateFact(self, fact, rhs=False):
		fact_code = ','.join( map(lambda f: self.generateFact(f),fact.facts) )
		
		comp_code = ','.join( map(lambda cr: self.generateCompRange(cr, rhs=rhs), fact.comp_ranges) )
		grd_code  = ','.join( map(lambda g: self.generateTerm(g), fact.guards) )

		if not rhs:
			if len(fact.comp_ranges) > 0 and len(fact.guards) > 0:
				quan_code = "|%s.%s" % (comp_code,grd_code)
			elif len(fact.comp_ranges) > 0 and len(fact.guards) == 0:
				quan_code = "|%s" % comp_code
			elif len(fact.comp_ranges) == 0 and len(fact.guards) > 0:
				quan_code = "|%s" % grd_code
			else:
				quan_code = ""
		else:
			if len(fact.comp_ranges) > 0:
				quan_code = "|%s" % comp_code
			else:
				quan_code = ""

		fact_comp_str = "{%s%s}" % (fact_code,quan_code)

		if not rhs:
			if fact.compre_mod == ast.COMP_NONE_EXISTS:
				fact_comp_str = "!%s" % fact_comp_str			
			if fact.compre_mod == ast.COMP_ONE_OR_MORE:
				fact_comp_str = "%s+" % fact_comp_str

		return fact_comp_str

	def generateAssignDec(self, assign):
		pat_code = self.generateTerm(assign.term_pat)
		exp_code = self.generateTerm(assign.builtin_exp)
		return "%s = %s" % (pat_code,exp_code)

def ext(name, post=""):
	return "%s__%s" % (name,post)

def mkLocFact(loc, pred_name, term_args):
	loc_var = ast.TermVar( loc )
	fact = ast.FactBase( pred_name, term_args )
	return ast.FactLoc( loc_var, fact )


