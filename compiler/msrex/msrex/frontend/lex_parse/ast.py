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

LOC = "loc"
INT = "int"
FLOAT  = "float"
CHAR   = "char"
STRING = "string"
DEST   = "dest"
BOOL   = "bool"

EQ  = "=="
NEQ = "!="
GT  = ">"
LT  = "<"
GEQ = ">="
LEQ = "<="

IN  = "in"
NOT = "not"

PLUS  = "+"
MINUS = "-"
TIMES = "*"
DIV   = "/"

BASE_TYPES = [LOC,INT,FLOAT,CHAR,STRING,DEST,BOOL]
BOOL_OPS_1 = [EQ,NEQ,GT,LT,GEQ,LEQ]
BOOL_OPS_2 = [IN]
BOOL_OPS_3 = [NOT]
NUM_OPS  = [PLUS,MINUS,TIMES,DIV]






TYPE_CONS = 'ty_cons'
TYPE_VAR  = 'ty_var'
TYPE_APP  = 'ty_app'
TYPE_TUP  = 'ty_tup'
TYPE_LIST = 'ty_list'
TYPE_ARR  = 'ty_arr'
TYPE_MSET = 'ty_mset'

# Base ASTNode class

class ASTNode:
	
	def reg_source_info(self, parse_frag, highlight_idx=0):
		if parse_frag != None:
			(line_start,line_end) = parse_frag.linespan(0)
			(lex_start,lex_end)   = parse_frag.lexspan(0)
			(highlight_start,highlight_end) = parse_frag.lexspan(highlight_idx)
			self.lex_start = lex_start
			self.lex_end   = lex_end + 1
			self.hl_start  = highlight_start
			self.hl_end    = highlight_end + 1
			self.has_source_info = True
			self.error_idxs = []
			self.adjust_lex()
		else:
			self.has_source_info = False
			self.error_idxs = []
		self.has_trans = False
		self.supp_src = []
		self.inferred_type = None

	def is_from_source(self):
		return self.has_source_info

	def extend_error(self, error_idx):
		self.error_idxs.append(error_idx)

	def has_errors(self):
		return len(self.error_idxs) > 0

	def adjust_lex(self):
		pass

	def get_node_type(self):
		return self.__class__.__name__

	def get_node_args(self):
		return ()

	def compare_value(self):
		return (self.get_node_type(), self.get_node_args())

	def add_trans_snippet(self, trans_text):
		self.trans_text = trans_text
		self.has_trans  = True

	def gen_snippet(self, source_text):
		if not self.has_source_info:
			return ""
		if not self.has_trans:
			return source_text[self.lex_start:self.lex_end]
		else:
			return self.trans_text

# Types

class TypeVar(ASTNode):
	def __init__(self, name, parse_frag=None):
		self.name = name
		self.type_kind = TYPE_VAR 
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (TYPE_VAR,self.name)
	def adjust_lex(self):
		self.lex_end = self.lex_start + len(self.name)
		self.hl_end = self.hl_start + len(self.name)
	def get_node_args(self):
		return [self.name]

class TypeCons(ASTNode):
	def __init__(self, name, parse_frag=None):
		self.name = name
		self.type_kind = TYPE_CONS
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (TYPE_CONS,self.name)
	def adjust_lex(self):
		self.lex_end = self.lex_start + len(self.name)
		self.hl_end = self.hl_start + len(self.name)
	def get_node_args(self):
		return [self.name]

class TypeApp(ASTNode):
	def __init__(self, type1, type2, parse_frag=None):
		self.type1 = type1
		self.type2 = type2
		self.type_kind = TYPE_APP
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s %s)" % (TYPE_APP,str(self.type1),str(self.type2))

class TypeArrow(ASTNode):
	def __init__(self, type1, type2, parse_frag=None):
		self.type1 = type1
		self.type2 = type2
		self.type_kind = TYPE_ARR
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s,%s)" % (TYPE_ARR,str(self.type1),str(self.type2))

class TypeTuple(ASTNode):
	def __init__(self, types, parse_frag=None):
		self.types = types
		self.type_kind = TYPE_TUP
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (TYPE_TUP,','.join(map(str,self.types)))

class TypeMSet(ASTNode):
	def __init__(self, type, parse_frag=None):
		self.type = type
		self.type_kind = TYPE_MSET
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (TYPE_MSET,str(self.type))

class TypeList(ASTNode):
	def __init__(self, type, parse_frag=None):
		self.type = type
		self.type_kind = TYPE_LIST
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (TYPE_LIST,str(self.type))

class FactType(ASTNode):	
	def __init__(self, name, types, parse_frag=None):
		self.name = name
		self.types = types
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (self.name,','.join(map(str,self.types)))

class ExternType(ASTNode):
	def __init__(self, name, types, parse_frag=None):
		self.name = name
		self.types = types
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (self.name,','.join(map(str,self.types)))

# Declarations

DEC_PRAGMA  = 'dec_pragma'
DEC_ENSEM   = 'dec_ensem'
DEC_EXTERN  = 'dec_extern'
DEC_EXEC    = 'dec_exec'
DEC_EXIST   = 'dec_exist'
DEC_LOCFACT = 'dec_locfact'
DEC_FACT    = 'dec_fact'
DEC_RULE    = 'dec_rule'
DEC_ASSIGN  = 'dec_assign'


class PragmaDec(ASTNode):
	def __init__(self, pragma_text, pragma_args=[], parse_frag=None):
		self.pragma_text = pragma_text
		self.pragma_args = pragma_args
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "pragma_dec(%s,%s)" % (self.pragma_text,self.pragma_args)

class EnsemDec(ASTNode):
	def __init__(self, name, decs, parse_frag=None):
		self.dec_type = DEC_ENSEM
		self.name = name
		self.decs = decs
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "ensem_dec(%s,[%s])" % (self.name, ','.join(map(str,self.decs)) )

class ExternDec(ASTNode):
	def __init__(self, name, type_sigs, parse_frag=None):
		self.dec_type = DEC_EXTERN
		self.name = name
		self.type_sigs = type_sigs
		self.reg_source_info(parse_frag)
	def __str__(self):
		strs = []
		for type_sig in self.type_sigs:
			strs.append( str(type_sig) )
		return "extern_dec(%s,[%s])" % (self.name,','.join(strs))

class ExternTypeSig(ASTNode):
	def __init__(self, name, type_sig, parse_frag=None):
		self.name = name
		self.type_sig = type_sig
		self.reg_source_info(parse_frag)
	def adjust_lex(self):
		self.lex_end += len(self.name)
		self.hl_end = self.hl_start + len(self.name)
	def __str__(self):
		return "%s :: %s" % (self.name,self.type_sig)

class ExecDec(ASTNode):
	def __init__(self, name, decs, parse_frag=None):
		self.dec_type = DEC_EXEC
		self.name = name
		self.decs = decs
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "exec_dec(%s,[%s],[%s])" % ( self.name, ','.join(self.locs), ','.join(map(str,self.decs)) )

class ExistDec(ASTNode):
	def __init__(self, exist_vars, parse_frag=None):
		self.dec_type = DEC_EXIST
		self.exist_vars = exist_vars
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "exist_dec([%s])" % (','.join(self.exist_vars))

class LocFactDec(ASTNode):
	def __init__(self, loc_facts, parse_frag=None):
		self.dec_type = DEC_LOCFACT
		self.loc_facts = loc_facts
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "loc_fact_dec([%s])" % ( ','.join(self.loc_facts) )

'''
class FactDec:
	def __init__(self, modifiers, fact_type):
		self.fact_type = fact_type
		self.modifiers = modifiers
	def __str__(self):
		return "fact_dec([%s],%s)" % (','.join(self.modifiers) if len(self.modifiers) > 0 else "None",self.fact_type)
'''

class FactDec(ASTNode):
	def __init__(self, modifiers, name, type, parse_frag=None):
		self.dec_type = DEC_FACT
		self.type = type
		self.name = name
		self.modifiers = modifiers
		self.reg_source_info(parse_frag, highlight_idx=2)
		self.persistent = False
		self.local      = False
		self.monotone   = False
		self.uses_priority = False
	def adjust_lex(self):
		self.hl_end = self.hl_start + len(self.name)
	def __str__(self):
		return "fact_dec([%s],%s,%s)" % (','.join(self.modifiers) if len(self.modifiers) > 0 else "None",self.name,self.type if self.type != None else "None")
	def arg_types(self):
		if self.type == None:
			return []
		type_kind = self.type.type_kind
		if type_kind == TYPE_TUP:
			return self.type.types
		else:
			return [self.type]

class RuleDec(ASTNode):
	def __init__(self, name, lhs, rhs, where=None, exists=None, parse_frag=None):
		self.dec_type = DEC_RULE
		self.name = name
		(slhs,plhs,grd) = lhs
		self.slhs = slhs
		self.plhs = plhs
		self.grd  = grd
		self.rhs  = rhs
		if where != None:
			self.where = where
		else:
			self.where = []
		if exists != None:
			self.exists = exists
		else:
			self.exists = []
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "rule_dec(%s,[%s],[%s],[%s],[%s],[%s],[%s])" % (str(self.name), ','.join( map(str,self.slhs) ), ','.join( map(str,self.plhs) ), ','.join( map(str,self.grd) ), ','.join(map(str,self.exists)), ','.join(map(str,self.rhs)) , ','.join(map(str,self.where)) )

class InitDec(ASTNode):
	def __init__(self, name, facts, parse_frag=None):
		self.name = name
		self.facts = facts
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "init_dec(%s,[%s])" % (str(self.name), ','.join(map(str,self.facts)) )

class AssignDec(ASTNode):
	def __init__(self, term_pat, builtin_exp, parse_frag=None):
		self.dec_type = DEC_ASSIGN
		self.term_pat = term_pat
		self.builtin_exp = builtin_exp
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "assign(%s,%s)" % (str(self.term_pat),str(self.builtin_exp))

# Fact and guard

FACT = 'fact'

FACT_BASE = 'fact_base'
FACT_LOC  = 'fact_loc'
FACT_LOC_CLUSTER = 'fact_loc_cluster'
FACT_COMPRE = 'fact_compre'

class FactBase(ASTNode):
	def __init__(self, name, terms, priority=None, parse_frag=None):
		self.name      = name
		self.terms     = terms
		self.fact_type = FACT_BASE
		self.reg_source_info(parse_frag)
		self.priority = priority
		self.local    = True
		self.monotone = False
	def __str__(self):
		return "%s(%s)" % (str(self.name),','.join(map(str,self.terms)))

class FactLoc(ASTNode):
	def __init__(self, loc, fact, priority=None, parse_frag=None):
		self.loc       = loc
		self.fact      = fact
		self.fact_type = FACT_LOC
		self.reg_source_info(parse_frag)
		self.priority = priority
	def __str__(self):
		return "[%s]%s" % (str(self.loc),str(self.fact))

class FactLocCluster(ASTNode):
	def __init__(self, loc, facts, priority=None, parse_frag=None):
		self.loc       = loc
		self.facts     = facts
		self.fact_type = FACT_LOC_CLUSTER
		self.reg_source_info(parse_frag)
		self.priority = priority
	def __str__(self):
		if len(self.facts) == 1:
			s = str(self.facts[0])
		else:
			s = "(%s)" % (','.join(map(str,self.facts)))
		return "[%s]%s" % (str(self.loc),s)

class FactCompre(ASTNode):
	def __init__(self, facts, comp_ranges, guards, priority=None, parse_frag=None):
		self.facts = facts
		self.comp_ranges = comp_ranges
		self.guards = guards
		self.fact_type = FACT_COMPRE
		self.reg_source_info(parse_frag)
		self.priority = priority
	def __str__(self):
		fact_str = ','.join(map(str,self.facts))
		if len(self.comp_ranges) == 0:
			comp_range_str = "Empty"
		else:
			comp_range_str = ','.join(map(str,self.comp_ranges))
		if len(self.guards) == 0:
			guard_str = "Empty"
		else:
			guard_str = ','.join(map(str,self.guards))
		return "factcompre(%s|%s|%s)" % (fact_str,comp_range_str,guard_str)

class CompRange(ASTNode):
	def __init__(self, term_vars, term_range, parse_frag=None):
		self.term_vars  = term_vars
		self.term_range = term_range
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s <- %s" % (str(self.term_vars),str(self.term_range))

GUARD = 'guard'

class Guard(ASTNode):
	def __init__(self, term, parse_frag=None):
		self.term = term
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "!(%s)" % ( str(self.term) )


# Terms

TERM_CONS  = 'tm_cons'
TERM_VAR   = 'tm_var'
TERM_APP   = 'tm_app'
TERM_LIST  = 'tm_list'
TERM_LISTCONS = 'tm_listcons'
TERM_TUPLE = 'tm_tuple'
TERM_BINOP = 'tm_binop'
TERM_UNAOP = 'tm_unaop'
TERM_LIT   = 'tm_lit'
TERM_UNDERSCORE = 'tm_us'
TERM_MSET  = 'tm_mset'
TERM_ENUM_MSET = 'tm_enum_mset'
TERM_COMPRE = 'tm_compre'

class TermCons(ASTNode):
	def __init__(self, name, parse_frag=None):
		self.name = name
		self.term_type = TERM_CONS
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s" % (self.name)
	def adjust_lex(self):
		self.lex_end = self.lex_start + len(self.name)
		self.hl_end = self.hl_start + len(self.name)
	def get_node_args(self):
		return (self.name)

class TermVar(ASTNode):
	def __init__(self, name, parse_frag=None):
		self.name = name
		self.term_type = TERM_VAR
		self.reg_source_info(parse_frag)
	def __str__(self):
		if hasattr(self,'rule_idx'):
			# return "%s(%s::%s)" % (TERM_VAR,self.name,self.rule_idx)
			return '%s' % (self.name)
			# return "%s" % self.name
		else:
			return "%s(%s)" % (TERM_VAR,self.name)
	def adjust_lex(self):
		self.lex_end = self.lex_start + len(self.name)
		self.hl_end = self.hl_start + len(self.name)
	def get_node_args(self):
		return (self.name)
	def __eq__(self, other):
		if hasattr(self,'rule_idx') and hasattr(other,'rule_idx'):
			return self.rule_idx == other.rule_idx
		else:
			return self.name == other.name

class TermApp(ASTNode):
	def __init__(self, term1, term2, parse_frag=None):
		self.term1 = term1
		self.term2 = term2
		self.term_type = TERM_APP
		self.reg_source_info(parse_frag)
	def __str__(self):
		# return "%s(%s %s)" % (TERM_APP,str(self.term1),str(self.term2))
		return "%s(%s)" % (self.term1,self.term2)

class TermTuple(ASTNode):
	def __init__(self, terms, parse_frag=None):
		self.terms = terms
		self.term_type = TERM_TUPLE
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "(%s)" % (','.join(map(str,self.terms)))

class TermList(ASTNode):
	def __init__(self, terms, parse_frag=None):
		self.terms = terms
		self.term_type = TERM_LIST
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "[%s]" % (','.join(map(str,self.terms)))

class TermListCons(ASTNode):
	def __init__(self, term1, term2, parse_frag=None):
		self.term1 = term1
		self.term2 = term2
		self.term_type = TERM_LISTCONS
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "[%s|%s]" % (self.term1,self.term2)

class TermMSet(ASTNode):
	def __init__(self, terms, parse_frag=None):
		self.terms = terms
		self.term_type = TERM_MSET
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "{%s}" % (','.join(map(str,self.terms)))

class TermEnumMSet(ASTNode):
	def __init__(self, texp1, texp2, parse_frag=None):
		self.texp1 = texp1
		self.texp2 = texp2
		self.term_type = TERM_ENUM_MSET
	def __str__(self):
		return "{%s..%s}" % (self.texp1,self.texp2)

class TermCompre(ASTNode):
	def __init__(self, term, comp_ranges, guards, parse_frag=None):
		self.term = term
		self.comp_ranges = comp_ranges
		self.guards = guards
		self.term_type = TERM_COMPRE
		self.reg_source_info(parse_frag)
	def __str__(self):
		if len(self.comp_ranges) == 0:
			comp_range_str = "Empty"
		else:
			comp_range_str = ','.join(map(str,self.comp_ranges))
		if len(self.guards) == 0:
			guard_str = "Empty"
		else:
			guard_str = ','.join(map(str,self.guards))
		return "{%s|%s. %s}" % (self.term,comp_range_str,guard_str)

class TermBinOp(ASTNode):
	def __init__(self, term1, binop, term2, parse_frag=None):
		self.term1 = term1
		self.term2 = term2
		self.op = binop
		self.term_type = TERM_BINOP
		self.reg_source_info(parse_frag)
	def adjust_lex(self):
		# self.hl_start  = self.term1.lex_end
		# self.hl_end    = self.term2.hl_start
		self.lex_end = self.term2.lex_end
		self.hl_end = self.term2.hl_end
	def __str__(self):
		return "%s %s %s" % (str(self.term1),self.op,str(self.term2))

class TermUnaryOp(ASTNode):
	def __init__(self, unaop, term, parse_frag=None):
		self.term = term
		self.op = unaop
		self.term_type = TERM_UNAOP
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s %s)" % (TERM_UNAOP,self.op,str(self.term))

class TermLit(ASTNode):
	def __init__(self, literal, ty, parse_frag=None):
		self.literal = literal
		self.type    = TypeCons( ty )
		self.term_type = TERM_LIT
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s" % (self.literal)
	def adjust_lex(self):
		self.lex_end = self.lex_start + len(str(self.literal))
		self.hl_end = self.hl_start + len(str(self.literal))
	def get_node_args(self):
		return (self.literal)

class TermUnderscore(ASTNode):
	def __init__(self, parse_frag=None):
		self.term_type = TERM_UNDERSCORE
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "uscore"

'''
# Builtin Exp

BUILTIN_FUNCALL = 'b_funcall'
BUILTIN_VAR     = 'b_var'
BUILTIN_LIT     = 'b_lit'
BUILTIN_BINOP   = 'b_bop'
BUILTIN_UNAOP   = 'b_uop'

class BuiltinFunCall(ASTNode):
	def __init__(self, name, args, internal=False, parse_frag=None):
		self.name = name
		self.args = args
		self.internal = internal
		self.builtin_type = BUILTIN_FUNCALL
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s(%s))" % (self.builtin_type, self.name, ','.join(map(str,self.args)) ) 

class BuiltinVar(ASTNode):
	def __init__(self, name, parse_frag=None):
		self.name = name
		self.builtin_type = BUILTIN_VAR
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (BUILTIN_VAR,self.name)
	
class BuiltinLit(ASTNode):
	def __init__(self, name, parse_frag=None):
		self.name = name
		self.builtin_type = BUILTIN_LIT
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s)" % (BUILTIN_LIT,self.name)
	
class BuiltinBinOp(ASTNode):
	def __init__(self, bexp1, binop, bexp2, parse_frag=None):
		self.bexp1 = bexp1
		self.bexp2 = bexp2
		self.op = binop
		self.builtin_type = BUILTIN_BINOP
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s %s %s)" % (BUILTIN_BINOP,str(self.bexp1),self.op,str(self.bexp2))

class BuiltinUnaryOp(ASTNode):
	def __init__(self, unaop, bexp, parse_frag=None):
		self.bexp = bexp
		self.op   = unaop
		self.builtin_type = BUILTIN_UNAOP
		self.reg_source_info(parse_frag)
	def __str__(self):
		return "%s(%s %s)" % (BUILTIN_UNAOP,self.op,str(self.bexp))
'''

