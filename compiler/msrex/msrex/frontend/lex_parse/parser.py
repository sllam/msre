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

from msrex.frontend.lex_parse.lexer import *
from msrex.frontend.lex_parse.ast import *

import ply.lex
import ply.yacc as yacc

# Declarations

def p_declarations(p):
	'''
	declarations : declaration declarations
                     |
	'''
	if len(p) == 3:
		p[0] = [p[1]] + p[2]
	else:
		p[0] = []

def p_pragma_declaration(p):
	'''
	declaration : PRAGMA NAME STOP
                    | PRAGMA NAME pragma_name_list STOP
	'''
	if len(p) == 4:
		p[0] = PragmaDec(p[2], pragma_args=[], parse_frag=p)
	else:
		p[0] = PragmaDec(p[2], pragma_args=p[3], parse_frag=p)

def p_pragma_name_list(p):
	'''
	pragma_name_list : NAME pragma_name_list
                         | NAME
	'''
	if len(p) == 3:
		p[0] = [p[1]] + p[2]
	else:
		p[0] = [p[1]]

def p_assign_declaration(p):
	'''
	declaration : assign_stmt STOP
	'''
	p[0] = p[1]

def p_declaration_scope(p):
	'''
	declaration : ENSEM NAME CLPAREN declarations CRPAREN
	'''
	# print p.linespan(0)
	# print p.lexspan(0)
	p[0] = EnsemDec(p[2],p[4],parse_frag=p)

# Extern Declarations

def p_declaration_extern(p):
	'''
	declaration : EXTERN mod_name_top extern_list
                    | MODULE mod_name_top IMPORT extern_list
	'''
	if len(p) == 4:
		p[0] = ExternDec(p[2],p[3],parse_frag=p)
	else:
		p[0] = ExternDec(p[2],p[4],parse_frag=p)

def p_mod_name_top(p):
	'''
	mod_name_top : DQUOTE mod_name DQUOTE
                     | TLPAREN mod_name TRPAREN
                     | mod_name
	'''
	if len(p) == 4:
		p[0] = p[1] + p[2] + p[3]
	else:
		p[0] = p[1]

def p_mod_name(p):
	'''
	mod_name : NAME DIV mod_name
                 | NAME STOP mod_name
                 | NAME
		 | VARIABLE
	'''
	if len(p) == 4:
		p[0] = p[1] + p[2] + p[3]
	else:
		p[0] = p[1]

def p_extern_list(p):
	'''
	extern_list : CLPAREN extern_elems CRPAREN 
                    | extern_elem STOP
	'''
	if len(p) == 4:
		p[0] = p[2]
	else:
		p[0] = [p[1]]

def p_extern_elems(p):
	'''
	extern_elems : extern_elem COMMA extern_elems
                     | extern_elem
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_extern_elems_alt(p):
	'''
	extern_elems : extern_elem STOP extern_elems
                     | extern_elem STOP
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_extern_elem(p):
	'''
	extern_elem : NAME COLON COLON type 
	'''
	p[0] = ExternTypeSig( p[1], p[4], parse_frag=p)
	# p[0] = (p[1],p[4])

# Predicate Declarations

def p_declaration_fact(p):
	'''
	declaration : PRED NAME COLON COLON fact_sort STOP
                    | PRED NAME COLON COLON type ARROW fact_sort STOP
	'''
	# print p.linespan(0)
	# print p.lexspan(0)
	if len(p) == 7:
		p[0] = FactDec([],p[2],None,fact_role=p[5],parse_frag=p)
	else:
		p[0] = FactDec([],p[2],p[5],fact_role=p[7],parse_frag=p)


def p_declaration_fact_with_modifiers(p):
	'''
        declaration : PRED NAME COLON COLON fact_sort WHERE typemodifiers STOP
	            | PRED NAME COLON COLON type ARROW fact_sort WHERE typemodifiers STOP
	'''

	if len(p) == 9:
		p[0] = FactDec(p[7],p[2],None,fact_role=p[5],parse_frag=p)
	else:
		p[0] = FactDec(p[9],p[2],p[5],fact_role=p[7],parse_frag=p)

def p_match_fact_sort(p):
	'''
	fact_sort : FACT
	'''
	p[0] = MATCH_FACT

def p_trigger_fact_sort(p):
	'''
	fact_sort : TRIGGER
	'''
	p[0] = TRIGGER_FACT

def p_actuator_fact_sort(p):
	'''
	fact_sort : ACTUATOR
	'''
	p[0] = ACTUATOR_FACT

# Export Declarations

def p_export_query(p):
	'''
	declaration : EXPORT QUERY fact STOP
	'''
	p[0] = ExportDec(QUERY_EXPORT,p[3],parse_frag=p)

# Location Declarations

def p_declaration_exec(p):
	'''
	declaration : EXEC NAME CLPAREN declarations CRPAREN
	'''
	p[0] = ExecDec(p[2],p[4],parse_frag=p)

def p_declaration_exist(p):
	'''
	declaration : EXISTS var_list STOP
	'''
	p[0] = ExistDec(p[2],parse_frag=p)

def p_declaration_forall(p):
	'''
	declaration : FORALL var_list STOP
	'''
	p[0] = ForallDec(p[2],parse_frag=p)

def p_declaration_loc_facts(p):
	'''
	declaration : rule_rhs STOP
	'''
	p[0] = LocFactDec(p[1],parse_frag=p)

def p_loc_name_list(p):
	'''
	loc_name_list : NAME COMMA loc_name_list
                      | NAME
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_fact_list(p):
	'''
	fact_list : fact COMMA fact_list
	          | fact
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

# Role and Init Declarations

def p_declaration_role_sig(p):
	'''
	declaration : ROLE NAME COLON COLON type STOP
	'''
	p[0] = RoleSigDec(p[2],p[5],parse_frag=p)

def p_declaration_role_def(p):
	'''
	declaration : ROLE SLPAREN location SRPAREN fact ASSIGN rule_rhs STOP
                    | ROLE SLPAREN location SRPAREN fact ASSIGN rule_rhs WHERE assign_stmts STOP
	'''
	if len(p) == 9:
		p[0] = RoleDefDec(p[3], p[5], p[7], parse_frag=p)
	else:
		p[0] = RoleDefDec(p[3], p[5], p[7], where=p[9], parse_frag=p)
		
def p_declaration_init_def(p):
	'''
	declaration : INIT var_list AS fact STOP
	'''
	p[0] = InitDec(p[2], p[4], parse_frag=p)

# Rule Declarations

def p_declaration_rule(p):
	'''
	declaration : RULE NAME COLON COLON rule_lhs IMPLIES exists_dec rule_rhs STOP
                    | RULE NAME COLON COLON rule_lhs IMPLIES exists_dec rule_rhs WHERE assign_stmts STOP
	'''
	if len(p) == 10:
		p[0] = RuleDec(p[2],p[5],p[8],exists=p[7],parse_frag=p)
	else:
		p[0] = RuleDec(p[2],p[5],p[8],where=p[10],exists=p[7],parse_frag=p)

def p_exists_dec(p):
	'''
	exists_dec : EXISTS var_list STOP
                   |
	'''
	if len(p) == 4:
		p[0] = p[2]
	else:
		p[0] = []

def p_assign_stmts(p):
	'''
	assign_stmts : assign_stmt COMMA assign_stmts
	             | assign_stmt
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_assign_stmt(p):
	'assign_stmt : term ASSIGN term'
	p[0] = AssignDec(p[1],p[3],parse_frag=p)	

def p_var_list(p):
	'''
	var_list : var_atom COMMA var_list
	         | var_atom
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_var(p):
	'''
	var_atom : VARIABLE
	'''
	p[0] = TermVar(p[1],parse_frag=p)

def p_location_var(p):
	'location : VARIABLE'
	p[0] = TermVar(p[1],parse_frag=p)

def p_location_name(p):
	'location : NAME'
	p[0] = TermCons(p[1],parse_frag=p)

def p_location_lit(p):
	'location : INT'
	p[0] = TermLit(p[1],parse_frag=p)

def p_rule_lhs(p):
	'''
	rule_lhs : rule_heads
	'''
	p[0] = (p[1],[],[])

def p_rule_chr_lhs(p):
	'''
	rule_lhs : rule_heads BACK rule_heads
                 | rule_heads BACK rule_heads BAR guards
	'''
	if len(p) == 4:
		p[0] = (p[3],p[1],[])
	else:
		p[0] = (p[3],p[1],p[5])
		
def p_rule_chr_lhs_2(p):
	'''
	rule_lhs : rule_heads BAR guards
	'''
	p[0] = (p[1],[],p[3])

def p_rule_heads(p):
	'''
	rule_heads : lhs_pat COMMA rule_heads
                   | lhs_pat  
	'''
	if len(p) == 4:
		if p[1] != None:
			p[0] = [p[1]] + p[3]
		else:
			p[0] = p[3]
	else:
		if p[1] != None:
			p[0] = [p[1]]
		else:
			p[0] = []

def p_rule_heads_one(p):
	'''
	rule_heads : INT
	'''
	p[0] = []

def p_lhs_fact(p):
	'''
	lhs_pat : loc_fact
		| fact_comp_pat
	'''
	p[0] = p[1]

def p_lhs_none(p):
	'lhs_pat : INT'
	p[0] = None

def p_rule_rhs(p):
	'''
	rule_rhs : rhs_pat COMMA rule_rhs
	         | rhs_pat
	'''
	if len(p) == 4:
		if p[1] != None:
			p[0] = [p[1]] + p[3]
		else:
			p[0] = p[3]
	else:
		if p[1] != None:
			p[0] = [p[1]]
		else:
			p[0] = []	

def p_rule_rhs_one(p):
	'rule_rhs : INT'
	p[0] = []

def p_rhs_fact(p):
	'''
	rhs_pat : loc_fact
	        | fact_comp_pat
	'''
	p[0] = p[1]

def p_rhs_fact_priority(p):
	'''
	rhs_pat : loc_fact PRIORITY INT
	        | fact_comp_pat PRIORITY INT
	'''
	p[1].priority = p[3]
	p[0] = p[1]

def p_rhs_none(p):
	'rhs_pat : INT'
	p[0] = None


def p_fact_compre_pat_1(p):
	'''
	fact_comp_pat : CLPAREN loc_fact_list BAR comp_ranges STOP guards CRPAREN comp_option
                      | CLPAREN loc_fact_list BAR comp_ranges CRPAREN comp_option
	'''
	# TODO
	if len(p) == 9:
		p[0] = FactCompre(p[2],p[4],p[6],compre_mod=p[8],parse_frag=p)
	else:
		p[0] = FactCompre(p[2],p[4],[],compre_mod=p[6],parse_frag=p)

def p_fact_compre_pat_2(p):
	'''
	fact_comp_pat : CLPAREN loc_fact_list BAR guards CRPAREN comp_option
                      | CLPAREN loc_fact_list CRPAREN comp_option
	'''
	# TODO
	if len(p) == 7:
		p[0] = FactCompre(p[2],[],p[4],compre_mod=p[6],parse_frag=p)
	else:
		p[0] = FactCompre(p[2],[],[],compre_mod=p[4],parse_frag=p)

def p_fact_compre_pat_3(p):
	'''
	fact_comp_pat : MINUS CLPAREN loc_fact_list BAR guards CRPAREN
                      | MINUS CLPAREN loc_fact_list CRPAREN
	'''
	if len(p) == 7:
		p[0] = FactCompre(p[3],[],p[5],compre_mod=COMP_NONE_EXISTS,parse_frag=p)
	else:
		p[0] = FactCompre(p[3],[],[],compre_mod=COMP_NONE_EXISTS,parse_frag=p)

def p_comp_option(p):
	'''
	comp_option : PLUS
                    | 
	'''
	if len(p) == 2:
		p[0] = COMP_ONE_OR_MORE
	else:
		p[0] = COMP_ANY

def p_comp_ranges(p):
	'''
	comp_ranges : comp_range COMMA comp_ranges
                    | comp_range
	'''
	# TODO
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_comp_range(p):
	'''
	comp_range : term UNIDIS term
                   | term ARROW term
	'''
	p[0] = CompRange(p[1],p[3],parse_frag=p)

def p_loc_fact(p):
	'''
	loc_fact : fact
                 | SLPAREN location SRPAREN fact
                 | SLPAREN location SRPAREN RLPAREN fact_list RRPAREN 
	'''
	if len(p) == 2:
		p[0] = p[1]
	elif len(p) == 5:
		p[0] = FactLoc(p[2],p[4],parse_frag=p)
	else:
		p[0] = FactLocCluster(p[2],p[5],parse_frag=p)

def p_fact_list(p):
	'''
	fact_list : fact COMMA fact_list
	          | fact
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_loc_fact_list(p):
	'''
	loc_fact_list : loc_fact COMMA loc_fact_list
	              | loc_fact
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_fact(p):
	'''
	fact : NAME RLPAREN termargs RRPAREN
             | NAME RLPAREN RRPAREN 
	'''
	if len(p) == 5:
		p[0] = FactBase(p[1],p[3],parse_frag=p)
	else:
		p[0] = FactBase(p[1],[],parse_frag=p)

def p_lhs_guard(p):
	'''
	guards : term COMMA guards
               | term
	'''
	if len(p) == 4:
		p[0] = [p[1]] + p[3]
	else:
		p[0] = [p[1]]

def p_termargs(p):
	"""
	termargs : term
	         | term COMMA termargs
	"""
	if len(p) == 2:
		p[0] = [p[1]]
	else:
		p[0] = [p[1]] + p[3]

def p_term_std(p):
	"""
	term : simp_term
             | simp_term term
	"""
	if len(p) == 2:
		p[0] = p[1]
	else:
		p[0] = TermApp(p[1],p[2],parse_frag=p)

def p_term_op(p):
	"""
	term : simp_term term_binop simp_term
	     | term_unaryop simp_term
	"""
	if len(p) == 4:
		p[0] = TermBinOp(p[1],p[2],p[3],parse_frag=p)
	else:
		p[0] = TermUnaryOp(p[1],p[2],parse_frag=p)

def p_term_binop(p):
	'''
	term_binop : NEQ
	           | EQUAL
	           | LEQ
	           | GEQ
	           | TLPAREN
	           | TRPAREN
	           | IN
	           | PLUS
	           | MINUS
	           | TIMES
	           | DIV
	           | COLON
	''' 
	p[0] = p[1]

def p_term_unary_op(p):
	'''
	term_unaryop : MINUS
	'''
	p[0] = p[1]

def p_simp_term_tuple(p):
	'''
	simp_term : RLPAREN termargs RRPAREN
	          | RLPAREN RRPAREN
	'''
	if len(p) == 4:
		p[0] = TermTuple(p[2],parse_frag=p)
	else:
		p[0] = TermTuple([],parse_frag=p)
		

def p_simp_term_list(p):
	'''
	simp_term : SLPAREN termargs SRPAREN
	          | SLPAREN SRPAREN
	'''
	if len(p) == 4:
		p[0] = TermList(p[2],parse_frag=p)
	else:
		p[0] = TermList([],parse_frag=p)

def p_simp_term_listcons(p):
	'''
	simp_term : SLPAREN term BAR term SRPAREN
	'''
	p[0] = TermListCons(p[2],p[4],parse_frag=p)

def p_simp_term_mset(p):
	'''
	simp_term : CLPAREN termargs CRPAREN
	          | CLPAREN CRPAREN
	'''
	# TODO
	if len(p) == 4:
		p[0] = TermMSet(p[2],parse_frag=p)
	else:
		p[0] = TermMSet([],parse_frag=p)

def p_simp_term_compre_pat_1(p):
	'''
	simp_term : CLPAREN term BAR comp_ranges STOP guards CRPAREN
                  | CLPAREN term BAR comp_ranges CRPAREN
	'''
	# TODO
	if len(p) == 8:
		p[0] = TermCompre(p[2],p[4],p[6],parse_frag=p)
	else:
		p[0] = TermCompre(p[2],p[4],[],parse_frag=p)

def p_simp_term_enum_mset(p):
	'''
	simp_term : CLPAREN term STOP STOP term CRPAREN
	'''
	p[0] = TermEnumMSet(p[2], p[5], parse_frag=p)

def p_simp_term_brackets(p):
	'simp_term : RLPAREN term RRPAREN'
	p[0] = p[2]

def p_simp_term_underscore(p):
	'simp_term : UNDERSCORE'
	p[0] = TermUnderscore(parse_frag=p)

def p_simp_term_cons(p):
	'simp_term : NAME'
	p[0] = TermCons(p[1],parse_frag=p) 

def p_simp_term_var(p):
	'simp_term : VARIABLE'
	p[0] = TermVar(p[1],parse_frag=p)

def p_simp_term_float(p):
	'simp_term : FLOAT'
	p[0] = TermLit(p[1],"float",parse_frag=p)	

def p_simp_term_int(p):
	'simp_term : INT'
	p[0] = TermLit(p[1],"int",parse_frag=p)

def p_simp_term_string(p):
	'simp_term : STRING'
	p[0] = TermLit(p[1],"string",parse_frag=p)

def p_simp_term_char(p):
	'simp_term : CHAR'
	p[0] = TermLit(p[1],"char",parse_frag=p)


# Types

'''
def p_externtype(p):
	"""
	externtype : NAME RLPAREN typeargs RRPAREN
	"""
	p[0] = ExternType(p[1],p[3])
'''

def p_typemodifiers(p):
	"""
	typemodifiers : typemodifier
	              | typemodifiers COMMA typemodifier
	"""	
	if len(p) == 2:
		p[0] = [p[1]]
	else:
		p[0] = p[1] + [p[3]]

def p_typemodifier(p):
	'''
	typemodifier : NAME
	'''
	p[0] = FactMod(p[1],[],parse_frag=p)

'''
def p_facttype(p):
	"""
	facttype : NAME RLPAREN typeargs RRPAREN
	"""
	p[0] = FactType(p[1],p[3])
'''

def p_typeargs(p):
	"""
	typeargs : type
	         | type COMMA typeargs
	"""
	if len(p) == 2:
		p[0] = [p[1]]
	else:
		p[0] = [p[1]] + p[3]

def p_type(p):
	"""
	type : singletype
	     | singletype type
	"""
	if len(p) == 2:
		p[0] = p[1]
	else:
		p[0] = TypeApp(p[1],p[2],parse_frag=p)

def p_singletype_func(p):
	'singletype : type ARROW type'
	p[0] = TypeArrow(p[1],p[3],parse_frag=p)

def p_singletype_tuple(p):
	'singletype : RLPAREN typeargs RRPAREN'
	p[0] = TypeTuple(p[2],parse_frag=p) 

def p_singletype_mset(p):
	'singletype : CLPAREN type CRPAREN'
	# TODO
	p[0] = TypeMSet(p[2],parse_frag=p)

def p_singletype_list(p):
	'singletype : SLPAREN type SRPAREN'
	p[0] = TypeList(p[2],parse_frag=p)

def p_singletype_brackets(p):
	'singletype : RLPAREN type RRPAREN'
	p[0] = p[2]
	
def p_singletype_cons(p):
	'singletype : NAME'
	p[0] = TypeCons(p[1],parse_frag=p)

def p_singletype_var(p):
	'singletype : VARIABLE'
	p[0] = TypeVar(p[1],parse_frag=p)


def p_error(p):
    raise TypeError("unknown text at %r" % (p.value,))

'''
lex.lex()

# f = open('test.msr')
f = open('hyper_quick_sort.msr')
# lex.input("type a . a(X,1,1.03),b(X,Y,\" sadfs+\") == -o = c(X,Y/X-).")
#lex.input(f.read())

lex.input(f.read())

for tok in iter(lex.token, None):
    print repr(tok.type), repr(tok.value)

f = open('hyper_quick_sort.msr')
# f = open('test.msr')

yacc.yacc()

ast = yacc.parse(f.read())

for n in ast:
	print str(n)
'''

def run_parser(file):
	lex.lex()
	f = open(file)
	yacc.yacc()
	input = f.read()
	# print "\033[41m" + input[94:134] + "\033[0m Ha ha"
	ast = yacc.parse(input, tracking=True)
	return (input, ast)

def run_parser_input(input):
	lex.lex()
	yacc.yacc()
	ast = yacc.parse(input, tracking=True)
	return ast


