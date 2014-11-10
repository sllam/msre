
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

import os
import sys
import traceback as t

import random as r

import subprocess as sp

from msrex.frontend.process import process_msre
from msrex.frontend.code.code_generator import CPPCodeGenerator

from msrex.misc.msr_logging import init_logger, log_info
from msrex.misc.template import template

from datetime import datetime

# Auxiliary operations

def gen_run_id():
	return r.randint(1000000,9999999)

def mk_cpp_name(src_name):
	return "%s.cpp" % src_name 

def mk_msre_name(src_name):
	return "%s.msr" % src_name

def mk_source_name(run_id):
	return "msre_source_%s" % run_id

def mk_log_file_name(run_id):
	return "run_%s" % run_id

CALL_STAT_SUCCESS = 'Success' 
CALL_STAT_FAIL    = 'Fail'
CALL_STAT_ERROR   = 'Error'

def mk_succ_stat():
	return { 'stat' : CALL_STAT_SUCCESS }

def mk_fail_stat():
	return { 'stat' : CALL_STAT_FAIL }

def mk_error_stat():
	return { 'stat' : CALL_STAT_ERROR }

def is_succ(call_stat):
	return call_stat['stat'] == CALL_STAT_SUCCESS

def is_fail(call_stat):
	return call_stat['stat'] == CALL_STAT_FAIL

def is_error(call_stat):
	return call_stat['stat'] == CALL_STAT_ERROR

# MSRE Compilation and Execution Pipe Operations.

def compile_msre_source(src_name, source):
	print "Compiling msre program..."
	try:
		msr_file_name = mk_msre_name(src_name)
		t1 = datetime.now()
		output = process_msre(msr_file_name, source)
		t2 = datetime.now()
		tdelta = t2 - t1
		if output['valid']:
			call_stat = mk_succ_stat()
			call_stat['output'] = output
		else:
			call_stat = mk_fail_stat()
			call_stat['fail_text'] = '\n'.join(output['error_reports']) 
		return call_stat,tdelta
	except:
		call_stat = mk_error_stat()		
		e1,e2,e3 = sys.exc_info()
		call_stat['error_text'] = "Unexpected error occurred while compiling msre program:\n%s\n%s\n%s" % (e1,e2,t.extract_tb(e3))
		return call_stat,None

def generate_cpp_source(src_name, output):
	print "Generating cpp source..."
	try:
		prog = output["prog"]
		t1 = datetime.now()
		cppGen = CPPCodeGenerator(prog, prog.fact_dir, output['data'])
		cppGen.generate()
		t2 = datetime.now()
		tdelta = t2 - t1
		return mk_succ_stat(),tdelta
	except:
		call_stat = mk_error_stat()
		e1,e2,e3 = sys.exc_info()
		call_stat['error_text'] = "Unexpected error occurred while generating cpp source:\n%s\n%s\n%s" % (e1,e2,t.extract_tb(e3))
		return call_stat,None	

def compile_cpp_source(src_name):
	print "Compiling cpp source..."
	try:
		cpp_file_name = mk_cpp_name(src_name)
		compile_cpp_cmd = ("mpiCC %s -lboost_mpi -lboost_serialization -o %s" % (cpp_file_name, src_name)).split(' ')
		t1 = datetime.now()
		sp.call(compile_cpp_cmd)
		t2 = datetime.now()
		tdelta = t2 - t1
		return mk_succ_stat(),tdelta
	except:
		call_stat = mk_error_stat()
		e1,e2,e3 = sys.exc_info()
		call_stat['error_text'] = "Unexpected error occurred while compiling cpp source:\n%s\n%s\n%s" % (e1,e2,t.extract_tb(e3))
		return call_stat,None

	
def execute_cpp_binary(src_name, run_id):
	print "Executing cpp program..."
	try:
		NUM_THREADS = 1
		log_name = mk_log_file_name(run_id)
		run_cpp_cmd = ("mpirun -n %s %s %s" % (NUM_THREADS,src_name,log_name)).split(' ')
		t1 = datetime.now()
		sp.call(run_cpp_cmd)
		t2 = datetime.now()
		tdelta = t2 - t1
		call_stat = mk_succ_stat()
		f = open("%s.html" % log_name,'r')
		call_stat['output_text'] = f.read()
		return call_stat,tdelta
	except:
		call_stat = mk_error_stat()
		e1,e2,e3 = sys.exc_info()
		call_stat['error_text'] = "Unexpected error occurred while executing cpp program:\n%s\n%s\n%s" % (e1,e2,t.extract_tb(e3))
		return call_stat,None



def run_full_msre_pipe(source, clean=True, with_time_data=True):

	run_id = gen_run_id()
	src_name = mk_source_name(run_id)
	cpp_name = mk_cpp_name(src_name)
	log_name = "%s.log" % mk_log_file_name(run_id)
	markdown_name = "%s.html" % mk_log_file_name(run_id)

	call_stat,tdel1 = compile_msre_source(src_name, source)
	if not is_succ(call_stat):
		return call_stat

	output = call_stat['output']
	call_stat,tdel2 = generate_cpp_source(src_name, output)
	if not is_succ(call_stat):
		return call_stat

	call_stat,tdel3 = compile_cpp_source(src_name)
	if not is_succ(call_stat):
		return call_stat

	call_stat,tdel4 = execute_cpp_binary(src_name, run_id)
	if not is_succ(call_stat):
		return call_stat

	if with_time_data:
		'''
		time_text = "Auxiliary time stamps:\n\n"
		time_text += "MSRE (source language) compile time: %s s\n\n" % tdel1.total_seconds() 
		time_text += "C++ code generation time: %s s\n\n" % tdel2.total_seconds()
		time_text += "C++ (target language) compile time: %s s\n\n" % tdel3.total_seconds()
		time_text += "Program execution time (with Py foreign call overheads): %s s\n\n" % tdel4.total_seconds()
		time_text += "Total time: %s s\n\n" % (tdel1 + tdel2 + tdel3 + tdel4).total_seconds()
		'''
		time_text  = "Program execution time (with foreign call overheads): %s s\n\n" % tdel4.total_seconds()
		time_text += "Total compilation time (currently unoptimized): %s s\n\n" % (tdel1 + tdel2 + tdel3).total_seconds() 
		# time_text += "Total time: %s s\n\n" % (tdel1 + tdel2 + tdel3 + tdel4).total_seconds()
		call_stat['output_text'] += "\n\n" + time_text

	if clean:
		remove_file_cmd = "rm %s"
		for file_name in [src_name, cpp_name, log_name, markdown_name]:
			this_remove_file_cmd = (remove_file_cmd % file_name).split(' ')
			sp.call(this_remove_file_cmd)

	return call_stat

def test_it(clean=True):

	source = template('''
	ensem shortpath {

		predicate trans_req :: (loc,int) -> fact.
		predicate edge :: (loc,int) -> fact.
		predicate path :: (loc,int) -> fact.

		rule base  :: [X]edge(Y,D) \ 1 --o [X]path(Y,D).
		rule elim  :: [X]path(Y,D1) \ [X]path(Y,D2) | D1 <= D2 --o 1.
		rule trans_1 :: [X]edge(Y,D) \ 1 --o [Y]trans_req(X,D).
		rule trans_2 :: [Y]trans_req(X,D1), [Y]path(Z,D2) \ 1 | X != Z --o [X]path(Z,D1+D2).
	}

	execute shortpath {
		exists L0, L1, L2, L3, L4, L5, L6, L7, L8.
		[L0]edge(L1,7), [L0]edge(L2,4).
		[L1]edge(L3,2).
		[L2]edge(L3,20).
		[L3]edge(L4,1), [L3]edge(L5,18), [L3]edge(L6,3).
		[L4]edge(L7,40), [L4]edge(L5,1).
		[L5]edge(L7,15), [L5]edge(L6,2).
		[L6]edge(L7,8).
		[L7]edge(L0,13), [L7]edge(L8,6).
		[L8]edge(L0,4).
	}
	''')

	return run_full_msre_pipe(source, clean=clean)


