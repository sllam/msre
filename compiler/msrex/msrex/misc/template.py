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


# A simple template processing library, for code generation.
# Currently, indentations are not generalized: Only responds to tabs ('\t').

DEFAULT_OPEN = "\{\|"
DEFAULT_CLOSE = "\|\}"

import re
	
def compile_template(template, topen=DEFAULT_OPEN, tclose=DEFAULT_CLOSE, **kwargs):

	open_re  = re.compile(topen)
	close_re = re.compile(tclose)

	def find_template_splice(raw_str):

		scan_idx = 0
		while scan_idx < len(raw_str):
			open_span = find_nearest(raw_str, scan_idx, open_re)
			if open_span != None:
				(open_start_idx,open_end_idx) = open_span
				scan_idx = open_end_idx
				close_span = find_nearest(raw_str, scan_idx, close_re)
				if close_span != None:
					(close_start_idx,close_end_idx) = close_span
					scan_idx = close_end_idx
					return (open_start_idx,open_end_idx,close_start_idx,close_end_idx)
				else:
					break
			else:
				break
		return None

	while True:
		match = find_template_splice(template)
		if match != None:
			(open_s,open_e,close_s,close_e) = match
			splice = template[open_e:close_s]


			for arg in kwargs:
				splice = splice.replace(arg,"kwargs[\'%s\']" % arg)

			# print "RUN: %s" % splice
			if len(splice) > 0:
				splice_res = str(eval(splice))
			else:
				splice_res = ''

			# Find number of indentation of this splice
			num_of_indents = find_indent(template, open_s)
			indents = ""
			for _ in range(0,num_of_indents):
				indents += '\t'
			splice_res = splice_res.replace('\n','\n%s' % indents)

			template = template[:open_s]  +  splice_res  + template[close_e:]
		else:
			break

	return template

def find_indent(raw_str, idx):
	newline_re = re.compile('\\n')
	m1 = find_nearest_backwards(raw_str, idx, newline_re)
	if m1 != None:
		(ms1,me1) = m1
		m2 = find_nearest_block(raw_str, me1, re.compile('\\t'))
		if m2 != None:
			(ms2,me2,count) = m2
			if ms2 < idx:
				return count
			else:
				return 0
		else:
			return 0
	else:
		return 0

def find_nearest_backwards(raw_str, idx, pat_re):
	curr_idx = idx
	while curr_idx >= 0:
		curr_str = raw_str[curr_idx:]
		m = pat_re.match(curr_str)
		if m != None:
			(ms,me) = m.span()
			return (ms+curr_idx,me+curr_idx)
		else:
			curr_idx -= 1

def find_nearest(raw_str, start_idx, pat_re):
	curr_idx = start_idx
	while curr_idx < len(raw_str):
		curr_str = raw_str[curr_idx:]
		m = pat_re.match(curr_str)
		if m != None:
			(ms,me) = m.span()
			return (ms+curr_idx,me+curr_idx)
		else:
			curr_idx += 1
	return None

def find_nearest_block(raw_str, start_idx, pat_re):
	curr_idx    = start_idx
	match_start = None
	match_end   = start_idx
	num = 0
	while True:
		m = find_nearest(raw_str, curr_idx, pat_re)
		if m != None:
			(ms,me) = m
			if match_start == None:
				match_start = ms
				match_end   = me
				num += 1
			else:
				# print match_start,match_end,ms,me
				if match_end == ms:
					match_end = me
					num += 1
				else:
					return (match_start,match_end,num)
			curr_idx = me
		else:
			if match_start != None:
				return (match_start,match_end,num)
			else:
				return None

def template(raw_str):
	proc_str = raw_str.strip(' \n')
	tab_re   = re.compile('\\t')
	m = find_nearest_block(proc_str, 0, tab_re)	
	if m != None:
		(ms,me,i) = m
		if ms == 0:
			for _ in range(0,i):
				proc_str = dedent(proc_str)
	return proc_str

def compact(raw_str):
	proc_str = raw_str.strip(' \n\t')
	excess_regions = []
	e_start = 0
	e_end = 0
	while e_start < len(proc_str):
		if proc_str[e_start] == '\n':
			e_start += 1
			e_end = e_start
			e_count = 0
			while e_end < len(raw_str) and proc_str[e_end] in ['\n','\t']:
				if proc_str[e_end] == '\n':
					e_count += 1
				e_end += 1
			while proc_str[e_end] != '\n':
				e_end -= 1
			if e_count > 0:
				excess_regions.append( (e_start,e_end+1) )
			e_start = e_end
		e_start += 1
	if len(excess_regions) > 0:
		start = 0
		output = ""
		for (end,next_start) in excess_regions:
			output += proc_str[start:end]
			start = next_start
		output += proc_str[start:len(proc_str)]
		return output
	else:
		return proc_str		

def indent(template):
	curr_idx = 0
	tab_re = re.compile('\\n')
	curr_template = '\t' + template
	while curr_idx < len(curr_template):
		m = find_nearest(curr_template, curr_idx, tab_re)
		if m != None:
			(ms,me) = m
			curr_template = curr_template[:ms] + '\n\t' + curr_template[me:]
			curr_idx = me + 1
		else:
			break
	return curr_template

def dedent(template):
	curr_idx = 0
	tab_re = re.compile('\\n\\t')
	if template[0] == '\t':
		curr_template = template[1:]
	else:
		curr_template = template
	while curr_idx < len(curr_template):
		m = find_nearest(curr_template, curr_idx, tab_re)
		if m != None:
			(ms,me) = m
			curr_template = curr_template[:ms] + '\n' + curr_template[me:]
			curr_idx = me - 1
		else:
			break
	return curr_template

def join_ext(sep, strs, prefix="", postfix="", alt=""):
	if len(strs) > 0:
		return prefix + sep.join( strs ) + postfix
	else:
		return alt

def join_ext_cond(sep, strs, prefix="", postfix="", threshold=1):
	if len(strs) <= threshold:
		return sep.join( strs )
	else:
		return prefix + sep.join( strs ) + postfix

test_str = template('''
class {|class_name|}:
	def __init__(self):
		self.initialize(forall={|num_of_vars|})
	{| another_template |}
''')

def test(test_str=test_str):
			
	another_template = template('''
		def awesome():
			return \"shit\"
	''')

	return compile_template(test_str, class_name="Gcd", num_of_vars=5, another_template=another_template)


def test2(test_str=test_str):

	tab_re = re.compile('\\t')

	return find_nearest_block(test_str, 0, tab_re)


