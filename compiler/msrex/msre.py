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

from msrex.frontend.process import process_msre
from msrex.frontend.code.code_generator import CPPCodeGenerator

from msrex.misc.msr_logging import init_logger, log_info

from string import split
from argparse import ArgumentParser


arg_parser = ArgumentParser(prog='msre.py')
arg_parser.add_argument('filename')
# arg_parser.add_argument('-o', dest="output")
args = arg_parser.parse_args()

output = process_msre(args.filename)

if output["valid"]:
	prog = output["prog"]
	print output["data"]
	for ana in output["analysis"]:
		print "\n"
		print ana
		print "\n"
	cppGen = CPPCodeGenerator(prog, prog.fact_dir, output['data'])
	cppGen.generate()
else:
	for report in output['error_reports']:
		print "\n"
		print report
		print "\n"

# mpiCC mergesort.cpp -lboost_mpi -lboost_serialization -o mergesort


