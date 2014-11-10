msre
====

MSRE: Decentralized Multiset Rewriting with Comprehensions for Ensembles

by Edmund S. L. Lam and Iliano Cervesato

* This implementation was made possible by an NPRP grant (NPRP 09-667-1-100, Effective Programming for Large Distributed Ensembles) from the Qatar National Research Fund (a member of the Qatar Foundation). 

Introduction
============

A prototype implementation of decentralized multiset rewriting with comprehension for ensembles.

See our paper and technical report for details:

i. "Decentralized Execution of Constraint Handling Rules for Ensembles", PPDP'2013
http://www.qatar.cmu.edu/%7Esllam/my_papers/published/SLLAM_ppdp13.pdf

ii. "Constraint Handling Rules with Comprehension", CHR'2014
http://www.qatar.cmu.edu/~sllam/my_papers/published/SLLAM_chr14.pdf

iii. "Optimized Compilation of Multiset Rewriting with Comprehensions", tech report (also appearing in APLAS'2014)
http://www.qatar.cmu.edu/~sllam/my_papers/techreport/SLLAM_TR14-119.pdf

Just want a quick demo? We have an online demo that compiles and runs MSRE programs! Visit http://rise4fun.com/msre

Basic Requirements
==================

System Applications:
   - Python 2.7 compiler and runtime
   - C++ compiler and runtime
   - MPI Distribution (preferably MPI-2)
   - C++ Boost Libraries (> 1.55.0)
   - System development libraries for Python and MPI

Non-standard Python packages:
   - ply (Python Lex-Yacc http://www.dabeaz.com/ply/)
   - z3Py: Python APIs for z3 SMT Solver (Check https://z3.codeplex.com/ for installation details)
   - pysetcomp: Set Comprehension Extension for z3 in Python (Download at https://github.com/sllam/pysetcomp)

* Currently only tested on Ubuntu, but do try on other platforms and feel free to report any bugs or issues to us!
** Apologies for the sparse instructions! More information to come soon! 

Quick Guide
===========

Once you got the system and library requirements sorted, you are ready to run the make file in the main directory
of the MSRE distribution (You probably need to `sudo' it). 

> sudo make install

This will build and install the MSRE compiler and place the necessary library and binary files in your system's
library and binary folders, those are defaulted to:

MSRE_LIB_PATH := /usr/local/lib
MSRE_BIN_PATH := /usr/local/bin

Once that is done you are set! Go to the `samples' directory and try out MSRE!

> cd samples
> msre ghs.msr

This should compile the MSRE program ghs.msr, producing an executable ghs. Its a standalone MPI program, so
you will need something like mpirun to execute it.

> mpirun -n 1 ghs outputfile

The program takes a (non-optional) argument that states the name of a file to write its output to.

Note: You can try running with multiple processes, but node that how the MSRE runtime maps abstract computation nodes of 
MSRE to actual physical MPI nodes (ranks) is controlled by several C++ pragmas. Its currently undocumented here, but we 
are working on fixing that. Apologies for this and please stay tuned for updates!

Acknowledgements
================

Many thanks to the following, who have made this prototype implementation possible:
  - Qatar Foundation, the sponsor of this project.
  - People who worked on z3 SMT solver, for building such an awesome easy to use SMT solver with Python bindings.
  - People who worked on Claytronics, which has inspired our work here (Flavio Cruz, Frank Pfenning and Seth Goldstein). 
  - Curtis Schlak for excellent suggests on light-weight visitor pattern for Python.
  - Reviewers of our papers, who tried (and hopefully successfully) install and test drive this prototype

Notes
=====

10 November 2014:
  - If you came from https://github.com/sllam/chrcp , this is the right place to be from now.
    We are deprecating CHR^cp and now we have merged the prototypes into one known as MSRE.
    MSRE is still shares the same essence with CHR^cp (it includes comprehension patterns),
    but it also allows decentralized execution over several computing nodes (must support MPI)

13 July 2014: 
  - There are some minor syntactic difference between the language implemented here, and that of 
    presented in our technical report. We are currently working on finalizing the concrete syntax 
    of our language and documentation, For now, please refer to the examples contained in this
    package. Stay tuned for updates!
  - We are currently merging this code base with that of from another project - Multi Set Rewriting 
    for Ensembles (MSRE). In the near future, CHR^CP and MSRE will be a unified language: combining 
    the idea of multiset rewriting with comprehensions, and decentralized execution of multiset rewritings.

