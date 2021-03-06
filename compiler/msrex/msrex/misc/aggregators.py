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

import operator as op

def foldl(xss, init_xs):
	return reduce(op.concat, xss, init_xs)

def tmerge(*ts):
	tts = list(ts[0])
	idx = 1
	while idx < len(ts):
		x = 0
		while x < len(tts):
			tts[x] += ts[idx][x]
			x += 1
		idx += 1
	return tuple(tts)

def subseteq(xs, ys, map_func=None):
	if map_func != None:
		xs = map(map_func,xs)
		ys = map(map_func,ys)
	for x in xs:
		if x not in ys:
			return False
	return True

def diff(xs, ys, fx=lambda x: x, fy=lambda y: y):
	zs = []
	fys = map(fy, ys)
	for x in xs:
		if fx(x) not in fys:
			zs.append( x )
	return zs



