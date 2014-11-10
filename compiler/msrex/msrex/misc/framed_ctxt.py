
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

class FramedCtxt:

	def __init__(self):
		self.fctxt   = [{}]
		self.var_idx = 0

	# Private Interfaces

	def new_index(self):
		new_idx = self.var_idx
		self.var_idx += 1
		return new_idx

	def read_index(self, key):
		for frame in self.fctxt:
			if key in frame:
				return frame[key]
		return None	

	# Public Interfaces

	def get_index(self, key):
		idx = self.read_index( key )
		if idx != None:
			return idx
		else:
			return self.add_index( key )

	def add_index(self, key):
		curr_frame = self.fctxt[0]
		new_idx = self.new_index()
		curr_frame[key] = new_idx
		return new_idx

	def push_frame(self, keys=[]):
		self.fctxt = [{}] + self.fctxt
		for key in keys:
			self.add_index( key )

	def pop_frame(self):
		self.fctxt = self.fctxt[1:]

	def __repr__(self):
		return "%s" % self.fctxt

