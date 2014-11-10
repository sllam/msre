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


T_RED_FORE     = "\033[31m"
T_RED_BACK     = "\033[41m"
T_GREEN_FORE   = "\033[32m"
T_GREEN_BACK   = "\033[42m"
T_YELLOW_FORE  = "\033[33m"
T_YELLOW_BACK  = "\033[43m"
T_BLUE_FORE    = "\033[34m"
T_BLUE_BACK    = "\033[44m"
T_MAGENTA_FORE = "\033[35m"
T_MAGENTA_BACK = "\033[45m"
T_CYAN_FORE    = "\033[36m"
T_CYAN_BACK    = "\033[46m"

T_NORM = "\033[0m"

def format_str(raw_str, color_regions, display_regions=[]):
	color_regions = sorted(color_regions, key=lambda (_,x,y): x)

	display_regions = map(lambda (x,y): ((),x,y),display_regions)
	display_regions = sorted(display_regions, key=lambda (_,x,y): x)
	display_regions = unify_regions( display_regions )

	curr_idx = 0
	curr_str = raw_str
	while curr_idx < len(color_regions):
		(ansi_escape,start_idx,end_idx) = color_regions[curr_idx]
		curr_str = curr_str[:start_idx] + ansi_escape + curr_str[start_idx:end_idx] + T_NORM + curr_str[end_idx:]
		disp1 = len(ansi_escape) 
		disp2 = len(T_NORM)
		for forw_idx in range(curr_idx,len(color_regions)):
			adjust_region(end_idx, disp2, color_regions, forw_idx)
			adjust_region(start_idx, disp1, color_regions, forw_idx)
		for forw_idx in range(0,len(display_regions)):
			adjust_region(end_idx, disp2, display_regions, forw_idx)
			adjust_region(start_idx, disp1, display_regions, forw_idx)
		curr_idx += 1

	if len(display_regions) > 0:
		display_str = ""
		prev_idx = 0
		for curr_idx in range(0,len(display_regions)):
			(_,start_idx,end_idx) = display_regions[curr_idx]
			if not only_spaces_between(curr_str,prev_idx,start_idx):
				display_str += "\n...\n"
			else:
				display_str += "\n"
			prev_idx = end_idx
			lead_idx = get_leading_tabs(curr_str, start_idx)
			display_str += curr_str[lead_idx:end_idx]
		if not prev_idx >= len(curr_str) - 1:
			display_str += "\n...\n"
	else:
		display_str = curr_str

	return display_str.strip('\n')

def adjust_region(ins_idx, disp, region, region_pos):
	(data, start_idx, end_idx) = region[region_pos]
	if ins_idx < start_idx:
		region[region_pos] = (data, start_idx+disp, end_idx+disp)
	elif ins_idx < end_idx:
		region[region_pos] = (data, start_idx, end_idx+disp)

def only_spaces_between(raw_str, start_idx, end_idx):
	spaces = " \n\t"
	for idx in range(start_idx,end_idx):
		if not (raw_str[idx] in spaces):
			return False
	return True

def get_leading_tabs(raw_str, idx):
	idx -= 1
	while idx >= 0:
		if raw_str[idx] != '\t':
			return idx + 1
		idx -= 1
	return 0

def unify_regions( regions ):
	new_region_idxs = {}
	for x in range(0,len(regions)):
		new_region_idxs[x] = True
	for x in range(0,len(regions)):
		(xd,xs,xe) = regions[x]
		for y in range(x+1,len(regions)):
			if new_region_idxs[y]:
				(yd,ys,ye) = regions[y]
				if xe >= ye:
					# Region x contains region y
					new_region_idxs[y] = False
				elif xe >= ys:
					# Region x overlaps with region y
					regions[x] = (xd,xs,ye)
					new_region_idxs[y] = False
	new_regions = []
	for idx in sorted(new_region_idxs.keys()):
		if new_region_idxs[idx]:
			new_regions.append( regions[idx] )
	return new_regions

s = "Ho ho ho ho ho\nThis is a-silly-test-test-crap!\nHo ho ho ho ho\nHo ho ho ho ho\nHah hah hah\nEnd"

def test(s=s):
	# s = "Ho ho ho ho ho\nThis is a-silly-test-test-crap!\nHo ho ho ho ho\nHo ho ho ho ho\nHah hah hah"
	rs = [(T_RED_FORE,77,80)
             ,(T_RED_FORE,25,30) 
             ,(T_GREEN_FORE,31,35)
             ,(T_CYAN_FORE,41,45)
             ,(T_BLUE_FORE,36,40)]
	ds = [(77,88),(15,46),(18,34),(80,92)]
	# print s[32:35]
	return format_str(s,rs,ds)

