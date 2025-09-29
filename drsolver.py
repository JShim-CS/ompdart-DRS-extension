from z3 import *
solver=Solver()
i = Int("i")
arr = Int("arr")
argv = Int("argv")
argc = Int("argc")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
wr_arr_index_0_0 = Int("wr_arr_index_0_0")
wr_arr_index__0_0 = Int("wr_arr_index__0_0")
i_drdVar_4 = Int("i_drdVar_4")
solver.add((i_drdVar_4>=0),(i_drdVar_4<200))
i_drdVar__4 = Int("i_drdVar__4")
solver.add((i_drdVar__4>=0),(i_drdVar__4<200))
solver.add(i_drdVar__4!=i_drdVar_4)
wr_cond_0_0 = And (wr_arr_index_0_0 == i_drdVar_4 % 20, True,wr_arr_index__0_0 == i_drdVar__4 % 20)
waw_cond_0 = And( wr_cond_0_0, wr_cond_0_0,
(wr_arr_index_0_0 == wr_arr_index__0_0))
waws = Or(waw_cond_0)

raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
