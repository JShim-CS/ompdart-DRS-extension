from z3 import *
solver=Solver()
b = Int("b")
a = Int("a")
len = Int("len")
i = Int("i")
argv = Int("argv")
argc = Int("argc")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
i_drdVar_26 = Int("i_drdVar_26")
wr_arr_index_0 = Int("wr_arr_index_0")
wr_cond_0 = And (wr_arr_index_0 == (i_drdVar_26 + 1), ( i_drdVar_26  >= 0) , ( i_drdVar_26 <len-1), True)
waws = False

i_drdVar_28 = Int("i_drdVar_28")
r_arr_index_0 = Int("r_arr_index_0")
r_cond_0 = And (r_arr_index_0 == (i_drdVar_28), ( i_drdVar_28  >= 0) , ( i_drdVar_28 <len-1), True)
i_drdVar_27 = Int("i_drdVar_27")
r_arr_index_1 = Int("r_arr_index_1")
r_cond_1 = And (r_arr_index_1 == (i_drdVar_27), ( i_drdVar_27  >= 0) , ( i_drdVar_27 <len-1), True)
raw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_1), r_cond_1, (i_drdVar_26 != i_drdVar_27))
raws = Or(raw_cond_0)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
