from z3 import *
solver=Solver()
b = Int("b")
a = Int("a")
len = Int("len")
i = Int("i")
argv = Int("argv")
_ret_val_0 = Int("_ret_val_0")
argc = Int("argc")
i_drdVar_11 = Int("i_drdVar_11")
wr_arr_index_0 = Int("wr_arr_index_0")
wr_cond_0 = And (wr_arr_index_0 == (i_drdVar_11 + 1), ( i_drdVar_11  >= 0) , ( i_drdVar_11 <= len - 1 - 1), True)
waws = False

i_drdVar_13 = Int("i_drdVar_13")
r_arr_index_0 = Int("r_arr_index_0")
r_cond_0 = And (r_arr_index_0 == (i_drdVar_13), ( i_drdVar_13  >= 0) , ( i_drdVar_13 <= len - 1 - 1), True)
i_drdVar_12 = Int("i_drdVar_12")
r_arr_index_1 = Int("r_arr_index_1")
r_cond_1 = And (r_arr_index_1 == (i_drdVar_12), ( i_drdVar_12  >= 0) , ( i_drdVar_12 <= len - 1 - 1), True)
raw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_1), r_cond_1, (i_drdVar_11 != i_drdVar_12))
raws = Or(raw_cond_0)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
