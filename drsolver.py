from z3 import *
solver=Solver()
b = Int("b")
a = Int("a")
len = Int("len")
i = Int("i")
argv = Int("argv")
_ret_val_0 = Int("_ret_val_0")
argc = Int("argc")
i_drdVar_23 = Int("i_drdVar_23")
wr_arr_index_0 = Int("wr_arr_index_0")
wr_cond_0 = And (wr_arr_index_0 == (i_drdVar_23), ( i_drdVar_23  >= 0) , ( i_drdVar_23 <= len - 1 - 1), (i_drdVar_23 % 2 != 0))
i_drdVar_14 = Int("i_drdVar_14")
wr_arr_index_1 = Int("wr_arr_index_1")
wr_cond_1 = And (wr_arr_index_1 == (i_drdVar_14 + 1), ( i_drdVar_14  >= 0) , ( i_drdVar_14 <= len - 1 - 1), (i_drdVar_14 % 2 == 0))
waw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == wr_arr_index_1), wr_cond_1, (i_drdVar_23 != i_drdVar_14))
waws = Or(waw_cond_0)

i_drdVar_24 = Int("i_drdVar_24")
r_arr_index_0 = Int("r_arr_index_0")
r_cond_0 = And (r_arr_index_0 == (i_drdVar_24), ( i_drdVar_24  >= 0) , ( i_drdVar_24 <= len - 1 - 1), (i_drdVar_23 % 2 != 0))
i_drdVar_16 = Int("i_drdVar_16")
r_arr_index_1 = Int("r_arr_index_1")
r_cond_1 = And (r_arr_index_1 == (i_drdVar_16), ( i_drdVar_16  >= 0) , ( i_drdVar_16 <= len - 1 - 1), (i_drdVar_14 % 2 == 0))
i_drdVar_15 = Int("i_drdVar_15")
r_arr_index_2 = Int("r_arr_index_2")
r_cond_2 = And (r_arr_index_2 == (i_drdVar_15), ( i_drdVar_15  >= 0) , ( i_drdVar_15 <= len - 1 - 1), (i_drdVar_14 % 2 == 0))
raw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_2), r_cond_2, (i_drdVar_23 != i_drdVar_15))
raw_cond_1 = And( wr_cond_1, (wr_arr_index_1 == r_arr_index_2), r_cond_2, (i_drdVar_14 != i_drdVar_15))
raws = Or(raw_cond_1, raw_cond_0)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
