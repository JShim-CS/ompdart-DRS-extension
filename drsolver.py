from z3 import *
solver=Solver()
argv = Int("argv")
threshold = Int("threshold")
i = Int("i")
array = Int("array")
size = Int("size")
argc = Int("argc")
flag = Int("flag")
nrows = Int("nrows")
j = Int("j")
rowstr = Int("rowstr")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
i_drdVar_25 = Int("i_drdVar_25")
wr_arr_index_0 = Int("wr_arr_index_0")
wr_cond_0 = And (wr_arr_index_0 == (0), ( i_drdVar_25  >= 0) , ( i_drdVar_25 < size), (flag)!= 0)
i_drdVar_20 = Int("i_drdVar_20")
wr_arr_index_1 = Int("wr_arr_index_1")
wr_cond_1 = And (wr_arr_index_1 == (i_drdVar_20), ( i_drdVar_20  >= 0) , ( i_drdVar_20 < size), (flag)!= 0)
waw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == wr_arr_index_1), wr_cond_1, (i_drdVar_25 != i_drdVar_20))
waws = Or(waw_cond_0)

i_drdVar_26 = Int("i_drdVar_26")
r_arr_index_0 = Int("r_arr_index_0")
r_cond_0 = And (r_arr_index_0 == (i_drdVar_26), ( i_drdVar_26  >= 0) , ( i_drdVar_26 < size), (flag)!= 0)
i_drdVar_21 = Int("i_drdVar_21")
r_arr_index_1 = Int("r_arr_index_1")
r_cond_1 = And (r_arr_index_1 == (0), ( i_drdVar_21  >= 0) , ( i_drdVar_21 < size), (flag)!= 0)
raw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_0), r_cond_0, (i_drdVar_25 != i_drdVar_26))
raw_cond_1 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_1), r_cond_1, (i_drdVar_25 != i_drdVar_21))
raw_cond_2 = And( wr_cond_1, (wr_arr_index_1 == r_arr_index_0), r_cond_0, (i_drdVar_20 != i_drdVar_26))
raw_cond_3 = And( wr_cond_1, (wr_arr_index_1 == r_arr_index_1), r_cond_1, (i_drdVar_20 != i_drdVar_21))
raws = Or(raw_cond_3, raw_cond_2, raw_cond_1, raw_cond_0)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
