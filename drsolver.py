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
i_drdVar_15 = Int("i_drdVar_15")
wr_arr_index_0 = Int("wr_arr_index_0")
wr_cond_0 = And (wr_arr_index_0 == (j), ( i_drdVar_15  >= 0) , ( i_drdVar_15 < size), True)
waws = False

i_drdVar_16 = Int("i_drdVar_16")
r_arr_index_0 = Int("r_arr_index_0")
r_cond_0 = And (r_arr_index_0 == (i_drdVar_16), ( i_drdVar_16  >= 0) , ( i_drdVar_16 < size), True!= 0)
raw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_0), r_cond_0, (i_drdVar_15 != i_drdVar_16))
raws = Or(raw_cond_0)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
