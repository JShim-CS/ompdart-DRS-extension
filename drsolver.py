from z3 import *
solver=Solver()
argv = Int("argv")
argc = Int("argc")
i = Int("i")
arr = Int("arr")
array = Int("array")
size = Int("size")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
N = Int("N")
solver.add(N == 100)
wr_arr_index_0 = Int("wr_arr_index_0")
i_drdVar_22 = Int("i_drdVar_22")
solver.add((i_drdVar_22>=0),(i_drdVar_22<size-1))
i_drdVar_17 = Int("i_drdVar_17")
solver.add((i_drdVar_17>=0),(i_drdVar_17<size-1))
i_drdVar_16 = Int("i_drdVar_16")
solver.add((i_drdVar_16>=0),(i_drdVar_16<size-1))
i_drdVar_12 = Int("i_drdVar_12")
solver.add((i_drdVar_12>=0),(i_drdVar_12<size-1))
i_drdVar_11 = Int("i_drdVar_11")
solver.add((i_drdVar_11>=0),(i_drdVar_11<size-1))
wr_cond_0 = And (wr_arr_index_0 == (i_drdVar_22 + 1), (i_drdVar_22==0))
wr_arr_index_1 = Int("wr_arr_index_1")
wr_cond_1 = And (wr_arr_index_1 == (i_drdVar_16), (i_drdVar_16!=0))
wr_arr_index_2 = Int("wr_arr_index_2")
wr_cond_2 = And (wr_arr_index_2 == (i_drdVar_11), (i_drdVar_11!=0))
waw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == wr_arr_index_1), wr_cond_1)
waw_cond_1 = And( wr_cond_0, (wr_arr_index_0 == wr_arr_index_2), wr_cond_2)
waw_cond_2 = And( wr_cond_1, (wr_arr_index_1 == wr_arr_index_2), wr_cond_2)
waws = Or(waw_cond_2, waw_cond_1, waw_cond_0)

r_arr_index_0 = Int("r_arr_index_0")
r_cond_0 = And (r_arr_index_0 == (i_drdVar_17 + 2), (i_drdVar_16!=0))
r_arr_index_1 = Int("r_arr_index_1")
r_cond_1 = And (r_arr_index_1 == (i_drdVar_12 + 3), (i_drdVar_11!=0))
raw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_0), r_cond_0)
raw_cond_1 = And( wr_cond_0, (wr_arr_index_0 == r_arr_index_1), r_cond_1)
raw_cond_2 = And( wr_cond_1, (wr_arr_index_1 == r_arr_index_0), r_cond_0)
raw_cond_3 = And( wr_cond_1, (wr_arr_index_1 == r_arr_index_1), r_cond_1)
raw_cond_4 = And( wr_cond_2, (wr_arr_index_2 == r_arr_index_0), r_cond_0)
raw_cond_5 = And( wr_cond_2, (wr_arr_index_2 == r_arr_index_1), r_cond_1)
raws = Or(raw_cond_5, raw_cond_3, raw_cond_2, raw_cond_1, raw_cond_4, raw_cond_0)
solver.add(i_drdVar_22 != i_drdVar_17)
solver.add(i_drdVar_22 != i_drdVar_16)
solver.add(i_drdVar_22 != i_drdVar_12)
solver.add(i_drdVar_22 != i_drdVar_11)
solver.add(i_drdVar_17 != i_drdVar_16)
solver.add(i_drdVar_17 != i_drdVar_11)
solver.add(i_drdVar_16 != i_drdVar_12)
solver.add(i_drdVar_16 != i_drdVar_11)
solver.add(i_drdVar_12 != i_drdVar_11)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
