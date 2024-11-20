from z3 import *
solver=Solver()
j = Int("j")
i = Int("i")
b = Int("b")
solver.add(b == 0)
arr = Int("arr")
a = Int("a")
solver.add(a == 100)
size = Int("size")
solver.add(size == 100)
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
N = Int("N")
solver.add(N == 100)
wr_arr_index_0_0 = Int("wr_arr_index_0_0")
i_drdVar_13 = Int("i_drdVar_13")
solver.add((i_drdVar_13>=0),(i_drdVar_13<10))
i_drdVar_12 = Int("i_drdVar_12")
solver.add((i_drdVar_12>=0),(i_drdVar_12<10))
i_drdVar_6 = Int("i_drdVar_6")
solver.add((i_drdVar_6>=0),(i_drdVar_6<10))
i_drdVar_5 = Int("i_drdVar_5")
solver.add((i_drdVar_5>=0),(i_drdVar_5<10))
wr_cond_0_0 = And (wr_arr_index_0_0 == i_drdVar_12 + 1, (b)!= 0)
wr_arr_index_1_0 = Int("wr_arr_index_1_0")
wr_cond_1_0 = And (wr_arr_index_1_0 == i_drdVar_5, (a)!= 0)
waw_cond_0 = And( wr_cond_0_0, wr_cond_1_0,
(wr_arr_index_0_0 == wr_arr_index_1_0))
waws = Or(waw_cond_0)

r_arr_index_0_0 = Int("r_arr_index_0_0")
r_cond_0_0 = And (r_arr_index_0_0 == i_drdVar_13 + 1, (b)!= 0)
r_arr_index_1_0 = Int("r_arr_index_1_0")
r_cond_1_0 = And (r_arr_index_1_0 == i_drdVar_6, (a)!= 0)
raw_cond_0= And( wr_cond_0_0, r_cond_0_0,
(wr_arr_index_0_0 == r_arr_index_0_0))
raw_cond_1= And( wr_cond_0_0, r_cond_1_0,
(wr_arr_index_0_0 == r_arr_index_1_0))
raw_cond_2= And( wr_cond_1_0, r_cond_0_0,
(wr_arr_index_1_0 == r_arr_index_0_0))
raw_cond_3= And( wr_cond_1_0, r_cond_1_0,
(wr_arr_index_1_0 == r_arr_index_1_0))
raws = Or(raw_cond_3, raw_cond_2, raw_cond_1, raw_cond_0)
solver.add(i_drdVar_13 != i_drdVar_12)
solver.add(i_drdVar_13 != i_drdVar_5)
solver.add(i_drdVar_12 != i_drdVar_6)
solver.add(i_drdVar_12 != i_drdVar_5)
solver.add(i_drdVar_6 != i_drdVar_5)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
