from z3 import *
solver=Solver()
argv = Int("argv")
argc = Int("argc")
i = Int("i")
b = Int("b")
arr = Int("arr")
a = Int("a")
solver.add(a == 100)
size = Int("size")
solver.add(size == 100)
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
N = Int("N")
solver.add(N == 100)
wr_arr_index_0_0 = Int("wr_arr_index_0_0")
i_drdVar_7 = Int("i_drdVar_7")
solver.add((i_drdVar_7>=0),(i_drdVar_7<99))
i_drdVar_6 = Int("i_drdVar_6")
solver.add((i_drdVar_6>=0),(i_drdVar_6<99))
wr_cond_0_0 = And (wr_arr_index_0_0 == i_drdVar_6, (a==b))
waws = False

r_arr_index_0_0 = Int("r_arr_index_0_0")
r_cond_0_0 = And (r_arr_index_0_0 == i_drdVar_7 + 1, (a==b))
raw_cond_0= And( wr_cond_0_0, r_cond_0_0,
(wr_arr_index_0_0 == r_arr_index_0_0), (i_drdVar_6 != i_drdVar_7)
)
raws = Or(raw_cond_0)
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
