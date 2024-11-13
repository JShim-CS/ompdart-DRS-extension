from z3 import *
solver=Solver()
argv = Int("argv")
argc = Int("argc")
temp = Int("temp")
index = Int("index")
j = Int("j")
i = Int("i")
b = Int("b")
arr = Int("arr")
a = Int("a")
array = Int("array")
size = Int("size")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
N = Int("N")
solver.add(N == 100)
wr_arr_index_0 = Int("wr_arr_index_0")
j_drdVar_8 = Int("j_drdVar_8")
i_drdVar_8 = Int("i_drdVar_8")
solver.add((i_drdVar_8>=0),(i_drdVar_8<100))
solver.add((j_drdVar_8>=0),(j_drdVar_8<200))
wr_cond_0 = And (wr_arr_index_0 == (j_drdVar_8 + 1), True)
waws = False

raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
