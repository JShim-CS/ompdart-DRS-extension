from z3 import *
solver=Solver()
argv = Int("argv")
argc = Int("argc")
read = Int("read")
idx = Int("idx")
index = Int("index")
j = Int("j")
i = Int("i")
b = Int("b")
arr = Int("arr")
a = Int("a")
size = Int("size")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
N = Int("N")
solver.add(N == 100)
wr_arr_index_0 = Int("wr_arr_index_0")
i_drdVar_13 = Int("i_drdVar_13")
solver.add((i_drdVar_13>=0),(i_drdVar_13<50))
wr_cond_0 = And (wr_arr_index_0 == (idx), (idx<0))
waws = False

raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
