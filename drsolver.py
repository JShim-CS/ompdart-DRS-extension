from z3 import *
solver=Solver()
sum = Int("sum")
j = Int("j")
i = Int("i")
v_out = Int("v_out")
v = Int("v")
a = Int("a")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
N = Int("N")
solver.add(N == 100)
waws = False

r_arr_index_0_0 = Int("r_arr_index_0_0")
i_drdVar_10 = Int("i_drdVar_10")
j_drdVar_10 = Int("j_drdVar_10")
solver.add((j_drdVar_10>=0),(j_drdVar_10<N))
i_drdVar_9 = Int("i_drdVar_9")
j_drdVar_9 = Int("j_drdVar_9")
solver.add((j_drdVar_9>=0),(j_drdVar_9<N))
solver.add((i_drdVar_10>=0),(i_drdVar_10<N))
solver.add((i_drdVar_9>=0),(i_drdVar_9<N))
r_cond_0_0 = And (r_arr_index_0_0 == j_drdVar_10, True)
r_arr_index_1_0 = Int("r_arr_index_1_0")
r_arr_index_1_1 = Int("r_arr_index_1_1")
r_cond_1_0 = And (r_arr_index_1_0 == i_drdVar_9, True)
r_cond_1_1 = And (r_arr_index_1_1 == j_drdVar_9, True)
raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
