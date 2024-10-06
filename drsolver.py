from z3 import *
solver=Solver()
i_drdVar_14 = Int("i_drdVar_14")
wr_arr_index_0 = Int("wr_arr_index_0")
wr_cond_0 = And (wr_arr_index_0 == (i_drdVar_14 + 10000), ( i_drdVar_14  >= 0) , ( i_drdVar_14 < 1000), True)
i_drdVar_11 = Int("i_drdVar_11")
wr_arr_index_1 = Int("wr_arr_index_1")
wr_cond_1 = And (wr_arr_index_1 == (i_drdVar_11 + 2), ( i_drdVar_11  >= 0) , ( i_drdVar_11 < 1000), True)
waw_cond_0 = And( wr_cond_0, (wr_arr_index_0 == wr_arr_index_1), wr_cond_1, (i_drdVar_14 != i_drdVar_11))
waws = Or(waw_cond_0)
solver.add(waws)
if solver.check() == z3.sat:
	print("data race(waw) exists within the loop!")
