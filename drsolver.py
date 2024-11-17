from z3 import *
solver=Solver()
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
wr_arr_index_0_0 = Int("wr_arr_index_0_0")
wr_arr_index_0_1 = Int("wr_arr_index_0_1")
wr_arr_index_0_2 = Int("wr_arr_index_0_2")
wr_arr_index_0_3 = Int("wr_arr_index_0_3")
i_drdVar_13 = Int("i_drdVar_13")
j_drdVar_13 = Int("j_drdVar_13")
k_drdVar_13 = Int("k_drdVar_13")
m_drdVar_13 = Int("m_drdVar_13")
solver.add((m_drdVar_13>=0),(m_drdVar_13<5))
solver.add((k_drdVar_13>=0),(k_drdVar_13<IMAX))
solver.add((j_drdVar_13>=0),(j_drdVar_13<IMAX))
solver.add((i_drdVar_13>=0),(i_drdVar_13<IMAX))
wr_cond_0_0 = And (wr_arr_index_0_0 == i_drdVar_13, True)
wr_cond_0_1 = And (wr_arr_index_0_1 == j_drdVar_13, True)
wr_cond_0_2 = And (wr_arr_index_0_2 == k_drdVar_13, True)
wr_cond_0_3 = And (wr_arr_index_0_3 == m_drdVar_13, True)
waws = False

raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
