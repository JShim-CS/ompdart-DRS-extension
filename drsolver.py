from z3 import *
solver=Solver()
i = Int("i")
j = Int("j")
histogram = Int("histogram")
histogramSize = Int("histogramSize")
solver.add(histogramSize == 200000000)
argv = Int("argv")
argc = Int("argc")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
wr_arr_index_0_0 = Int("wr_arr_index_0_0")
i_drdVar_31 = Int("i_drdVar_31")
solver.add((i_drdVar_31>=0),(i_drdVar_31<100))
i_drdVar_23 = Int("i_drdVar_23")
solver.add((i_drdVar_23>=0),(i_drdVar_23<100))
i_drdVar_14 = Int("i_drdVar_14")
solver.add((i_drdVar_14>=0),(i_drdVar_14<100))
i_drdVar_7 = Int("i_drdVar_7")
solver.add((i_drdVar_7>=0),(i_drdVar_7<100))
wr_cond_0_0 = And (wr_arr_index_0_0 == ((i_drdVar_31 - 1) * (i_drdVar_31 - 1) * (i_drdVar_31 + 2) * (i_drdVar_31 + 3)), (i_drdVar_31%13!=0),(i_drdVar_31%5!=0),((i_drdVar_31*i_drdVar_31*i_drdVar_31)%2!=0))
wr_arr_index_1_0 = Int("wr_arr_index_1_0")
wr_cond_1_0 = And (wr_arr_index_1_0 == ((i_drdVar_23 - 1) * (i_drdVar_23 - 1) * (i_drdVar_23 - 1) * (i_drdVar_23 - 1)), (i_drdVar_23%13==0),(i_drdVar_23%5!=0),((i_drdVar_23*i_drdVar_23*i_drdVar_23)%2!=0))
wr_arr_index_2_0 = Int("wr_arr_index_2_0")
wr_cond_2_0 = And (wr_arr_index_2_0 == ((i_drdVar_14 + 1) * (i_drdVar_14 + 1) * (i_drdVar_14 + 1) * (i_drdVar_14 + 1)), (i_drdVar_14%5==0),((i_drdVar_14*i_drdVar_14*i_drdVar_14)%2!=0))
wr_arr_index_3_0 = Int("wr_arr_index_3_0")
wr_cond_3_0 = And (wr_arr_index_3_0 == (i_drdVar_7 * i_drdVar_7 * i_drdVar_7), ((i_drdVar_7*i_drdVar_7*i_drdVar_7)%2==0))
waw_cond_0 = And( wr_cond_0_0, wr_cond_1_0,
(wr_arr_index_0_0 == wr_arr_index_1_0), (i_drdVar_31 != i_drdVar_23)
)
waw_cond_1 = And( wr_cond_0_0, wr_cond_2_0,
(wr_arr_index_0_0 == wr_arr_index_2_0), (i_drdVar_31 != i_drdVar_14)
)
waw_cond_2 = And( wr_cond_0_0, wr_cond_3_0,
(wr_arr_index_0_0 == wr_arr_index_3_0), (i_drdVar_31 != i_drdVar_7)
)
waw_cond_3 = And( wr_cond_1_0, wr_cond_2_0,
(wr_arr_index_1_0 == wr_arr_index_2_0), (i_drdVar_23 != i_drdVar_14)
)
waw_cond_4 = And( wr_cond_1_0, wr_cond_3_0,
(wr_arr_index_1_0 == wr_arr_index_3_0), (i_drdVar_23 != i_drdVar_7)
)
waw_cond_5 = And( wr_cond_2_0, wr_cond_3_0,
(wr_arr_index_2_0 == wr_arr_index_3_0), (i_drdVar_14 != i_drdVar_7)
)
waws = Or(waw_cond_5, waw_cond_4, waw_cond_3, waw_cond_2, waw_cond_1, waw_cond_0)

raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
