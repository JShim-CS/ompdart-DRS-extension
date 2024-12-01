from z3 import *
solver=Solver()
g = Int("g")
c = Int("c")
m = Int("m")
k = Int("k")
size = Int("size")
solver.add(size == 100)
array = Int("array")
a = Int("a")
arr = Int("arr")
b = Int("b")
i = Int("i")
j = Int("j")
index = Int("index")
temp = Int("temp")
argc = Int("argc")
rhs = Int("rhs")
argv = Int("argv")
u = Int("u")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
N = Int("N")
solver.add(N == 100)
wr_arr_index_0_0 = Int("wr_arr_index_0_0")
i_drdVar_10 = Int("i_drdVar_10")
solver.add((i_drdVar_10>=0),(i_drdVar_10<10))
i_drdVar_9 = Int("i_drdVar_9")
solver.add((i_drdVar_9>=0),(i_drdVar_9<10))
i_drdVar_5 = Int("i_drdVar_5")
solver.add((i_drdVar_5>=0),(i_drdVar_5<10))
i_drdVar_4 = Int("i_drdVar_4")
solver.add((i_drdVar_4>=0),(i_drdVar_4<10))
wr_cond_0_0 = And (wr_arr_index_0_0 == i_drdVar_9 + 2, True)
wr_arr_index_1_0 = Int("wr_arr_index_1_0")
wr_cond_1_0 = And (wr_arr_index_1_0 == i_drdVar_4, True)
waw_cond_0 = And( wr_cond_0_0, wr_cond_1_0,
(wr_arr_index_0_0 == wr_arr_index_1_0))
waws = Or(waw_cond_0)

r_arr_index_0_0 = Int("r_arr_index_0_0")
r_cond_0_0 = And (r_arr_index_0_0 == i_drdVar_10 * 3, True)
r_arr_index_1_0 = Int("r_arr_index_1_0")
r_cond_1_0 = And (r_arr_index_1_0 == i_drdVar_5 + 1, True)
raw_cond_0= And( wr_cond_0_0, r_cond_0_0,
(wr_arr_index_0_0 == r_arr_index_0_0))
raw_cond_1= And( wr_cond_0_0, r_cond_1_0,
(wr_arr_index_0_0 == r_arr_index_1_0))
raw_cond_2= And( wr_cond_1_0, r_cond_0_0,
(wr_arr_index_1_0 == r_arr_index_0_0))
raw_cond_3= And( wr_cond_1_0, r_cond_1_0,
(wr_arr_index_1_0 == r_arr_index_1_0))
raws = Or(raw_cond_3, raw_cond_2, raw_cond_1, raw_cond_0)
finalCond0 = And(i_drdVar_10 != i_drdVar_9, True)
finalCond1 = And(i_drdVar_10 != i_drdVar_4, True)
finalCond2 = And(i_drdVar_9 != i_drdVar_5, True)
finalCond3 = And(i_drdVar_9 != i_drdVar_4, True)
finalCond4 = And(i_drdVar_5 != i_drdVar_4, True)
myfinalcond = Or(finalCond0
, finalCond1
, finalCond2
, finalCond3
, finalCond4
)
cstrnts = Or(waws,raws,myfinalcond)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
