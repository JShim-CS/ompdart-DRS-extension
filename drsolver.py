from z3 import *
solver=Solver()
b = Int("b")
a = Int("a")
DRD_RANDOM_VAR = Int("DRD_RANDOM_VAR")
waws = False

raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("seems like data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
