from z3 import *
solver=Solver()
b = Int("b")
a = Int("a")
len = Int("len")
i = Int("i")
argv = Int("argv")
_ret_val_0 = Int("_ret_val_0")
argc = Int("argc")
waws = False

raws = False
cstrnts = Or(waws,raws)
solver.add(cstrnts)
if solver.check() == z3.sat:
	print("data race(waw/raw/war) exists within the loop!")
else:
	print("seems like no data race exists (please double check)")
