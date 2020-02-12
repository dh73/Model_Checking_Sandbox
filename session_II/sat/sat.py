#!/usr/bin/python
from z3 import *

square, circle, diamond, triangle = Ints('square circle diamond triangle')
s = Solver()
s.add(square+circle+diamond==200)
s.add(square*square+circle==150)
s.add(diamond-square+triangle==circle)
print (s.check())
print (s.model())
