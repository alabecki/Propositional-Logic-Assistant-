import sympy.abc
from sympy.logic.boolalg import Not, And, Or
from sympy.logic import simplify_logic

from sympy import*
from sympy.logic.inference import satisfiable, valid
from sympy.logic.boolalg import to_cnf
from mpmath import*
import mpmath
from itertools import product
from itertools import*
import pprint
import re
from copy import deepcopy

from PLA_functions import*

_input = {"(~(a & b))", "(a|b)", "a", "b" }


a, b, c, d, p, q, r = symbols("a, b, c, d, p, q, r")

props = {a, b, c, d}

form1 = (~(a & d) | (b & c))
form2 = a|b|d

res = And(form1, form2)

res = to_cnf(res)
print (res)


regular = pre_cnf_to_cnf(res, props)
print(regular)


flist = build_formula_list(_input)
print("f list")
for f in flist:
	print(f)


basis = build_res_set(flist, props)
print("f set")
for s in basis:
	for e in s:
		print(e, end = " ")
	print("\n")


#attempt = resolution(basis, props)
#print(attempt)


var1 = "~(p & ~ q) | ~(~a & ~t)"
print("var1 to cnf: %s" % (to_cnf(var1)))
var1 = "r & (p | q)"
print("var1 simp: %s" % (simplify_logic(var1)))


var2 = "~u | (t | (~s & p))"
print("var1 to cnf: %s" % (to_cnf(var2)))
var2 = "~p | (q & r)"
print("var1 simp: %s" % (simplify_logic(var2)))


if a|b == b|a:
	print("yes they are!")

