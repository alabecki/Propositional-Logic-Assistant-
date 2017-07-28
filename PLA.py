import sympy.abc
from sympy.logic.boolalg import Not, And, Or
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

from os import*

from PLA_functions import*


res = base()

file = res[0]
file_name = res[1]

file.seek(0)
propositions = obtain_atomic_formulas(file)
file.seek(0)


conjunction = conjoin(file)
print("Conjunction: %s " % (conjunction))


form = pre_cnf_to_cnf(conjunction, propositions)
print("Form: %s " % (form))


fset = cnf_to_set(form)
print("fset = %s" % (fset))

#fset = get_sat_input(conjunction, propositions)
#print("fset: %s " % (fset))


if resolution(fset, propositions):
	print("SAT")
else:
	print("UNSAT")







