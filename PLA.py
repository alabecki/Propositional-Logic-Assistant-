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
from sys import*
from copy import deepcopy

from os import*

from PLA_functions import*


commands = {
	"1": "Convert the KB to Conjunctive Normal Form (CNF)",
	"2": "Make Resolution Refutation Query with Respect to the KB",
	"3": "Get set of Models that satisfy the KB",
	"4": "Get the set of Models that satisfy a query given KB",
	"5": "Return"
}

res = {
	"1": "Just tell me if the query is a consequence of the KB ",
	"2": "Print all Resolution Steps",
	"3": "Print only Resolution Steps used in a sucessful refutation"
}



while True:

	res = base()

	file = res[0]
	file_name = res[1]

	file.seek(0)
	print("Formulas in KB:")
	print("_________________________________________________________________________________\n")
	for f in file:
		print (f)

	file.seek(0)
	propositions = obtain_atomic_formulas(file)
	print("Propositions:")
	for p in propositions:
		print(p)
	file.seek(0)


	conjunction = conjoin(file)
	print("Conjunction: %s " % (conjunction))


	form = pre_cnf_to_cnf(conjunction, propositions)
	print("Form: %s " % (form))


	fset = cnf_to_set(form)
	print("fset = %s" % (fset))

	file.close()

	#fset = get_sat_input(conjunction, propositions)
	#print("fset: %s " % (fset))
	while True:
		com = ""
		while com not in commands.keys():
			print("\n")
			print("What would you like to do?")
			for c, cmd in commands.items():
				print(c, cmd)
			com = input()

		if com == "1":
			print("The given set of formulas in CNF:\n")
			print(form)
			print("\n")

		if com == "2":
			proof = dict()
			step = 1
			step_tracker = dict()
			for c in fset:
				proof[str(step)] = str(c) + "    Given"
				step_tracker[str(c)] = str(step)
				step += 1

			print("Please input a query \n")
			query = input()
			mfset = add_query(query, propositions, fset, proof, step_tracker)
			
			if resolution(mfset, propositions, proof, step_tracker):
				print("\n")
				print("%s is not entailed by the KB \n" % (query))
			else:
				print("\n")
				print("%s is entailed by the KB \n" % (query))

				print("Proof:")
				for k, v in proof.items():
					print(k, v)


		if com == "3":

			
			models = satisfiable(conjunction, all_models = True)
			models = list(models)
			if models[0] == False:
				print("The KB is not satisifed by any model\n")
			else:
				print("The KB is satisfied by the following models: \n")
				for m in models:
					print(m)



		if com == "5":
			break





