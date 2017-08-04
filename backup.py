def resolution(flist, propositions):		#takes a list of disjunctions (sets of literals) as input
	#worlds = construct_worlds(propositions)
	flag = True
	stage = 0
	stages = dict()
	current = deepcopy(flist)
	neg = flist[-1]
	new = "stage" + str(stage)
	stages[new] = current
	props = deepcopy(propositions)

	if all_literals(current):
		return True  
	if contains_empty(current):
		return False
	for item in current:
		if item in propositions:
			for other in current:
				if item in other and other != item:
					current.remove(other)
				if "~" + item in other:
					other.discard("~" + item)
				
		if "~" + item in propositions:
			for other in current:
				if "~" + item in other and other != item:
					current.remove(other)
				if item in other:
					other.discard(item)
			

	current_shadow = deepcopy(current)
	for member in neg:
		if member in propositions:
			res = set()
			if member.startswith("~"):
				for other in current:
					if member in other:
						res = (neg | other) - (set(member) | set(comp))
						print("Other: %s" % (other))
						pprint("CS: %s" % (current_shadow))
						try:
							current_shadow.remove(other)
						except ValueError:
							pass	
						current_shadow.append(res)
			else:
				for other in current:
					comp = "~" + member
					if comp in other:
						res = (neg | other) - (set(member) | set(comp))
						print("Other: %s" % (other))
						pprint("CS: %s" % (current_shadow))
						try:
							current_shadow.remove(other)
						except ValueError:
							pass
						current_shadow.append(res)
	current = deepcopy(current_shadow)
	print("Current")
	for c in current:
		for i in c:
			print(i)
	stage += 1
	new = "stage" + str(stage)
	stages[new] = current

	
	def pre_cnf_to_cnf(formula, propositions):
	temp = to_cnf(formula)
	temp = str(temp)
	print("temp: %s" % (temp))
	if temp.startswith("And"):
		temp = temp.replace("And", "")
		temp = temp[1:]
		temp = temp[:-1]
	print(temp)
	temp = tem.replace("Or", "")
	temp = temp.split(",")
	result = ""
	for t in temp:
		print("temp %s" % (temp))
		for p in propositions:
			if "Not(" + str(p) + ")" in t:
				bef = "Not(" + str(p) + ")"
				aft = "~" + str(p)
				t = t.replace(bef, aft)
				print("t: %s " % (t))
		t = t.strip()
		if t.endswith(","):
			t = t[:-1]
		t = t.replace(",", " |")
		if result == "":
			result = t
		else:
			result = result + " & " + t 
	return(result)


def conjoin(formulas):		
	#print(formulas)
	AAA = Symbol("AAA")
	conjunction = AAA
	for f in formulas:
		f = f.lstrip()
		if f.startswith("#"):
			continue
		if len(f) >= 1:
			if f[0].isdigit():
				#f = f.lstrip()
				g = ''.join([i for i in f if not i.isdigit()])
				#print(g)
				g = g.lstrip()
				g = g.rstrip()
				#print("Before -> replace: %s" % (g))
				g = g.replace("->", ">>")
				#print("After -> replace: %s" % (g))
				g = to_cnf(g)
				#print("Afrer to_cnf: %s " % (g)) 
				#print("%s to CNF: %s" % (f, g)) 
				conjunction = And(conjunction, g)
	conjunction = str(conjunction)
	conjunction = conjunction.replace("AAA,", "")
	conjunction = to_cnf(conjunction)
	return conjunction


def resolution(clauses, propositions, proof, step_tracker):
	step = len(proof.keys()) + 1
	print("\n")
	print("Beginning Resolution Refutation:")
	print("________________________________")
	props = deepcopy(propositions)
	while True:
		print("Clauses at start of the round:")
		for c in clauses:
			print(c)
		if find_empty(clauses):
			print("Empty clause found: %s" % ())
			return False
		if all_literals(clauses):
			print("All remaining clauses are literals")

			if literal_consistancy(clauses, propositions):
				print("The set of literals is consistant")

				return True
		clauses = eliminate_tautologies(clauses, props, 0)
		clauses = eliminate_supersets(clauses, 0)
		clauses = eliminate_unipolar(clauses, props, 0)
		if len(clauses) == 0:
			return True
		print("Clauses after preliminaries:")
		for c in clauses:
			print(c)
		unit_clauses = []
		for c in clauses:
			if len(c) == 1:
				for i in c:
					unit_clauses.append(i)
		print("Now onto employment of the Resolution Rule:")
		if len(unit_clauses) > 0:
			print("It is preferble to begin with unit clauses")
			print("List of unit clauses:")
		for uc in unit_clauses:
			print(uc)
			print("\n")
		while unit_clauses:
			a = choice(unit_clauses)
			print("%s is chosen \n" % (a))
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 0):
				unit_clauses.remove(a)
			else:
				return False
		if props:
			print("There are currently no unit clauses from which to choose")
			print("and some propositions remain \n")
			a = choice(list(props))
			res = resolve(a, clauses, props, proof, step_tracker, 0)
			if res == False:
				return False
			print("Clauses at end of loop:")
			for c in clauses:
				print(c)
		else:
			return True




def resolution_no_diagonsis(clauses, propositions, proof, step_tracker):
	step = len(proof.keys()) + 1
	
	props = deepcopy(propositions)
	while True:
		if find_empty(clauses):
			return False
		if all_literals(clauses):
			if literal_consistancy(clauses, propositions):
				return True
			#else:
			#	return False
		clauses = eliminate_tautologies(clauses, props, 0)
		clauses = eliminate_supersets(clauses, 0)
		clauses = eliminate_unipolar(clauses, props, 0)
		if len(clauses) == 0:
			return True
		
		unit_clauses = []
		for c in clauses:
			if len(c) == 1:
				#print("%s has len 1" % (c))
				for i in c:
					unit_clauses.append(i)
					
		while unit_clauses:
			a = choice(unit_clauses)
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 0):
				unit_clauses.remove(a)
			else:
				return False
		if props:
			a = choice(list(props))
			res = resolve(a, clauses, props, proof, step_tracker, 0)
			if res == False:
				return False
		else:
			return True


def update_unit_clauses:
	for c in clauses:
		if len(c) == 1:
			for i in c:
				unit_clauses.append(i)


while True:
	if negated_units > 0:
		a = choice(negated_unit)
		print("%s is both a unit clause and occurs in the negated conclusion, so it is an ideal choice:" % (a))
		if str(a).startswith("~"):
			negs = count_negations(a)
			if negs % 2 == 0:
				a = str(a).strip("~")
			else:
				a = str(a).strip("~")
				a = "~" + str(a) 
		if resolve(a, clauses, props, proof, step_tracker, 1):
			negated_unit.remove(a)
			if a in negated_conclusion:
				negated_conclusion.remove(a)
			unit_clauses = update_unit_clauses(clauses)
		else:
			return False
	elif unit_clauses > 0:
		a = choice(unit_clauses)
		print("%s is chosen \n" % (a))
		if str(a).startswith("~"):
			negs = count_negations(a)
			if negs % 2 == 0:
				a = str(a).strip("~")
			else:
				a = str(a).strip("~")
				a = "~" + str(a) 
		if resolve(a, clauses, props, proof, step_tracker, 1):
			unit_clauses = update_unit_clauses(clauses)

		else:
			return False

	elif negated_conclusion > 0:
		a = choice(negated_conclusion)
		print("%s is chosen because it is found in the negation of the conclusion" % (a))
		if str(a).startswith("~"):
			negs = count_negations(a)
			if negs % 2 == 0:
				a = str(a).strip("~")
			else:
				a = str(a).strip("~")
				a = "~" + str(a) 
		if resolve(a, clauses, props, proof, step_tracker, 1):
			negated_conclusion.remove(a)
			unit_clauses = update_unit_clauses(clauses)
		else:
			return False

	elif props > 0:
		a = choice(list(props))
		print("%s is chosen" % (a))
		res = resolve(a, clauses, props, proof, step_tracker, 1)
		unit_clauses = update_unit_clauses(clauses)
		if res == False:
			return False
	else:
		return True



def resolution(clauses, propositions, proof, step_tracker):
	step = len(proof.keys()) + 1
	print("\n")
	print("################################\n")
	print("Beginning Resolution Refutation:")
	print("################################")
	props = deepcopy(propositions)
	negated_conclusion = []
	for k, v in proof.items():
		#print(v[1])
		if v[1] == "Negated Conclusion":
			for p in propositions:
				if "~" + str(p) in str(v[0]):
					negated_conclusion.append("~" + str(p))
				elif str(p) in str(v[0]):
					negated_conclusion.append(str(p))

	print("Negated Conclusion Items")
	for nc in negated_conclusion:
		print(nc)
	while True:
		num_clauses = len(clauses)
		print("Clauses at start of the round:")
		for c in clauses:
			print(c)
		if find_empty(clauses):
			print("Empty clause found: %s" % ())
			return False
		if all_literals(clauses):
			print("All remaining clauses are literals")

			if literal_consistancy(clauses, propositions):
				print("The set of literals is consistant")

				return True
		clauses = eliminate_tautologies(clauses, props, 1)
		clauses = eliminate_supersets(clauses, 1)
		clauses = eliminate_unipolar(clauses, props, 1)
		if len(clauses) == 0:
			return True
		if len(clauses) < num_clauses:
			print("Clauses after preliminaries:")
			for c in clauses:
				print(c)
		
		
		unit_clauses = update_unit_clauses(clauses)
		print("Unit Clauses:")
		for uc in unit_clauses:
			print(uc)

		print("Employment of the Resolution Rule:")

		#negated_unit = [list(filter(lambda x: x in negated_conclusion, sublist)) for sublist in unit_clauses]
		#negated_unit = set(negated_conclusion).intersection(set(unit_clauses))
		negated_unit = []
		for nc in negated_conclusion:
			#print("nc: %s" % (nc))
			for uc in unit_clauses:
				#print("uc: %s" % (uc))
				if nc == uc:
					negated_unit.append(nc)
		print("Negated Units:")
		for nu in negated_unit:
			print(nu)
		while len(negated_unit) > 0:
			a = choice(negated_unit)
			print("%s is both a unit clause and occurs in the negated conclusion, so it is an ideal choice:" % (a))
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 1):
				negated_unit.remove(a)
				if a in negated_conclusion:
					negated_conclusion.remove(a)
				unit_clauses = update_unit_clauses(clauses)
			else:
				return False

		if len(unit_clauses) > 0:
			print("List of unit clauses:")
			for uc in unit_clauses:
				print(uc)
		#print("\n")
		while len(unit_clauses) > 0:
			a = choice(unit_clauses)
			print("%s is chosen \n" % (a))
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 1):
				unit_clauses.remove(a)
				unit_clauses = update_unit_clauses(clauses)

			else:
				return False


		if props:
			print("There are currently no unit clauses from which to choose")

			while negated_conclusion:
				a = choice(negated_conclusion)
				print("%s is chosen because it is found in the negation of the conclusion" % (a))
				if str(a).startswith("~"):
					negs = count_negations(a)
					if negs % 2 == 0:
						a = str(a).strip("~")
					else:
						a = str(a).strip("~")
						a = "~" + str(a) 
				if resolve(a, clauses, props, proof, step_tracker, 1):
					negated_conclusion.remove(a)
					unit_clauses = update_unit_clauses(clauses)
				else:
					return False
			print("Remaining Propositions:")
			for p in props:
				print(p)
			a = choice(list(props))
			print("%s is chosen" % (a))
			res = resolve(a, clauses, props, proof, step_tracker, 1)
			unit_clauses = update_unit_clauses(clauses)
			if res == False:
				return False
		else:
			return True


def resolution_no_diagonsis(clauses, propositions, proof, step_tracker):
	step = len(proof.keys()) + 1
	props = deepcopy(propositions)
	while True:
		if find_empty(clauses):
			return False
		if all_literals(clauses):
			if literal_consistancy(clauses, propositions):
				return True
		clauses = eliminate_tautologies(clauses, props, 0)
		clauses = eliminate_supersets(clauses, 0)
		clauses = eliminate_unipolar(clauses, props, 0)
		if len(clauses) == 0:
			return True
		
		unit_clauses = []
		for c in clauses:
			if len(c) == 1:
				#print("%s has len 1" % (c))
				for i in c:
					unit_clauses.append(i)			
		while unit_clauses:
			a = choice(unit_clauses)
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs % 2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props, proof, step_tracker, 0):
				unit_clauses.remove(a)
			else:
				return False
		if props:
			a = choice(list(props))
			res = resolve(a, clauses, props, proof, step_tracker, 0)
			if res == False:
				return False
		else:
			return True