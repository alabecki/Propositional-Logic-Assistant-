import sympy.abc
from sympy.logic.boolalg import Not, And, Or, Implies
from sympy.logic import simplify_logic
from sympy import*
from sympy.logic.inference import satisfiable, valid
from sympy.logic.boolalg import to_cnf, to_dnf
from mpmath import*
import mpmath
from itertools import product
from itertools import*
import pprint
import re
from pprint import*
from copy import deepcopy
import os
from random import choice 
import sys



def base():
	do = ""
	res = []
	while len(res) == 0:
		print("\n")
		print("What would you like to do? \n")
		do = input("1: Open a file, 2: Exit program\n")
		if(do == "2"):
			sys.exit()
		if(do == "1"):
			print("Please input the name of a text-file containing a set of rules ")
			print("(or press 'r' to return) \n")
			name = input()
			if name != "r":
				res = get_file(name)
				if res == []:
					continue
				#print(type(res))
				return res


def get_file(name):
	while True:
		if name.endswith(".txt") == False:
			name = name + ".txt"
		if(os.path.exists(name)):
			_file = open(name, "r+")
			print("\n")
			print("Name of file: %s " % (name))
			res = [_file, name]
			return res
		else:
			print("The file you selected does not exist, please try again")
			print("(Or press 'r' to return) \n ")
			name = input()
			if name == 'r':
				res = []
				return res

def get_atoms(formula):
	for ch in formula:
		ch = Symbol(ch)
	formula = Symbol(formula)
	return formula.atoms()


def obtain_atomic_formulas(file):
	propositions = set()
	for f in file:
		f = f.lstrip()
		if f.startswith("#"):
			continue
		if len(f) >= 1:
			if f[0].isdigit():
				#f = f.lstrip()
				g = ''.join([i for i in f if not i.isdigit()])
				g = g.replace("~", "")
				g = g.replace("&", ",")
				g = g.replace("|", ",")
				g = g.replace("(", "")
				g = g.replace(")", "")
				g = g.replace("<->", ",")
				g = g.replace("->", ",")
				g = g.replace("!", "")
				g = g.replace("TRUE", "")
				g = g.replace("FALSE", "")
				g = g.strip()
				new_props = g.split(",")
				new_props = list(filter(None, new_props))
				for prop in new_props:
					if prop == "":
						continue
					prop = prop.strip() 
					new = Symbol(prop)
					propositions.add(new)
				#propositions.add(_new)
	return propositions


def is_literal(formula):
	temp = str(formula)
	for ch in temp:
		if ch == "|" or ch == "&":
			return False
	return True

def all_literals(formulas):
	for f in formulas:
		if len(f) != 1:
			return False
	print("All remaining clauses are literals")
	return True

def contains_empty(formulas):
	for f  in formulas:
		if len(f) == 0:
			return True
	return False 

def set_to_formulas(fset):
	temp = str(fset)
	temp = temp.replace("{", "")
	temp = temp.replace("}", "")
	temp = temp.replace(",", "&")
	for ch in temp:
		ch = Symbol(ch)
	return temp


def matched(st, start):
	end_pos = start
	count = 0
	st = st[start:]
	for i in st:
		#print(i)
		#print("Count: %s " % (count))
		#print (end_pos)
		if i == "(":
			count += 1
		if i == ")":
			count -= 1
		if count == 0:
		#	print("RETURN_________________________________________-")
			return end_pos
		end_pos += 1
	return 0

def get_sat_input(formula, propositions):
	print("Initial formula : %s" % (formula))
	result = []
	t1 = formula.split("&")
	shadow = deepcopy(t1)
	for t2 in t1:
		print("t2 %s" % (t2))
		if t2.startswith("And"):
			t2 = pre_cnf_to_cnf(t2, propositions)
			print("t2 after: %s" % (t2))
			for t3 in t2:
				shadow.append(t3)

		for p in propositions:
			if "Not(" + str(p) + ")" in t2:
				bef = "Not(" + str(p) + ")"
				aft = "~" + str(p)
				t2 = t2.replace(bef, aft)
		t2 = t2.replace("(", "")
		t2 = t2.replace(")", "")
	
		for t3 in t2:
			print
			t3 = t3.strip()
			t3 = t3.split(",")
			add = set()
			for i in t3:
				i = i.strip()
				add.add(i)
		result.append(add)
	print(len(result))
	return result



def pre_cnf_to_cnf(formula, propositions):
	temp = to_cnf(formula)
	temp = str(temp)
	print("temp: %s" % (temp))
	if temp.startswith("And"):
		temp = temp.replace("And", "")
		temp = temp[1:]
		temp = temp[:-1]
	print(temp)
	temp = temp.split("Or")
	result = ""
	check = []
	for t in temp:
		print("t %s" % (t))
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
		if t == "" or t == " ":
			continue
		t = re.split(r'\|\s*(?![^()]*\))', t)
		for item in t:
			flag = True
			for prop in propositions:
				if "~" + str(p) in item:
					if "(" + str(p) in item or " " + str(p) in item or "|"+str(p) in item:
						flag = False
			print (flag)
			if flag == False:
				continue
			if item not in check:
				result = result + " & " + item
				print("add item: %s" % (item))
				check.append(item)
	result = result.replace("&", "", 1)
	return(result)

def cnf_to_set(formula):
	result = []
	formula = formula.replace("(", "")
	formula = formula.replace(")", "")
	#formula = formula.replace("&", "")
	formula = formula.split("&")
	for f in formula:
		addition = set()
		print("Item: %s " % (f))
		f = str(f)
		if "|" not in f:
			f = f.strip()
			addition.add(f)
		else:
			f = f.split("|")
			for i in f:
				print(i)
				i = i.strip()
				addition.add(i)
		if addition not in result:
			result.append(addition)
	return result

	

def build_formula_list(file):
	lines = []
	for line in file:
		line = line.strip()
		#if line.startswith("("):
		line = re.sub(r'\s+', '', line)
		lines.append(line.strip())
	return lines

def build_res_set(flist, props):
	basis = list()
	for f in flist:
		for ch in f:
			ch = Symbol(ch)
		f = to_cnf(f)
		print("to cnf: %s __________________________________________---" % (f))
		res = pre_cnf_to_cnf(f, props)
		res = res.replace("(", "")
		res = res.replace(")", "")
		res = res.split("|")
		items = set()
		for r in res:
			r = r.strip()
			#print(r)
			items.add(r)
		basis.append(items)
		#print("Basis %s" % (basis))
	return basis


def conjoin(formulas):			#need to create a new function to add query
	print(formulas)
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
				print(g)
				g = g.lstrip()
				g = g.rstrip()
				print("WTF?")
				print(g)
				#g = str(g)

				g = g.replace("->", ">>")

				#while "<->" in g:
			#		g = re.split(r'<->\s*(?![^()]*\))', g)
			#		g = "(~" + g[0] + " | " + g[1] + ") & (~" + g[1] + " | " + g[0] + ")"
			#	while "->" in g:
			#		g = re.split(r'->\s*(?![^()]*\))', g)
			#		print("g[0]: %s" % (g[0]))
			#		print("g[1]: %s " % (g[1]))
			#		g[0] = "~(" + g[0] + ")"
			#		g = g[0] + " | " + g[1]
				
				print(g)  
				g = to_cnf(g)
				print(g)  


				conjunction = And(conjunction, g)
	conjunction = str(conjunction)
	conjunction = conjunction.replace("AAA,", "")
	conjunction = to_cnf(conjunction)
	return conjunction

def eliminate_supersets(clauses):
	shadow = deepcopy(clauses)
	for i in clauses:
		for j in clauses:
			if i.issubset(j) and i != j:
				if j in shadow:
					print("%s is eliminated because it is a superset of %s " % (j, i))
					shadow.remove(j)
	return shadow

def eliminate_unipolar(clauses, propositions):
	shadow = deepcopy(clauses)
	props = deepcopy(propositions)
	for p in propositions:
		t_flag = False
		f_flag = False
		#print(len(shadow))
		for c in clauses:
			if str(p) in c:
				#print("%s true in %s " % (p, c))
				t_flag = True
			if "~" + str(p) in c:
				#print("%s false in %s " % (p, c))
				f_flag = True 
		if t_flag == True and f_flag == False:
			print("%s is always true, so all clauses containing %s will be eliminated" % (p, p))
			if p in props:
				props.discard(p)
			for c in clauses:
				if str(p) in c and c in shadow:
					print("Eliminating %s" % (c))
					shadow.remove(c)
		if t_flag == False and f_flag == True:
			print("%s is always false, so all clauses containing %s will be eliminated" % (p, p))
			if p in props:
				props.discard(p)
			for c in clauses:
				if "~" + str(p) in c and c in shadow:
					print("Eliminating %s" % (c))
					shadow.remove(c)

	return shadow


def eliminate_tautologies(clauses, propositions):
	shadow = deepcopy(clauses)
	for p in propositions:
		for c in clauses:
			if str(p) in c and "~" + str(p) in c:
				#print("tautology %s" % (c))
				if c in shadow:
					print("%s is removed because it is a tautology" % (c))
					shadow.remove(c)
	return shadow

def get_atom(literal):
	literal = str(literal)
	literal = literal.strip("~")
	return literal 


def find_empty(clauses):
	for c in clauses:
		if len(c) == 0 or "False" in c:
			print("Empty clause found: %s" % ())
			return True
	return False



def literal_consistancy(clauses, propositions):
	for p in propositions:
			np = "~" + str(p)
			n = set()
			n.add(np)
			#print(set(str(p)), n)
			if set(str(p)) in clauses and n in clauses:
				print("The set of literals is inconsistant")
				return False
	print("The set of literals is consistant")
	return True 

def count_negations(a):
	a = str(a)
	count = 0
	for ch in a:
		if ch == "~":
			count += 1
	return count 

def resolve(a, clauses, props):	
	trash = []
	a = str(a)
	b = ""
	#print("a: %s" % (a))
	if a.startswith("~"):
		b = a[1:]
	else:
		b = "~" + a

	for i in clauses:
		#print(i)
		for j in clauses:
			#print(j)
			if a in i and b in j:
				print(str(i) + " is to be resolved with " + str(j) + ": ")
				resolvant = i.union(j)
				print("\n")
				print("   " + str(resolvant))
				print("______________________________")
				minus = {a, b}
				#print("Minus: %s" % (minus))
				resolvant = resolvant.difference(minus)
				if len(resolvant) == 0:
					print("   {  }    \n")
					print("The empty clause has been derived")
					return False
				else:
					print("   " + str(resolvant) + "\n")
					clauses.append(resolvant)
					if i not in trash:
						trash.append(i)
					if j not in trash:
						trash.append(j)

	print("The resolved clauses are now removed:")
	for t in trash:
		print(t)
		clauses.remove(t)
	print("\n")
	a = get_atom(a)
	a = Symbol(a)
	#print(a)
	if a in props:
		print("%s is removed from the set of Propositions\n" % (a))
		props.remove(a)
	return True


def resolution(clauses, propositions):
	print("\n")
	print("Beginning Resolution Refutation:")
	print("________________________________")
	props = deepcopy(propositions)
	while True:

		print("Clauses at start of the round:")
		for c in clauses:
			print(c)
		if find_empty(clauses):
			return False
		if all_literals(clauses):
			if literal_consistancy(clauses, props):
				print("True")
				return True
			else:
				return False
		clauses = eliminate_tautologies(clauses, props)
		clauses = eliminate_supersets(clauses)
		clauses = eliminate_unipolar(clauses, props)
		if len(clauses) == 0:
			return True
		print("Clauses after preliminaries:")
		for c in clauses:
			print(c)
		unit_clauses = []
		for c in clauses:
			if len(c) == 1:
				#print("%s has len 1" % (c))
				for i in c:
					unit_clauses.append(i)
		print("Now onto employment of the Resolution Rule:")
		if len(unit_clauses) > 0:
			print("It is preferble to begin with unit clauses")
			print("List of unit clauses:")
		for uc in unit_clauses:
			print(uc)
		while unit_clauses:
			a = choice(unit_clauses)
			print("%s is chosen \n" % (a))
			if str(a).startswith("~"):
				negs = count_negations(a)
				if negs/2 == 0:
					a = str(a).strip("~")
				else:
					a = str(a).strip("~")
					a = "~" + str(a) 
			if resolve(a, clauses, props):
				unit_clauses.remove(a)
			else:
				return False
		if props:
			print("There are currently no unit clauses from which to choose")
			print("and some propositions remain \n")
			a = choice(list(props))
			print("%s is chosen for the next round of resolution \n" % (a))
			res = resolve(a, clauses, props)
			if res == False:
				return False
			print("Clauses at end of loop:")
			for c in clauses:
				print(c)
		else:
			return True








	

















































