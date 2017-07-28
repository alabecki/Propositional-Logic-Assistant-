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
from pprint import*
from copy import deepcopy
import os
from random import choice 



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
		if t == "" or t == " ":
			continue
		t = re.split(r'\|\s*(?![^()]*\))', t)
		for item in t:
			result = result + " & " + item
	return(result)

def cnf_to_set(formula):
	result = []
	formula = formula.replace("(", "")
	formula = formula.replace(")", "")
	#formula = formula.replace("&", "")
	formula = formula.split("&")
	for f in formula:
		addition = set()
		print(f)
		f = str(f)
		if "|" not in f:
			addition.add(f)
			continue
		f = f.split("|")
		for i in f:
			i = i.strip()
			addition.add(i)
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


def conjoin(formulas):
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
				g = g.lstrip()
				g = g.rstrip()
				#print(g)
				g = to_cnf(g)

				print("g:::: %s" % (g))
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
				print("%s is a superset of %s " % (j, i))
				if j in shadow:
					shadow.remove(j)
	return shadow

def eliminate_unipolar(clauses, propositions):
	shadow = deepcopy(clauses)
	props = deepcopy(propositions)
	for p in propositions:
		t_flag = False
		f_flag = False
		for c in clauses:
			if str(p) in c:
				t_flag = True
			if "~" + str(p) in c:
				f_flag = True 
		if t_flag == True and f_flag == False:
			for c in clauses:
				if str(p) in c:
					shadow.remove(c)
					props.discard(p)
		if t_flag == False and f_flag == True:
			for c in clauses:
				if "~" + str(p) in c:
					shadow.remove(c)
					props.discard(p)
	return shadow


def eliminate_tautologies(clauses, propositions):
	shadow = deepcopy(clauses)
	for p in propositions:
		for c in clauses:
			if str(p) in c and "~" + str(p) in c:
				print("tautology %s" % (c))
				if c in shadow:
					shadow.remove(c)
	return shadow

def get_atom(literal):
	literal = str(literal)
	if literal.startswith("~"):
		return(literal[1:])
	else:
		return literal 


def find_empty(clauses):
	for c in clauses:
		print(c)
		if len(c) == 0 or "False" in c:
			return True
	return False

def all_literals(clauses):
	for c in clauses:
		if len(c) != 1:
			return False
	return True 



def literal_consistancy(clauses, propositions):
	for p in propositions:
			np = "~" + str(p)
			n = set()
			n.add(np)
			print(set(str(p)), n)
			if set(str(p)) in clauses and n in clauses:
				print("Seriously?")
				return False
	return True 

def resolve(a, clauses, props):		
	trash = []
	a = str(a)
	print("a: %s" % (a))
	print("not a: %s" % ("~" + a))
	for i in clauses:
		print(i)
		for j in clauses:
			print("______%s" % (j))
			if a in i and "~" + a in j:
				print("Finally" + str(i) + " " + str(j))
				resolvant = i.union(j)
				print("Pre-Resolvant %s " % (resolvant))
				minus = {a, "~" + a}
				print("Minus: %s" % (minus))
				resolvant = resolvant.difference(minus)
				print("Resolvant %s " % (resolvant))
				clauses.append(resolvant)
				if i not in trash:
					trash.append(i)
				if j not in trash:
					trash.append(j)
	print("Trash")
	for t in trash:
		print(t)
		clauses.remove(t)
	a = get_atom(a)
	print(a)
	if a in props:
		props.remove(a)




def resolution(clauses, propositions):
	props = deepcopy(propositions)
	while True:

		print("Clauses at start of loop:")
		for c in clauses:
			print(c)
		if find_empty(clauses):
			print("False")
			return False
		if all_literals(clauses):
			if literal_consistancy(clauses, props):
				print("True")
				return True
		clauses = eliminate_tautologies(clauses, props)
		clauses = eliminate_supersets(clauses)
		clauses = eliminate_unipolar(clauses, props)
		print("Clauses after preliminaries:")
		for c in clauses:
			print(c)
		unit_clauses = []
		for c in clauses:
			if len(c) == 1:
				for i in c:
					unit_clauses.append(i)
		print("Unit Clauses:")
		for uc in unit_clauses:
			print(uc)
		while unit_clauses:
			a = choice(unit_clauses)
			resolve(a, clauses, props)
			unit_clauses.remove(a)

		a = choice(list(props))
		resolve(a, clauses, props)
		print("Clauses at end of loop:")
		for c in clauses:
			print(c)








	

















































