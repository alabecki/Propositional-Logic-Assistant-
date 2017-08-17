_____________________________________________________________________________________
Propositional Logic Assistant (PLA)
_____________________________________________________________________________________


0. Introduction
_____________________________________________________________________________________

The Propositional Logic Assistant (PLA) is designed to assist undergraduate students in computing science in to acquire a solid understanding of Propositional Logic.

_____________________________________________________________________________________ 


0. Installation

To run the program, a computer must have Python 3.x installed. The program 
was written on Python 3.6 but may run correctly on older versions. Version 
3.4 or higher, however, is recommended. The program can be opened in on the 
command-line in Windows or Linux machines. 

In the command line, go to the directory in which you have placed the 
folder containing the program and type:

	python main.py

(If you have Anaconda installed on your computer you need only type 
“z_main.py”)

If both Python 2 and Python 3 are installed on your system you may need to write as follows:
	
	python3 main.py

The program makes use of the logic module from the sympy library. It is 
recommended that the user employ pip when installing Python libraries. To 
install sympy simply type:

       pip install sympy	(perhaps with a “sudo”)

If you have both Python 2.x and 3.x installed on your system install sympy as follows:

	python3   -m pip install SomePackage    (Mac, Linux OS)

	or

	py -3   -m pip install SomePackage	(Windows)

 If you have trouble installing sympy through pip, please try using Easy Install:

	easy_install sympy		(perhaps with sudo prefixed)

This second way of installing sympy may be necessary even if you already
have python 3 active.

If none of these methods of installing sympy work see:

http://docs.sympy.org/latest/install.html

_________________________________________________________________________

2. Input Files

Upon opening PLA, the user will be prompted to load a text file (or close the program).
Each text file will consist a list of propositional formulas, which we will 
hereafter refer to as the Knowledge Base (KB). 
Each item in the KB will is written on a line in the text file like so:

	1.  (pa -> q) & rex

Each entry begins with an integer, which may be followed by a period. Lines that do not begin with an integer will be 
ignored. Lines that begin with an integer that is not followed by a well formed 
formula (and only a well-formed formula) will crash the program. 

Propositional atoms/variables may be strings containing upper and lower-case letters (but not integers). The sympy module reserves I, E, S, N, C, O, and Q for various purposes, so they should not be used in propositions. For this reason, it is 
recommended that the user stick with lower-case letters.

The following Boolean operators will be recognized by the program:

	&	for AND
	|	for OR
	->	for IF...THEN
	~	for NOT

Bi-conditional formulas must be expressed in terms of the other operators.  

Also, make sure that your propositional variables are not identical with any function
names, for this will also cause the program to crash. 

Several example files are included in with the program.
______________________________________________________________________________________

3. Commands and Overview

Upon loading a file, the user will be presented with the following options:

	1: Convert the KB to Conjunctive Normal Form (CNF)
	2: Make Resolution Refutation Query with Respect to the KB
	3: Get set of Models that satisfy the KB
	4: Get the set of Models that satisfy a query given the KB
	5: Return

The first option will convert the KB into CNF. The CNF or each component of the KB
will be displayed, followed by the entire CNF expression.

The second option allows the user to make use of Resolution Refutation to 
check if a query, provided by the user, follows from the KB. 
Upon selection the second option, the user will be prompted to input a propositional
logic formula as a query.  

After providing a query, the user will be presented with the following sub-options:

	1: Just tell me if the query is a consequence of the KB 
	2: Show the Resolution Proof
	3: Show the whole Diagnostic
	4: Show both the Resolution Proof and the Diagnostic

In the first case, the user is merely told whether the query follows from the 
KN. In the second case, if the query does follow from the KB, a Resolution Proof will be printed. For example, suppose that the following is the KB:
	1.	~(p & q) | r
	2. 	~p | q
	3.	p

And suppose that our query is r. The program will generate the following as a proof 
that r does, indeed, follow from the KB:
	Proof:
	1: {'~q', 'r', '~p'}         Given
	2: {'q', '~p'}               Given
	3: {'p'}                     Given
	4: {'~r'}                    Negated Conclusion
	5: {'~q', 'r'}               3, 1
	6: {'q'}                     3, 2
	7: {'~q'}                    4, 5
	8: {''}                      6, 7

The first three lines the result of taking each line of the KB, converting it into CNF
and then representing each disjunct as a set of literals. 
The fourth line adds the negation of the query, while the remaining lines are produced
by sequential applications of the resolution rule. 

The third sub-option will print out the query diagnostic, which presents the proof procedure in a more fine-grained and detailed manner. 

Finally, the fourth sub-option, prints out both the diagnostic and the refutation 
proof. 

Returning to the primary options, the third option will print out all models (i.e., truth assignments to atomic formulas) that satisfy the KB. 

The fourth option will print our all models that satisfy the KB in addition to a query provided by the user. 
 
