load("~/iitb2020/Spring/EE793/ANF-allSAT/anf.sage")
import os
os.environ["SAGE_NUM_THREADS"] = '9' 

def heurestic(F:set): return min(F,key=lambda f:len(f.variables()))

def solve_thread(tup):
	F,t = tup
	F1 = set({q(quotient(s,t)) for s in F})
	if 1 in F1:
		F1.remove(1)
	Y = solve(F1)
	return set({t*y for y in Y})

def q(qu):
	if qu == [True]:
		return 1
	elif qu == [False]:
		return 0
	else:
		return qu[1]

@parallel
def solve_parallel(F,t):
	#F1 = set({custom_q_2(s,t) for s in F})
	#one=t.variable(0)+t.variable(0)+1
	#if one in F1:
	#	F1.remove(one)
	F1 = set({q(quotient(s,t)) for s in F})
	if 1 in F1:
		F1.remove(1)
	Y = solve_2(F1)
	return set({t*y for y in Y})

def solve(F2:set):
	F_cp=F2.copy()
	if 0 in F2:
		return set()
	elif len(F2) == 1:
		return gen_implicant(F_cp.__iter__().__next__())
	elif len(F2) == 0:
		return set([1])
	else:
		I=set()
		f = heurestic(F_cp)
		X = gen_implicant(f)
		F_cp.remove(f)
		seeds = [(F_cp,t) for t in X]
		succ = lambda l: []
		S = RecursivelyEnumeratedSet(seeds, succ, structure='forest', enumeration='depth')
		map_function = lambda x: solve_thread(x)
		reduce_function = lambda x, y: x.union(y)
		reduce_init = I
		return S.map_reduce(map_function, reduce_function, reduce_init)

def solve_2(F):
	if 0 in F:
		return set()
	elif len(F) == 1:
		return gen_implicant(F.__iter__().__next__())
	elif len(F) == 0:
		return set([1])
	else:
		from datetime import datetime
		f = heurestic(F)
		X = gen_implicant(f)
		F_cp = F.copy()
		F_cp.remove(f)
		seed = [(F_cp.copy(),t) for t in X]
		e=set().union(*[t[-1] for t in list(solve_parallel(seed))])
		return e

def non_thread_solve(F2):
	F=F2.copy()
	I=set()
	if 0 in F:
		return set()
	elif len(F) == 1:
		return gen_implicant(F.__iter__().__next__())
	elif len(F) == 0:
		return set([1])
	else:
		f = heurestic(F)
		X = gen_implicant(f)
		F.remove(f)
		for t in X:
			F1 = set({q(quotient(s,t)) for s in F})
			if 1 in F1:
				I.union({t})
				F1.remove(1)
			Y = non_thread_solve(F1)
			I.union({t*y for y in Y})
		return I
