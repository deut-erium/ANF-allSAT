def orthonormal_exp(variables):
	""" 
    variables:[x0,x1,x2,x3] 
    sage: ortho = orthonormal_exp(variables)
	sage: ortho
	[x0,
 	x0*x1 + x1,
 	x0*x1*x2 + x0*x2 + x1*x2 + x2,
 	x0*x1*x2*x3 + x0*x1*x3 + x0*x2*x3 + x0*x3 + x1*x2*x3 + x1*x3 + x2*x3 + x3,
 	x0*x1*x2*x3 + x0*x1*x2 + x0*x1*x3 + x0*x1 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + x3 + 1]
    """ 
	result = []
	s = variables[0]+variables[0]+1
	for var in variables:
		result.append(var*s)
		s=var*s+s
	result.append(1-sum(result))
	return result

def custom_ortho_exp(variables):
	""" 
    variables:[x0,x1,x2,x3] 
    sage: ortho = orthonormal_exp(variables)
	sage: ortho
	[x0,
 	x0*x1 + x1,
 	x0*x1*x2 + x0*x2 + x1*x2 + x2,
 	x0*x1*x2*x3 + x0*x1*x3 + x0*x2*x3 + x0*x3 + x1*x2*x3 + x1*x3 + x2*x3 + x3,
 	x0*x1*x2*x3 + x0*x1*x2 + x0*x1*x3 + x0*x1 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + x3 + 1]
    """ 
	result = []
	if len(variables) > 0:
		s = variables[0]+variables[0]+1
		z = {}
		past = None
		for var in variables:
			if past is not None:
				z[past]=0
			z[var]=1
			past=var
			result.append((var*s,z.copy()))
			s=var*s+s
		z[past]=0
		result.append((1-reduce(lambda x,y:x+y[0],result,0),z))
	return result

# All formulas used are BooleanPolynomial class objects in ANF form
# All variables used are initialized by BooleanPolynomialRing class,notation used as x0,x1,x2,...For expressions +,- = xor,* = and
# Formulae passed are assigned to Polynomial class and passed,taken as implicit to demonstrate

def variables(formula):return list(formula.variables())
# returns The symbolic variables used in formula

def anf_not(formula):return formula+1
# returns an ANF formula referring to ~formula
# ~a = 1^a

def anf_xor(form1,form2):return form1+form2
# Taking two formulae to return xor of the two
# (1^x0)^(1^x0^x1) = x1
# sage: anf_xor(1+x0,1+x0+x1)
# x1

def anf_and(form1,form2):return form1*form2
# Taking two formulae to return their and
# (1^x0)*(1^x0^x1) = 1^x0^x1^x0*x1
# sage: anf_and(1+x0,1+x0+x1)
# 1+x0+x1+x0*x1

def anf_or(form1,form2):return anf_xor(anf_xor(form1,form2),anf_and(form1,form2))
# Taking two formulae to return their or
# x0+x1 = x0^x1^x0*x1
# sage: anf_or(x0,x1)
# x0+x1+x0*x1

@parallel
def get_assign_parallel(implicant,var):
	res=implicant.subs({var:1})
	if res.is_zero():
		return 0
	else:
		return 1

def get_assignment(implicant):
	""" 
    util to decide required partial assignment to be performed for implicant in ANF
	implicant = x0*x1*x2*x3 + x0*x1*x3 + x0*x2*x3 + x0*x3 + x1*x2*x3 + x1*x3 + x2*x3 + x3 = ~x0^~x1^~x2^x3
	sage: get_assignment(implicant)
	{x0: 0, x1: 0, x2: 0, x3: 1}
    """ 
	X = variables(implicant)
	d={}
	for x in X:
		res = implicant.subs({x:1})
		if res.is_zero():
			d[x] = 0
			implicant = implicant.subs({x:0})
		else:
			d[x] = 1
			implicant = res
	return d

def custom_quotient(formula,implicant):
	f_part = formula.subs(implicant[1])
	f = [f_part.is_one()]
	if f_part.is_constant() == False:
		f += [f_part]
	return f

def custom_q_2(formula,implicant):
	f_part = formula.subs(get_assignment(implicant))
	return f_part

def quotient(formula,implicant):
	""" 
    util to compute quotient for implicant in ANF based on .subs method of BooleanPolynomial
	formula = x0*x1*x2 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3 + 1
	implicant = x0
	sage: quotient(formula,implicant)
	[False, x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2]
    """ 
	f_part = formula.subs(get_assignment(implicant))
	f = [f_part.is_one()]
	if f_part.is_constant() == False:
		f += [f_part]
	return f

@parallel
def gen_implicant_parallel(f,t):
	I=set()
	q = custom_quotient(f,t)
	if q == [True] : 
		I.add(t[0])
	elif q == [False] :
		return I 
	else: 
		I_temp = gen_implicant(q[1]) 
		I.update({t[0]*x for x in I_temp})
	return I
	

def gen_implicant(f): 
     """ 
	 w = x0,x = x1,y = x2,z = x3
     f = x0*x1*x2 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3 + 1 = 1 ⊕ w ⊕ x ⊕ z ⊕ wy ⊕ wz ⊕ xz ⊕ wxy ⊕ xyz ⊕ wyz
     implicands(1^w^x^z^wy^wz^xz^wxy^xyz^wyz) =  
     wxz', wx'yz', w'xyz, w'x'yz', w'x'y'z'
	 Mentioned in paper  
     sage: gen_implicant(f) 
     {x0*x1*x3 + x0*x1,
 	 x0*x1*x2*x3 + x1*x2*x3,
 	 x0*x1*x2*x3 + x0*x1*x2 + x0*x2*x3 + x0*x2,
 	 x0*x1*x2*x3 + x0*x1*x2 + x0*x2*x3 + x0*x2 + x1*x2*x3 + x1*x2 + x2*x3 + x2,
 	 x0*x1*x2*x3 + x0*x1*x2 + x0*x1*x3 + x0*x1 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + x3 + 1}
     """ 
     from datetime import datetime
     X = list(f.variables()) 
     on_terms = custom_ortho_exp(X)
     """
     for t in on_terms:
         continue
         t1=datetime.now()
         q = custom_quotient(f,t)
         t2=datetime.now()
         if q == [True] : 
             I.add(t[0]) 
         elif q==[False]: 
             continue 
         else: 
             I_temp = gen_implicant(q[1]) 
             I.update({t[0]*x for x in I_temp})
         t3=datetime.now()
         print(t2-t1,t3-t2)
     """
     I = set().union(*[l[-1] for l in list(gen_implicant_parallel([(f,t) for t in on_terms]))])
     return I 

def OG_coeff(formula):
	"""
	Generates the OG coefficients(actually ON) corresponding to ON_terms
	w = x0,x = x1,y = x2,z = x3
	f = x0*x1*x2 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3 + 1 = 1 ⊕ w ⊕ x ⊕ z ⊕ wy ⊕ wz ⊕ xz ⊕ wxy ⊕ xyz ⊕ wyz
	sage: OG_coeff(f)
	[(x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2, x0),
 	(x2*x3, x0*x1 + x1),
 	(x3 + 1, x0*x1*x2 + x0*x2 + x1*x2 + x2),
 	(0,
  	x0*x1*x2*x3 + x0*x1*x3 + x0*x2*x3 + x0*x3 + x1*x2*x3 + x1*x3 + x2*x3 + x3),
 	(1,
  	x0*x1*x2*x3 + x0*x1*x2 + x0*x1*x3 + x0*x1 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + x3 + 1)]
	"""
	X = variables(formula)
	on_terms = orthonormal_exp(X)
	zero = X[0]+X[0]
	one = zero + 1
	result = []
	for t in on_terms:
		q = quotient(formula,t)
		if q == [True]:
			result.append((one,t))
		elif q == [False]:
			result.append((zero,t))
		else:
			result.append((q[1],t))
	return result

def Co_OG_coeff(formula):
	"""
	generates the dual(co-OG) coefficients. co-OG coeff = ~OG coeff
	w = x0,x = x1,y = x2,z = x3
	f = x0*x1*x2 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3 + 1 = 1 ⊕ w ⊕ x ⊕ z ⊕ wy ⊕ wz ⊕ xz ⊕ wxy ⊕ xyz ⊕ wyz
	sage: Co_OG_coeff(f)
	[(x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + 1, x0),
 	(x2*x3 + 1, x0*x1 + x1),
 	(x3, x0*x1*x2 + x0*x2 + x1*x2 + x2),
 	(1,
  	x0*x1*x2*x3 + x0*x1*x3 + x0*x2*x3 + x0*x3 + x1*x2*x3 + x1*x3 + x2*x3 + x3),
 	(0,
  	x0*x1*x2*x3 + x0*x1*x2 + x0*x1*x3 + x0*x1 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + x3 + 1)]

	"""
	OG_repr = OG_coeff(formula)
	return [(anf_not(coeff[0]),coeff[1]) for coeff in OG_repr]

def OG_to_ANF(coeff):
	"""
	util to convert OG representation to ANF's
	coeff = result in OG_coeff docstring
	sage: OG_to_ANF(coeff)
	x0*x1*x2 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3 + 1
	"""
	s = 0
	for i in coeff:
		s+=i[0]*i[1]
	return s

def compose(F,f,g):
	"""
	creating a composition of 2 functions given in OG form
	F = anf_or
	f = OG_coeff(x1*x3)
	g = OG_coeff(x1^x3)
	sage: compose(F,f,g)
	x1*x3 + x1 + x3
	"""
	assert len(f) == len(g)
	
	new_coeff = []	
	for i in range(len(f)):
		new_coeff.append((F(f[i][0],g[i][0]),f[i][1]))
	return OG_to_ANF(new_coeff)	