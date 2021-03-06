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
     X = variables(f) 
     on_terms = orthonormal_exp(X) 
     I = set() 
     for t in on_terms: 
         q = quotient(f,t)
         if q == [True] : 
             I.add(t) 
         elif q==[False]: 
             continue 
         else: 
             I_temp = gen_implicant(q[1]) 
             I.update({t*x for x in I_temp}) 
     return I 

def OG_coeff(formula):
	"""
	Generates the OG coefficients(actually ON) corresponding to ON_terms
	w = x0,x = x1,y = x2,z = x3
	f = x0*x1*x2 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3 + 1 = 1 ⊕ w ⊕ x ⊕ z ⊕ wy ⊕ wz ⊕ xz ⊕ wxy ⊕ xyz ⊕ wyz
	sage: OG_coeff(f)
	[x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2, x2*x3, x3 + 1, 0, 1]
	"""
	X = variables(formula)
	on_terms = orthonormal_exp(X)
	zero = X[0]+X[0]
	one = zero + 1
	result = []
	for t in on_terms:
		q = quotient(formula,t)
		if q == [True]:
			result.append(one)
		elif q == [False]:
			result.append(zero)
		else:
			result.append(q[1])
	return result

def Co_OG_coeff(formula):
	"""
	generates the dual(co-OG) coefficients. co-OG coeff = ~OG coeff
	w = x0,x = x1,y = x2,z = x3
	f = x0*x1*x2 + x0*x2*x3 + x0*x2 + x0*x3 + x0 + x1*x2*x3 + x1*x3 + x1 + x3 + 1 = 1 ⊕ w ⊕ x ⊕ z ⊕ wy ⊕ wz ⊕ xz ⊕ wxy ⊕ xyz ⊕ wyz
	sage: Co_OG_coeff(f)
	[x1*x2*x3 + x1*x2 + x1*x3 + x1 + x2*x3 + x2 + 1, x2*x3 + 1, x3, 1, 0]s
	"""
	OG_repr = OG_coeff(formula)
	return [anf_not(coeff) for coeff in OG_repr]
