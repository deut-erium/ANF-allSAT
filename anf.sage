def orthonormal_exp(variables):
	result = []
	last = []
	for var in variables:
		if last:
			last[-1]+=1
		last.append(var)
		result.append(expression(last))
	last[-1]+=1
	result.append(expression(last))
	return result

def expression(last):
	s = 1
	for i in last:
		s = s*i
	return s

def variables(formula):return list(formula.variables())

def anf_not(formula):return formula+1

def anf_xor(form1,form2):return form1+form2

def anf_and(form1,form2):return form1*form2

def anf_or(form1,form2):return anf_xor(anf_xor(form1,form2),anf_and(form1,form2))

def get_assignment(implicant):
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
	f_part = formula.subs(get_assignment(implicant))
	f = [f_part.is_one()]
	if f_part.is_constant() == False:
		f += [f_part]
	return f

def gen_implicant(f): 
     """ 
     f = [const, (conj), (conj2) ...] 
     implicands(1^w^w^z^wy^wz^xz^wxy^xyz^wyz) =  
     wxz', wx'yz', w'xyz, w'x'yz', w'x'y'z'  
     >>> gen_implicant( 
         [1,(1,),(2,),(4,),(1,3),(1,4),(2,4),(1,2,3),(2,3,4),(1,3,4)]) 
     {(1, 2, 3, -4), (1, -2, 3, -4), (1, 2, -3, -4), (-1, 2, 3, 4),  
      (-1, -2, 3, -4), (-1, -2, -3, -4)} 
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

