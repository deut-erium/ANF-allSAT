from operator import or_
from functools import reduce
from collections import Counter

def orthonormal_exp(variables: list) -> list:
    """
    orthonormal expansion of a list of distinct variables

    >>> orthonormal_exp([1,2,3])
        [(1,), (-1, 2), (-1, -2, 3), (-1, -2, -3)]
    """
    result = []
    last = []
    for var in variables:
        if last:
            last[-1]*=-1
        last.append(var)
        result.append(last.copy())
    last[-1]*=-1
    result.append(last)
    return [tuple(i) for i in result]


def assign(term: list, assignment:list):
    """
    partial assignment of `term` which is list representing
    a conjunction with a list of assignment of literals

    returns:
        const, unassigned variables

        const=1 represents whether term evaluates to true under
        assignment
    """
    unassigned = []
    for literal in term:
        if -literal in assignment:
            return 0,[]
        elif literal in assignment:
            continue
        else:
            unassigned.append(literal)
    if unassigned:
        return 0,unassigned
    return 1,unassigned

def quotient(formula: list, implicant:list) -> list:
    """
    returns formula/implicant

    representation of formula and the resulting quotient:
        [const,(1,2),(2,3),(3,)]
        const = {0,1}
    """
    result = [formula[0]] #[constant]
    for prod in formula[1:]:
        const, unassigned = assign(prod,implicant)
        result[0]^=const
        if unassigned:
            result.append(unassigned)
    return result

def variables(formula):
    """
    set of variables in formula
    >>> variables([1,(1,-2),(3,4),(-3,-1)])
        {1, 2, 3, 4}
    """
    return reduce(or_,map(lambda x:set(map(abs,x)), formula[1:]))


def gen_implicant(f: list) -> list:
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
        if q==[1]:
            I.add(tuple(t))
        elif q==[0]:
            continue
        else:
            I_temp = gen_implicant(q)
            I.update({t+x for x in I_temp})
    return I

def anf_not(formula):
    """
    xoring with 1 
    not(1^x^y) = 0^x^y
    >>> anf_not([1,(1,),(2,)])
        [0, (1,), (2,)]
    """
    formula[0]^=1
    return formula

def anf_xor(form1,form2):
    """
    (1^x)^(1^x^y) = 0^y
    >>> anf_xor([1,(1,)],[1,(1,),(2,)])
        [0, (2,)]
    """
    const = form1[0]^form2[0]
    xored = Counter(form1[1:])+Counter(form2[1:])
    return [const] + [ i for i in xored if xored[i]&1] 


def anf_and_term(term,formula):
    if term==0:
        return [0]
    elif term==1:
        return formula
    result = Counter()
    if formula[0]==1:
        result[term]^=1
    t = set(term)
    for conj in formula[1:]:
        result[tuple(set(conj)|t)]^=1
    return [0]+[i for i in result if result[i]]

def anf_and(form1,form2):
    """
    (1^x)(1^x^y) = 1^x^y^xy
    >>> anf_and([1,(1,)],[1,(1,),(2,)])
        [1, (1,), (2,), (1, 2)]
    """
    return reduce(anf_xor,map(lambda x:anf_and_term(x,form2),form1))

def anf_or(form1,form2):
    """
    a or b = a^b^ab
    >>> anf_or([1,(1,)],[1,(1,),(2,)])
        [1, (1,), (1, 2)]
    """
    return anf_xor(anf_xor(form1,form2),anf_and(form1,form2))


#def ort_exp_gen(variables):
#    last = []
#    for var in variables:
#        if last:
#            last[-1]*=-1
#        last.append(var)
#        yield last.copy()
#    last[-1]*=-1
#    yield last
#
#
#[[4],[1,3],[2,4],[1,3,4],[2,3,4]]


