# Load the solver.sage file 
load("solver.sage")

N = 10
subset_size = 4
no_of_samples = 5
m = 2

# create a boolean polynomial ring of 10 variables
B = BooleanPolynomialRing(N, 'x') 

# gets a list of the variables in the boolean polynomial ring, 
# x_0, x_1, ..., x_99
vars = list(B.gens()) 

# create an empty set to store the formula
S = set() 
 
# sample two subsets of size given by subset_size from vars
s1 = sample(vars, subset_size)
s2 = sample(vars, subset_size)

# Find the sum of products of each pair of terms (t1, t2) where t1 \in s1, t2 \in s2
P = 0

for x in s1:
	for y in s2:
		P = x * y + P # make sure to do it this way, not P = P + x * y

# create M sub-formulae that constitute the formula
for i in range(M):
	Q = 0

	# sample a subset of size no_of_samples from the list P.set()
	sa = sample(list(P.set()), no_of_samples)

	# compute Q, the subformula
	for x in sa: 
		Q = x + Q

	# add the subformula to the final set
	S.add(Q)














