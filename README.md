# inseparables
Sage code to compute the endomorphism ring of a supersingular elliptic curve

Sample usage: 

load("cycles.sage")
load("isogeny_graphs.sage")
load("schoof.sage")
load("inner_products.sage")
load("endomorphism_algebra.sage")
load("fast_elkies.sage")
p = next_prime(2**16)
j = find_supersingular_j(p)
j = random_walk(j,2)[-1]
out = endo_ring_from_inseparables(j)