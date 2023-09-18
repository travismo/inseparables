# generalized schoof implementation adapted
# from the implementation of Schoof's algorithm available here:
# https://math.mit.edu/classes/18.783/2019/lectures.html
# The elliptic curve E is in Weierstrass form y^2=f(x)=x^3+Ax+B

divpoly_factor = 0    # global variable for factor of the division polynomial when ZeroDivisionError's occur

# Elements of End(E[ell]) are represented as pairs (a,b*y), with a,b in Fp[x]/(h(x)), where h is the ell-th divpoly (or a factor of it, for example, the kernel polynomial of an isogeny)
# The y is implicit, but must be accounted for when applying the group law -- using the curve equation y^2=f(x) we can replace y^2 with f(x) whenever it appears (this effectively hides all the y's)

# In many of the functions below we pass in both A and f
# where f is the image of x^3+Ax+B in Fp[x]/(h(x)) -- we need both because if deg(h)<= 3 we cannot recover A from (x^3+Ax+B) mod h(x)

def add(P,Q,A,f,h):
    """add endomorphisms P and Q in End(E[ell])"""
    global divpoly_factor
    if not P: return Q
    if not Q: return P
    a1 = P[0]; b1 = P[1]; a2=Q[0]; b2=Q[1]
    if a1.mod(h) == a2.mod(h):
        if b1.mod(h) == b2.mod(h): return dbl(P,A,f,h)
        else: return ()
    try:
        m = (b2-b1)*((a2-a1).inverse_mod(h))
        m = m.mod(h)
    except ValueError:
        ### given that a2-a1 is already reduced mod h, a ZeroDivisionError means that gcd(a2-a1,h) must be a nontrivial divisor g of h
        ### raise an error so that we can restart the algorithm working in a smaller quotient ring
        divpoly_factor = a2-a1
        raise
    a3 = (f*m^2 -a1 - a2).mod(h)
    b3 = (m*(a1-a3) - b1).mod(h)
    return (a3,b3)

def dbl(P,A,f,h):
    """double the endomorphism P in End(E[ell]) """
    global divpoly_factor
    if not P: return P
    a1 = P[0]; b1 = P[1]
    try:
        m = (3*a1^2+A)*((2*b1*f).inverse_mod(h))
        m = m.mod(h)
    except ValueError:
        divpoly_factor = 2*b1*f
        raise
    a3 = (f*m^2 - 2*a1).mod(h)
    b3 = (m*(a1-a3) - b1).mod(h)
    return (a3,b3)

def neg(P,h):
    """ negate the endomorphism P in End(E[ell]) """
    if not P: return P
    return (P[0],(-P[1]).mod(h))

def smul (n,P,A,f,h):
    """ compute the scalar multiple n*P in End(E[ell]) using double and add"""
    if not n: return ()
    nbits = n.digits(2)
    i = len(nbits)-2
    Q = P
    while i >= 0:
        Q = dbl(Q,A,f,h)
        if nbits[i]: Q = add(P,Q,A,f,h)
        i -= 1
    return Q

def naive_modular_composition(f,g,h):
    """Returns f(g) modulo h."""
    g_i = g
    c = f[0]
    for i in range(1,f.degree()+1):
        if f[i]:
            c = (c + f[i] * g_i)
        g_i = (g_i*g).mod(h)
    return c
def isogeny_compose_mod(phi, alpha, h):
    """Returns the coordinate functions of phi*alpha modulo h."""
    a = alpha[0]
    b = alpha[1]
    #phi(x,y) = (u(x)/k(x), (s(x)/(k(x)))*y)
    # u(a), v(a), s(a), s(t)
    phix = phi.x_rational_map()
    u = phix.numerator()
    v = phix.denominator()
    phiy = phi.rational_maps()[1](y=1)
    s = phiy.numerator().univariate_polynomial()
    t = phiy.denominator().univariate_polynomial()
    max_deg = max(u.degree(),v.degree(),s.degree(),t.degree())
    ua = va = sa = ta = 0
    a_h = 1
    for i in range(max_deg+1):
        ua = ua + u[i]*a_h
        va = va + v[i]*a_h
        sa = sa + s[i]*a_h
        ta = ta + t[i]*a_h
        a_h = (a_h*a).mod(h)
    va_inv = va.inverse_mod(h)
    ta_inv = ta.inverse_mod(h)
    c = (ua * va_inv).mod(h)
    d = (sa * ta_inv * b).mod(h)
    return (c,d)

def mul (P,Q,h):
    """ compute the product (i.e. composition of) P*Q of two endomorphisms in
    End(E[ell]) """
    a = naive_modular_composition(P[0], Q[0], h)
    b = naive_modular_composition(P[1], Q[0], h)
    b = (b*Q[1]).mod(h)
    return (a,b)

def endo_mod_from_factors(chain1, chain2, h):
    """Returns the restriction of the endomorphism phi2*phi1 modulo h, where
    phi1, phi2 are isogenies represented by the chains of isogenies phi1, phi2.
    We also cache the computation of phi1 modulo h and return that as well.
    """
    if isinstance(chain1, list):
        # Check to see if chain1 is a chain of isogenies
        (a,b) = compose_and_reduce_chain(chain1, h)
    else:
        # We assume phi1 is the output of compose_and_reduce_chain()
        (a,b) = chain1
    phi1 = (a,b)
    endo_mod = compose_and_reduce_chain(chain2, h, phi1)
    return endo_mod, phi1
def compose_and_reduce_chain(chain, h, phi=None):
    """Returns the coordinate functions of the isogeny phi represented by chain,
     a list of isogenies, modulo h. phi is an optional input which is
     precomposed with chain."""
    if phi:
        (a,b) = phi
    else:
        x = h.parent().gen()
        (a,b) = (x,1)
    for psi in chain:
        (a,b) = isogeny_compose_mod(psi, (a,b), h)
    return (a,b)



def trace_of_endo_mod(endo, deg, M, use_kerpols = True):
    """Computes the trace of endo mod M, where deg is the degree of the
    endomorphism.

    If use_kerpols is True, then this algorithm computes the kernel polynomial h
    of an M-isogeny and we work mod h. Otherwise, we work modulo the
    M-division polynomial.
    """
    E = endo[0].domain()
    FF = E.base_ring()
    ell = endo[0].degree()                       # deg(endo) = ell^(len(endo))
    # deg = ell^(len(endo))
    R.<x> = PolynomialRing(FF)
    A=E.a4(); B=E.a6()                          # E: y^2 = x^3 + Ax + B
    if use_kerpols:
        neighbors = get_neighbors(E,M)
        found_kerpol = False
        for neighbor in neighbors:
            jtilde, e = neighbor
            if e == 1 and jtilde not in [FF(0), FF(1728)]:
                A_tilde, B_tilde, p1 = get_ABsigma(E, jtilde, M)
                h = fastElkiesOdd(A, B, A_tilde, B_tilde, M, p1)
                found_kerpol = True
                break
        # every root of phi(j(E),Y) is a multiple root, use div poly
        if not found_kerpol: h = E.division_polynomial(M, x, 0).monic()
    else:
        h = E.division_polynomial(M, x, 0).monic()
    while true:
        try:
            f = x^3+A*x+B
            alpha = compose_and_reduce_chain(endo, h)
            alpha2 = compose_and_reduce_chain(endo,h,phi=alpha)          # alpha2 = alpha^2
            identity = (x,R(1))             # identity aka mult-by-1 map
            Q = smul(deg%M, identity, A, f, h)     # Q is the mult-by-deg map
            S = add(alpha2, Q, A, f, h)            # S = alpha^2 + deg = t*alpha
            if not S: return 0                  # if S=0 then t=0
            if S == alpha: return 1             # if S=alpha then t=1
            if neg(S, h) == alpha: return -1       # if S=-alpha then t=-1
            P = alpha
            for t in range(2,M-1):
                P = add(P, alpha, A, f, h)         # P = t*pi
                if P == S: return t             # if S=P then we have found t
            assert false, "Error, endo satisfies no charpoly!!"
        except ValueError:
            h = gcd(h,divpoly_factor)    # if we hit a zero divisor, start over with new h
            print("found %d-divpoly factor of degree %d"%(M,h.degree()))


def generalized_Schoof(endo,use_kerpols = True, verbose = False):
    """ compute the trace of endo using generalized Schoof's algorithm """
    degree = 1
    for phi in endo:
        degree = degree * phi.degree()
    t = 0; N = 1; M = 2;
    while N <= 4*sqrt(degree):
        M = next_prime(M)
        while degree % M == 0:
            M = next_prime(M)
        start = cputime()
        tM = trace_of_endo_mod(endo, degree, M, use_kerpols)
        if verbose: print("trace %d mod %d computed in %.2f secs"%(tM, M, cputime()-start))
        a = N * N.inverse_mod(M); b = M * M.inverse_mod(N)
        N *= M
        t = (a*tM + b*t) % N
    if t >= N/2: return t-N
    else: return t

def evaluate_chain(chain, P):
    for phi in chain:
        P = phi(P)
    return P

def test_char_poly(t,E,endo):
    P = E.random_point()
    d = prod([phi.degree() for phi in endo])
    endoP = evaluate_chain(endo, P)
    endo2P = evaluate_chain(endo, endoP)
    return endo2P - t*endoP + d*P == E(0)
# sample usage
# p = next_prime(100);
# ell = 2;
# j = find_supersingular_j(p);
# j = random_walk(j, ell)[-1];
# cycle = CGL_cycle(j, ell);
# endo = path_to_chain(cycle, ell);
# t = generalized_Schoof(endo);
# check our work:
# E = endo[0].domain();
# P = E.random_point();
# endoP = evaluate_chain(endo, P);
# endo2P = evaluate_chain(endo, endoP);
# deg_endo = ell^(len(endo));
# check characteristic equation evaluated at P
# endo2P - t*endoP + deg_endo*P
# (0 : 1 : 0)
