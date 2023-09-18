# Functions for navigating isogeny graphs and finding cycles.
def adjacent_vertices(j, ell):
    """
    Returns the j-invariants adjacent to j in the ell-isogeny graph.
    """
    F = j.parent()
    p = F.characteristic()
    phi_ell = ClassicalModularPolynomialDatabase()[ell];
    FX.<X> = PolynomialRing(F)
    FXY.<X, Y> = PolynomialRing(F)
    phi_ell = FXY(phi_ell)
    phi_ell_j = FX(phi_ell(Y = j))
    neighbors = []
    # append roots of phi_ell_j to neighbors with multiplicity
    roots = phi_ell_j.roots()
    for root in roots:
        for i in range(root[1]):
            neighbors.append(root[0])
    return neighbors

def ell_isogenies(E, ell):
    """Returns all ell-isogenies of E."""
    # we are going to factor the ellth divisoin poly of E.
    assert E.is_supersingular(), "E must be supersingular"
    # TODO: check that degree of ground field of E has even degree over GF(p)
    psi_ell = E.division_polynomial(ell)
    # roots of psi_ell are all x(P) where P is in E[ell]
    kernel_polys = [factor[0] for factor in psi_ell.factor()]
    assert len(kernel_polys) == ell + 1, "Wrong ammount of kernel polys"
    return [EllipticCurveIsogeny(E, h) for h in kernel_polys]



def random_walk(j0, ell, length = None):
    F = j0.parent()
    p = F.characteristic()
    if not length: length = floor(log(p,ell))
    path = [j0]
    for k in range(length):
        jk = path[k]
        neighbors = adjacent_vertices(jk, ell)
        idx = randint(0, len(neighbors) - 1)
        path.append(neighbors[idx])
    return path

def random_walks_to_Fp(j0, ell):
    """Returns a non-backtracking path in the ell-isogeny graph from j0 to a random supersingular j-invariant in Fp."""
    p = j0.parent().characteristic()
    length = floor(log(p, ell))
    while True:
        walk = [randint(0, ell)] + [randint(0, ell-1) for _ in range(length-1)]
        j1 = adjacent_vertices(j0, ell)[walk[0]]
        path = [j0, j1]
        for k in range(1,length):
            jk = path[k]
            neighbors = adjacent_vertices(jk, ell)
            # remove jk from neighbors so we don't backtrack. jk may still be in neighbors if there are multiple edges at jk.
            neighbors.remove(path[k-1])
            j = neighbors[walk[k]]
            path.append(j)
            if j**p == j:
                return path

def frob(E):
    """Returns the image of E under the p-power Frobenius map"""
    p = E.base_field().characteristic()
    Ep = EllipticCurve([a**p for a in E.a_invariants()])
    return Ep


def CGL_cycle(j, ell):
    """ Compute a cycle in G(p,ell) at j.

    When j is in Fp, this cycle may be trivial.
    """
    F = j.parent()
    Fp = F.base_ring()
    p = F.characteristic()
    P1 = random_walks_to_Fp(j, ell)
    P1_conjugate = [j**p for j in P1]
    P1_conjugate.reverse()
    half_cycle_1 = P1 + P1_conjugate[1:]
    if j in Fp:
        return half_cycle_1
    P2 = random_walks_to_Fp(j, ell)
    while P2[-1] == P1[-1]:
        P2 = random_walks_to_Fp(j, ell)
    P2_conjugate = [j**p for j in P2]
    P2.reverse()
    half_cycle_2 = P2_conjugate[1:] + P2[1:]
    cycle = half_cycle_1 + half_cycle_2
    return cycle



def cycle_to_endo(path, ell):
    """ Given path a list of adjacent j-invariants in G(p,ell), return a corresponding isogeny chain.
    """
    jk = path[0]
    Ek = EllipticCurve(j=jk)
    chain = []
    for k in range(1, len(path)):
        neighbors = find_neighbors(Ek, ell)
        chain.append(neighbors[path[k]][0])
        Ek = chain[k - 1].codomain()
    # recompute last isogeny so that its codomain is E0
    f = chain[-1].kernel_polynomial()
    phi = EllipticCurveIsogeny(chain[-1].domain(), f, chain[0].domain())
    chain[-1] = phi
    return chain

def path_to_isogeny(path, ell):
    """ Given path a list of adjacent j-invariants in G(p,ell), return a corresponding isogeny chain.
    """
    jk = path[0]
    Ek = EllipticCurve(j=jk)
    chain = []
    for k in range(1, len(path)):
        neighbors = find_neighbors(Ek, ell)
        chain.append(neighbors[path[k]][0])
        Ek = chain[k - 1].codomain()
    return chain

def find_supersingular_j(p):
    """ Returns a supersingular j-invariant in Fp using Broker's algorithm."""
    F = GF(p^2)
    if not p.is_prime():
        raise ValueError('input must be prime')
    elif p%12 == 7:
        E = EllipticCurve([F(1),F(0)])
        j = E.j_invariant()
        epsilon = 1
    elif p%12 == 5:
        E = EllipticCurve([F(0),F(1)])
        j = E.j_invariant()
        epsilon = 1
    elif p%12 == 11:
        E = EllipticCurve([F(0),F(1)])
        j = E.j_invariant()
        epsilon = 2
    else:
        q = 3
        while kronecker(-q,p) == 1 or q%4 == 1:
            q = next_prime(q)
        PK = hilbert_class_polynomial(-q)
        Fx = F['x']
        PK = Fx(PK)
        j = PK.roots()[0][0]
        E = EllipticCurve(j=j)
        epsilon = 0
    return j


def polynomial_frob(f):
    """Returns the polynomial whose nth coefficient is a**p where a is the nth
    coefficient of f."""
    return f.parent()([c**(f.parent().characteristic()) for c in f.coefficients()])

def isogeny_to_Ep(path, ell):
    """Returns a chain of isogenies from E(j) to E(j)^(p) from a sequence of adjacent j-invariants path from j to an Fp-rational j-invariant"""
    phi = path_to_isogeny(path, ell)
    phipdual = [EllipticCurveIsogeny(frob(f.domain()),
                                     polynomial_frob(f.kernel_polynomial()),
                                     frob(f.codomain())).dual() for f in phi]
    phipdual.reverse()
    assert phi[-1].codomain().j_invariant() == phipdual[0].domain().j_invariant()
    phi[-1] = EllipticCurveIsogeny(phi[-1].domain(),
                                   phi[-1].kernel_polynomial(),
                                   phipdual[0].domain())
    return phi + phipdual

def evaluate_isogeny(isogeny, P):
    for phi in isogeny:
        P = phi(P)
    return P

def evaluate_insep_endo(endo, P):
    P = evaluate_isogeny(endo, P)
    p = endo[0].domain().base_ring().characteristic()
    return endo[0].domain()([P[0]^p,P[1]^p,P[2]^p])
