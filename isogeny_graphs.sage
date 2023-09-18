def isogeny_graph(p,ell):
    """Computes the ell-isogeny graph of supersingular elliptic curves in characteristic p.

    Arguments:
        p: a prime, the characteristic of the ground field
        ell: a prime not equal to p, the degree of the isogenies

    Returns:
        a dictionary whose keys are j invariants, and the value of j is a dictionary of
    neighboring j-invariants j', the value of j' being the edges between j and j' (the output of find_neighbors(E(j),ell).
    The function first computes one supersingular j invariant using the CM method. We add j = j(E) and
    its neighbors to the graph dictionary, then add the neighbors of j to a temporary list, irregular_vertices.
    Then we grab a pair (j',phi) from irregular_vertices, add j' along with its neighbors to the graph. Now the graph is
    ell+1-regular at j', so we remove (j',phi) from irregular_vertices. Each neighbor j'' of j' is either
    already a key in the dictionary, meaning we have computed it and all of its neighbors, or we have visited it but not
    yet found all its neighbors, or we have never visited it. If this is the first visit to j'', we add it to
    irregular_vertices. The output is Gpell, which stores the j-invariants, curves (all in the same isogeny class),
    and isogenies used to represent edges, along with either a graph or directed graph SAGE object for G(p,ell).
    """

    F = GF(p^2)
    if not p.is_prime() and ell.is_prime():
        raise ValueError('inputs must be primes')
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
    Gpell = {}
    irregular_vertices = []
    neighbors = find_neighbors(E,ell)
    Gpell[j] = {}
    Gpell[j]['curve'] = E
    Gpell[j]['neighbors'] = find_neighbors(E,ell)
    finished_vertices = 1
    graph_size = int(p/12) + epsilon
    for vertex in Gpell[j]['neighbors']:
        edge = Gpell[j]['neighbors'][vertex]
        irregular_vertices.append((vertex, edge))
    while finished_vertices < graph_size:
        edge = irregular_vertices.pop(0)
        j = edge[0]
        phi = edge[1][0]
        if j in Gpell:
            continue
        phiE = phi.codomain()
        Gpell[j] = {}
        Gpell[j]['curve'] = phiE
        Gpell[j]['neighbors'] = find_neighbors(phiE,ell)
        finished_vertices = finished_vertices + 1
        for vertex in Gpell[j]['neighbors']:
            if vertex in Gpell:
                continue
            edges = Gpell[j]['neighbors'][vertex]
            irregular_vertices.append((vertex, edges))
    graph_dict = {}
    for j in Gpell:
        neighbors = []
        for vertex in Gpell[j]['neighbors']:
            edges = Gpell[j]['neighbors'][vertex]
            for phi in edges:
                neighbors.append(vertex)
        graph_dict[j] = neighbors
    if p%12 == 1:
        return Gpell, Graph(graph_dict)
    else:
        return Gpell, DiGraph(graph_dict)

def find_y_coordinate(E,xP):

    """
    Given elliptic curve E/F, and xP in F, this function calculates yP in F such that (xP,yP) is in E(F), if such a yP exists.
    """

    R.<y> = (E.base_field())['y']
    a1,a2,a3,a4,a6 = E.a_invariants()
    G = y^2 +(a1*xP+a3)*y-xP^3-a2*xP^2-a4*xP-a6
    factor = G.factor()[0][0]
    if factor.degree()>1:
        raise ValueError('Point is not defined over ',E.base_field())
    else:
        return -factor[0]
def find_neighbors(E,ell):
    """
    Computes the isosogenies whose kernels are the ell+1 nonzero cyclic subgroups of E[ell].

    The output is a dictionary, whose keys are the neighbor j-invariants and the value of j' is a
    list of isogenies between E and E(j').
    """

    F = E.base_field()
    Fx.<x> = F['x']
    if ell == 2:
        f = x^3 + F(E.a_invariants()[3])*x + F(E.a_invariants()[4])
        kernel_polys = [factor[0] for factor in f.factor()]
    else:
        factors = [factor[0] for factor in E.division_polynomial(ell).factor()]
        kernel_polys = []
        for factor in factors:
            # factor is either irreducible of degree (ell-1)/2 or linear
            if factor.degree() == (ell-1)/2:
                kernel_polys.append(factor)
            else:
                # factor is linear
                xP = -factor[0]
                K.<c> = F.extension(2)
                Kx.<x> = K['x']
                EK = E.change_ring(K)
                xP = -factor[0]
                yP = find_y_coordinate(EK,xP)
                P = EK(xP,yP)
                kernel_poly = Kx((x-xP))
                for k in range(2,ell):
                    P = P + P
                    xP = P[0]
                    if kernel_poly(xP) == 0:
                        continue
                    else:
                        kernel_poly = kernel_poly*(x-xP)
                kernel_polys.append(Fx(kernel_poly))
    kernel_polys = list(set(kernel_polys)) # lazy way to deal with problems with linear factors of div poly
    edges = {}
    E = E.change_ring(F)
    for kernel_poly in kernel_polys:
        phi = EllipticCurveIsogeny(E,kernel_poly)
        phiE = phi.codomain()
        j = phiE.j_invariant()
        if j in edges:
            multiple_edges = edges[j]
            multiple_edges.append(phi)
            edges[j] = multiple_edges
        else:
            edges[j] = [phi]
    return edges
