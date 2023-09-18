def inseparable_suborder(j, verbose = False):
    """
    Returns the endomorphism algebra of E, a supersingular elliptic curve with j-invariant j.

    Input: supersingular j invariant j
    Output: - endos, a list of three isogenies psi_i: E -> E^{(p)}
            - G, the gram matrix of the basis 1,pi*psi_1,pi*psi_2,pi*psi_3
                where pi: E^{(p)} -> E is the Frobenius
            - B, a quaternion algebra H(a,b) with basis 1,i,j,ij such that End^0(E) = H(a,b)
            - M, the matrix corresponding to the map sending 1, i , j , ij to
                1, pi*psi1, pi*psi2, pi*psi3
            - Minv, the inverse of M
            - basis_matrix, whose rows give basis elements for the order
                generated by the image of 1 and endos in B
    """
    ell1 = 2
    path1 = random_walks_to_Fp(j, ell1)
    psi1 = isogeny_to_Ep(path1, ell1)
    print(f"Found {ell1}-isogeny chain to Ep of length {len(psi1)}")
    ell2 = 2
    path2 = random_walks_to_Fp(j, ell2)
    psi2 = isogeny_to_Ep(path2, ell2)
    print(f"Found {ell2}-isogeny chain to Ep of length {len(psi2)}")
    ell3 = 3
    path3 = random_walks_to_Fp(j, ell3)
    psi3 = isogeny_to_Ep(path3, ell3)
    print(f"Found {ell3}-isogeny chain to Ep of length {len(psi3)}")
    psi1_dual = [phi.dual() for phi in reversed(psi1)]
    psi2_dual = [phi.dual() for phi in reversed(psi2)]
    psi3_dual = [phi.dual() for phi in reversed(psi3)]
    # Given endomorphisms alpha, beta, define <alpha,beta> = (1/2) * Trd(alpha*beta_conjugate).
    # If alpha = frob*phi and beta = frob*psi where phi,psi: E to Ep are isogenies, then
    # <alpha, beta> = (1/2) * p * Trd(psi_hat*phi)
    start = cputime()
    t = generalized_Schoof(psi1 + psi2_dual, use_kerpols = True,verbose=verbose)
    G12 = p * t
    print(f"<frob*psi1, frob*psi2> = {G12}")
    t = generalized_Schoof(psi3 + psi1_dual, use_kerpols = True,verbose=verbose)
    G13 = p * t
    print(f"<frob*psi1, frob*psi3> = {G13}")
    t = generalized_Schoof(psi2 + psi3_dual, use_kerpols = True,verbose=verbose)
    G23 = p * t
    print(f"<frob*psi2, frob*psi3> = {G23}")
    print(f"3 traces computed in {(cputime()-start):0.2f} seconds")
    Nrd_frobpsi1 = p * (ell1**(len(psi1)))
    Nrd_frobpsi2 = p * (ell2**(len(psi2)))
    Nrd_frobpsi3 = p * (ell3**(len(psi3)))
    # make the Gram matrix
    G = Matrix([
            [2, 0, 0, 0],
            [0, 2*Nrd_frobpsi1, G12, G13],
            [0, G12, 2*Nrd_frobpsi2, G23],
            [0, G13, G23, 2*Nrd_frobpsi3]
        ])
    if G.det() == 0:
        # TODO
        raise ValueError("Endos do not generate an order")
    basis = [
        vector([1, 0, 0 ,0]), # 1
        vector([0, 1, 0, 0]), # frob*psi1
        vector([0, 0, 1, 0]),# frob*psi2
        vector([0, 0, 0, 1]) # frob*psi3
    ]
    orthogonal_basis = my_gram_schmidt(G,basis)
    # get a, b so that H(a,b) = End(E) x Q
    # if b1 = orthogonal_basis[1], then b1^2 = -(1/2)*inner_product(G,b1,b1)
    b1 = orthogonal_basis[1]
    b2 = orthogonal_basis[2]
    b3 = orthogonal_basis[3]
    a = (-1/2) * inner_product(G, b1, b1) # -a = <b1,b1> = tr(b1,b1_conj) = tr(norm(b1)) = norm(b1) = b1*b1_conj = -b1^2
    orthogonal_basis[1], a = b1 * a.denominator(), a * a.denominator()**2
    b = (-1/2) * inner_product(G, b2, b2) # b = b2^2
    orthogonal_basis[2], b = b2 * b.denominator(), b * b.denominator()**2
    orthogonal_basis[3] = (2*a*b / inner_product(G,b3,b3))^(1/2) * b3
    # M is the matrix sending 1, i , j , ij to 1, frob*psi1, frob*psi2, frob*psi3
    M = Matrix(orthogonal_basis)
    Minv = M.inverse()
    # B is the quaternion algebra with basis i,j such that i^2=a, j^2=b.
    B = QuaternionAlgebra(a,b)
    basis_matrix = identity_matrix(Integers(), 4)
    # compute image of order O in B
    quat_basis =  [B(r * Minv) for r in basis_matrix.rows()]
    # compute product of all basis elements to get generating set for an order
    new_gens = [vector(quat_basis[i] * quat_basis[j]) for i in range(1,4) for j in range(i,4)]
    # enlarge lattice with new generators
    basis_matrix = augment_lattice(basis_matrix, new_gens, B, M, Minv)
    return [psi1, psi2, psi3], G, B, M, Minv, basis_matrix

def embed_inseparable_endo(gamma, B, G, Minv, endos, verbose = False):
    """Returns the image of gamma in B with respect to the orthogonal basis computed from endos=[alpha, beta]"""
    psi1 = endos[0]
    psi2 = endos[1]
    psi3 = endos[2]
    p = psi1[0].domain().base().characteristic()
    gamma_hat = [phi.dual() for phi in reversed(gamma)]
    G_0_gamma = 0
    start = cputime()
    t = generalized_Schoof(psi1 + gamma_hat, use_kerpols = True,verbose=verbose)
    G_1_gamma = p * t
    t = generalized_Schoof(psi2 + gamma_hat, use_kerpols = True,verbose=verbose)
    G_2_gamma = p * t
    t = generalized_Schoof(psi3 + gamma_hat, use_kerpols = True,verbose=verbose)
    G_3_gamma = p * t
    # print(f"4 traces computed in {(cputime()-start):0.2f} seconds")
    inner_products = vector((G_0_gamma, G_1_gamma, G_2_gamma, G_3_gamma))
    # express gamma in terms of 1, frob*psi1, frob*psi2, frob*psi3
    x = G.solve_right(inner_products)
    # express gamma in terms of quaternionic basis:
    quat_gamma = B(x * Minv)
    return quat_gamma

def endo_ring_from_inseparables(j):
    p = j.parent().characteristic()
    endos, G, B, M, Minv, basis_matrix = inseparable_suborder(j)
    discrd = (basis_matrix.transpose()*(G)*basis_matrix).det().sqrt()
    count = 3
    ell = 3
    print(f"discrd(O) = {discrd.factor()}")
    # Compute new inseparable endomorphisms and adjoin them until we compute Z+Frob*Hom(E^p,E), which has index p in EndE
    while discrd != p^2:
        path = random_walks_to_Fp(j, ell)
        gamma = isogeny_to_Ep(path, ell)
        print(f"Found {ell}-isogeny chain to Ep of length {len(gamma)}")
        endos.append(gamma)
        quat_gamma = embed_inseparable_endo(gamma, B, G, Minv, endos)
        # compute image of order O in B
        quat_basis =  [B(r * Minv) for r in basis_matrix.rows()]
        # compute product of images of basis elements for O and gamma in B
        new_gens = [vector(quat_basis[i] * quat_gamma) for i in range(4)]
        # enlarge O with new generators
        basis_matrix = augment_lattice(basis_matrix, new_gens, B, M, Minv)
        discrd = (basis_matrix.transpose()*(G)*basis_matrix).det().sqrt()
        count = count + 1
        print(f"discrd(O) = {discrd.factor()}")
        ell = next_prime(ell)
    print(f"End(E) generated with {count} inseparable endomorphisms")
    O = B.quaternion_order([B(r*Minv) for r in basis_matrix.rows()])
    O_basis = O.basis()
    print("basis of Z+P:")
    for i in range(4):
        print(f"\t {O_basis[i]}")
    basis_matrix = p_saturated_order(basis_matrix, G, p)
    O = B.quaternion_order([B(r*M.inverse()) for r in basis_matrix.rows()])
    O_basis = O.basis()
    print("basis of End(E):")
    for i in range(4):
        print(f"\t {O_basis[i]}")
    return O, G, M, basis_matrix, endos

def augment_lattice(basis_matrix, new_generators, B, M, Minv):
    generators = Matrix([v for v in basis_matrix.rows()] + [vector(g)*M for g in new_generators])
    denom = lcm([_.denominator() for _ in generators.list()])
    # clear denominators of the coefficients of generators
    generators = Matrix(ZZ, denom*generators)
    # compute echelon form of generators to get a basis
    reduced_generators = generators.hermite_form()
    # print(reduced_generators)
    # get top 4 rows to get the basis
    reduced_generators = Matrix(4, reduced_generators.rows()[:4])
    # divide through by denom to get our basis matrix
    basis_matrix = (denom)^(-1) * reduced_generators
    return basis_matrix

def p_saturated_order(basis_matrix, G, p):
    """
    Algorithm 3.12 and Algorithm 7.9 in John's paper
    Input: generators of O=Z+Frob*Hom(E^p,E)
    Output: p-saturated order which contains O=Z+Frob*Hom(E^p,E)
    """
    basis_matrix_copy=[basis_matrix[i] for i in range(4)] #I need a copy for adding the new generators to the previous ones
    basis_matrix2=[basis_matrix[i] for i in range(4)]
    #Algorithm 3.12 for getting a normalized basis for O
    for m in range(4):
        min_valuation=+Infinity
        for  i in range(m,4):
            for  j in range (i,4):
                inn=inner_product(G, basis_matrix2[i], basis_matrix2[j])
                if inn.valuation(p)<min_valuation:
                    min_valuation=inn.valuation(p)
                    i0=i
                    j0=j
                    if i0==j0:
                        basis_matrix2[m]=basis_matrix[i0]
                    else:
                        basis_matrix2[m]=basis_matrix[i0]+basis_matrix[j0]
                    for k in range(m+1,4):
                        basis_matrix2[k]=basis_matrix[k]-(inner_product(G, basis_matrix2[m], basis_matrix[k]))/(inner_product(G, basis_matrix2[m], basis_matrix2[m]))*basis_matrix2[m]
                        basis_matrix[k]=basis_matrix2[k]
    for i in range(4):
        c=lcm(_.denominator() for _ in basis_matrix2[i])
        basis_matrix2[i]=[c*b for b in basis_matrix2[i]]
        e=(inner_product(G, vector(basis_matrix2[i]), vector(basis_matrix2[i]))).valuation(p)
        basis_matrix2[i]=[(p^(-floor(e/2)))*b for b in basis_matrix2[i]]
    #compute echelon form to find a basis
    generators = Matrix([v for v in basis_matrix_copy] + [v for v in basis_matrix2])
    denom = lcm([_.denominator() for _ in generators.list()])
    generators = Matrix(ZZ, denom*generators)
    reduced_generators = generators.hermite_form()
    reduced_generators = Matrix(4, reduced_generators.rows()[:4])
    basis_matrix = (denom)^(-1) * reduced_generators
    # Compute a basis of the maximal order with respect to the orthogonal basis
    return basis_matrix
