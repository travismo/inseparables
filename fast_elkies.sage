def get_neighbors(E, ell):
    Phi_inst = inst_mod_poly(ell, E.j_invariant())
    neighbors = Phi_inst.roots()
    return neighbors


# Gives the M'th modular polynomial Phi(X,Y) instantiated at Y=j.
#
# Current implementation loads the polynomial from the Kohel database and evaluates it
#
# Inputs:
#     ell: A positive integer
#     j: An element of the finite field F of size p^2
# Outputs:
#     Phi: A polynomial in F[x] of degree ell+1
#
# Runs in O(ell^2 M(log p))
def inst_mod_poly(ell, j):
    FF = j.parent()
    R.<x> = FF[]
    Phi = ClassicalModularPolynomialDatabase()[ell](x,j)
    return Phi


# Computes an elliptic curve E~ with the given j-invariant such that there exists an ell isogeny from E to E~
#
# If E has an ell-isogeny to an elliptic curve E~ with j-invariant j_tilde, then this function will return the coefficients A_tilde and B_tilde such that E~ is defined by y^2 = x^3 + A_tilde*x + B_tilde, as well as the sum of the x-coordinates of the kernel of the ell-isogeny.
#
# Inputs:
#     E: An elliptic curve defined over the finite field F of size p^2. Must have j(E) not in {0, 1728}
#     j_tilde: An element of F. Must have that (j(E), j_tilde) is a single root of the ell'th modular polynomial
#     ell: A positive integer with ell + 2 < p
# Outputs:
#     A_tilde, B_tilde, sigma: Elements of F
#
# Source: [2]
#
# Runs in O(ell^2 M(log p) + M(log p) llog p)
def get_ABsigma(E, j_tilde, ell):
    # Set-up
    j = E.j_invariant()
    A = E.a_invariants()[3]
    B = E.a_invariants()[4]
    F = E.base_field()
    FXY.<X,Y> = PolynomialRing(F)

    # Compute all deriviatives and partial derivatives of the ell'th modular polynomial at (j, j_tilde)
    # Takes O(ell^2 M(log p))
    PHI = ClassicalModularPolynomialDatabase()
    Phi_ell = PHI[ell]
    Phi_ell = FXY(Phi_ell)
    Phi_X = Phi_ell.derivative(X)
    Phi_Y = Phi_ell.derivative(Y)
    Phi_XX = Phi_X.derivative(X)(j,j_tilde)
    Phi_YY = Phi_Y.derivative(Y)(j,j_tilde)
    Phi_XY = Phi_X.derivative(Y)(j,j_tilde)
    Phi_X = Phi_X(j,j_tilde)
    Phi_Y = Phi_Y(j,j_tilde)

    # Recover the coefficients of E~
    # Takes O(M(log p) llog p)
    m = 18*B/A
    j_prime = m*j
    k = j_prime / (1728-j)
    j_tilde_prime = -j_prime * Phi_X / (ell*Phi_Y)
    m_tilde = j_tilde_prime / j_tilde
    k_tilde = j_tilde_prime / (1728 - j_tilde)
    A_tilde = ell^4 * m_tilde * k_tilde / 48
    B_tilde = ell^6 * m_tilde^2 * k_tilde / 864

    # Recover the sum of the abscissas of the kernel
    # Takes O(M(log p) llog p)
    r = -(j_prime^2*Phi_XX
          + 2*ell*j_prime*j_tilde_prime*Phi_XY
          + ell^2*j_tilde_prime^2*Phi_YY) / (j_prime*Phi_X)
    p1 = ell*(r/2 + (k-ell*k_tilde)/4 + (ell*m_tilde - m)/3)

    return A_tilde, B_tilde, p1
def fastElkiesOdd(A, B, A_tilde, B_tilde, ell, p1):
    K = A.parent()
    R.<x> = K[]
    R2.<z,t> = K['z,t']

    # Step 1: Compute C(x)
    # This step takes O(M(ell log p) + M(log p) llog p)
    C = reciprocal(B*x^6 + A*x^4 + 1, ell)

    # Step 2: Compute S(x) mod x^2*ell and T(x) mod x^ell
    # Takes O(M(ell log p) + ell M(log p) llog p)
    G = C(z) * (1 + A_tilde*t^4 + B_tilde*t^6)
    S = first_order_NL(G, 0, 1, ell+1)
    S_coeff = S.list()
    while len(S_coeff) < ell + 1:
        S_coeff.append(0)
    T_coeff = [S_coeff[i*2 + 1] for i in range((ell+1)//2)]
    T = sum([x^i * T_coeff[i] for i in range((ell+1)//2)])
    # Step 3: Compute U(x)
    # Takes O(M(ell log p) + M(log p) llog p)
    U = reciprocal(T.power_trunc(2, (ell+1)/2), ((ell+1)//2))
    # Step 4: Deduce coefficients h_i
    # Takes O(1)
    h = U.list()[1:]
    while len(h) < ((ell-1)/2):
        h.append(0)
    # Step 5: Compute D(x)
    # Takes O(M(ell log p) + ell M(log p) llog p)
    g = get_denom_odd(h, A, B, ell, p1/2)
    return R(g)


# Recovers the kernel polynomial of the isogeny phi = (phi_x, phi_y) from its Laurent expansion using power series manipulations
#
# Let E be the elliptic curve defined by y^2 = x^3 + Ax + B, and let phi = (phi_x, phi_y) be a degree ell isogeny with domain E. Write phi_x = N(x)/D(x) where since ell is odd, D(x) = g(x)^2. Let N(x)/(g(x)^2) have Laurent expansion at infinity x + h[1]/x + h[2]/x^2 + ... + h[(ell-1)/2]/x^((ell-1)/2) + ... . This function returns g.
#
# Inputs:
#     h: A list of (ell-1)/2 elements of the finite field F with p^2 elements
#     A, B, q1: Elements of F
#     ell: An odd positive integer with ell > 3
# Outputs:
#     g: A degree (ell-1)/2 polynomial in F[x]
#
# Source: [1]
#
# Runs in O(M(ell log p) + ell M(log p) llog p)
def get_denom_odd(h, A, B, ell, q1):
    F = A.parent()
    # Step 1: Use the recurrence relation to obtain the first (ell+1)/2 power sums
    # This step takes O(ell M(log p) llog p + ell M(log p)) time
    q = [0] * ((ell+1)//2)
    # q0 is the degree of g
    q[0] = F((ell-1)/2)
    q[1] = q1
    for i in range(1, ((ell-1)//2)):
        q[i+1] = h[i]/(4*i+2) - F((2*i-1)/(2*i+1))*A*q[i-1] - F((2*i-2)/(2*i+1))*B*q[i-2]

    # Step 2: Recover g(x) from its power sums
    # This step takes O(ell M(log p) llog p + M(ell log p))
    coeffs = [-1*q[i]/i for i in range(1,((ell+1)//2))]
    R.<z> = PolynomialRing(F)
    f = sum([F(coeffs[i]) * z^(i+1) for i in range(((ell-1)//2))])
    g = poly_exp(f,(ell+1)/2).reverse()

    return g


# Calculates the exponent of f to n terms
#
# Inputs:
#     f: An element of F[x] satisfying f(0)=0, where F is the finite field of size p^2
#     n: A positive integer such that n < p
# Outputs:
#     g: A degree n-1 univariate polynomial over F whose coefficients agree with the first n terms of exp(f)
#
# Runs in O(n M(log p) llog p + M(n log p))
#
# Source: [2]
def poly_exp(f,n):
    R = f.parent()
    if f == 0:
        return R(1)
    g = R(1)
    i = 1
    while i < n:
        i = 2*i
        h = 1 + f - poly_log(g, i)
        g = g.multiplication_trunc(h, i)
    return g.truncate(n)


# Calculats the logarithm of f to n terms
#
# Inputs:
#     f: An element of F[x] satisfying f(0)=1, where F is the finite field of size p^2
#     n: A positive integer such that n < p
# Outputs:
#     log_f: The logarithm of f in F[[x]] truncated to n terms
#
# Runs in O(n M(log p) llog p + M(n log p))
#
# Source [2]
def poly_log(f, n):
    R = f.parent()
    x = R.gen()

    f_prime = f.derivative()
    a = reciprocal(f, n-1)
    log_f = f_prime.multiplication_trunc(a, n-1)
    log_f = log_f.integral()
    return log_f


# Computes the inverse of f mod x^n using Newton iteration
#
# Inputs:
#     f: An element of F[x] with f(0) nonzero, where F is the finite field of size p^2
#     n: A positive integer
# Outputs:
#     f^-1: The degree n-1 polynomial in F[x] such that x^n divides (f*f^-1) - 1
#
# Runs in O(M(n log p) + M(log p) llog p)
#
# Source: [4]
def reciprocal(f, n):
    R = f.parent()
    h = R(f.coefficients()[0]^(-1))
    i = 1
    while i < n:
        i = 2*i
        h = (h*(2-f*h)).truncate(i)
    return h.truncate(n)


# Solves a first order non-linear differential equation of the form (f'(z))^2 = G(z,f)
#
# Inputs:
#     G: A polynomial of total degree d over the finite field F of size p^2 in two variables
#     alpha: An element of F
#     beta: A nonzero element of F
#     n: A positive integer
# Outputs:
#     f: A degree (n-1) polynomial over F whose first n terms agree with the solution to (f'(z))^2 = G(z,f) with initial conditions f(0) = alpha and f'(0) = beta
#
# Source: [3]
#
# Runs in O(M(n log p) + n M(log p) llog p)
def first_order_NL(G, alpha, beta, n):
    t = G.parent().gens()[1]
    K = G.base_ring()
    R.<z> = PolynomialRing(K)

    Gt = G.derivative(t)
    f1 = alpha + beta*z
    f2 = 0
    s = 2
    while s < n:
        a = 2*f1.derivative(z)
        b = -1*Gt(z, f1)
        c = G(z, f1) - (f1.derivative(z))^2
        f2 = first_order( a, b, c, alpha, 2*s-1)
        f1 = f1 + f2
        s = 2*s - 1
    return f1.truncate(n)


# Solves a first order linear differential equation with polynomial coefficients
#
# Inputs:
#     a, b, c: Elements of F[x] where F is the finite field of size p^2. Requires a(0) non-zero.
#     alpha: An element of F
#     n: A positive integer such that n < p
# Outputs:
#     f: A univariate polynomial of degree (n-1) which agrees in the first n terms with the solution to the first order linear differential equation af' + bf = c with initial condition f(0) = alpha
#
# Source: [3]
#
# Runs in O( M(n log p) + n M(log p) llog p)
def first_order(a, b, c, alpha, n):
    z = a.parent().gens()[0]

    a_inv = reciprocal(a, n-1)
    B = (b * a_inv).truncate(n-1)
    C = (c * a_inv).truncate(n-1)
    B_int = B.integral()
    J = poly_exp(B_int, n)
    f = reciprocal(J, n) * (alpha + (C*J).integral())
    return f

def mydual(phi):
    # Set-up
    # TODO: implement mydual for non-normalized isogenies.
    E0 = phi.domain()
    d = phi.kernel_polynomial().degree()
    ell = phi.degree()
    j0 = E0.j_invariant()
    E1 = phi.codomain()
    j1 = E1.j_invariant()
    A0 = E0.a4()
    B0 = E0.a6()
    A1 = E1.a4()
    B1 = E1.a6()
    m_old = 18*B0 / A0
    jprimeold = m_old * j0
    kold = jprimeold / (1728-j0)
    mtildeold = 18 * (B1/(ell^2 * A1))
    jtildeprimeold = mtildeold * j1
    ktildeold = jtildeprimeold / (1728 - j1)
    phix_over_phiy = -(jtildeprimeold / jprimeold) * ell
    sigma = phi.kernel_polynomial()[d-1]
    p1 = -2*sigma
    r = 2 * (p1/ell - (kold-ell*ktildeold)/4 -(ell*mtildeold-m_old)/3)
    rnew = -ell*r
    mnew = 18*B1 / A1
    jprimenew = mnew * j1
    knew = jprimenew / (1728-j1)
    mtildenew = m_old
    jtildeprimenew = jprimeold
    ktildenew = kold
    p1new = ell * (rnew/2 + (knew - ell*ktildenew)/4 + (ell*mtildenew - mnew)/3)
    h = fastElkiesOdd(A1,B1,ell**4 * A0, ell**6 * B0,ell,p1new)
    phidual = EllipticCurveIsogeny(E1, h)
    assert phidual.codomain().j_invariant() == j0
    isoms = phidual.codomain().isomorphisms(E)
    psi = isoms[0] if isoms[0].u == phi.degree() else isoms[1]
    phidual = psi*phidual
    return phidual
