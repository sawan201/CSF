#   load("DeltaReconstruction.sage")
#   T2 = reconstruct(X)        # X = X_T only. Needs Theorem 1: Delta(T) > m. Holds when n >= m^2 + 2.
#   T2 = reconstruct(X, SB)    # SB = S_{B,b} in QQ[z,y] for a principal branch (B,b). Any T.
#
# X can be in any basis of Sym; it is converted to the power-sum basis.
# SB is the only information about the branch that is used. If you have the
# branch itself, root_poly(B, b) computes SB. If you don't, principal_branch_polys(X)
# finds it from X_T when Delta(T) > m.

R = PolynomialRing(QQ, 'z,y')
z, y = R.gens()
p = SymmetricFunctions(QQ).p()


def H_from_csf(X):
    """H_T(z,y) from X_T, via equations (1) and (2)."""
    X = p(X)
    if not X.is_homogeneous():
        raise ValueError("X is not homogeneous")
    n = X.degree()
    uu = {la: (-1)**(n - len(la)) * c for la, c in X.monomial_coefficients().items()}
    H = R.zero()
    for r in range(1, n + 1):
        for la, ul in uu.items():
            m = list(la).count(r)
            if m:
                H += ul * m * (1 - y)**(n - len(la) - r + 1) * y**(len(la) - 1) * z**r
    return H


def root_poly(D, r, parent=None):
    """S_{D,r} = y + z * prod S_{D_j,r_j} over the children r_j of r."""
    prod = R.one()
    for c in D.neighbors(r):
        if c != parent:
            prod *= root_poly(D, c, r)
    return y + z * prod


def quo_z(F, G):
    """Quotient and remainder of F by G in Q[y][z]. G needs leading coefficient 1 in z."""
    Gz = G.polynomial(z)
    if Gz.leading_coefficient() != 1:
        raise ValueError("divisor is not monic in z")
    q, rem = F.polynomial(z).quo_rem(Gz)
    return R(q), R(rem)


def monic_factors(P):
    """Irreducible factors of P in Q[z,y], scaled to leading coefficient 1 in z, with multiplicity."""
    out = []
    for f, e in P.factor():
        lc = f.polynomial(z).leading_coefficient()
        if not lc.is_constant():
            raise ValueError("factor %s is not monic in z up to a constant" % f)
        out += [f / QQ(lc)] * e
    return out


def rooted_tree(F):
    """Algorithm 2: rooted tree (D, r) with S_{D,r} = F. Returns (Graph, root)."""
    G, rem = (F - y).quo_rem(z)
    if rem != 0:
        raise ValueError("F - y is not divisible by z")
    D = Graph({0: []})
    if G == 1:
        return D, 0
    nxt = 1
    for H in monic_factors(G):
        E, h = rooted_tree(H)
        E.relabel({x: x + nxt for x in E.vertices(sort=False)})
        D.add_vertices(E.vertices(sort=False))
        D.add_edges(E.edges(sort=False))
        D.add_edge(0, h + nxt)
        nxt += E.order()
    return D, 0


def invariants(H):
    """
    (n, Delta, m) from H_T (Theorem 1, Step 1).
    n = deg_z H, Delta = deg_y [z^1]H, m = max{s <= n/2 : [z^s y]H != 0}.
    """
    n = H.degree(z)
    Delta = H.coefficient({z: 1}).degree(y)
    m = max(s for s in range(1, n // 2 + 1) if H.monomial_coefficient(z**s * y) != 0)
    return n, Delta, m


def centroid_part(H, m):
    """
    H_T^+, the terms h z^i y^j of H with i + j >= m + 2.
    When Delta > m these come from exactly the connected sets W containing the centroid v (Theorem 1, Step 3).
    """
    return R.sum([c * mon for c, mon in H if mon.degree(z) + mon.degree(y) >= m + 2])


def centroid_branch_product(X, H=None):
    """
    Theorem 1 as an algorithm. Returns prod_i S_{D_i,r_i} over all branches (D_i,r_i) at the centroid v,
    computed from X_T. Needs Delta > m, and then the product is A = H_T^+ / z (Step 4).
    """
    if H is None:
        H = H_from_csf(X)
    n, Delta, m = invariants(H)
    if Delta <= m:
        raise ValueError("Delta = %s <= m = %s, so Theorem 1 does not apply; pass SB" % (Delta, m))
    A, rem = centroid_part(H, m).quo_rem(z)
    if rem != 0:
        raise ValueError("X is not the chromatic symmetric function of a tree")
    if A.subs(z=0) != y**Delta:
        raise ValueError("the branch product does not have constant term y^Delta")
    return A


def principal_branch_polys(X, H=None):
    """S_{B,b} for every principal branch (B,b), with multiplicity, from X_T by Theorem 1 (Step 5)."""
    if H is None:
        H = H_from_csf(X)
    n, Delta, m = invariants(H)
    return [f for f in monic_factors(centroid_branch_product(X, H)) if f.degree(z) == m]


def whole_tree_poly(X, SB, H=None):
    """S_{T,v} = y + z S_{B,b} Q, where Q = quo_z(H_T, z S_{B,b})."""
    SB = R(SB)
    if H is None:
        H = H_from_csf(X)
    Q, L = quo_z(H, z * SB)
    if L.degree(z) > SB.degree(z):
        raise ValueError("remainder has z-degree > c, so B is not a largest branch")
    return y + z * SB * Q

#MAIN ALGORITHM
def reconstruct(X, SB=None, verbose=False):
    """
    Algorithm 1: a tree isomorphic to T from X_T and S_{B,b}.
    If SB is not given it is taken from principal_branch_polys(X), which needs Delta(T) > m.
    """
    H = H_from_csf(X)
    if SB is None:
        SB = principal_branch_polys(X, H)[0]
    S = whole_tree_poly(X, SB, H)
    if verbose:
        print("S_{B,b} =", SB)
        print("S_{T,v} - y = z *", ' * '.join('(%s)' % f for f in monic_factors((S - y) // z)))
    D, r = rooted_tree(S)
    return D

complete = reconstruct


def principal_branch(T):
    """A principal branch (B, b) of T, found from T itself. Only used by check."""
    best = None
    for v in T:
        Tv = T.copy()
        Tv.delete_vertex(v)
        B = max(Tv.connected_components_subgraphs(), key=lambda C: C.order())
        if best is None or B.order() < best[0].order():
            best = (B, v)
    B, c = best
    b = next(u for u in T.neighbors(c) if B.has_vertex(u))
    return B, b


def branch_product_from_tree(T):
    """prod_i S_{D_i,r_i} over all branches at the centroid of the principal branch, found from T itself. Only used by check."""
    B, b = principal_branch(T)
    c = next(u for u in T.neighbors(b) if not B.has_vertex(u))
    return R.prod([root_poly(T, r, c) for r in T.neighbors(c)])


def check(nmax):
    """
    Every tree with 3 <= n <= nmax: reconstruct(X, SB) with the true SB, and, when Delta > m,
    the branch product, the principal branch polynomials and reconstruct(X) from X_T alone.
    """
    for n in range(3, nmax + 1):
        total = alone = 0
        for T in graphs.trees(n):
            total += 1
            X = T.chromatic_symmetric_function()
            B, b = principal_branch(T)
            SB = root_poly(B, b)
            assert reconstruct(X, SB).is_isomorphic(T)
            H = H_from_csf(X)
            n_, Delta, m = invariants(H)
            assert Delta == max(T.degree()) and m == B.order()
            if Delta <= m:
                continue
            alone += 1
            assert centroid_branch_product(X, H) == branch_product_from_tree(T)
            assert SB in principal_branch_polys(X, H)
            assert reconstruct(X).is_isomorphic(T)
        print("n = %s: %s trees, rebuilt from X_T alone %s" % (n, total, alone))
