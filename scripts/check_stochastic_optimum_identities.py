#!/usr/bin/env python3
"""Expand the polynomial identities used in docs/binary-stochastic-optimum.md.

Requires sympy. Every check is an exact symbolic expansion or an exact
rational evaluation; nothing here is a proof step, and nothing is numerical.
Run from anywhere:

    python scripts/check_stochastic_optimum_identities.py
"""

from __future__ import annotations

import sys

try:
    from sympy import Rational, expand, factor, integrate, simplify, sqrt, symbols
except ImportError:  # pragma: no cover
    sys.exit("sympy is required: pip install sympy")


def main() -> int:
    a, b, c, d, x, u = symbols("a b c d x u", positive=True)
    failures = []

    def check(label, ok):
        print(f"{'ok  ' if ok else 'FAIL'} {label}")
        if not ok:
            failures.append(label)

    # Marginals and the quantities of (4.1), on a normalized law.
    mu0, mu1 = a + b, c + d
    nu0, nu1 = a + c, b + d
    A = nu0**2 - a**3 / mu0**2 - c**3 / mu1**2
    E = nu1**2 - b**3 / mu0**2 - d**3 / mu1**2
    V = (a * d - b * c) ** 2 / (mu0 * mu1)
    M = nu0 * nu1
    normalize = {d: 1 - a - b - c}

    # (4.6): A + E = M - 3V.
    check("(4.6) A + E = M - 3V", simplify(((A + E) - (M - 3 * V)).subs(normalize)) == 0)

    # (4.4) and (4.5): P = (x-1)^2 Q.
    P = (nu0 * x**3 + nu1) ** 2 - (a * x**2 + b) ** 3 / mu0**2 - (c * x**2 + d) ** 3 / mu1**2
    Q = A * x**4 + 2 * A * x**3 - 3 * V * x**2 + 2 * E * x + E
    check("(4.5) P = (x-1)^2 Q", simplify((P - (x - 1) ** 2 * Q).subs(normalize)) == 0)

    # (5.1): Q = A (x-t)^2 [x^2 + 2(1+t)x + t] + 3 (sigma - V) x^2 with E = A t^3.
    t, As, Es, Vs = symbols("t A E V", positive=True)
    Qs = As * x**4 + 2 * As * x**3 - 3 * Vs * x**2 + 2 * Es * x + Es
    sigma = As * t * (t + 1)
    rhs = As * (x - t) ** 2 * (x**2 + 2 * (1 + t) * x + t) + 3 * (sigma - Vs) * x**2
    check("(5.1) quartic factorization", expand((Qs - rhs).subs(Es, As * t**3)) == 0)
    check("sigma^3 = A E (A + E + 3 sigma)",
          expand(sigma**3 - As * (As * t**3) * (As + As * t**3 + 3 * sigma)) == 0)
    G = As * (x**2 + 2 * x) + Es * (2 / x + 1 / x**2) - 3 * Vs
    check("G' = 2(x+1)(A - E/x^3)", simplify(G.diff(x) - 2 * (x + 1) * (As - Es / x**3)) == 0)
    check("G(t) = 3(sigma - V)", simplify(G.subs(x, t).subs(Es, As * t**3) - 3 * (sigma - Vs)) == 0)

    # (6.2): the norm margin factors, as an identity of polynomials in four cells.
    z = a + b + c + d
    X, Y = a * d, b * c
    Lam = a * b * c + a * b * d + a * c * d + b * c * d
    An = nu0**2 * mu0**2 * mu1**2 - z * (a**3 * mu1**2 + c**3 * mu0**2)
    En = nu1**2 * mu0**2 * mu1**2 - z * (b**3 * mu1**2 + d**3 * mu0**2)
    lhs = An * En * nu0 * nu1 - (X - Y) ** 6 * mu0 * mu1
    rhs = z**2 * (Lam**2 - X * (X - Y) ** 2) * (Lam**2 - Y * (X - Y) ** 2)
    check("(6.2) unnormalized polynomial identity", expand(lhs - rhs) == 0)
    rhs_n = (Lam**2 - X * (X - Y) ** 2) * (Lam**2 - Y * (X - Y) ** 2) / (mu0**4 * mu1**4)
    check("(6.2) normalized", simplify((A * E * M - V**3 - rhs_n).subs(normalize)) == 0)

    # (6.3): Lam - u (X - Y) = -f(u) when u^2 = a d.
    v, w, s = b + c, b * c, a + d
    f = u**3 - v * u**2 - w * u - w * s
    check("(6.3) Lam - u(X-Y) = -f(u)", simplify((Lam - u * (X - Y) + f).subs(a, u**2 / d)) == 0)

    # Lemma 6.4: the diagonal-swap tangent identity.
    alpha, beta = symbols("alpha beta", positive=True)
    uu = alpha * beta
    lhs = alpha**3 * (beta**2 + b) * (beta**2 + c) - beta**3 * (alpha**2 + b) * (alpha**2 + c)
    rhs = (alpha - beta) * (-(uu**3) + (b + c) * uu**2 + b * c * (alpha**2 + beta**2 + uu))
    check("Lemma 6.4 swap identity", expand(lhs - rhs) == 0)
    # Lemma 6.4, a = d: f(a) = 0 is 3bc = a(a-b-c); then mu0 mu1 = nu0 nu1 = 2(ad - bc).
    fa = f.subs(u, a).subs(d, a)
    check("Lemma 6.4 a=d reduction", expand(fa - a * (a * (a - b - c) - 3 * b * c)) == 0)
    check("Lemma 6.4 a=d marginal product",
          expand(((a + b) * (a + c) - 2 * (a * a - b * c)) - (a * (b + c) + 3 * b * c - a * a)) == 0)

    # Lemma 6.5: mixing a diagonal swap pair.
    lam, Ap, Dp = symbols("lambda A' D'", positive=True)
    p00 = lam * Ap + (1 - lam) * Dp
    p11 = lam * Dp + (1 - lam) * Ap
    check("Lemma 6.5 mixing identity",
          expand(p00 * p11 - (Ap * Dp + lam * (1 - lam) * (Ap - Dp) ** 2)) == 0)

    # Lemma 6.1: f(v) = -w when s = 1 - v.
    check("Lemma 6.1 f(v) = -w", simplify(f.subs(u, v).subs(a, 1 - v - d) + w) == 0)

    # Example 4.10 and 7.3: uniform marginals.
    r = symbols("r")
    uni = {a: (1 + r) / 4, b: (1 - r) / 4, c: (1 - r) / 4, d: (1 + r) / 4}
    check("Example 4.10 A", simplify(A.subs(uni) - (1 - 3 * r**2) / 8) == 0)
    check("Example 4.10 V, M", simplify(V.subs(uni) - r**2 / 4) == 0 and simplify(M.subs(uni) - Rational(1, 4)) == 0)
    check("Example 4.10 margin",
          simplify((A * E * M - V**3).subs(uni) - (1 - r**2) ** 2 * (1 - 4 * r**2) / 256) == 0)
    check("Example 7.3 f at sqrt(ad)",
          simplify(f.subs(u, (1 + r) / 4).subs(uni) - (1 + r) * (2 * r - 1) / 16) == 0)

    # Examples 4.11, 4.12, 7.4, 7.5: exact rational evaluations.
    def at(law):
        return dict(zip((a, b, c, d), law))

    tri = at((Rational(1, 3), Rational(1, 3), Rational(1, 3), 0))
    check("Example 4.11 values",
          (A.subs(tri), E.subs(tri), V.subs(tri), M.subs(tri)) == (Rational(1, 36), Rational(1, 36), Rational(1, 18), Rational(2, 9))
          and (A * E * M - V**3).subs(tri) == 0)
    full = at((Rational(1, 2), Rational(1, 5), Rational(1, 10), Rational(1, 5)))
    check("Example 4.12 values",
          (A.subs(full), E.subs(full), V.subs(full), M.subs(full)) == (Rational(1034, 11025), Rational(604, 11025), Rational(16, 525), Rational(6, 25))
          and (A * E * M - V**3).subs(full) == Rational(1808, 1500625))
    ex74 = at((Rational(3, 5), Rational(1, 20), Rational(1, 20), Rational(3, 10)))
    f74 = f.subs(ex74)
    check("Example 7.4 f(sqrt(ad))",
          simplify(f74.subs(u, sqrt(Rational(9, 50))) - (Rational(71, 400) * sqrt(Rational(9, 50)) - Rational(81, 4000))) == 0
          and (a * d - b * c).subs(ex74) == Rational(71, 400))
    f75 = f.subs(full)
    check("Example 7.5 f(sqrt(ad))",
          simplify(f75.subs(u, 1 / sqrt(10)) - (Rational(2, 25) / sqrt(10) - Rational(11, 250))) == 0)

    # Corollary 7.1: band volume.
    vv = symbols("v")
    check("Corollary 7.1 band volume 13/27", 6 * integrate(vv * (1 - vv), (vv, Rational(1, 3), Rational(2, 3))) == Rational(13, 27))

    if failures:
        print(f"{len(failures)} check(s) failed")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
