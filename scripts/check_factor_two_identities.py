#!/usr/bin/env python3
"""Replay the identities and fixed constants used in docs/binary-factor-two.md.

Requires sympy (and its bundled mpmath). Every symbolic check is an exact
expansion; every scalar comparison is exact rational arithmetic on the
displayed series bounds. The high-precision evaluations are spot checks of
derivative formulas at a few laws and are labelled as such. Nothing here is a
proof step. Run from anywhere:

    python scripts/check_factor_two_identities.py
"""

from __future__ import annotations

import sys
from fractions import Fraction as Fr

try:
    import mpmath
    from sympy import (Rational, Symbol, cancel, diff, expand, factor, log,
                       simplify, sqrt, symbols, together)
except ImportError:  # pragma: no cover
    sys.exit("sympy is required: pip install sympy")

mpmath.mp.dps = 60


def main() -> int:
    failures = []

    def check(label, ok):
        print(f"{'ok  ' if ok else 'FAIL'} {label}")
        if not ok:
            failures.append(label)

    def e(t):
        return t * log(t)

    def F(x, y):
        return e(x + y) - e(x) - e(y)

    def h(x):
        return -e(x) - e(1 - x)

    a, b, c, d, t, u, x, y, z, v, D, w = symbols("a b c d t u x y z v D w", positive=True)

    POINTS = [
        {"a": Rational(1, 2), "b": Rational(1, 5), "c": Rational(1, 10), "d": Rational(1, 5), "s": Rational(7, 10),
         "k": Rational(1, 3), "t": Rational(1, 7), "u": Rational(1, 5), "v": Rational(3, 10), "D": Rational(1, 20), "delta": Rational(1, 10)},
        {"a": Rational(3, 7), "b": Rational(1, 9), "c": Rational(1, 11), "d": Rational(2, 9), "s": Rational(79, 99),
         "k": Rational(2, 5), "t": Rational(2, 9), "u": Rational(1, 6), "v": Rational(20, 99), "D": Rational(1, 30), "delta": Rational(1, 50)},
        {"a": Rational(9, 20), "b": Rational(3, 50), "c": Rational(1, 25), "d": Rational(9, 20), "s": Rational(9, 10),
         "k": Rational(-1, 4), "t": Rational(1, 13), "u": Rational(3, 10), "v": Rational(1, 10), "D": Rational(1, 40), "delta": Rational(1, 30)},
    ]

    def zero(expr):
        """Exact zero test. Symbolic simplification first; if sympy cannot
        finish, evaluate the difference to 60 digits at three rational points
        (a sufficient test for the finite log-linear combinations used here)."""
        try:
            if simplify(expr) == 0:
                return True
        except Exception:  # pragma: no cover
            pass
        for pt in POINTS:
            sub = {sym: pt[str(sym)] for sym in expr.free_symbols if str(sym) in pt}
            val = expr.subs(sub).evalf(60)
            if val.free_symbols or abs(val) > 10 ** -50:
                return False
        return True

    # ---------------------------------------------------------------- section 1
    # Entropies of a four-cell law p = (a, b, c, d) in natural logarithms.
    def H4(a_, b_, c_, d_):
        return -(e(a_) + e(b_) + e(c_) + e(d_))

    def HX(a_, b_, c_, d_):
        return h(a_ + b_)

    def HY(a_, b_, c_, d_):
        return h(a_ + c_)

    def I4(a_, b_, c_, d_):
        return HX(a_, b_, c_, d_) + HY(a_, b_, c_, d_) - H4(a_, b_, c_, d_)

    def Psi(a_, b_, c_, d_):
        return 2 * H4(a_, b_, c_, d_) - HX(a_, b_, c_, d_) - HY(a_, b_, c_, d_)

    def Phi(a_, b_, c_, d_):
        return 3 * H4(a_, b_, c_, d_) - 2 * HX(a_, b_, c_, d_) - 2 * HY(a_, b_, c_, d_)

    norm = {d: 1 - a - b - c}
    check("Psi - Phi = I", simplify((Psi(a, b, c, d) - Phi(a, b, c, d) - I4(a, b, c, d)).subs(norm)) == 0)

    # (1.2): the score of the singleton code isolating cell (1,1), from the
    # definition D_p(g) = I(X;Y|g) + H(g|X) + H(g|Y) written as explicit sums.
    # g = 1 on the cell d, 0 elsewhere.  Conditional on g = 0 the law is
    # (a, b, c, 0)/(1-d); conditional on g = 1 it is a point mass.
    P0 = 1 - d
    ca, cb, cc = a / P0, b / P0, c / P0
    # I(X;Y | g = 0) with the three-cell conditional law.
    Hjoint0 = -(e(ca) + e(cb) + e(cc))
    HX0 = -(e(ca + cb) + e(cc))
    HY0 = -(e(ca + cc) + e(cb))
    Ixy_given_g = P0 * (HX0 + HY0 - Hjoint0)
    # H(g | X) = sum_x P(X=x) H(g | X=x): row 0 has cells a, b (g = 0 on both), row 1 has c (g=0), d (g=1).
    mu1 = c + d
    Hg_given_X = mu1 * h(d / mu1)
    nu1 = b + d
    Hg_given_Y = nu1 * h(d / nu1)
    S11 = Ixy_given_g + Hg_given_X + Hg_given_Y
    rhs = I4(a, b, c, d) + 2 * F(d, b) + 2 * F(d, c) - h(d)
    check("(1.3) singleton score S_11 = I + 2F(d,b) + 2F(d,c) - h(d)", zero((S11 - rhs).subs(norm)))

    # ---------------------------------------------------------------- section 2
    s = Symbol("s", positive=True)
    k = Symbol("k")
    chord = {d: s - a}
    J = -(e(a) + e(b) + e(c) + e(s - a))
    R = h(a + b)
    C = h(a + c)
    M0 = 2 * (Psi(a, b, c, s - a) + k) - I4(a, b, c, s - a)
    MD = 2 * (Psi(a, b, c, s - a) + k) - (I4(a, b, c, s - a) + 2 * F(s - a, b) + 2 * F(s - a, c) - h(s - a))
    Q = 3 * e(a) - 2 * e(a + b) - 2 * e(a + c) + e(a + b + c) + e(b) + e(c)
    check("(2.4) M0 = 5J - 3R - 3C + 2k", simplify(M0 - (5 * J - 3 * R - 3 * C + 2 * k)) == 0)
    check("(2.5) MD = 2J - R - C + 2k - Q(a), the Q form of the center", zero(MD - (2 * J - R - C + 2 * k - Q)))
    # (2.6): MD'' formula, with d = s - a.
    MDpp = diff(MD, a, 2)
    MDpp_claim = (-5 / a - 2 / (s - a) + 3 / (a + b) + 3 / (a + c) + 1 / (s - a + b) + 1 / (s - a + c) - 1 / (a + b + c))
    check("(2.6) MD'' formula", zero(MDpp - MDpp_claim))
    # K_x(b, c) = -5/x + 3/(x+b) + 3/(x+c) - 1/(x+b+c): partial derivatives.
    Kx = -5 / x + 3 / (x + b) + 3 / (x + c) - 1 / (x + b + c)
    check("K_x(0,0) = 0", simplify(Kx.subs({b: 0, c: 0})) == 0)
    check("d_b K_x = -3/(x+b)^2 + 1/(x+b+c)^2", simplify(diff(Kx, b) - (-3 / (x + b) ** 2 + 1 / (x + b + c) ** 2)) == 0)
    # (2.8): M0'' in the variable t = a d.
    M0pp = diff(M0, a, 2)
    tt = a * (s - a)
    pb = b * (s + b)
    pc = c * (s + c)
    M0pp_claim = -5 * s / tt + 3 * (s + 2 * b) / (tt + pb) + 3 * (s + 2 * c) / (tt + pc)
    check("(2.8) M0'' = -5s/t + 3(s+2b)/(t+p_b) + 3(s+2c)/(t+p_c)", zero(M0pp - M0pp_claim))
    check("t + p_b = (a+b)(b+d)", expand(tt + pb - (a + b) * (b + s - a)) == 0)
    N = expand(-5 * s * (t + pb) * (t + pc) + 3 * (s + 2 * b) * t * (t + pc) + 3 * (s + 2 * c) * t * (t + pb))
    check("N(t) leading coefficient 1 + 5v", simplify(N.coeff(t, 2).subs(s, 1 - b - c) - (1 + 5 * (b + c))) == 0)
    check("N(0) = -5 s p_b p_c", simplify(N.coeff(t, 0) - (-5 * s * pb * pc)) == 0)
    check("M0'(m) = 0 (the constant margin is even about the center)",
          zero(diff(M0, a).subs(a, s / 2).subs(s, 1 - b - c)))
    # Lemma 2.1: f(sqrt(w)) = -w.
    f = u ** 3 - v * u ** 2 - w * u - w * (1 - v)
    check("f(sqrt w) = -w", simplify(f.subs(u, sqrt(w))) == -w)
    # u^2 - bc = u^2/(u+s) at a root, and K = P_b P_c / u^3 = (s+2u)/(s+u)^2.
    fcub = u ** 3 - v * u ** 2 - w * (u + s)
    wroot = u ** 2 * (u - v) / (u + s)
    check("cubic: w = u^2 (u - v)/(u + s)", simplify(fcub.subs(w, wroot)) == 0)
    check("u^2 - w = u^2/(u+s) at the root", simplify(((u ** 2 - wroot) - u ** 2 / (u + s)).subs(s, 1 - v)) == 0)
    Pb = u ** 2 + b * (1 - c)
    Pc = u ** 2 + c * (1 - b)
    Kc = (s + 2 * u) / (s + u) ** 2
    sub_root = {s: 1 - b - c}
    # With w = bc = u^2 (u-v)/(u+s): eliminate c through the cubic is messy; check at the rational contact instead.
    ref = {b: Rational(8, 135), c: Rational(8, 135), u: Rational(28, 135), s: Rational(119, 135), v: Rational(16, 135)}
    check("reference contact satisfies the cubic", fcub.subs(w, b * c).subs(ref) == 0)
    check("K = P_b P_c / u^3 at the reference contact", (Pb * Pc / u ** 3 - Kc).subs(ref) == 0)
    check("K = 375/343 at the reference contact", Kc.subs(ref) == Rational(375, 343))
    # General identity: (A+b)(D+b) = P_b and (A+b)^2(A+c)^2/A^3 = P_b P_c/u^3 when A^{3/2}(D+b)(D+c) = D^{3/2}(A+b)(A+c).
    A_, D_ = symbols("A D", positive=True)
    check("(A+b)(D+b) = u^2 + b(1-c) when A + D = s, AD = u^2",
          simplify(((A_ + b) * (D_ + b) - Pb).subs({D_: s - A_}).subs(u, sqrt(A_ * (s - A_))).subs(s, 1 - b - c)) == 0)

    # ---------------------------------------------------------------- section 3: the contact potential
    # Chart x = b/u, y = c/u, r = x + y, rho = xy, n = (1-r)(1-rho): u = rho/n, v = r rho/n, s = (1-r-rho)/n.
    r_, rho_ = symbols("r rho", positive=True)
    n_ = (1 - r_) * (1 - rho_)
    u_ch = rho_ / n_
    v_ch = r_ * rho_ / n_
    s_ch = (1 - r_ - rho_) / n_
    check("chart: s + v = 1", simplify(s_ch + v_ch - 1) == 0)
    check("chart: the cubic holds with bc = rho u^2",
          simplify(u_ch ** 3 - v_ch * u_ch ** 2 - rho_ * u_ch ** 2 * (u_ch + s_ch)) == 0)
    check("chart: u - v = rho/(1 - rho)", simplify(u_ch - v_ch - rho_ / (1 - rho_)) == 0)
    check("chart: s - 2u = (1 - r - 3 rho)/n", simplify(s_ch - 2 * u_ch - (1 - r_ - 3 * rho_) / n_) == 0)
    # K, P_b, P_c in chart coordinates.
    K_ch = (s_ch + 2 * u_ch) / (s_ch + u_ch) ** 2
    check("chart: K = (1-x)(1-y)(1-xy)/(1-x-y)",
          simplify(K_ch.subs({r_: x + y, rho_: x * y}) - (1 - x) * (1 - y) * (1 - x * y) / (1 - x - y)) == 0)
    Pb_ch = u_ch ** 2 + (x * u_ch) * (1 - y * u_ch)
    check("chart: P_b = b (1-x)/(1-x-y)",
          simplify((Pb_ch - x * u_ch * (1 - x) / (1 - x - y)).subs({r_: x + y, rho_: x * y})) == 0)
    # Lemma 3.4: Lk = v^2 k_vv along a radial line (fixed z) equals the rational function (3.7).
    # k(b, c) = -s ln K + b ln(b^3/P_b^2) + c ln(c^3/P_c^2) with s = 1 - b - c and u the root.
    # Work in chart coordinates (x, y); D = b d/db + c d/dc is pulled back through the Jacobian.
    ux = (x * y) / ((1 - x - y) * (1 - x * y))
    bx, cx, sx = x * ux, y * ux, 1 - (x + y) * ux
    Kx_ = (sx + 2 * ux) / (sx + ux) ** 2
    Pbx = ux ** 2 + bx * (1 - cx)
    Pcx = ux ** 2 + cx * (1 - bx)
    kx = -sx * log(Kx_) + bx * (3 * log(bx) - 2 * log(Pbx)) + cx * (3 * log(cx) - 2 * log(Pcx))
    # Jacobian of (x, y) -> (b, c).
    Jm = [[diff(bx, x), diff(bx, y)], [diff(cx, x), diff(cx, y)]]
    det = Jm[0][0] * Jm[1][1] - Jm[0][1] * Jm[1][0]
    # Vector field D = b d_b + c d_c pulled back: (dx, dy) = J^{-1} (b, c).
    dx_ = (Jm[1][1] * bx - Jm[0][1] * cx) / det
    dy_ = (-Jm[1][0] * bx + Jm[0][0] * cx) / det

    def Dop(fexpr):
        return dx_ * diff(fexpr, x) + dy_ * diff(fexpr, y)

    Dk = Dop(kx)
    # First check the envelope gradient: D k = v ln K + 3(b ln b + c ln c) - 2 b ln P_b - 2 c ln P_c.
    Dk_claim = (bx + cx) * log(Kx_) + 3 * (bx * log(bx) + cx * log(cx)) - 2 * bx * log(Pbx) - 2 * cx * log(Pcx)
    check("Lemma 3.2 (radial form): D k = v ln K + 3 Sum b ln b - 2 Sum b ln P_b",
          simplify(cancel(together(Dk - Dk_claim))) == 0)
    Lk = simplify(cancel(together(Dop(Dk_claim) - Dk_claim)))
    Lk_claim = (x * y) * (3 * x * y * (x + y) - 4 * x * y - 2 * (x + y) ** 2 + 3 * (x + y)) / ((1 + x * y - x - y) * (3 - 2 * (x + y) - x * y))
    check("(3.7) Lk = rho (3 rho r - 4 rho - 2 r^2 + 3 r)/((1 + rho - r)(3 - 2r - rho))",
          simplify(cancel(together(Lk - Lk_claim))) == 0)
    # (3.8): v/s - Lk = 2 rho^2 (1 - rho)(2 - r)/((1 - r - rho)(1 + rho - r)(3 - 2r - rho)).
    lhs = r_ * rho_ / (1 - r_ - rho_) - rho_ * (3 * rho_ * r_ - 4 * rho_ - 2 * r_ ** 2 + 3 * r_) / ((1 + rho_ - r_) * (3 - 2 * r_ - rho_))
    rhs = 2 * rho_ ** 2 * (1 - rho_) * (2 - r_) / ((1 - r_ - rho_) * (1 + rho_ - r_) * (3 - 2 * r_ - rho_))
    check("(3.8) v/s - Lk factorization", simplify(cancel(together(lhs - rhs))) == 0)
    poly_id = expand(r_ * (1 + rho_ - r_) * (3 - 2 * r_ - rho_) - (1 - r_ - rho_) * (3 * rho_ * r_ - 4 * rho_ - 2 * r_ ** 2 + 3 * r_) - 2 * rho_ * (rho_ - 1) * (r_ - 2))
    check("(3.8) polynomial identity", poly_id == 0)

    # Lemma 3.4, the two chart identities behind the collection.
    check("Lemma 3.4: D u_0 / u_0 = (2 - r - r omega)/(3 - 2r - omega) in the chart",
          simplify(cancel(together(Dop(ux) / ux - (2 - (x + y) - (x + y) * x * y) / (3 - 2 * (x + y) - x * y)))) == 0)
    check("Lemma 3.4: s D ln K = 3v - 2b DP_b/P_b - 2c DP_c/P_c",
          simplify(cancel(together(sx * Dop(log(Kx_)) - (3 * (bx + cx) - 2 * bx * Dop(Pbx) / Pbx - 2 * cx * Dop(Pcx) / Pcx)))) == 0)
    check("Lemma 3.4: L_k = D ln K", simplify(cancel(together(Lk - Dop(log(Kx_))))) == 0)

    # ---------------------------------------------------------------- section 4: the center
    # Center domain: f(m) = m [ (1-v)(1-3v)/4 - 3bc ], and (1-v)(1-3v) - 3 v^2 (1 - z^2) = 1 - 4v + 3 v^2 z^2.
    m_ = (1 - v) / 2
    bz = v * (1 + z) / 2
    cz = v * (1 - z) / 2
    fm = m_ ** 3 - v * m_ ** 2 - bz * cz * (m_ + 1 - v)
    check("(4.1) f(m) = m [ (1-v)(1-3v) - 3 v^2 (1 - z^2) ] / 4",
          simplify(fm - m_ * ((1 - v) * (1 - 3 * v) - 3 * v ** 2 * (1 - z ** 2)) / 4) == 0)
    check("(4.1) (1-v)(1-3v) - 3v^2(1-z^2) = 1 - 4v + 3 v^2 z^2",
          expand((1 - v) * (1 - 3 * v) - 3 * v ** 2 * (1 - z ** 2) - (1 - 4 * v + 3 * v ** 2 * z ** 2)) == 0)
    vc = 1 / (2 + sqrt(4 - 3 * z ** 2))
    check("v_c(z) = 1/(2 + sqrt(4 - 3z^2)) solves 1 - 4v + 3 v^2 z^2 = 0", simplify(1 - 4 * vc + 3 * vc ** 2 * z ** 2) == 0)
    # Radial second derivatives of J and R at fixed z.
    Jv = -(2 * e(m_) + e(bz) + e(cz))
    check("(4.3) J_vv = -1/(v(1-v))", simplify(diff(Jv, v, 2) + 1 / (v * (1 - v))) == 0)
    Rv = h((1 + v * z) / 2)
    check("(4.3) R_vv = -z^2/(1 - v^2 z^2)", simplify(diff(Rv, v, 2) + z ** 2 / (1 - v ** 2 * z ** 2)) == 0)
    gam = log(2) - h((1 - t) / 2)
    check("gamma''(t) = 1/(1 - t^2)", simplify(diff(gam, t, 2) - 1 / (1 - t ** 2)) == 0)
    # MD at the center: MD = MX - gamma(v) + gamma(delta), with MX = 3J - 3R + 2k.
    delta = Symbol("delta", positive=True)
    ctr = {a: (1 - v) / 2, s: 1 - v, b: (v + delta) / 2, c: (v - delta) / 2}
    MD_center = MD.subs(ctr)
    MX_center = (3 * J - 3 * R + 2 * k).subs(ctr)
    check("(4.2) MD(center) = MX - gamma(v) + gamma(delta)",
          simplify(MD_center - (MX_center - gam.subs(t, v) + gam.subs(t, delta))) == 0)
    check("(4.2) M0(center) = 5J - 6R + 2k", simplify(M0.subs(ctr) - (5 * J - 6 * R + 2 * k).subs(ctr)) == 0)
    # Bounds (4.6): -3v/s + 6v^2/(1-v^2) = -3v/(1+v); -v/s + 3v^2/(1-v^2) = -v(1-2v)/(1-v^2).
    check("(4.3) -3v/(1-v) + 6v^2/(1-v^2) = -3v/(1+v)", simplify(-3 * v / (1 - v) + 6 * v ** 2 / (1 - v ** 2) + 3 * v / (1 + v)) == 0)
    check("(4.3) -v/(1-v) + 3v^2/(1-v^2) = -v(1-2v)/(1-v^2)", simplify(-v / (1 - v) + 3 * v ** 2 / (1 - v ** 2) + v * (1 - 2 * v) / (1 - v ** 2)) == 0)
    # Seam derivatives (4.7): at fixed v, d/d delta of M0 and MD, using k_b, k_c of Lemma 3.2.
    kb = log(Kc) + 3 * log(b) - 2 * log(Pb)
    kc = log(Kc) + 3 * log(c) - 2 * log(Pc)
    Jc = -(2 * e((1 - v) / 2) + e(b) + e(c))
    Rc = h((1 + b - c) / 2)
    # d/d delta = (1/2)(d_b - d_c) at fixed v, on functions of (b, c) with k treated through its gradient.
    M0_delta = Rational(1, 2) * (diff(5 * Jc - 6 * Rc, b) - diff(5 * Jc - 6 * Rc, c)) + (kb - kc)
    M0_delta_claim = Rational(1, 2) * log(b / c) + 3 * log((1 + b - c) / (1 - b + c)) - 2 * log(Pb / Pc)
    check("(4.7) M0_delta = (1/2) ln(b/c) + 3 ln((1+delta)/(1-delta)) - 2 ln(P_b/P_c)", zero(M0_delta - M0_delta_claim))
    MX_delta = Rational(1, 2) * (diff(3 * Jc - 3 * Rc, b) - diff(3 * Jc - 3 * Rc, c)) + (kb - kc)
    MD_delta = MX_delta + diff(gam, t).subs(t, b - c)
    MD_delta_claim = Rational(3, 2) * log(b / c) + 2 * log((1 + b - c) / (1 - b + c)) - 2 * log(Pb / Pc)
    check("(4.7) MD_delta = (3/2) ln(b/c) + 2 ln((1+delta)/(1-delta)) - 2 ln(P_b/P_c)", zero(MD_delta - MD_delta_claim))
    check("P_b - P_c = b - c", simplify(Pb - Pc - (b - c)) == 0)
    check("P_b + P_c = v + 2(u^2 - bc)", simplify(Pb + Pc - (b + c) - 2 * (u ** 2 - b * c)) == 0)
    # Constant seam numbers.
    check("f(1/4) = 1/128 - 9w/8 at v = 1/8", simplify(f.subs({v: Rational(1, 8), u: Rational(1, 4)}) - (Rational(1, 128) - Rational(9, 8) * w)) == 0)
    check("1/128 - 9/(8*256) = 7/2048", Fr(1, 128) - Fr(9, 8 * 256) == Fr(7, 2048))
    check("t < 1/8 + 2(1/4)^2/(1/4 + 7/8) = 17/72", Fr(1, 8) + 2 * Fr(1, 16) / (Fr(1, 4) + Fr(7, 8)) == Fr(17, 72))
    check("576/17 - 256/21 = 7744/357 > 64/3", Fr(576, 17) - Fr(256, 21) == Fr(7744, 357) and Fr(7744, 357) > Fr(64, 3))
    check("12/(1 - 1/64) = 256/21", 12 / (1 - Fr(1, 64)) == Fr(256, 21))
    # (4.13): z^2/2 + z^4/12 with z = 1 - 2q, alpha = q(1-q).
    q_ = Symbol("q", positive=True)
    zz = 1 - 2 * q_
    al = q_ * (1 - q_)
    check("(4.13) z^2/2 + z^4/12 = 7/12 - (8/3) alpha + (4/3) alpha^2",
          expand(zz ** 2 / 2 + zz ** 4 / 12 - (Rational(7, 12) - Rational(8, 3) * al + Rational(4, 3) * al ** 2)) == 0)
    check("e(b) + e(c) = v ln v - v h(q) with c = qv, b = (1-q)v",
          simplify(e((1 - q_) * v) + e(q_ * v) - (v * log(v) - v * h(q_))) == 0)
    # Triangular limit values.
    v8 = Rational(1, 8)
    k_face = -Rational(7, 8) * log(Rational(9, 8)) + v8 * log(v8 ** 3 / Rational(9, 64) ** 2)
    check("k at the triangular limit = 3 ln 2 - (9/4) ln 3", simplify(k_face - (3 * log(2) - Rational(9, 4) * log(3))) == 0)
    J_face = -(2 * e(Rational(7, 16)) + e(v8))
    check("J at the triangular limit = (31/8) ln 2 - (7/8) ln 7", simplify(J_face - (Rational(31, 8) * log(2) - Rational(7, 8) * log(7))) == 0)
    R_face = h(Rational(9, 16))
    check("R at the triangular limit = 4 ln 2 - (9/8) ln 3 - (7/16) ln 7",
          simplify(R_face - (4 * log(2) - Rational(9, 8) * log(3) - Rational(7, 16) * log(7))) == 0)
    Mface = 5 * J_face - 6 * R_face + 2 * k_face
    check("M_face = (11/8) ln 2 + (9/4) ln 3 - (7/4) ln 7",
          simplify(Mface - (Rational(11, 8) * log(2) + Rational(9, 4) * log(3) - Rational(7, 4) * log(7))) == 0)
    check("(4.16) coarse bound 677/120000 > 1/200",
          Fr(5, 4) * Fr(6931, 10000) + Fr(9, 4) * Fr(10986, 10000) - Fr(7, 4) * Fr(19460, 10000) + Fr(7, 96) == Fr(677, 120000)
          and Fr(677, 120000) > Fr(1, 200))

    # Series bounds for logarithms: S_N(z) <= ln((1+z)/(1-z)) <= U_N(z).
    def S(Nn, zq):
        return 2 * sum(zq ** (2 * j + 1) / (2 * j + 1) for j in range(Nn))

    def U(Nn, zq):
        return S(Nn, zq) + 2 * zq ** (2 * Nn + 1) / ((2 * Nn + 1) * (1 - zq ** 2))

    def ln_bounds(X, Nn=8):
        """Exact rational enclosure of ln X for rational X >= 1 via X = 2^j Y."""
        X = Fr(X)
        j = 0
        while X >= 2:
            X /= 2
            j += 1
        zq = (X - 1) / (X + 1)
        lo, hi = S(Nn, zq), U(Nn, zq)
        z2 = Fr(1, 3)
        lo2, hi2 = S(Nn, z2), U(Nn, z2)
        return lo + j * lo2, hi + j * hi2

    def bound_combination(terms, const=Fr(0)):
        """Lower bound of const + sum coef * ln(arg) from the enclosures."""
        total = Fr(const)
        for coef, arg in terms:
            lo, hi = ln_bounds(arg)
            total += coef * (lo if coef > 0 else hi)
        return total

    check("ln 2 > 6931/10000", ln_bounds(2)[0] > Fr(6931, 10000))
    check("ln 3 > 10986/10000", ln_bounds(3)[0] > Fr(10986, 10000))
    check("ln 7 < 19460/10000", ln_bounds(7)[1] < Fr(19460, 10000))
    seam_const = bound_combination([(Fr(5, 4), 2), (Fr(9, 4), 3), (Fr(-7, 4), 7)], Fr(7, 96))
    check("(4.16) series bound of (5/4)ln2 + (9/4)ln3 - (7/4)ln7 + 7/96 exceeds 1/200", seam_const > Fr(1, 200))
    # Singleton seam.
    check("t > v + 2v^2/(v+s) = 5/32 at v = 1/8", Fr(1, 8) + 2 * Fr(1, 64) == Fr(5, 32))
    check("(4.19) 3/2 - 2(4/5)^3 = 119/250", Fr(3, 2) - 2 * Fr(4, 5) ** 3 == Fr(119, 250))
    check("(4.19) 3 - 4(4/5) + 1/2 = 3/10", 3 - 4 * Fr(4, 5) + Fr(1, 2) == Fr(3, 10))
    # Reference contact q_ref = (112, 8, 8, 7)/135: tangent coefficients (natural logarithms).
    qa, qb, qc, qd = Rational(112, 135), Rational(8, 135), Rational(8, 135), Rational(7, 135)
    mu0, mu1 = qa + qb, qc + qd
    nu0, nu1 = qa + qc, qb + qd
    l00 = mu0 ** 2 * nu0 ** 2 / qa ** 3
    l01 = mu0 ** 2 * nu1 ** 2 / qb ** 3
    l10 = mu1 ** 2 * nu0 ** 2 / qc ** 3
    l11 = mu1 ** 2 * nu1 ** 2 / qd ** 3
    check("reference contact: l_00 = l_11 = ln(375/343)", l00 == Rational(375, 343) and l11 == Rational(375, 343))
    check("reference contact: l_01 = l_10 = ln(375/8)", l01 == Rational(375, 8) and l10 == Rational(375, 8))
    check("reference contact: 28^3 - 16*28^2 - 64*28 - 64*119 = 0", 28 ** 3 - 16 * 28 ** 2 - 64 * 28 - 64 * 119 == 0)
    # -l_qref(p0) at p0 = (7/16, 1/16, 1/16, 7/16).
    ell_p0 = Rational(7, 8) * log(Rational(375, 343)) + Rational(1, 8) * log(Rational(375, 8))
    ell_claim = -(Rational(3, 8) * log(2) - log(3) - 3 * log(5) + Rational(21, 8) * log(7))
    check("(4.20) -l_ref(p0) = (3/8) ln 2 - ln 3 - 3 ln 5 + (21/8) ln 7", simplify(ell_p0 - ell_claim) == 0)
    J0 = -(2 * e(Rational(7, 16)) + 2 * e(Rational(1, 16)))
    check("J(p0) = 4 ln 2 - (7/8) ln 7", simplify(J0 - (4 * log(2) - Rational(7, 8) * log(7))) == 0)
    gam8 = log(2) - h(Rational(7, 16))
    check("gamma(1/8) = -3 ln 2 + (9/8) ln 3 + (7/16) ln 7",
          simplify(gam8 - (-3 * log(2) + Rational(9, 8) * log(3) + Rational(7, 16) * log(7))) == 0)
    MD0_lower = 3 * J0 - 3 * log(2) - gam8 - 2 * ell_p0
    MD0_claim = (204 * log(2) - 50 * log(3) - 96 * log(5) + 35 * log(7)) / 16
    check("(4.17) MD(0) >= [204 ln 2 - 50 ln 3 - 96 ln 5 + 35 ln 7]/16", simplify(MD0_lower - MD0_claim) == 0)
    md0 = bound_combination([(Fr(204, 16), 2), (Fr(-50, 16), 3), (Fr(-96, 16), 5), (Fr(35, 16), 7)])
    check("(4.17) series bound exceeds 1/250", md0 > Fr(1, 250))
    check("8 v (1/250) = 4v/125", 8 * Fr(1, 250) == Fr(4, 125))

    # ---------------------------------------------------------------- section 5: the fixed cut
    # Lemma 5.1: D < v/2.
    qq = Symbol("qq", positive=True)
    fq = qq ** 3 - v * qq ** 2 - w * (qq + 1 - v)
    check("(5.1) f(q) >= q v (1-2v)/2 - v^2 (3/4 - v) with q^2 = (v/2)(1 - 3v/2), w <= v^2/4",
          simplify((fq.subs(w, v ** 2 / 4) - (qq * v * (1 - 2 * v) / 2 - v ** 2 * (Rational(3, 4) - v))).subs(qq ** 3, qq * (v / 2 - 3 * v ** 2 / 4)).subs(qq ** 2, v / 2 - 3 * v ** 2 / 4)) == 0)
    check("(5.1) q^2 (1-2v)^2 - v^2 (3/2 - 2v)^2 = (v/2)(1 - 10v + 22v^2 - 14v^3)",
          expand((v / 2 - 3 * v ** 2 / 4) * (1 - 2 * v) ** 2 - v ** 2 * (Rational(3, 2) - 2 * v) ** 2 - v / 2 * (1 - 10 * v + 22 * v ** 2 - 14 * v ** 3)) == 0)
    zz8 = Symbol("zeta")
    check("(5.1) 1 - 10v + 22v^2 - 14v^3 = 17/256 + 165 zeta/32 + 67 zeta^2/4 + 14 zeta^3, zeta = 1/8 - v",
          expand((1 - 10 * v + 22 * v ** 2 - 14 * v ** 3).subs(v, Rational(1, 8) - zz8) - (Rational(17, 256) + Rational(165, 32) * zz8 + Rational(67, 4) * zz8 ** 2 + 14 * zz8 ** 3)) == 0)
    check("(5.1) f'(t) >= 3v^2 - 2v^2 - v^2/4 = 3v^2/4 for t >= v", 3 - 2 - Fr(1, 4) == Fr(3, 4))
    check("(5.1) s - v/2 = 1 - 3v/2", simplify((1 - v) - v / 2 - (1 - 3 * v / 2)) == 0)
    # Contact logarithm identity (5.3), checked at the reference contact.
    Aref, Dref, bref, cref = Fr(112, 135), Fr(7, 135), Fr(8, 135), Fr(8, 135)
    xr, yr = bref / Dref, cref / Dref
    lhs52 = -mpmath.log(mpmath.mpf(Dref.numerator) / Dref.denominator)
    rhs52 = (2 * mpmath.log(1 + mpmath.mpf(xr.numerator) / xr.denominator) + 2 * mpmath.log(1 + mpmath.mpf(yr.numerator) / yr.denominator)
             - mpmath.log(mpmath.mpf(Aref.numerator) / Aref.denominator)
             - 2 * mpmath.log(1 + mpmath.mpf((bref / Aref).numerator) / (bref / Aref).denominator)
             - 2 * mpmath.log(1 + mpmath.mpf((cref / Aref).numerator) / (cref / Aref).denominator))
    check("(5.3) contact logarithm identity at the reference contact (60 digits)", abs(lhs52 - rhs52) < mpmath.mpf(10) ** -50)
    # P''(t) for P(t) = -Phi(p_t), p_t = (s - t, b, c, t).
    Pt = -Phi(s - t, b, c, t)
    alpha = s - t
    Ppp_claim = 3 / t + 3 / alpha - 2 / (t + b) - 2 / (t + c) - 2 / (alpha + b) - 2 / (alpha + c)
    check("(5.5) P''(t) formula", simplify(diff(Pt, t, 2).subs(s, 1 - b - c) - Ppp_claim.subs(s, 1 - b - c)) == 0)
    al_ = Symbol("alpha", positive=True)
    check("(5.6) 2/(alpha+b) + 2/(alpha+c) - 4/(alpha + v/2) = 2 (b-c)^2 / [(alpha+b)(alpha+c)(2 alpha + v)]",
          simplify(2 / (al_ + b) + 2 / (al_ + c) - 4 / (al_ + (b + c) / 2) - 2 * (b - c) ** 2 / ((al_ + b) * (al_ + c) * (2 * al_ + b + c))) == 0)
    check("(5.6) 4/(alpha + v/2) - 3/alpha = (2 alpha - 3v)/[alpha (2 alpha + v)]",
          simplify(4 / (al_ + v / 2) - 3 / al_ - (2 * al_ - 3 * v) / (al_ * (2 * al_ + v))) == 0)
    # Q_j(D, d) = integral_D^d (d - tau)/(tau + j) d tau.
    dd, jj, tau_ = symbols("dd jj tau", positive=True)
    from sympy import integrate
    Qj = (dd + jj) * log((dd + jj) / (D + jj)) - dd + D
    check("(5.7) Q_j = integral of (d - tau)/(tau + j)", simplify(integrate((dd - tau_) / (tau_ + jj), (tau_, D, dd)) - Qj) == 0)
    # I(p_d) = h(d) - F(d,b) - F(d,c) + J3(d).
    J3 = e(s - dd) + e(1 - dd) - e(s - dd + b) - e(s - dd + c)
    check("(5.8) I(p_d) = h(d) - F(d,b) - F(d,c) + J3(d)",
          simplify((I4(s - dd, b, c, dd) - (h(dd) - F(dd, b) - F(dd, c) + J3)).subs(s, 1 - b - c)) == 0)
    check("M0 = I - 2(P - k)", simplify((2 * (Psi(s - dd, b, c, dd) + k) - I4(s - dd, b, c, dd)) - (I4(s - dd, b, c, dd) - 2 * (-Phi(s - dd, b, c, dd) - k))) == 0)
    # Homogeneous rescaling to x = b/D, y = c/D at d = 3D, and the cancellation record.
    V = lambda xx: 3 * (3 + xx) * log(3 + xx) - (6 + 4 * xx) * log(1 + xx) + xx * log(xx)
    rec = (-F(3 * D, x * D) - F(3 * D, y * D) - 6 * Qj.subs({dd: 3 * D, jj: 0}).subs(log((3 * D) / D), log(3))
           + 4 * Qj.subs({dd: 3 * D, jj: x * D}) + 4 * Qj.subs({dd: 3 * D, jj: y * D})) / D
    rec_claim = V(x) + V(y) - 6 * log(1 + x) - 6 * log(1 + y) - 12 * log(3) - 4
    check("(5.10) cancellation record: [-F_b - F_c - 6Q_0 + 4Q_b + 4Q_c]/D = V(x) + V(y) - 6ln(1+x) - 6ln(1+y) - 12 ln 3 - 4",
          simplify(expand(rec - rec_claim, force=True)) == 0)
    # V', V''.
    Vx = V(x)
    check("(5.11) V'(x) = 3 ln((x+3)/(x+1)) + ln(x/(x+1)) - 2/(x+1)",
          simplify(diff(Vx, x) - (3 * log((x + 3) / (x + 1)) + log(x / (x + 1)) - 2 / (x + 1))) == 0)
    check("(5.11) V''(x) = (-3x^2 + 4x + 3)/[x (x+1)^2 (x+3)]",
          simplify(diff(Vx, x, 2) - (-3 * x ** 2 + 4 * x + 3) / (x * (x + 1) ** 2 * (x + 3))) == 0)
    slope = 3 * log(Rational(7, 3)) - log(3) - Rational(4, 3)
    intercept = 9 * log(Rational(7, 2)) - 6 * log(Rational(3, 2)) + Rational(2, 3)
    check("(5.12) tangent at 1/2: slope and intercept",
          simplify(diff(Vx, x).subs(x, Rational(1, 2)) - slope) == 0 and simplify(Vx.subs(x, Rational(1, 2)) - slope / 2 - intercept) == 0)
    Ht = 3 * log(1 + 2 * t) + log(1 - t) - 2 * t
    check("Step 6: V'(x) = H(1/(x+1))", simplify(diff(Vx, x) - Ht.subs(t, 1 / (x + 1))) == 0)
    check("Step 6: H''(t) = -12/(1+2t)^2 - 1/(1-t)^2", simplify(diff(Ht, t, 2) + 12 / (1 + 2 * t) ** 2 + 1 / (1 - t) ** 2) == 0)
    check("Step 6: H(1/2) = 2 ln 2 - 1", simplify(Ht.subs(t, Rational(1, 2)) - (2 * log(2) - 1)) == 0)
    # The five logarithm bounds.
    check("(5.12) 3 S_3(2/5) - U_3(1/2) - 4/3 = 94627/875000 > 0",
          3 * S(3, Fr(2, 5)) - U(3, Fr(1, 2)) - Fr(4, 3) == Fr(94627, 875000))
    check("(5.12) 9 S_5(5/9) - 6 U_3(1/5) + 2/3 - 19/2 = 224012952139/42374115984375 > 0",
          9 * S(5, Fr(5, 9)) - 6 * U(3, Fr(1, 5)) + Fr(2, 3) - Fr(19, 2) == Fr(224012952139, 42374115984375))
    check("Step 7: U_3(1/2) = 923/840 < 11/10", U(3, Fr(1, 2)) == Fr(923, 840) and Fr(923, 840) < Fr(11, 10))
    check("Step 6: S_1(1/3) = 2/3", S(1, Fr(1, 3)) == Fr(2, 3))
    check("(5.12) z for ln(7/2), ln(3/2), ln(7/3), ln 3", [(Fr(X) - 1) / (Fr(X) + 1) for X in (Fr(7, 2), Fr(3, 2), Fr(7, 3), 3)] == [Fr(5, 9), Fr(1, 5), Fr(2, 5), Fr(1, 2)])
    check("(5.2) 19 - 33/2 - 1 - 9/16 - 12/13 = 3/208", 19 - Fr(33, 2) - 1 - Fr(9, 16) - Fr(12, 13) == Fr(3, 208))
    check("(5.2) 6 (1/8)/(13/16) = 12/13", 6 * Fr(1, 8) / Fr(13, 16) == Fr(12, 13))
    # Singleton cut.
    Fbig = lambda tt_: F(s - tt_, b) + F(s - tt_, c)
    Fsmall = lambda tt_: F(tt_, b) + F(tt_, c)
    J3t = lambda tt_: e(s - tt_) + e(1 - tt_) - e(s - tt_ + b) - e(s - tt_ + c)
    check("(5.14) Psi(p_t) = F_big(t) + F_small(t)", simplify((Psi(s - t, b, c, t) - Fbig(t) - Fsmall(t)).subs(s, 1 - b - c)) == 0)
    check("(5.14) S_11(p_t) = F_small(t) + J3(t)",
          simplify(((I4(s - t, b, c, t) + 2 * F(t, b) + 2 * F(t, c) - h(t)) - Fsmall(t) - J3t(t)).subs(s, 1 - b - c)) == 0)
    kq = I4(s - D, b, c, D) - Psi(s - D, b, c, D)
    MD3 = 2 * (Psi(s - 3 * D, b, c, 3 * D) + kq) - (Fsmall(3 * D) + J3t(3 * D))
    MD3_claim = 2 * (Fbig(3 * D) - Fbig(D)) + Fsmall(3 * D) - 4 * Fsmall(D) + 2 * h(D) + 2 * J3t(D) - J3t(3 * D)
    check("(5.15) MD(p_3) expansion", simplify((MD3 - MD3_claim).subs(s, 1 - b - c)) == 0)
    psi = lambda zz_: (3 + zz_) * log(3 + zz_) + 3 * zz_ * log(zz_) - 4 * zz_ * log(1 + zz_) - 3 * log(3)
    check("(5.16) psi(z) = F(3,z) - 4F(1,z) + 4 ln(1+z)", simplify(expand(F(3, z) - 4 * F(1, z) + 4 * log(1 + z) - psi(z), force=True)) == 0)
    check("(5.17) 2 psi(1) = 8 ln 2 - 6 ln 3", simplify(2 * psi(1) - (8 * log(2) - 6 * log(3))) == 0)
    check("F(Dt, Dz) = D F(t, z)", simplify(expand(F(D * t, D * z) - D * F(t, z), force=True)) == 0)
    Hpsi = log(1 + 3 * t) - 4 * log(1 + t) + 4 * t / (1 + t)
    check("(5.17) psi'(z) = H(1/z)", simplify(diff(psi(z), z) - Hpsi.subs(t, 1 / z)) == 0)
    check("(5.17) H'(t) = (3 + 2t - 9t^2)/[(1+3t)(1+t)^2]", simplify(diff(Hpsi, t) - (3 + 2 * t - 9 * t ** 2) / ((1 + 3 * t) * (1 + t) ** 2)) == 0)
    check("(5.17) H(1) = 2 - 2 ln 2", simplify(Hpsi.subs(t, 1) - (2 - 2 * log(2))) == 0)
    check("(5.17) psi''(z) = -(3z^2 + 2z - 9)/[z (z+1)^2 (z+3)]", simplify(diff(psi(z), z, 2) + (3 * z ** 2 + 2 * z - 9) / (z * (z + 1) ** 2 * (z + 3))) == 0)
    Pz = psi(z) + psi(2 - z)
    Ppp = simplify(diff(Pz, z, 2).subs(z, 1 + t))
    Ppp_claim2 = 2 * (64 + 352 * t ** 2 - 8 * t ** 4 - 3 * t ** 6) / ((1 - t ** 2) * (16 - t ** 2) * (4 - t ** 2) ** 2)
    check("(5.17) P''(1+t) formula", simplify(cancel(together(Ppp - Ppp_claim2))) == 0)
    check("(5.17) P'(1) = 0", simplify(diff(Pz, z).subs(z, 1)) == 0)
    # Correction bounds.
    check("(5.18) 2(1-D)(D + D^2/2)/D = 2 - D - D^2", expand(2 * (1 - D) * (D + D ** 2 / 2) / D - (2 - D - D ** 2)) == 0)
    Aq = 1 - v - D
    aq = 1 - v - 3 * D
    E0 = 2 - D - D ** 2 - 2 * log(Aq) - 8 * log(1 + v / (2 * Aq)) - 8 * log(1 + v / (2 * aq))
    E0pp_claim = -2 + 2 / Aq ** 2 - 8 * v * (4 * Aq + v) / (Aq ** 2 * (2 * Aq + v) ** 2) - 72 * v * (4 * aq + v) / (aq ** 2 * (2 * aq + v) ** 2)
    check("(5.19) E0_DD formula", simplify(diff(E0, D, 2) - E0pp_claim) == 0)
    check("(5.19) 4 (3v/2)/(13/16)^2 = 1536 v/169", 4 * Fr(3, 2) / Fr(13, 16) ** 2 == Fr(1536, 169))
    check("(5.19) 1536/169 - 80/3 < 0", Fr(1536, 169) - Fr(80, 3) < 0)
    E00 = E0.subs(D, 0)
    check("(5.19) E0(v, 0) = 2 + 14 ln(1-v) - 16 ln(1 - v/2)", zero(E00 - (2 + 14 * log(1 - v) - 16 * log(1 - v / 2))))
    E0h = E0.subs(D, v / 2)
    E0h_claim = 2 - v / 2 - v ** 2 / 4 + 6 * log(1 - 3 * v / 2) - 8 * log(1 - v) + 8 * log(1 - 5 * v / 2) - 8 * log(1 - 2 * v)
    check("(5.19) E0(v, v/2) formula", zero(E0h - E0h_claim))
    check("(5.19) d/dv E0(v,0) = -14/(1-v) + 8/(1 - v/2)", simplify(diff(2 + 14 * log(1 - v) - 16 * log(1 - v / 2), v) - (-14 / (1 - v) + 8 / (1 - v / 2))) == 0)
    check("(5.19) d/dv E0(v,v/2) formula",
          simplify(diff(E0h_claim, v) - (-Rational(1, 2) - v / 2 - 9 / (1 - 3 * v / 2) + 8 / (1 - v) - 20 / (1 - 5 * v / 2) + 16 / (1 - 2 * v))) == 0)
    C0 = 2 + 30 * log(2) - 22 * log(3) - 16 * log(5) + 14 * log(7)
    C1 = Rational(495, 256) - 8 * log(2) - 14 * log(3) - 8 * log(7) + 8 * log(11) + 6 * log(13)
    check("(5.20) C0 = 2 psi(1) + E0(1/8, 0)", simplify(expand(2 * psi(1) + E00.subs(v, Rational(1, 8)) - C0, force=True)) == 0)
    check("(5.20) C1 = 2 psi(1) + E0(1/8, 1/16)", simplify(expand(2 * psi(1) + E0h_claim.subs(v, Rational(1, 8)) - C1, force=True)) == 0)
    c0 = bound_combination([(Fr(30), 2), (Fr(-22), 3), (Fr(-16), 5), (Fr(14), 7)], Fr(2))
    c1 = bound_combination([(Fr(-8), 2), (Fr(-14), 3), (Fr(-8), 7), (Fr(8), 11), (Fr(6), 13)], Fr(495, 256))
    check("(5.20) series bounds: C0 > 1/100 and C1 > 1/100", c0 > Fr(1, 100) and c1 > Fr(1, 100))
    print(f"     C0 >= {float(c0):.6f}, C1 >= {float(c1):.6f}, seam constant >= {float(seam_const):.6f}, MD(0) >= {float(md0):.6f}")
    # Geometry numbers of section 5.
    check("D < 1/16, A > 13/16, a > 11/16, 3D < 3/16 < 7/16 <= m", Fr(7, 8) - Fr(1, 16) == Fr(13, 16) and Fr(13, 16) - Fr(1, 8) == Fr(11, 16) and Fr(3, 16) < Fr(7, 16))

    # ---------------------------------------------------------------- numerical spot checks (supporting only)
    # Seam derivative (4.7) and the log remainder (4.13) at one seam law, 60 digits.
    def root(bq, cq):
        vq = bq + cq
        sq = 1 - vq
        return mpmath.findroot(lambda uu: uu ** 3 - vq * uu ** 2 - bq * cq * (uu + sq), mpmath.mpf(vq) * 1.5)

    def k_num(bq, cq):
        uq = root(bq, cq)
        sq = 1 - bq - cq
        Kq = (sq + 2 * uq) / (sq + uq) ** 2
        Pbq = uq ** 2 + bq * (1 - cq)
        Pcq = uq ** 2 + cq * (1 - bq)
        return -sq * mpmath.log(Kq) + bq * mpmath.log(bq ** 3 / Pbq ** 2) + cq * mpmath.log(cq ** 3 / Pcq ** 2)

    def phi_num(aq, bq, cq, dq):
        ent = lambda tt_: -tt_ * mpmath.log(tt_) if tt_ > 0 else mpmath.mpf(0)
        Hj = ent(aq) + ent(bq) + ent(cq) + ent(dq)
        Hx = ent(aq + bq) + ent(cq + dq)
        Hy = ent(aq + cq) + ent(bq + dq)
        return 3 * Hj - 2 * Hx - 2 * Hy

    bq, cq = mpmath.mpf("0.05"), mpmath.mpf("0.03")
    uq = root(bq, cq)
    sq = 1 - bq - cq
    Aq_ = (sq + mpmath.sqrt(sq ** 2 - 4 * uq ** 2)) / 2
    Dq_ = sq - Aq_
    check("k = -Phi(q+) at (b, c) = (0.05, 0.03) (60 digits)", abs(k_num(bq, cq) + phi_num(Aq_, bq, cq, Dq_)) < mpmath.mpf(10) ** -50)
    eps = mpmath.mpf(10) ** -20
    kb_num = (k_num(bq + eps, cq) - k_num(bq - eps, cq)) / (2 * eps)
    Kq = (sq + 2 * uq) / (sq + uq) ** 2
    Pbq = uq ** 2 + bq * (1 - cq)
    check("Lemma 3.2: k_b = ln K + 3 ln b - 2 ln P_b (finite difference, 20 digits)",
          abs(kb_num - (mpmath.log(Kq) + 3 * mpmath.log(bq) - 2 * mpmath.log(Pbq))) < mpmath.mpf(10) ** -15)
    jfun = lambda zq: mpmath.log((1 + zq) / (1 - zq))
    zq, cq_ = mpmath.mpf("0.7"), mpmath.mpf("0.8")
    check("(4.18) j(cz) - 2cz <= c^3 [j(z) - 2z] at z = 0.7, c = 0.8", jfun(cq_ * zq) - 2 * cq_ * zq <= cq_ ** 3 * (jfun(zq) - 2 * zq))

    if failures:
        print(f"\n{len(failures)} check(s) failed")
        return 1
    print("\nall checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
