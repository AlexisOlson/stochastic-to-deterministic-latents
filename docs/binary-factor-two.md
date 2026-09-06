# Binary factor two

This page proves the binary constant two. It is `paper proof` in the sense of
the [claim ledger](claims.md#status-vocabulary): a complete rigorous prose
derivation with no unresolved step, not formalized. No Lean
declaration in this repository states it. Where a kernel-verified declaration
supplies an input, it is quoted in its own words.

Write a binary law as $`p = (a,b,c,d) = (p_{00},p_{01},p_{10},p_{11})`$ and put
$`\Delta = ad - bc`$.

> **Binary factor-two theorem.** For every binary $`2 \times 2`$ law $`p`$,
>
> ```math
> T(p) \le 2\,\tau(p).
> ```
>
> If $`p`$ has full support, the witness can be read off the law: either the
> constant code or one of the four singleton codes (the code whose only
> nontrivial class is one cell) has $`D_p(g) \le 2\,\tau(p)`$; when
> $`\Delta > 0`$ the singleton may be taken at a lightest diagonal cell, and when
> $`\Delta < 0`$ at a lightest off-diagonal cell.

The inequality is the ledger row [`BIN-C2`](claims.md#ledger). Its right-hand
side is the exact stochastic optimum of the
[binary stochastic optimum](binary-stochastic-optimum.md) page: $`\tau(p)`$ is
either $`I_p(X;Y)`$, in which case there is nothing to prove, or
$`\Psi(p) - \Phi(q^+)`$ with $`q^+`$ one of the two diagonal-swap contacts
located by one cubic root. The proof compares two deterministic scores with
that value along each contact chord. On the chord, the singleton margin is
concave and the constant margin has no interior minimum on any subinterval, so
one point at which both margins are nonnegative, together with a nonnegative
singleton margin at the chord center, settles the whole chord. That
point is the chord center when the disagreement mass $`b + c`$ is at least
$`1\text{/}8`$, and a fixed cut at three times the smaller contact mass when it is
smaller. Laws with a zero cell inherit the bound from the kernel-verified
transfer theorem of [`SparseLimit`](../StochasticToDeterministicLatents/SparseLimit.lean).

The constant is not claimed to be sharp, and nothing here identifies the laws
that maximize $`T(p)\text{/}\tau(p)`$. See [section 7](#7-scope-and-formalization).

| Step | Sections |
|---|---|
| Units, the five codes, and the symmetries | [1](#1-setting) |
| The contact chord and the cut theorem | [2](#2-the-contact-chord) |
| The contact potential and its radial curvature | [3](#3-the-contact-potential) |
| The center theorem | [4](#4-the-center) |
| The fixed cut at three times the smaller contact mass | [5](#5-the-fixed-cut) |
| Assembly on full support, then every law | [6](#6-assembly) |
| Scope and Lean targets | [7](#7-scope-and-formalization) |

## 1. Setting

**Units.** Everything on this page is in natural logarithms. The entropies
$`H`$, the functionals $`\Psi`$ and $`\Phi`$ of the
[blueprint](blueprint.md#1-laws-entropy-and-codes) and the
[score decomposition](binary-factor-nine.md#the-score-decomposition), the
mutual information $`I_p(X;Y)`$, the scores $`D_p(g)`$, and the optima
$`\tau(p)`$ and $`T(p)`$ all denote $`\ln 2`$ times the bit-valued quantities
used elsewhere in this repository. Every statement compared below is
homogeneous of degree one in this factor, so each inequality proved here holds
verbatim in bits; a numerical margin such as $`1\text{/}200`$ is a margin in nats and
becomes $`1\text{/}(200 \ln 2)`$ in bits. Write

```math
\eta(t) = t \ln t, \qquad h(t) = -\eta(t) - \eta(1-t), \qquad
F(x,y) = \eta(x+y) - \eta(x) - \eta(y),
```

with $`\eta(0) = 0`$. For a law $`p'`$ on the four cells,

```math
\begin{aligned}
\Psi(p') &= 2\,H(p') - H(p'_X) - H(p'_Y), \\
\Phi(p') &= 3\,H(p') - 2\,H(p'_X) - 2\,H(p'_Y), \\
\Psi(p') - \Phi(p') &= H(p'_X) + H(p'_Y) - H(p') = I_{p'}(X;Y). \qquad \text{(1.1)}
\end{aligned}
```

**Public inputs.** The proof uses the following results of the
[binary stochastic optimum](binary-stochastic-optimum.md) page, all at
`paper proof`, and three kernel-verified declarations.

- [Theorem 6.6](binary-stochastic-optimum.md#6-the-cubic) (the cubic decides
  and locates the optimum), with [Lemma 6.1](binary-stochastic-optimum.md#6-the-cubic)
  on the root and [Lemma 6.4](binary-stochastic-optimum.md#6-the-cubic) on the
  tangent coefficients of a contact, together with display (1.2) of that page,
  $`\tau(p) \le T(p) \le I_p(X;Y)`$ with equality throughout when
  $`\tau(p) = I_p(X;Y)`$.
- [Theorem 3.2](binary-stochastic-optimum.md#3-the-deficit-and-the-tangent-test)
  (the tangent test), used once, for a single reference law in
  [section 4](#4-the-center), and
  [Lemma 3.1](binary-stochastic-optimum.md#3-the-deficit-and-the-tangent-test)
  (the derivative of $`\Phi`$), the envelope step of Lemma 3.2 and of
  Theorem 5.2 below.
- `exists_optimalCode` in
  [Deterministic](../StochasticToDeterministicLatents/Deterministic.lean):
  $`T(p)`$ is an attained minimum over the finite code space, and
  `T_le_detScore`: $`T(p) \le D_p(g)`$ for every code $`g`$.
- `T_le_mul_tau_of_forall_fullSupport` in
  [SparseLimit](../StochasticToDeterministicLatents/SparseLimit.lean): for
  $`C \ge 0`$, if $`T(p) \le C\,\tau(p)`$ for every full-support law, then
  $`T(p) \le C\,\tau(p)`$ for every law.

The tangent function of a law $`q`$ with support $`S`$, in the units of this
page, is

```math
\ell_q(r) = \sum_{z = (x,y) \in S} r_z\,\ln\left( \frac{\mu_x^2\,\nu_y^2}{q_z^3} \right),
\qquad \mu = q_X,\ \nu = q_Y, \qquad \text{(1.2)}
```

the display (3.1) of the stochastic-optimum page with $`\log_2`$ replaced by
$`\ln`$. It satisfies $`\ell_q(q) = \Phi(q)`$ by direct substitution.

**The five codes.** A code on four cells is a partition of the cells. Two kinds
are used: the constant code, with one class, and the four singleton codes
$`g_z`$, whose classes are $`\{z\}`$ and its complement. Write
$`S_z(p) = D_p(g_z)`$.

**Lemma 1.1 (scores of the five codes).** The constant code has
$`D_p = I_p(X;Y)`$. For a cell $`z`$ with mass $`x`$, let $`y`$ be the mass of the
other cell in its row and $`y'`$ the mass of the other cell in its column. Then

```math
S_z(p) = I_p(X;Y) + 2\,F(x,y) + 2\,F(x,y') - h(x). \qquad \text{(1.3)}
```

*Proof.* For any code $`g`$, the chain rule gives
$`I(X;Y \mid g) = H(X \mid g) + H(Y \mid g) - H(X,Y \mid g)`$, and since $`g`$ is a
function of $`(X,Y)`$, $`H(X,Y \mid g) = H(X,Y) - H(g)`$, $`H(X \mid g) = H(X,g) - H(g)`$,
$`H(g \mid X) = H(X,g) - H(X)`$. Adding,

```math
D_p(g) - I_p(X;Y) = 2\,H(g \mid X) + 2\,H(g \mid Y) - H(g). \qquad \text{(1.4)}
```

For the constant code every term on the right vanishes. For $`g_z`$, the
indicator of the cell has $`H(g_z) = h(x)`$; conditional on the row of $`z`$,
which has mass $`x + y`$, it is a Bernoulli variable of parameter
$`x\text{/}(x+y)`$, and it is constant on the other row, so
$`H(g_z \mid X) = (x+y)\,h(x\text{/}(x+y)) = F(x,y)`$; likewise
$`H(g_z \mid Y) = F(x,y')`$.

**Lemma 1.2 (symmetries).** Let $`\sigma`$ be a bijection of the four cells
induced by relabeling $`X`$, relabeling $`Y`$, or exchanging the roles of
$`X`$ and $`Y`$, and let $`\sigma p`$ be the transported law. Then
$`\tau(\sigma p) = \tau(p)`$, $`T(\sigma p) = T(p)`$, and
$`D_{\sigma p}(g \circ \sigma^{-1}) = D_p(g)`$ for every code $`g`$. Exchanging
$`X`$ and $`Y`$ sends $`(a,b,c,d)`$ to $`(a,c,b,d)`$; relabeling both
observables and then exchanging them sends $`(a,b,c,d)`$ to $`(d,b,c,a)`$.
Both preserve $`\Delta`$. Relabeling $`Y`$ alone sends $`(a,b,c,d)`$ to
$`(b,a,d,c)`$ and changes the sign of $`\Delta`$.

*Proof.* Each of the three operations is a bijection of the observation space
that maps rows to rows and columns to columns (possibly exchanging the two
families). Every entropy in the score of a latent or a code is invariant under
such a bijection; latents and codes transport bijectively, so the two optima
are preserved. The three coordinate formulas are read off the cell map:
relabeling both observables exchanges the cells $`(0,0)`$ and $`(1,1)`$ and
the cells $`(0,1)`$ and $`(1,0)`$, giving $`(d,c,b,a)`$, and the exchange then
returns the off-diagonal cells to their places.

**Lemma 1.3 (rational enclosures of logarithms).** For $`0 < \zeta < 1`$ and
$`N \ge 1`$ put

```math
S_N(\zeta) = 2 \sum_{j=0}^{N-1} \frac{\zeta^{2j+1}}{2j+1}, \qquad
U_N(\zeta) = S_N(\zeta) + \frac{2\,\zeta^{2N+1}}{(2N+1)(1-\zeta^2)}.
```

Then $`S_N(\zeta) \le \ln \frac{1+\zeta}{1-\zeta} \le U_N(\zeta)`$. For a rational
$`Y > 1`$, $`\ln Y = \ln \frac{1+\zeta}{1-\zeta}`$ with $`\zeta = (Y-1)\text{/}(Y+1) \in (0,1)`$;
for a large $`Y`$ one may instead write $`Y = 2^j Y'`$ with $`Y' \in [1,2)`$ and
$`\ln Y = j \ln 2 + \ln Y'`$, with $`\ln 2`$ enclosed at $`\zeta = 1\text{/}3`$.

*Proof.* $`\ln \frac{1+\zeta}{1-\zeta} = 2 \int_0^\zeta \frac{dr}{1-r^2} = 2 \sum_{j \ge 0} \frac{\zeta^{2j+1}}{2j+1}`$
with all terms positive; replacing every denominator of the tail by $`2N+1`$
and summing the geometric series gives the upper bound.

Every scalar comparison on this page is a finite combination of logarithms of
small rationals with rational coefficients, decided by these enclosures with
$`N \le 8`$; `scripts/check_factor_two_identities.py` replays each of them in
exact rational arithmetic, together with the algebraic identities of the page.
The script is a convenience for the reader and is not proof evidence.

## 2. The contact chord

Throughout sections 2 to 5, $`p = (a,b,c,d)`$ has full support and, after the
symmetries of Lemma 1.2,

```math
\Delta > 0, \qquad a \ge d, \qquad b \ge c > 0. \qquad \text{(2.1)}
```

Put $`s = a + d`$, $`v = b + c`$, $`w = bc`$, $`m = s\text{/}2`$, and let $`u_0`$ be the
positive root of

```math
f(u) = u^3 - v u^2 - w u - w s.
```

By [Theorem 6.6](binary-stochastic-optimum.md#6-the-cubic), either
$`\sqrt{ad} \le u_0`$, and then $`\tau(p) = I_p(X;Y)`$ and $`T(p) = \tau(p)`$ by
display (1.2) of that page, or
$`\sqrt{ad} > u_0`$. Assume the latter, and call $`p`$ nonconstant. Set

```math
\rho = \sqrt{\smash[b]{s^2 - 4u_0^2}}, \qquad A = \frac{s + \rho}{2}, \qquad D = \frac{s - \rho}{2},
\qquad q^+ = (A, b, c, D),
```

so that $`A + D = s`$ and $`AD = u_0^2`$ ($`D`$ is a cell mass; the deterministic
score keeps its subscript, $`D_p(g)`$). For $`m \le a' \le A`$ the chord law is

```math
p_{a'} = (a', b, c, s - a').
```

**Lemma 2.1 (the chord).** Under (2.1) with $`p`$ nonconstant:

1. $`v < u_0 < m`$, $`u_0 > \sqrt{w}`$, $`0 < D < m < A`$, and $`v < 1\text{/}3`$.
2. $`p = p_a`$ with $`m \le a < A`$.
3. Every $`p_{a'}`$ with $`m \le a' \le A`$ has full support and
   $`\det p_{a'} \ge u_0^2 - w > 0`$; for $`m \le a' < A`$ it is nonconstant, and
   $`p_A = q^+`$ is constant-optimal.
4. On the closed chord,

   ```math
   \tau(p_{a'}) = \Psi(p_{a'}) + k, \qquad k = -\Phi(q^+), \qquad m \le a' \le A. \qquad \text{(2.2)}
   ```

*Proof.* (1) [Lemma 6.1](binary-stochastic-optimum.md#6-the-cubic) gives
$`u_0 > v`$, and $`u_0 < \sqrt{ad} \le (a+d)\text{/}2 = m`$. Also
$`f(\sqrt{w}) = w^{3\text{/}2} - vw - w^{3\text{/}2} - ws = -w\,(v + s) = -w < 0`$, so
$`u_0 > \sqrt{w}`$ by the sign pattern of Lemma 6.1. Since $`u_0 < m`$, $`\rho > 0`$ and
$`D < m < A`$, with $`D > 0`$ because $`AD = u_0^2 > 0`$. Finally $`v < u_0 < m = (1-v)\text{/}2`$
gives $`v < 1\text{/}3`$.

(2) $`a \ge d`$ gives $`a \ge m`$. On $`[m, s]`$ the function $`x \to x(s-x)`$ is
strictly decreasing, and $`a(s-a) = ad > u_0^2 = A(s-A)`$, so $`a < A`$.

(3) The cells $`a'`$ and $`s - a' \ge D > 0`$ are positive, and
$`a'(s-a') \ge A D = u_0^2 > w`$. The laws $`p_{a'}`$ share $`b`$, $`c`$, $`s`$, hence
the cubic and its root $`u_0`$; for $`a' < A`$, $`a'(s-a') > u_0^2`$ places them in the
mixed case of Theorem 6.6, and at $`a' = A`$, $`\sqrt{AD} = u_0`$ places $`q^+`$ in
the constant case.

(4) For $`a' < A`$, Theorem 6.6 gives $`\tau(p_{a'}) = \Psi(p_{a'}) - \Phi(q^+)`$
with the same pair $`q^\pm`$ for every point of the chord, since the pair is
determined by $`b`$, $`c`$, $`s`$, and $`u_0`$. At $`a' = A`$,
$`\tau(q^+) = I_{q^+}(X;Y) = \Psi(q^+) - \Phi(q^+)`$ by (1.1).

**The two margins.** For $`m \le a' \le A`$ define

```math
\begin{aligned}
M_0(a') &= 2\,\tau(p_{a'}) - I_{p_{a'}}(X;Y), \\
M_1(a') &= 2\,\tau(p_{a'}) - S_{11}(p_{a'}),
\end{aligned}
```

the margins of the constant code and of the singleton code at the cell
$`(1,1)`$, whose mass $`s - a' \le m`$ is the smaller diagonal cell. By
`T_le_detScore`,

```math
M_0(a') \ge 0 \ \text{or}\ M_1(a') \ge 0 \implies T(p_{a'}) \le 2\,\tau(p_{a'}). \qquad \text{(2.3)}
```

Write $`J(a') = H(p_{a'})`$, $`R_X(a') = h(a' + b)`$, $`R_Y(a') = h(a' + c)`$ for the
joint and marginal entropies, so that $`I = R_X + R_Y - J`$ and
$`\Psi = 2J - R_X - R_Y`$. By (2.2) and (1.3), with $`d' = s - a'`$,

```math
\begin{aligned}
M_0(a') &= 5J - 3R_X - 3R_Y + 2k \\
&= -5\,[\eta(a') + \eta(b) + \eta(c) + \eta(d')] + 3\,[\eta(a'+b) + \eta(c+d')] + 3\,[\eta(a'+c) + \eta(b+d')] + 2k, \qquad \text{(2.4)} \\[1ex]
M_1(a') &= M_0(a') - 2F(d',b) - 2F(d',c) + h(d') \\
&= -5\eta(a') - 3\eta(b) - 3\eta(c) - 2\eta(d') + 3\eta(a'+b) + 3\eta(a'+c) + \eta(c+d') + \eta(b+d') - \eta(a'+b+c) + 2k. \qquad \text{(2.5)}
\end{aligned}
```

The second line of (2.5) is the first with $`F`$ and $`h`$ expanded and
$`1 - d' = a' + b + c`$.

**Lemma 2.2 (the contact end).** $`M_0(A) = I_{q^+}(X;Y) > 0`$.

*Proof.* By (2.2) at $`a' = A`$, $`M_0(A) = 2\,I_{q^+}(X;Y) - I_{q^+}(X;Y)`$. The
mutual information of a full-support law vanishes only for a product law, and
$`q^+`$ is not one: $`AD = u_0^2 > w = bc`$ by Lemma 2.1.

**Lemma 2.3 (the singleton margin is concave).** $`M_1`$ is strictly concave
on $`[m, A]`$.

*Proof.* Differentiate (2.5) twice along $`d' = s - a'`$, using
$`\eta''(t) = 1\text{/}t`$ and $`(d')' = -1`$:

```math
M_1''(a') = -\frac{5}{a'} - \frac{2}{d'} + \frac{3}{a'+b} + \frac{3}{a'+c} + \frac{1}{d'+b} + \frac{1}{d'+c} - \frac{1}{a'+b+c}. \qquad \text{(2.6)}
```

The $`d'`$ terms are negative: $`1\text{/}(d'+b) + 1\text{/}(d'+c) < 2\text{/}d'`$. For the $`a'`$
terms put $`K_x(b,c) = -5\text{/}x + 3\text{/}(x+b) + 3\text{/}(x+c) - 1\text{/}(x+b+c)`$ for fixed
$`x > 0`$. Then $`K_x(0,0) = 0`$ and
$`\partial_b K_x = -3\text{/}(x+b)^2 + 1\text{/}(x+b+c)^2 < 0`$, symmetrically in $`c`$, so
$`K_x(b,c) < 0`$ whenever $`b + c > 0`$. Hence $`M_1'' < 0`$.

**Lemma 2.4 (the constant margin has no interior minimum).** $`M_0`$ is
nondecreasing on $`[m, a_1]`$ and nonincreasing on $`[a_1, A]`$ for some
$`a_1 \in [m, A]`$. Consequently, for $`m \le x \le y \le z \le A`$,

```math
M_0(y) \ge \min\{ M_0(x), M_0(z) \}. \qquad \text{(2.7)}
```

*Proof.* Differentiating (2.4) twice, and grouping the marginal terms by
pairs of complementary masses ($`1\text{/}(a'+b) + 1\text{/}(b+d') = (s + 2b)\text{/}((a'+b)(b+d'))`$
and $`(a'+b)(b+d') = a'd' + b(s+b)`$),

```math
M_0''(a') = -\frac{5s}{\lambda} + \frac{3\,(s+2b)}{\lambda + p_b} + \frac{3\,(s+2c)}{\lambda + p_c}, \qquad
\lambda = a'd', \quad p_b = b\,(s+b), \quad p_c = c\,(s+c), \qquad \text{(2.8)}
```

($`\lambda`$ is not the mixture weight of the stochastic-optimum page.) Multiplying by $`\lambda\,(\lambda+p_b)(\lambda+p_c) > 0`$ gives a quadratic
$`N(\lambda) = -5s\,(\lambda+p_b)(\lambda+p_c) + 3(s+2b)\,\lambda\,(\lambda+p_c) + 3(s+2c)\,\lambda\,(\lambda+p_b)`$ with
leading coefficient $`-5s + 6s + 6v = s + 6v = 1 + 5v > 0`$ and constant term
$`-5s\,p_b\,p_c < 0`$. So $`N`$ has exactly one positive root $`\lambda_0`$, is negative on
$`(0, \lambda_0)`$ and positive beyond. Along the chord, $`\lambda = a'(s - a')`$ decreases
strictly from $`m^2`$ to $`u_0^2`$ as $`a'`$ runs from $`m`$ to $`A`$. Hence there is
$`a_0 \in [m, A]`$ with $`M_0'' \ge 0`$ on $`[m, a_0]`$ and $`M_0'' \le 0`$ on $`[a_0, A]`$.
The right side of (2.4), regarded as a function of $`a' \in (0, s)`$, is unchanged
when the two diagonal cells are exchanged ($`J`$ and $`k`$ are fixed and $`R_X`$,
$`R_Y`$ trade places), so it is symmetric about $`m`$ and $`M_0'(m) = 0`$. Therefore $`M_0'`$
rises from $`0`$ on $`[m, a_0]`$ and falls on $`[a_0, A]`$, crossing zero at most
once, at some $`a_1 \ge a_0`$. A function that is nondecreasing then nonincreasing
on an interval takes its minimum over any subinterval at an endpoint of that
subinterval, which is (2.7).

**Theorem 2.5 (the cut theorem).** Under (2.1) with $`p`$ nonconstant, each of
the following implies $`T(p_{a'}) \le 2\,\tau(p_{a'})`$ for every $`a' \in [m, A]`$,
in particular for $`p`$:

- (G0) $`M_0(m) \ge 0`$;
- (GC) there is $`a_{\mathrm{cut}} \in [m, A]`$ with $`M_1(m) \ge 0`$, $`M_1(a_{\mathrm{cut}}) \ge 0`$, and $`M_0(a_{\mathrm{cut}}) \ge 0`$.

Under (GC) the singleton code at the lighter diagonal cell is a witness on
$`[m, a_{\mathrm{cut}}]`$ and the constant code on $`[a_{\mathrm{cut}}, A]`$; under (G0) the constant code is a
witness on the whole chord.

*Proof.* (G0): by (2.7) with $`x = m`$, $`z = A`$ and Lemma 2.2,
$`M_0 \ge \min\{M_0(m), M_0(A)\} \ge 0`$ on the chord. (GC): on $`[m, a_{\mathrm{cut}}]`$, the
concave function $`M_1`$ lies above the chord joining its two nonnegative
endpoint values; on $`[a_{\mathrm{cut}}, A]`$, (2.7) and Lemma 2.2 give
$`M_0 \ge \min\{M_0(a_{\mathrm{cut}}), M_0(A)\} \ge 0`$. Conclude by (2.3).

## 3. The contact potential

The constant $`k = -\Phi(q^+)`$ of (2.2) depends on $`(b,c)`$ alone. This
section computes it, its gradient, and its curvature along rays of fixed
imbalance.

**Lemma 3.1 (closed form).** With $`u_0`$, $`A`$, $`D`$ as in section 2,

```math
K = \frac{s + 2u_0}{(s + u_0)^2}, \qquad P_b = u_0^2 + b\,(1-c), \qquad P_c = u_0^2 + c\,(1-b),
```

```math
k = -s \ln K + b \ln \frac{b^3}{P_b^2} + c \ln \frac{c^3}{P_c^2}. \qquad \text{(3.1)}
```

*Proof.* $`\Phi(q^+) = \ell_{q^+}(q^+)`$ by display (1.2). The rows of $`q^+`$ are
$`(A+b, c+D)`$ and its columns $`(A+c, b+D)`$. At the cell $`(0,1)`$ the
coefficient is $`\ln\left( (A+b)^2 (b+D)^2 \text{/} b^3 \right)`$, and
$`(A+b)(D+b) = AD + b\,(A+D) + b^2 = u_0^2 + b\,(s+b) = P_b`$ because $`s + b = 1 - c`$.
Likewise the coefficient at $`(1,0)`$ is $`\ln (P_c^2 \text{/} c^3)`$. At the two
diagonal cells the coefficients are $`\ln\left( (A+b)^2(A+c)^2 \text{/} A^3 \right)`$ and
$`\ln\left( (D+b)^2(D+c)^2 \text{/} D^3 \right)`$, and they are equal: the computation in
[Lemma 6.4](binary-stochastic-optimum.md#6-the-cubic) shows that
$`A^{3\text{/}2}(D+b)(D+c) - D^{3\text{/}2}(A+b)(A+c)`$ is a multiple of $`f(\sqrt{AD}) = f(u_0) = 0`$.
Their common value is half the logarithm of the product,
$`(A+b)^2(A+c)^2(D+b)^2(D+c)^2 \text{/} (AD)^3 = P_b^2 P_c^2 \text{/} u_0^6`$, that is
$`\ln (P_b P_c \text{/} u_0^3)`$. To evaluate this, rewrite the cubic
$`u_0^2 (u_0 - v) = w\,(u_0 + s)`$ as

```math
u_0^2 - w = \frac{u_0^2}{u_0 + s} =: g, \qquad \text{(3.2)}
```

using $`s + v = 1`$. Then $`P_b = g + b`$, $`P_c = g + c`$, and
$`P_b P_c = g^2 + g v + w = g^2 + g(v - 1) + u_0^2 = g^2 - gs + u_0^2`$. Substituting
$`g`$,

```math
P_b P_c = \frac{u_0^2\,[\,u_0^2 - s(u_0 + s) + (u_0 + s)^2\,]}{(u_0+s)^2} = \frac{u_0^3\,(2u_0 + s)}{(u_0 + s)^2},
```

so $`P_b P_c \text{/} u_0^3 = K`$. Summing the coefficients against the cells of
$`q^+`$, $`\Phi(q^+) = (A + D) \ln K + b \ln (P_b^2\text{/}b^3) + c \ln (P_c^2 \text{/} c^3)`$,
and $`A + D = s`$.

**Lemma 3.2 (gradient).** On the open set of $`(b,c)`$ with $`b, c > 0`$ and
$`v < u_0 < m`$, the root $`u_0`$ and hence $`q^+`$ and $`k`$ are smooth functions
of $`(b,c)`$, and

```math
\partial_b k = \ln K + 3 \ln b - 2 \ln P_b, \qquad \partial_c k = \ln K + 3 \ln c - 2 \ln P_c. \qquad \text{(3.3)}
```

*Proof.* The root is simple: $`f'(u_0) = 3u_0^2 - 2vu_0 - w = (u_0^2 - w) + 2u_0(u_0 - v) > 0`$
by Lemma 2.1. The implicit function theorem makes $`u_0`$ smooth in the
coefficients, hence in $`(b,c)`$; $`\rho > 0`$ on this set, so $`A`$, $`D`$, and
$`q^+`$ are smooth. A variation of $`(b,c)`$ moves $`q^+`$ along a vector
$`\chi`$ with zero coordinate sum, and $`q^+`$ is interior to the simplex, so
[Lemma 3.1](binary-stochastic-optimum.md#3-the-deficit-and-the-tangent-test) of
the stochastic-optimum page gives $`\Phi(q^+)' = \ell_{q^+}(\chi)`$. By the
coefficients computed in the proof of Lemma 3.1,

```math
\ell_{q^+}(\chi) = \ln K \cdot (\chi_{00} + \chi_{11}) + \ln \frac{P_b^2}{b^3}\,\chi_{01} + \ln \frac{P_c^2}{c^3}\,\chi_{10},
```

and $`\chi_{00} + \chi_{11} = -\chi_{01} - \chi_{10}`$ because the coordinates of $`\chi`$ sum to zero. Take $`\chi`$ to be the velocity of $`q^+`$ under a unit change of $`b`$ (so $`\chi_{01} = 1`$, $`\chi_{10} = 0`$), then under a unit change of $`c`$; negating gives (3.3).

**The contact chart.** Put

```math
x = \frac{b}{u_0}, \quad y = \frac{c}{u_0}, \quad r = x + y, \quad \omega = xy, \quad n = (1 - r)(1 - \omega).
```

**Lemma 3.3 (chart).** On the set of Lemma 3.2,

```math
u_0 = \frac{\omega}{n}, \qquad v = \frac{r \omega}{n}, \qquad s = \frac{1 - r - \omega}{n}, \qquad
u_0 - v = \frac{\omega}{1 - \omega}, \qquad s - 2u_0 = \frac{1 - r - 3\omega}{n}, \qquad \text{(3.4)}
```

and the set corresponds exactly to $`x, y > 0`$ with $`r + 3\omega < 1`$. In the
chart,

```math
K = \frac{(1-x)(1-y)(1-\omega)}{1-r}, \qquad P_b = \frac{b\,(1-x)}{1-r}, \qquad P_c = \frac{c\,(1-y)}{1-r}. \qquad \text{(3.5)}
```

*Proof.* Divide the cubic by $`u_0^2`$ and use $`w = \omega u_0^2`$, $`v = r u_0`$,
$`s = 1 - r u_0`$: $`u_0 - r u_0 - \omega\,(u_0 + 1 - r u_0) = 0`$, that is
$`u_0\,(1 - r - \omega + r\omega) = \omega`$, which is $`u_0 n = \omega`$. Since
$`u_0 > v = r u_0`$, $`r < 1`$; since $`u_0 n = \omega > 0`$, $`n > 0`$ and so
$`\omega < 1`$. The remaining formulas in (3.4) follow, and $`u_0 < m`$ is
$`1 - r - 3\omega > 0`$. Conversely, $`x, y > 0`$ with $`r + 3\omega < 1`$ give
$`r < 1`$, $`\omega < 1\text{/}3`$, positive $`b = x u_0`$, $`c = y u_0`$, $`s`$, and a
positive $`u_0`$ satisfying the cubic with $`u_0 > v`$ and $`u_0 < m`$; by Lemma 6.1
it is the positive root. For (3.5): $`s + 2u_0 = (1 - r + \omega)\text{/}n`$,
$`s + u_0 = (1 - r)\text{/}n`$, and $`1 - r + \omega = (1-x)(1-y)`$; and
$`P_b = u_0\,[u_0 + x - xy\,u_0] = u_0\,[x + u_0 (1 - \omega)] = u_0\,[x + \omega\text{/}(1-r)] = b\,(1 - r + y)\text{/}(1-r)`$.

**Radial derivatives.** Fix $`z \in [0, 1)`$ and move along the ray

```math
b = \frac{v\,(1+z)}{2}, \qquad c = \frac{v\,(1-z)}{2}, \qquad \delta = b - c = vz, \qquad \text{(3.6)}
```

with $`v`$ as the parameter; this $`z`$ is a number in $`[0, 1)`$, not a cell. Along
the ray $`v\,\partial_v = b\,\partial_b + c\,\partial_c =: \mathcal{D}`$.

**Lemma 3.4 (curvature of the potential).** Along any ray (3.6), inside the set
of Lemma 3.2, put $`L_k = v^2\,\partial_v^2 k`$. Then

```math
L_k = \frac{\omega\,(3\omega r - 4\omega - 2r^2 + 3r)}{(1 + \omega - r)(3 - 2r - \omega)}, \qquad \text{(3.7)}
```

```math
\frac{v}{s} - L_k = \frac{2\,\omega^2\,(1 - \omega)(2 - r)}{(1 - r - \omega)(1 + \omega - r)(3 - 2r - \omega)} > 0. \qquad \text{(3.8)}
```

*Proof.* By (3.3), $`\mathcal{D} k = v \ln K + 3\,[\eta(b) + \eta(c)] - 2\,[b \ln P_b + c \ln P_c]`$.
Since $`\mathcal{D} v = v`$, $`\mathcal{D}\,\eta(b) = \eta(b) + b`$, and
$`\mathcal{D}(b \ln P_b) = b \ln P_b + b\,\mathcal{D} \ln P_b`$,

```math
L_k = \mathcal{D}^2 k - \mathcal{D} k = v\,\mathcal{D} \ln K + 3v - 2b\,\frac{\mathcal{D} P_b}{P_b} - 2c\,\frac{\mathcal{D} P_c}{P_c}. \qquad \text{(3.9)}
```

The remaining derivatives come from the cubic, with $`\mathcal{D} v = v`$ and
$`\mathcal{D} w = 2w`$: differentiating $`f(u_0) = 0`$,

```math
\mathcal{D} u_0 = \frac{v\,(u_0^2 - w) + 2w\,(u_0 + s)}{f'(u_0)}, \qquad
\mathcal{D} P_b = 2u_0\,\mathcal{D}u_0 + b - 2w, \qquad \mathcal{D} P_c = 2u_0\,\mathcal{D}u_0 + c - 2w,
```

and $`\mathcal{D} \ln K = (2\,\mathcal{D}u_0 - v)\text{/}(s + 2u_0) - 2\,(\mathcal{D}u_0 - v)\text{/}(s + u_0)`$.
In the chart these become

```math
\frac{\mathcal{D} u_0}{u_0} = \frac{2 - r - r\omega}{3 - 2r - \omega}, \qquad
s\,\mathcal{D} \ln K = 3v - 2b\,\frac{\mathcal{D} P_b}{P_b} - 2c\,\frac{\mathcal{D} P_c}{P_c},
```

the first from the displayed $`\mathcal{D} u_0`$ and (3.4), and the second by
applying $`\mathcal{D} = (1 - \mathcal{D}u_0\text{/}u_0)\,(x\,\partial_x + y\,\partial_y)`$ to
(3.5), since $`\mathcal{D} x = x\,(1 - \mathcal{D}u_0\text{/}u_0)`$ for $`x = b\text{/}u_0`$ and
likewise for $`y`$, with $`1 - \mathcal{D}u_0\text{/}u_0 = (1-r)(1-\omega)\text{/}(3 - 2r - \omega)`$;
so (3.9) reads $`L_k = (v + s)\,\mathcal{D} \ln K = \mathcal{D} \ln K`$, and
$`\mathcal{D} \ln K`$ in the chart is the right side of (3.7). The check script
replays both identities. For (3.8), $`v\text{/}s = r\omega\text{/}(1 - r - \omega)`$
by (3.4), and the difference has the displayed denominator and numerator
$`\omega\,[\,r\,(1 + \omega - r)(3 - 2r - \omega) - (1 - r - \omega)(3\omega r - 4\omega - 2r^2 + 3r)\,]`$,
where the bracket expands to $`2\omega\,(1 - \omega)(2 - r)`$. Every factor is
positive: $`1 - r - \omega > 0`$ and $`1 + \omega - r > 0`$ from $`r + 3\omega < 1`$,
$`3 - 2r - \omega > 0`$ from $`r, \omega < 1`$.

The meaning of (3.8): $`-h''(v) = 1\text{/}(v(1-v))`$, so $`v^2 (-h''(v)) = v\text{/}s`$; the
convex contact correction $`k`$ curves less than the concave entropy of
mixing agreement with disagreement. That comparison is what makes both center
margins concave along rays.

## 4. The center

The center of the chord of section 2 is the law
$`p^\circ = (m, b, c, m)`$, $`m = (1-v)\text{/}2`$. This section proves:

**Theorem 4.1 (center theorem).** Under (2.1) with $`p`$ nonconstant:

1. if $`0 < v \le 1\text{/}8`$, then $`M_1(m) \ge 4v\text{/}125`$;
2. if $`v \ge 1\text{/}8`$, then $`M_0(m) > 0`$.

The margins at the center are functions of $`(b,c)`$ alone. Fix the imbalance
$`z = (b-c)\text{/}v \in [0,1)`$ and use the ray (3.6). The plan is: both margins
are concave in $`v`$ along the ray (Lemma 4.3); their values at the ends of the
ray are known (Lemma 4.4); their values on the seam $`v = 1\text{/}8`$ are positive
(Propositions 4.5 and 4.6); concavity propagates positivity from the seam to
the rest of the ray.

**Lemma 4.2 (the center domain).** $`p^\circ`$ is nonconstant if and only if

```math
1 - 4v + 3v^2 z^2 > 0, \qquad \text{that is,} \qquad v < v_c(z) := \frac{1}{2 + \sqrt{\smash[b]{4 - 3z^2}}}, \qquad \frac14 \le v_c(z) < \frac13. \qquad \text{(4.1)}
```

Moreover $`p^\circ`$ is nonconstant whenever $`p`$ is.

*Proof.* By Lemma 6.1, $`\sqrt{m \cdot m} = m > u_0`$ if and only if $`f(m) > 0`$.
Since $`m + s = 3m`$,

```math
f(m) = m^2 (m - v) - 3m\,bc = \frac{m}{4}\,\left[ (1-v)(1-3v) - 3v^2(1 - z^2) \right] = \frac{m}{4}\,(1 - 4v + 3v^2 z^2).
```

The quadratic $`1 - 4v + 3v^2z^2`$ is positive at $`v = 0`$ and decreasing on
$`[0, 1\text{/}3]`$, an interval that contains every $`v`$ under (2.1) by Lemma 2.1,
so there it is positive exactly on $`[0, v_c)`$ with $`v_c`$ its smaller root, $`v_c = (4 - \sqrt{16 - 12z^2})\text{/}(6z^2) = 1\text{/}(2 + \sqrt{4 - 3z^2})`$, which
also covers $`z = 0`$; the bounds follow from $`1 < \sqrt{4 - 3z^2} \le 2`$. The last
sentence: $`m^2 \ge ad > u_0^2`$.

**The margins at the center.** At $`a' = m`$ the marginals are $`(m+b, m+c)`$ and
$`(m+c, m+b)`$, so $`R_X = R_Y = h((1+\delta)\text{/}2) =: R`$, and
$`J = -2\eta(m) - \eta(b) - \eta(c)`$. From (2.4) and (2.5),

```math
\begin{aligned}
M_0(m) &= 5J - 6R + 2k, \\
M_1(m) &= 3J - 3R + 2k - \gamma(v) + \gamma(\delta), \qquad \gamma(t) = \ln 2 - h\left( \frac{1-t}{2} \right). \qquad \text{(4.2)}
\end{aligned}
```

For the second line, (2.5) at $`a' = m`$ reads
$`M_1(m) = 2J - 2R + 2k - Q`$ with
$`Q = 3\eta(m) - 2\eta(m+b) - 2\eta(m+c) + \eta(m+v) + \eta(b) + \eta(c)`$; here
$`-2\eta(m+b) - 2\eta(m+c) = 2R`$ and $`\eta(m) + \eta(m+v) = -h((1-v)\text{/}2) = \gamma(v) - \ln 2`$,
so $`Q = -J + 2R + \gamma(v) - \ln 2`$, and $`\ln 2 - R = \gamma(\delta)`$.

**Lemma 4.3 (radial concavity).** Along the ray (3.6), for $`0 < v < v_c(z)`$,

```math
\begin{aligned}
v^2\,\partial_v^2 M_0(m) &= -\frac{5v}{s} + \frac{6\delta^2}{1 - \delta^2} + 2L_k < -\frac{3v}{1+v} < 0, \\
v^2\,\partial_v^2 M_1(m) &= -\frac{3v}{s} + \frac{4\delta^2}{1 - \delta^2} - \frac{v^2}{1 - v^2} + 2L_k < -\frac{v\,(1-2v)}{1 - v^2} < 0. \qquad \text{(4.3)}
\end{aligned}
```

*Proof.* On the ray, $`m = (1-v)\text{/}2`$ and $`b, c`$ are linear in $`v`$, and
$`\partial_v^2 J = -1\text{/}(v(1-v))`$: indeed
$`\partial_v J = \ln m - \frac{1+z}{2} \ln b - \frac{1-z}{2} \ln c`$ and
$`\partial_v^2 J = -\frac{1}{2m} - \frac{(1+z)^2}{4b} - \frac{(1-z)^2}{4c} = -\frac{1}{1-v} - \frac{1}{v}`$.
Next $`R = h((1 + vz)\text{/}2)`$ and $`h''(t) = -1\text{/}(t(1-t))`$ give
$`\partial_v^2 R = -z^2\text{/}(1 - \delta^2)`$; and $`\gamma''(t) = 1\text{/}(1 - t^2)`$ gives
$`\partial_v^2 \gamma(v) = 1\text{/}(1 - v^2)`$, $`\partial_v^2 \gamma(vz) = z^2\text{/}(1 - \delta^2)`$.
With $`L_k = v^2 \partial_v^2 k`$ this proves the two equalities. For the
inequalities, (3.8) gives $`2L_k < 2v\text{/}s`$, and $`\delta \le v`$ with
$`t \to t\text{/}(1-t)`$ increasing gives $`\delta^2\text{/}(1-\delta^2) \le v^2\text{/}(1-v^2)`$; then

```math
-\frac{3v}{1-v} + \frac{6v^2}{1-v^2} = -\frac{3v}{1+v}, \qquad
-\frac{v}{1-v} + \frac{3v^2}{1-v^2} = -\frac{v\,(1-2v)}{1-v^2},
```

both negative because $`v < v_c < 1\text{/}3`$. The formulas apply on the open ray
because it lies inside the set of Lemma 3.2 by Lemma 4.2.

**Lemma 4.4 (the ends of the ray).** Along the ray (3.6):

1. $`M_1(m) \to 0`$ as $`v \to 0^+`$;
2. the closed forms (4.2) extend continuously to $`v = v_c(z)`$, where
   $`M_0(m) = I_{p^\circ}(X;Y) > 0`$.

*Proof.* (1) From the cubic, $`u_0 < m < 1\text{/}2`$, $`bc \le v^2\text{/}4`$ and $`u_0 + s < 3\text{/}2`$
give $`u_0^3 = v u_0^2 + bc\,(u_0 + s) \le v\text{/}4 + 3v^2\text{/}8`$, so $`u_0 \to 0`$. Then
$`K \to 1`$, $`\eta(b), \eta(c) \to 0`$, and $`b(1-c) \le P_b \le u_0^2 + b`$ gives
$`b \ln P_b \to 0`$, likewise for $`c`$; so $`k \to 0`$ in (3.1). Also
$`J \to \ln 2`$, $`R \to \ln 2`$, $`\gamma(v), \gamma(\delta) \to 0`$, and (4.2)
gives $`M_1(m) \to 0`$.

(2) The root $`u_0`$ depends continuously on $`(b,c)`$ (Lemma 6.1 brackets it
by the sign of $`f`$), and so do $`\rho`$, $`A`$, $`D`$, and $`k = -\Phi(q^+)`$, through
$`v = v_c`$ where $`\rho = 0`$ and $`q^+ = p^\circ`$. At that point
$`M_0(m) = 2\,[\Psi(p^\circ) - \Phi(p^\circ)] - I_{p^\circ}(X;Y) = I_{p^\circ}(X;Y)`$ by
(1.1), and $`p^\circ`$ is not a product law: $`m^2 = u_0^2 > bc`$, since
$`f(\sqrt{w}) = -w < 0`$ places $`\sqrt{w}`$ below the root (Lemma 6.1).

**The seam.** The rest of the section works at $`v = 1\text{/}8`$, $`s = 7\text{/}8`$,
$`m = 7\text{/}16`$, with $`\delta = b - c \in [0, 1\text{/}8)`$ and $`w = bc \in (0, 1\text{/}256]`$.
Since $`1\text{/}8 < 1\text{/}4 \le v_c(z)`$, the seam lies inside every ray. Two facts hold on
the seam. First, $`u_0 < 1\text{/}4`$: with $`w \le 1\text{/}256`$,

```math
f(1\text{/}4) = \frac{1}{64} - \frac{1}{128} - w\left( \frac14 + \frac78 \right) = \frac{1}{128} - \frac{9w}{8} \ge \frac{7}{2048} > 0. \qquad \text{(4.4)}
```

Second, put

```math
t_P = v + \frac{2u_0^2}{u_0 + s}, \qquad \text{so that} \qquad P_b = \frac{t_P + \delta}{2}, \quad P_c = \frac{t_P - \delta}{2}, \qquad \text{(4.5)}
```

because $`P_b - P_c = b - c`$ and $`P_b + P_c = v + 2\,(u_0^2 - w) = v + 2g`$ by
(3.2). The function $`u \to u^2\text{/}(u+s)`$ is increasing on $`u > 0`$, and
$`v < u_0 < 1\text{/}4`$, so

```math
\frac{5}{32} = v + 2v^2 < t_P < \frac18 + \frac{2 \cdot (1\text{/}16)}{1\text{/}4 + 7\text{/}8} = \frac{17}{72}. \qquad \text{(4.6)}
```

The seam derivatives of the two margins follow from (4.2) and (3.3). At fixed
$`v`$, $`b = (v + \delta)\text{/}2`$, $`c = (v - \delta)\text{/}2`$, and $`d\text{/}d\delta = (\partial_b - \partial_c)\text{/}2`$;
so $`dJ\text{/}d\delta = -\frac12 \ln(b\text{/}c)`$, $`dR\text{/}d\delta = \frac12 \ln \frac{1-\delta}{1+\delta}`$
(from $`h'(x) = \ln((1-x)\text{/}x)`$), $`dk\text{/}d\delta = \frac32 \ln(b\text{/}c) - \ln(P_b\text{/}P_c)`$
(the $`\ln K`$ terms cancel), and $`\gamma'(t) = \frac12 \ln \frac{1+t}{1-t}`$. Hence, for
$`0 < \delta < v`$,

```math
\begin{aligned}
\frac{dM_0(m)}{d\delta} &= \frac12 \ln \frac{b}{c} + 3 \ln \frac{1+\delta}{1-\delta} - 2 \ln \frac{P_b}{P_c}, \\
\frac{dM_1(m)}{d\delta} &= \frac32 \ln \frac{b}{c} + 2 \ln \frac{1+\delta}{1-\delta} - 2 \ln \frac{P_b}{P_c}. \qquad \text{(4.7)}
\end{aligned}
```

**Proposition 4.5 (the constant seam).** If $`b \ge c > 0`$ and $`b + c = 1\text{/}8`$,
then $`M_0(m) > 1\text{/}200`$.

*Proof.* Separate the entropy of the two off-diagonal cells from the rest:
$`M_0(m) = F_{\mathrm{sm}} + \eta(b) + \eta(c)`$ with, by (4.2) and (3.1),

```math
F_{\mathrm{sm}} = -10\,\eta(m) - 6R - 2s \ln K - 4b \ln P_b - 4c \ln P_c. \qquad \text{(4.8)}
```

(The coefficient of $`\eta(b)`$ in $`5J + 2k`$ is $`-5 + 6 = 1`$.) Regard
$`F_{\mathrm{sm}}`$ as a function of $`w = bc = (v^2 - \delta^2)\text{/}4 \in [0, 1\text{/}256]`$,
with $`\delta = \sqrt{v^2 - 4w}`$. It extends continuously to $`w = 0`$, where
$`\delta = v`$, $`c = 0`$, $`u_0 = v`$ (the root is continuous, and $`f(u) = u^2(u - v)`$
at $`w = 0`$), $`K = 9\text{/}8`$, $`P_b = 9\text{/}64`$, $`P_c = 1\text{/}64`$, all logarithms finite;
and it is differentiable for $`0 < w < 1\text{/}256`$, where $`\delta > 0`$. Since
$`d(\eta(b) + \eta(c))\text{/}d\delta = \frac12 \ln(b\text{/}c)`$, the first line of (4.7) gives
$`dF_{\mathrm{sm}}\text{/}d\delta = 3 \ln \frac{1+\delta}{1-\delta} - 2 \ln \frac{P_b}{P_c}`$, and
$`dw\text{/}d\delta = -\delta\text{/}2`$, so by (4.5)

```math
F_{\mathrm{sm}}'(w) = \frac{1}{\delta}\left[ 4 \ln \frac{t_P + \delta}{t_P - \delta} - 6 \ln \frac{1+\delta}{1-\delta} \right]. \qquad \text{(4.9)}
```

This cancellation of the $`\ln(b\text{/}c)`$ term is the reason for separating
$`\eta(b) + \eta(c)`$. For $`0 < \delta < \theta`$,
$`\ln \frac{\theta+\delta}{\theta-\delta} = 2\int_0^\delta \frac{\theta\,dr}{\theta^2 - r^2} \ge \frac{2\delta}{\theta}`$,
and for $`\theta = 1`$ the same integral is at most $`2\delta\text{/}(1 - \delta^2)`$. With
(4.6) and $`\delta \le 1\text{/}8`$,

```math
F_{\mathrm{sm}}'(w) \ge \frac{8}{t_P} - \frac{12}{1 - \delta^2} > \frac{576}{17} - \frac{256}{21} = \frac{7744}{357} > \frac{64}{3}. \qquad \text{(4.10)}
```

So $`F_{\mathrm{sm}}(w) - (64\text{/}3)\,w`$ is nondecreasing on $`[0, 1\text{/}256]`$ (mean value
theorem inside, continuity at the ends), and

```math
F_{\mathrm{sm}}(w) \ge F_{\mathrm{sm}}(0) + \frac{64}{3}\,w. \qquad \text{(4.11)}
```

Now write $`q = c\text{/}v \in (0, 1\text{/}2]`$ (a number, not a law), so $`w = v^2 q(1-q)`$ and
$`\eta(b) + \eta(c) = v \ln v - v\,h(q)`$. With $`M_{\mathrm{face}} := F_{\mathrm{sm}}(0) + v \ln v`$
and $`(64\text{/}3)\,v = 8\text{/}3`$,

```math
M_0(m) \ge M_{\mathrm{face}} + v\,\left[ \frac83\,q(1-q) - h(q) \right]. \qquad \text{(4.12)}
```

To bound the bracket, put $`\zeta = 1 - 2q \in [0, 1)`$, so that, with $`\gamma`$ as
in (4.2), $`\gamma(\zeta) = \ln 2 - h((1 - \zeta)\text{/}2) = \ln 2 - h(q)`$. Then
$`\gamma(0) = \gamma'(0) = 0`$ and
$`\gamma''(\zeta) = 1\text{/}(1 - \zeta^2) \ge 1 + \zeta^2`$, so integrating twice,
$`\gamma(\zeta) \ge \zeta^2\text{/}2 + \zeta^4\text{/}12`$. With $`\alpha = q(1-q)`$ and
$`\zeta^2 = 1 - 4\alpha`$ this reads

```math
h(q) \le \ln 2 - \frac{7}{12} + \frac83\,\alpha - \frac43\,\alpha^2, \qquad \text{(4.13)}
```

so the bracket in (4.12) is at least $`7\text{/}12 - \ln 2 + (4\text{/}3)\alpha^2 \ge 7\text{/}12 - \ln 2`$,
and

```math
M_0(m) \ge M_{\mathrm{face}} + \frac{7\text{/}12 - \ln 2}{8}. \qquad \text{(4.14)}
```

It remains to evaluate $`M_{\mathrm{face}}`$, the limit of the closed form at
$`b = 1\text{/}8`$, $`c = 0`$, $`u_0 = 1\text{/}8`$. There $`K = 9\text{/}8`$, $`P_b = 9\text{/}64`$, and

```math
\begin{aligned}
k &= -\frac78 \ln \frac98 + \frac18 \ln \frac{(1\text{/}8)^3}{(9\text{/}64)^2} = 3 \ln 2 - \frac94 \ln 3, \\
J &= -2\eta\left( \frac{7}{16} \right) - \eta\left( \frac18 \right) = \frac{31}{8} \ln 2 - \frac78 \ln 7, \\
R &= h\left( \frac{9}{16} \right) = 4 \ln 2 - \frac98 \ln 3 - \frac{7}{16} \ln 7, \\
M_{\mathrm{face}} &= 5J - 6R + 2k = \frac{11}{8} \ln 2 + \frac94 \ln 3 - \frac74 \ln 7. \qquad \text{(4.15)}
\end{aligned}
```

(This is the value of a continuous formula at a boundary parameter; nothing is
claimed about the boundary law itself.) Therefore

```math
M_0(m) \ge \frac54 \ln 2 + \frac94 \ln 3 - \frac74 \ln 7 + \frac{7}{96} > \frac{677}{120000} > \frac{1}{200}, \qquad \text{(4.16)}
```

where the middle inequality uses $`\ln 2 > 6931\text{/}10000`$, $`\ln 3 > 10986\text{/}10000`$,
and $`\ln 7 < 19460\text{/}10000`$, all from Lemma 1.3.

**Proposition 4.6 (the singleton seam).** If $`b \ge c > 0`$ and $`b + c = 1\text{/}8`$,
then, writing $`M_1(m)`$ as a function of $`\delta`$,

```math
M_1(m)(\delta) \ge M_1(m)(0) + \frac65\,\delta^2, \qquad
M_1(m)(0) \ge \frac{204 \ln 2 - 50 \ln 3 - 96 \ln 5 + 35 \ln 7}{16} > \frac{1}{250}. \qquad \text{(4.17)}
```

*Proof.* Put $`j(\zeta) = \ln \frac{1+\zeta}{1-\zeta}`$ for $`0 \le \zeta < 1`$, an increasing
function with $`j(\zeta) \ge 2\zeta`$. By (4.7) and (4.5), for $`0 < \delta < v`$,

```math
\frac{dM_1(m)}{d\delta} = \frac32\,j\left( \frac{\delta}{v} \right) + 2\,j(\delta) - 2\,j\left( \frac{\delta}{t_P} \right).
```

By (4.6), $`t_P > 5v\text{/}4`$, so $`j(\delta\text{/}t_P) \le j(4\delta\text{/}(5v))`$. With
$`\zeta = \delta\text{/}v = 8\delta \in (0,1)`$,

```math
\frac{dM_1(m)}{d\delta} \ge \frac32\,j(\zeta) + 2\,j\left( \frac{\zeta}{8} \right) - 2\,j\left( \frac{4\zeta}{5} \right).
```

The one estimate needed is the remainder inequality: for $`0 \le \kappa \le 1`$,

```math
j(\kappa\zeta) - 2\kappa\zeta \le \kappa^3\,[\,j(\zeta) - 2\zeta\,]. \qquad \text{(4.18)}
```

Indeed $`j(\zeta) - 2\zeta = 2 \int_0^\zeta \frac{r^2\,dr}{1 - r^2}`$, and substituting
$`r = \kappa u`$, $`j(\kappa\zeta) - 2\kappa\zeta = 2\kappa^3 \int_0^\zeta \frac{u^2\,du}{1 - \kappa^2u^2} \le 2\kappa^3 \int_0^\zeta \frac{u^2\,du}{1 - u^2}`$.
Apply (4.18) at $`\kappa = 4\text{/}5`$ and $`j(\zeta\text{/}8) \ge \zeta\text{/}4`$:

```math
\frac{dM_1(m)}{d\delta} \ge \frac32\,j(\zeta) + \frac{\zeta}{2} - \frac{16}{5}\,\zeta - \frac{128}{125}\,[\,j(\zeta) - 2\zeta\,]
= \frac{119}{250}\,[\,j(\zeta) - 2\zeta\,] + \frac{3}{10}\,\zeta \ge \frac{3}{10}\,\zeta = \frac{12}{5}\,\delta. \qquad \text{(4.19)}
```

The closed form (4.2) is continuous at $`\delta = 0`$, so integrating (4.19)
from $`0`$ gives the first inequality of (4.17).

For the balanced value, $`b = c = 1\text{/}16`$ and $`p^\circ = (7\text{/}16, 1\text{/}16, 1\text{/}16, 7\text{/}16)`$.
The contact potential is bounded below through one reference law,

```math
q_{\mathrm{r}} = \frac{(112, 8, 8, 7)}{135}.
```

Its cubic has $`v = 16\text{/}135`$, $`w = 64\text{/}135^2`$, $`s = 119\text{/}135`$, and
$`u = 28\text{/}135`$ is a root: $`135^3 f(u) = 28^3 - 16 \cdot 28^2 - 64 \cdot 28 - 64 \cdot 119 = 0`$.
Since $`\sqrt{112 \cdot 7}\text{/}135 = 28\text{/}135`$, the law $`q_{\mathrm{r}}`$ has
$`\sqrt{ad} = u_0`$ and is constant-optimal by
[Theorem 6.6](binary-stochastic-optimum.md#6-the-cubic). By
[Theorem 3.2](binary-stochastic-optimum.md#3-the-deficit-and-the-tangent-test)
(items 1 and 3, on the full support), $`\Phi \le \ell_{q_{\mathrm{r}}}`$ on the
whole simplex. The rows and columns of $`q_{\mathrm{r}}`$ are both
$`(8\text{/}9, 1\text{/}9)`$, and its tangent coefficients, from display (1.2), are

```math
\ln \frac{(8\text{/}9)^4}{(112\text{/}135)^3} = \ln \frac{375}{343} \ \text{at } (0,0), \qquad
\ln \frac{(1\text{/}9)^4}{(7\text{/}135)^3} = \ln \frac{375}{343} \ \text{at } (1,1), \qquad
\ln \frac{(8\text{/}9)^2 (1\text{/}9)^2}{(8\text{/}135)^3} = \ln \frac{375}{8} \ \text{at } (0,1), (1,0).
```

The two diagonal coefficients agree, as Lemma 6.4 requires of a contact, so
$`\ell_{q_{\mathrm{r}}}(q)`$ depends on a law $`q`$ only through its diagonal sum
and its off-diagonal sum. For the contact $`q^+`$ of $`p^\circ`$ these are
$`s = 7\text{/}8`$ and $`v = 1\text{/}8`$, hence

```math
k = -\Phi(q^+) \ge -\ell_{q_{\mathrm{r}}}(q^+) = -\frac78 \ln \frac{375}{343} - \frac18 \ln \frac{375}{8}
= \frac38 \ln 2 - \ln 3 - 3 \ln 5 + \frac{21}{8} \ln 7. \qquad \text{(4.20)}
```

At balance, $`J = -2\eta(7\text{/}16) - 2\eta(1\text{/}16) = 4 \ln 2 - \frac78 \ln 7`$,
$`R = h(1\text{/}2) = \ln 2`$, $`\gamma(0) = 0`$, and
$`\gamma(1\text{/}8) = \ln 2 - h(7\text{/}16) = -3 \ln 2 + \frac98 \ln 3 + \frac{7}{16} \ln 7`$. By (4.2),

```math
M_1(m)(0) = 12 \ln 2 - \frac98 \ln 3 - \frac{49}{16} \ln 7 + 2k
\ge \frac{51}{4} \ln 2 - \frac{25}{8} \ln 3 - 6 \ln 5 + \frac{35}{16} \ln 7,
```

which is the displayed combination. Lemma 1.3 with $`N = 8`$ encloses the four
logarithms and shows that the combination exceeds $`1\text{/}250`$; its value is
about $`0.0045`$.

*Proof of Theorem 4.1.* Fix $`z = (b-c)\text{/}v`$ and use the ray (3.6); by Lemma 4.2
the ray's nonconstant part is $`0 < v < v_c(z)`$, which contains $`1\text{/}8`$.

(1) On $`(0, 1\text{/}8]`$, $`M_1(m)`$ is concave (Lemma 4.3) with continuous extension
$`0`$ at $`v = 0`$ (Lemma 4.4) and value above $`1\text{/}250`$ at $`v = 1\text{/}8`$ (Proposition
4.6). Concavity gives $`M_1(m)(v) \ge (1 - 8v) \cdot 0 + 8v \cdot M_1(m)(1\text{/}8) \ge 8v\text{/}250 = 4v\text{/}125`$.

(2) On $`[1\text{/}8, v_c(z))`$, $`M_0(m)`$ is concave, positive at $`v = 1\text{/}8`$
(Proposition 4.5), and extends continuously to $`v_c(z)`$ with a positive value
there (Lemma 4.4). A concave function on a closed interval with positive values
at both ends is positive throughout.

Proposition 4.5 was stated for $`b \ge c`$; the ray (3.6) has $`z \ge 0`$, which
is the same condition, and (2.1) supplies it.

## 5. The fixed cut

Under (2.1) with $`p`$ nonconstant, assume in this section

```math
0 < v \le \frac18.
```

**Lemma 5.1 (the smaller contact mass).** $`D < v\text{/}2`$. Consequently

```math
D < \frac{1}{16}, \qquad A > \frac{13}{16}, \qquad 3D < \frac{3}{16} < \frac{7}{16} \le m, \qquad A - 2D > \frac{11}{16}, \qquad A > 4D, \qquad \text{(5.1)}
```

and the cut law $`p_{\mathrm{cut}} = p_{s - 3D} = (A - 2D, b, c, 3D)`$ lies on the open
chord $`(m, A)`$.

*Proof.* Put $`q^2 = (v\text{/}2)(1 - 3v\text{/}2)`$ with $`q > 0`$ (a number, not a law). Then $`q > v`$ (as $`1\text{/}2 - 3v\text{/}4 > v`$) and
$`q < m`$. With $`w \le v^2\text{/}4`$ and $`q^3 - vq^2 = q\,(q^2 - vq)`$,

```math
f(q) \ge q^3 - v q^2 - \frac{v^2}{4}\,(q + s) = \frac{q\,v\,(1 - 2v)}{2} - v^2\left( \frac34 - v \right).
```

The right side is positive if and only if $`q\,(1 - 2v) > v\,(3\text{/}2 - 2v)`$, both sides
positive, and squaring,

```math
q^2 (1-2v)^2 - v^2 \left( \tfrac32 - 2v \right)^2 = \frac{v}{2}\,\left( 1 - 10v + 22v^2 - 14v^3 \right),
```

where, with $`\epsilon = 1\text{/}8 - v \ge 0`$,
$`1 - 10v + 22v^2 - 14v^3 = 17\text{/}256 + 165\epsilon\text{/}32 + 67\epsilon^2\text{/}4 + 14\epsilon^3 > 0`$.
So $`f(q) > 0`$. On $`[v, \infty)`$, $`f'(u) = 3u^2 - 2vu - w \ge v^2 - v^2\text{/}4 > 0`$, and
$`f(u_0) = 0 < f(q)`$ with $`q > v`$ forces $`u_0 < q`$. Finally
$`D\,(s - D) = u_0^2 < q^2 = (v\text{/}2)(s - v\text{/}2)`$, and since $`x \to x(s-x)`$ is
increasing on $`[0, m]`$ and both $`D`$ and $`v\text{/}2`$ lie there, $`D < v\text{/}2`$. The
numbers (5.1) follow from $`v \le 1\text{/}8`$ and $`s = 1 - v \ge 7\text{/}8`$; and
$`D < 3D < m`$ gives $`m < s - 3D < s - D = A`$.

**Theorem 5.2 (the constant margin at the cut).**

```math
M_0(s - 3D) > \frac{3D}{208}. \qquad \text{(5.2)}
```

*Proof.* In this section write $`x = b\text{/}D`$ and $`y = c\text{/}D`$ (the chart of
section 3 is not used here).

*Step 1: the contact logarithm identity.* The identity
$`A^{3\text{/}2}(D+b)(D+c) = D^{3\text{/}2}(A+b)(A+c)`$ at $`q^+`$ (the computation in the proof
of Lemma 6.4, with $`f(u_0) = 0`$) becomes after taking logarithms and
writing $`D + b = D\,(1 + x)`$, $`A + b = A\,(1 + b\text{/}A)`$,

```math
-\ln D = 2 \ln(1+x) + 2 \ln(1+y) - \ln A - 2 \ln\left( 1 + \frac{b}{A} \right) - 2 \ln\left( 1 + \frac{c}{A} \right). \qquad \text{(5.3)}
```

*Step 2: curvature of the potential along the chord.* For $`D \le t \le 3D`$ put
$`p_t = (s - t, b, c, t)`$ (so $`p_D = q^+`$ and $`p_{3D} = p_{\mathrm{cut}}`$) and
$`P(t) = -\Phi(p_t)`$, so that $`P(D) = k`$. By (1.1) and (2.2),

```math
M_0(s - t) = 2\,[\Psi(p_t) + k] - I_{p_t}(X;Y) = I_{p_t}(X;Y) - 2\,[P(t) - k]. \qquad \text{(5.4)}
```

The derivative of $`P`$ is $`-\ell_{p_t}(\chi)`$ with $`\chi = (-1, 0, 0, 1)`$, by
Lemma 3.1 of the stochastic-optimum page; at $`t = D`$ this is the difference of
the two diagonal tangent coefficients of $`q^+`$, which vanishes by the identity of
step 1. So
$`P'(D) = 0`$. Differentiating $`-\Phi(p_t)`$ twice, with $`\alpha = s - t`$ and
$`h''(x) = -1\text{/}(x(1-x))`$,

```math
P''(t) = \frac{3}{t} + \frac{3}{\alpha} - \frac{2}{t+b} - \frac{2}{t+c} - \frac{2}{\alpha+b} - \frac{2}{\alpha+c}. \qquad \text{(5.5)}
```

Since $`\alpha \ge m \ge 3v\text{/}2`$,

```math
\frac{2}{\alpha+b} + \frac{2}{\alpha+c} - \frac{4}{\alpha + v\text{/}2} = \frac{2\,(b-c)^2}{(\alpha+b)(\alpha+c)(2\alpha+v)} \ge 0, \qquad
\frac{4}{\alpha + v\text{/}2} - \frac{3}{\alpha} = \frac{2\alpha - 3v}{\alpha\,(2\alpha + v)} \ge 0,
```

and therefore

```math
P''(t) \le \frac{3}{t} - \frac{2}{t+b} - \frac{2}{t+c}. \qquad \text{(5.6)}
```

*Step 3: integration.* With $`P'(D) = 0`$,
$`P(3D) - k = \int_D^{3D} (3D - t)\,P''(t)\,dt`$, and the weight is nonnegative, so
(5.6) gives

```math
P(3D) - k \le 3\,Q_0 - 2\,Q_b - 2\,Q_c, \qquad
Q_j = \int_D^{3D} \frac{3D - t}{t + j}\,dt = (3D + j) \ln \frac{3D + j}{D + j} - 2D. \qquad \text{(5.7)}
```

*Step 4: the mutual information at the cut.* Expanding the entropies,

```math
I_{p_t}(X;Y) = h(t) - F(t,b) - F(t,c) + J_3(t), \qquad
J_3(t) = \eta(\alpha) + \eta(1-t) - \eta(\alpha+b) - \eta(\alpha+c) = \int_0^b \int_0^c \frac{dr\,dr'}{\alpha + r + r'} > 0. \qquad \text{(5.8)}
```

(The eight $`\eta`$ terms of $`I`$ match those of the right side; the integral
representation is the inclusion-exclusion of $`\eta(\alpha + r + r')`$ over
the rectangle, whose mixed second derivative is $`1\text{/}(\alpha + r + r')`$.)
By (5.4), (5.7), and (5.8), dropping $`J_3 > 0`$,

```math
M_0(s - 3D) > h(3D) - F(3D, b) - F(3D, c) - 6\,Q_0 + 4\,Q_b + 4\,Q_c. \qquad \text{(5.9)}
```

*Step 5: rescaling.* $`F`$ is homogeneous, $`F(3D, xD) = D\,F(3, x)`$, and
$`Q_0 = D\,(3 \ln 3 - 2)`$, $`Q_b = D\,\left[ (3 + x) \ln \frac{3+x}{1+x} - 2 \right]`$; also
$`h(3D) \ge 3D\,[-\ln(3D) + 1 - 3D]`$, from $`-\ln(1 - 3D) \ge 3D`$. Define

```math
V(x) = 3\,(3+x) \ln(3+x) - (6 + 4x) \ln(1+x) + x \ln x, \qquad x > 0.
```

Collecting the terms of (5.9) divided by $`D`$: the $`F`$ and $`Q`$ terms give
$`V(x) + V(y) - 6 \ln(1+x) - 6 \ln(1+y) - 12 \ln 3 - 4`$ (a check against lost
constants: every affine term is accounted for here), and $`h(3D)\text{/}D`$ gives at
least $`-3 \ln 3 - 3 \ln D + 3 - 9D`$. Substituting (5.3) for $`-3 \ln D`$ cancels
the $`\ln(1+x)`$ and $`\ln(1+y)`$ terms:

```math
\frac{M_0(s - 3D)}{D} > V(x) + V(y) - 15 \ln 3 - 1 - 9D - 3 \ln A - 6 \ln\left( 1 + \frac{b}{A} \right) - 6 \ln\left( 1 + \frac{c}{A} \right). \qquad \text{(5.10)}
```

*Step 6: the scalar lemma.* $`V(x) > 19\text{/}2`$ for every $`x > 0`$. Differentiating,

```math
V'(x) = 3 \ln \frac{x+3}{x+1} + \ln \frac{x}{x+1} - \frac{2}{x+1}, \qquad
V''(x) = \frac{-3x^2 + 4x + 3}{x\,(x+1)^2\,(x+3)}. \qquad \text{(5.11)}
```

On $`0 < x \le 1`$ the numerator is at least $`x + 3 > 0`$, so $`V`$ is convex there
and lies above its tangent at $`x = 1\text{/}2`$, whose slope and intercept are

```math
\sigma = 3 \ln \frac73 - \ln 3 - \frac43, \qquad \beta = 9 \ln \frac72 - 6 \ln \frac32 + \frac23. \qquad \text{(5.12)}
```

With Lemma 1.3, $`\ln \frac73 \ge S_3(2\text{/}5)`$, $`\ln 3 \le U_3(1\text{/}2)`$,
$`\ln \frac72 \ge S_5(5\text{/}9)`$, $`\ln \frac32 \le U_3(1\text{/}5)`$, and exact arithmetic gives

```math
3\,S_3(2\text{/}5) - U_3(1\text{/}2) - \frac43 = \frac{94627}{875000} > 0, \qquad
9\,S_5(5\text{/}9) - 6\,U_3(1\text{/}5) + \frac23 - \frac{19}{2} = \frac{224012952139}{42374115984375} > 0,
```

so $`\sigma > 0`$, $`\beta > 19\text{/}2`$, and $`V(x) \ge \beta + \sigma x > 19\text{/}2`$ on
$`(0, 1]`$. For $`x \ge 1`$ put $`\theta = 1\text{/}(x+1) \in (0, 1\text{/}2]`$; then
$`V'(x) = \Theta(\theta) := 3 \ln(1 + 2\theta) + \ln(1 - \theta) - 2\theta`$, with
$`\Theta'' = -12\text{/}(1+2\theta)^2 - 1\text{/}(1-\theta)^2 < 0`$, $`\Theta(0) = 0`$, and
$`\Theta(1\text{/}2) = 2 \ln 2 - 1 > 0`$ (from $`\ln 2 \ge S_1(1\text{/}3) = 2\text{/}3`$). A concave
function above its chord on $`[0, 1\text{/}2]`$ is positive on $`(0, 1\text{/}2]`$, so $`V`$
increases on $`[1, \infty)`$ and stays above $`V(1) > 19\text{/}2`$.

*Step 7: the finish.* In (5.10) use $`V(x) + V(y) > 19`$,
$`\ln 3 \le U_3(1\text{/}2) = 923\text{/}840 < 11\text{/}10`$, $`D < 1\text{/}16`$, $`-3 \ln A > 0`$, and
$`\ln(1 + r) \le r`$ with $`6\,(b + c)\text{/}A < 6 \cdot (1\text{/}8) \text{/} (13\text{/}16) = 12\text{/}13`$:

```math
\frac{M_0(s - 3D)}{D} > 19 - \frac{33}{2} - 1 - \frac{9}{16} - \frac{12}{13} = \frac{3}{208}.
```

**Theorem 5.3 (the singleton margin at the cut).**

```math
M_1(s - 3D) > \frac{D}{100}. \qquad \text{(5.13)}
```

*Proof.* Keep $`x = b\text{/}D`$, $`y = c\text{/}D`$, so $`x, y > 0`$ and $`x + y = v\text{/}D > 2`$ by
Lemma 5.1; write $`a = A - 2D = s - 3D`$ for the large diagonal cell of the cut.

*Step 1: exact expansion.* For $`p_t = (s - t, b, c, t)`$ put
$`F_{\mathrm{big}}(t) = F(s-t, b) + F(s-t, c)`$ and $`F_{\mathrm{small}}(t) = F(t,b) + F(t,c)`$.
Expanding the entropies,

```math
\Psi(p_t) = F_{\mathrm{big}}(t) + F_{\mathrm{small}}(t), \qquad
S_{11}(p_t) = F_{\mathrm{small}}(t) + J_3(t), \qquad \text{(5.14)}
```

the second from (1.3) and (5.8). At the contact, (1.1) gives
$`k = -\Phi(q^+) = I_{q^+}(X;Y) - \Psi(q^+) = h(D) - 2F_{\mathrm{small}}(D) + J_3(D) - F_{\mathrm{big}}(D)`$.
Hence, exactly,

```math
M_1(s - 3D) = 2\,[F_{\mathrm{big}}(3D) - F_{\mathrm{big}}(D)] + F_{\mathrm{small}}(3D) - 4F_{\mathrm{small}}(D) + 2h(D) + 2J_3(D) - J_3(3D). \qquad \text{(5.15)}
```

*Step 2: rescaling.* Define

```math
\psi(\xi) = F(3, \xi) - 4F(1, \xi) + 4 \ln(1+\xi) = (3+\xi) \ln(3+\xi) + 3\xi \ln \xi - 4\xi \ln(1+\xi) - 3 \ln 3.
```

Using $`F(D\theta, D\xi) = D\,F(\theta, \xi)`$ and $`h(D) = -D \ln D - (1-D)\ln(1-D)`$, and
substituting (5.3) in the form
$`-2 \ln D = 4 \ln(1+x) + 4 \ln(1+y) + 6 \ln A - 4 \ln(A+b) - 4 \ln(A+c)`$, (5.15)
becomes

```math
\frac{M_1(s - 3D)}{D} = \psi(x) + \psi(y) + E, \qquad \text{(5.16)}
```

```math
E = 6 \ln A - 4 \ln(A+b) - 4 \ln(A+c) - \frac{2\,(1-D) \ln(1-D)}{D}
+ \frac{2}{D} \sum_{j \in \{b, c\}} [F(a, j) - F(A, j)] + \frac{2J_3(D) - J_3(3D)}{D}.
```

*Step 3: the pair inequality.* For $`x, y > 0`$ with $`x + y \ge 2`$,

```math
\psi(x) + \psi(y) \ge 2\,\psi(1) = 8 \ln 2 - 6 \ln 3. \qquad \text{(5.17)}
```

First, $`\psi`$ is increasing on $`[1, \infty)`$: $`\psi'(\xi) = \Xi(1\text{/}\xi)`$ with
$`\Xi(\theta) = \ln(1 + 3\theta) - 4 \ln(1 + \theta) + 4\theta\text{/}(1 + \theta)`$, and
$`\Xi'(\theta) = (3 + 2\theta - 9\theta^2)\text{/}((1+3\theta)(1+\theta)^2)`$ changes sign once on
$`[0,1]`$, from positive to negative, while $`\Xi(0) = 0`$ and
$`\Xi(1) = 2 - 2 \ln 2 > 0`$; so $`\Xi > 0`$ on $`(0, 1]`$. Second, the symmetric sum
$`\Pi(\xi) = \psi(\xi) + \psi(2 - \xi)`$ on $`(0, 2)`$ is convex with $`\Pi'(1) = 0`$:
from $`\psi''(\xi) = -(3\xi^2 + 2\xi - 9)\text{/}(\xi (\xi+1)^2 (\xi+3))`$, with $`\theta = \xi - 1`$,

```math
\Pi''(1 + \theta) = \frac{2\,(64 + 352\theta^2 - 8\theta^4 - 3\theta^6)}{(1 - \theta^2)(16 - \theta^2)(4 - \theta^2)^2} > 0 \quad (\lvert \theta \rvert < 1),
```

the numerator being at least $`64 + 341\theta^2`$. So $`\Pi \ge \Pi(1) = 2\psi(1)`$.
Now if $`x, y \ge 1`$, monotonicity gives (5.17). Otherwise, say $`x < 1`$; then
$`y \ge 2 - x > 1`$, so $`\psi(y) \ge \psi(2 - x)`$ and
$`\psi(x) + \psi(y) \ge \Pi(x) \ge 2\psi(1)`$. Finally
$`\psi(1) = 4 \ln 4 - 4 \ln 2 - 3 \ln 3 = 4 \ln 2 - 3 \ln 3`$.

*Step 4: the correction.* Each piece of $`E`$ is bounded below by an
elementary estimate. From (5.8) and $`A \ge 4D`$,
$`1\text{/}(a + r + r') \le 2\text{/}(A + r + r')`$, so
$`J_3(3D) \le 2 J_3(D)`$ and the last term is nonnegative. From
$`-\ln(1 - D) \ge D + D^2\text{/}2`$, $`-2(1-D)\ln(1-D)\text{/}D \ge 2 - D - D^2`$. From
$`\partial_\theta F(\theta, j) = \ln(1 + j\text{/}\theta)`$, decreasing in $`\theta`$,
$`F(a, j) - F(A, j) = -\int_a^A \ln(1 + j\text{/}\theta)\,d\theta \ge -2D \ln(1 + j\text{/}a)`$. And by
concavity of the logarithm, $`\ln(1 + b\text{/}\theta) + \ln(1 + c\text{/}\theta) \le 2 \ln(1 + v\text{/}(2\theta))`$
for $`\theta > 0`$, applied at $`\theta = a`$ and, after writing
$`6 \ln A - 4 \ln(A+b) - 4 \ln(A+c) = -2 \ln A - 4 \ln(1 + b\text{/}A) - 4 \ln(1 + c\text{/}A)`$, at
$`\theta = A`$. Altogether

```math
E \ge E_0(v, D) := 2 - D - D^2 - 2 \ln A - 8 \ln\left( 1 + \frac{v}{2A} \right) - 8 \ln\left( 1 + \frac{v}{2a} \right), \qquad A = 1 - v - D, \quad a = 1 - v - 3D. \qquad \text{(5.18)}
```

*Step 5: two endpoints.* For fixed $`v \in (0, 1\text{/}8]`$, $`E_0`$ is concave in
$`D \in [0, v\text{/}2]`$:

```math
\partial_D^2 E_0 = -2 + \frac{2}{A^2} - \frac{8v\,(4A + v)}{A^2 (2A + v)^2} - \frac{72v\,(4a + v)}{a^2 (2a + v)^2}. \qquad \text{(5.19)}
```

Here $`2\text{/}A^2 - 2 = 2(1-A)(1+A)\text{/}A^2 \le 4(1-A)\text{/}A^2 \le 1536v\text{/}169`$, using
$`1 - A = v + D \le 3v\text{/}2`$ and $`A \ge 13\text{/}16`$; and for $`\theta \in \{A, a\}`$,
$`0 < \theta \le 1`$ and $`v \le 1\text{/}8`$ give
$`(4\theta + v)\text{/}(\theta^2 (2\theta + v)^2) \ge 1\text{/}(\theta^2 (2\theta + v)) > 1\text{/}3`$. So
$`\partial_D^2 E_0 < v\,(1536\text{/}169 - 80\text{/}3) < 0`$, and
$`E_0(v, D) \ge \min\{ E_0(v, 0), E_0(v, v\text{/}2) \}`$. Both endpoint functions
decrease in $`v`$:

```math
\begin{aligned}
E_0(v, 0) &= 2 + 14 \ln(1-v) - 16 \ln\left( 1 - \frac{v}{2} \right), \\
E_0(v, v\text{/}2) &= 2 - \frac{v}{2} - \frac{v^2}{4} + 6 \ln\left( 1 - \frac{3v}{2} \right) - 8 \ln(1-v) + 8 \ln\left( 1 - \frac{5v}{2} \right) - 8 \ln(1-2v),
\end{aligned}
```

with derivatives $`-14\text{/}(1-v) + 8\text{/}(1 - v\text{/}2) < 0`$ and
$`-\frac12 - \frac{v}{2} - \frac{9}{1 - 3v\text{/}2} + \frac{8}{1-v} - \frac{20}{1 - 5v\text{/}2} + \frac{16}{1-2v} < 0`$,
the latter because $`9\text{/}(1 - 3v\text{/}2) > 8\text{/}(1-v)`$ and $`20\text{/}(1 - 5v\text{/}2) > 16\text{/}(1 - 2v)`$.
Hence $`E_0(v, D) \ge \min\{E_0(1\text{/}8, 0), E_0(1\text{/}8, 1\text{/}16)\}`$, and with (5.16),
(5.17),

```math
\frac{M_1(s - 3D)}{D} \ge \min\{ C_0, C_1 \}, \qquad
\begin{aligned}
C_0 &= 2 + 30 \ln 2 - 22 \ln 3 - 16 \ln 5 + 14 \ln 7, \\
C_1 &= \frac{495}{256} - 8 \ln 2 - 14 \ln 3 - 8 \ln 7 + 8 \ln 11 + 6 \ln 13.
\end{aligned} \qquad \text{(5.20)}
```

*Step 6: two scalar comparisons.* Lemma 1.3 with $`N = 8`$ at the primes
$`2, 3, 5, 7, 11, 13`$ gives $`C_0 > 1\text{/}100`$ and $`C_1 > 1\text{/}100`$; their values are
about $`0.1167`$ and $`0.0134`$. The check script replays both enclosures.

## 6. Assembly

**Theorem 6.1 (full support).** Let $`p`$ be a full-support binary law. Then
$`T(p) \le 2\,\tau(p)`$, and the constant code or one of the four singleton codes
attains $`D_p(g) \le 2\,\tau(p)`$, as stated at the head of the page.

*Proof.* If $`\Delta = 0`$, $`p`$ is a product law, so $`I_p(X;Y) = 0`$ and
$`\tau(p) = T(p) = 0`$ from $`0 \le \tau(p) \le T(p) \le I_p(X;Y)`$ (display (1.2) of
the stochastic-optimum page); the constant code is a witness. If $`\Delta < 0`$, relabel $`Y`$ (Lemma 1.2), which
preserves $`\tau`$, $`T`$, and code scores, maps the off-diagonal cells to the
diagonal, and reduces to $`\Delta > 0`$. If $`\Delta > 0`$, the two remaining
symmetries of Lemma 1.2 arrange $`a \ge d`$ and $`b \ge c`$ without changing
$`\Delta`$, the diagonal pair, or the off-diagonal pair; transporting a witness
back is again a witness of the same kind at the corresponding cell. So assume
(2.1). If $`\sqrt{ad} \le u_0`$, then $`\tau(p) = I_p(X;Y)`$ by Theorem 6.6, hence
$`T(p) = \tau(p)`$ by display (1.2) of the stochastic-optimum page, and the
constant code is a witness. Otherwise $`p`$ is nonconstant, $`p = p_a`$ on the
chord of section 2 by Lemma 2.1, and Theorem 2.5 applies:

- if $`v \ge 1\text{/}8`$, Theorem 4.1(2) gives $`M_0(m) > 0`$, which is (G0);
- if $`v \le 1\text{/}8`$, take $`a_{\mathrm{cut}} = s - 3D`$, which lies in $`(m, A)`$ by
  Lemma 5.1; Theorem 4.1(1) gives $`M_1(m) \ge 4v\text{/}125 > 0`$, Theorem 5.3 gives
  $`M_1(a_{\mathrm{cut}}) > D\text{/}100 > 0`$, and Theorem 5.2 gives
  $`M_0(a_{\mathrm{cut}}) > 3D\text{/}208 > 0`$, which is (GC).

Theorem 2.5 names the witness: the constant code, or the singleton at the cell
$`(1,1)`$, which under (2.1) is a lightest diagonal cell. At $`v = 1\text{/}8`$ both
cases apply and agree.

**Theorem 6.2 (every law).** $`T(p) \le 2\,\tau(p)`$ for every binary $`2 \times 2`$ law.

*Proof.* Theorem 6.1 supplies the hypothesis of
`T_le_mul_tau_of_forall_fullSupport` with $`C = 2`$:

```lean
theorem T_le_mul_tau_of_forall_fullSupport
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    {C : ℝ} (hC : 0 ≤ C)
    (hfull : ∀ p : α × β → ℝ, IsPMF p → (∀ z, 0 < p z) → T p ≤ C * tau p)
    (p : α × β → ℝ) (hp : IsPMF p) :
    T p ≤ C * tau p
```

That declaration is kernel-verified and generic in the alphabet and the
constant; its proof smooths $`p`$ toward the uniform product law, applies the
full-support bound along the smoothing, and passes to the limit using the
continuity of $`T`$ and the transport of an optimal latent. The conclusion
covers laws with one, two, or three zero cells. On such a law the theorem
gives no code witness beyond the one that `exists_optimalCode` attaches to
$`T(p)`$ itself, and the five-code statement of Theorem 6.1 is not claimed
there.

## 7. Scope and formalization

**What is proved here.** Everything above is a complete prose derivation from
the public inputs of [section 1](#1-setting), elementary calculus (the mean
value theorem, integration of monotone bounds, convexity of one-variable
functions), and finitely many rational-logarithm comparisons decided by the
series of Lemma 1.3. It is `paper proof` in the ledger's sense. The ledger rows
are `BIN-C2` (Theorems 6.1 and 6.2), `BIN-CHORD-CUT` (Theorem 2.5 with Lemmas
2.2 to 2.4), `BIN-CENTER` (Theorem 4.1), and `BIN-FIXED-CUT` (Lemma 5.1 with
Theorems 5.2 and 5.3). The quantitative margins $`1\text{/}200`$, $`1\text{/}250`$,
$`4v\text{/}125`$, $`3D\text{/}208`$, and $`D\text{/}100`$ are in nats; only their positivity is
used downstream.

**What is not proved here.** Nothing is claimed about the sharpness of the
constant $`2`$, about the laws that maximize $`T(p)\text{/}\tau(p)`$, or about the
equality cases. The five-code witness is stated for full support only. Nothing
is claimed for alphabets larger than $`2 \times 2`$ or for latents that are not
finite mixtures; the general problem keeps its standing on the
[open problems](open-problems.md) page.

**How the proof is organized, for a reader planning a formalization.** The
route has four independent analytic blocks joined by one assembly. Each block
is stated on its own domain with explicit hypotheses, and the assembly only
consumes signs:

1. the chord calculus of [section 2](#2-the-contact-chord): a concavity, a
   no-interior-minimum property, and the algebraic value at the contact end;
2. the center theorem of [section 4](#4-the-center), through the radial
   curvature comparison (3.8), two seam estimates, and two endpoint limits;
3. the two fixed-cut margins of [section 5](#5-the-fixed-cut), each a
   one-parameter reduction ending in a rational-logarithm comparison;
4. the reduction of every law to the oriented nonconstant full-support case,
   by the symmetries, the product case, the constant regime, and the sparse
   transfer.

Every margin is an explicit entropy expression in the cells, the root $`u_0`$,
and the contact pair; the identification of $`\Psi(p_{a'}) + k`$ with
$`\tau(p_{a'})`$ enters only through Lemma 2.1, and only in the direction
$`\tau \ge \Psi + k`$ is needed for the final comparison. A formalization may
therefore prove each block about the formal expressions and invoke the exact
optimum once.

**Formalization.** The public library contains the root and the contact pair
in chart coordinates (`contact_root_identity` in
[NormalForm](../StochasticToDeterministicLatents/Binary/NormalForm.lean)), the
generic transfer theorem, the constant and singleton codes, and the
cell-symmetry transports of
[Symmetry](../StochasticToDeterministicLatents/Binary/Symmetry.lean), but no
declaration computing $`\tau`$ from a law and none of the four blocks above.
The target declarations are listed in the
[Lean contracts](lean-contracts.md#binary-factor-two); the endpoint is a
theorem `Binary.T_le_two_mul_tau` for every binary law, together with a
full-support witness theorem naming the code. The natural order is the
stochastic-optimum targets first (the cubic and the formula for $`\tau`$),
then the chord calculus, then the two seam and two cut estimates, then the
assembly.

`scripts/check_factor_two_identities.py` expands every algebraic identity
displayed on this page with sympy and replays every fixed logarithm comparison
in exact rational arithmetic from the series of Lemma 1.3; a few derivative
formulas are additionally evaluated at sample laws to sixty digits as a spot
check. It is a reading aid, not proof evidence.
