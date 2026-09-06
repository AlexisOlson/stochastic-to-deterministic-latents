# The binary stochastic optimum

This page computes $`\tau(p)`$ exactly for every binary $`2 \times 2`$ law
$`p`$, together with the optimal latent. The results are `paper proof` in the
sense of the [claim ledger](claims.md#status-vocabulary): complete prose
derivations, not formalized. No Lean declaration in this repository states
them. Where the library's kernel-verified normal form already covers a special
case, that declaration is quoted in its own words and nothing stronger is
attributed to it.

Write a binary law as $`p = (a,b,c,d) = (p_{00},p_{01},p_{10},p_{11})`$ and put
$`\Delta = ad - bc`$.

> **Theorem (exact binary stochastic optimum).** Let $`p`$ be a binary law.
>
> 1. If $`\Delta = 0`$, then $`\tau(p) = T(p) = I_p(X;Y) = 0`$.
> 2. If $`\Delta < 0`$, exchange the two $`Y`$ labels; this preserves $`\tau`$ and
>    reduces to the next case.
> 3. If $`\Delta > 0`$, put $`s = a+d`$, $`v = b+c`$, $`w = bc`$, and let $`u_0`$ be the
>    largest nonnegative root of
>
>    ```math
>    f_p(u) = u^3 - vu^2 - wu - ws.
>    ```
>
>    If $`\sqrt{ad} \le u_0`$, the constant latent is optimal:
>    $`\tau(p) = T(p) = I_p(X;Y)`$. If $`\sqrt{ad} > u_0`$, put
>    $`\rho = \sqrt{s^2 - 4u_0^2} > 0`$ and
>
>    ```math
>    \begin{aligned}
>    q^+ &= ((s+\rho)/2, b, c, (s-\rho)/2), \\
>    q^- &= ((s-\rho)/2, b, c, (s+\rho)/2), \\
>    \lambda &= (a - (s-\rho)/2) / \rho.
>    \end{aligned}
>    ```
>
>    Then $`0 < \lambda < 1`$, $`p = \lambda q^+ + (1-\lambda)\,q^-`$, and
>
>    ```math
>    \tau(p) = \Psi(p) - \Phi(q^+) = \Psi(p) - \Phi(q^-),
>    ```
>
>    with $`\Phi`$ as in the [blueprint](blueprint.md#1-laws-entropy-and-codes) and
>    $`\Psi`$ as in the [score decomposition](binary-factor-nine.md#the-score-decomposition)
>    of the factor-nine proof.
>
> In every case the optimal component measure is unique: every $`\tau`$-optimal
> finite latent has, after merging labels with equal component laws and
> discarding zero-weight labels, exactly the components $`p`$ (constant case) or
> $`q^+`$, $`q^-`$ with weights $`\lambda`$, $`1-\lambda`$ (mixed case; when $`\Delta < 0`$,
> their images under the relabeling of case 2).

Along the way three statements of independent interest are proved: a
rational test deciding whether the constant latent is optimal
([section 4](#4-the-rational-constant-optimality-test)); the fact that every
optimal finite latent of a binary law has at most two distinct component laws,
on every support ([section 5](#5-at-most-two-component-laws)); and the band
$`1/3 \le b+c \le 2/3`$ on which the constant latent is always optimal
([section 7](#7-consequences)).

None of this proves an inequality between $`T(p)`$ and $`\tau(p)`$. What it
does is make the right-hand side of the conjecture [`BIN-C2`](claims.md#ledger)
explicit: $`T(p) \le 2\,\tau(p)`$ becomes a comparison between the minimum over
the fifteen partitions of four cells and an explicit function of $`(a,b,c,d)`$
and one cubic root. See [section 8](#8-scope-and-formalization).

| Step | Sections |
|---|---|
| Notation and what the library already proves | [1](#1-setting-and-public-inputs) |
| The concave envelope and the contact set | [2](#2-the-support-face-and-the-concave-envelope) |
| When the constant latent is optimal | [3](#3-the-deficit-and-the-tangent-test), [4](#4-the-rational-constant-optimality-test) |
| At most two component laws, every optimizer, every support | [5](#5-at-most-two-component-laws) |
| The cubic and the optimum | [6](#6-the-cubic) |
| Consequences and examples | [7](#7-consequences) |
| Scope and Lean targets | [8](#8-scope-and-formalization) |

## 1. Setting and public inputs

Entropies, divergences, and information quantities are in bits, with
$`0 \log 0 = 0`$. For laws $`q`$ and $`r`$ on a finite set with
$`\mathrm{supp} q`$ contained in $`\mathrm{supp} r`$,
$`D(q \| r) = \sum_z q_z \log_2(q_z / r_z)`$ is the relative entropy; it is
nonnegative and vanishes only at $`q = r`$.

For a binary law $`p = (a,b,c,d)`$ write its marginals

```math
\begin{aligned}
\mu &= p_X = (\mu_0, \mu_1) = (a+b, c+d), \\
\nu &= p_Y = (\nu_0, \nu_1) = (a+c, b+d).
\end{aligned}
```

The blueprint defines $`\Phi`$, and the factor-nine proof's
[score decomposition](binary-factor-nine.md#the-score-decomposition) defines
$`\Psi`$; for a law $`m`$ on the four cells,

```math
\begin{aligned}
\Psi(m) &= 2\,H(m) - H(m_X) - H(m_Y) = H(X \mid Y) + H(Y \mid X), \\
\Phi(m) &= 3\,H(m) - 2\,H(m_X) - 2\,H(m_Y).
\end{aligned}
```

A finite stochastic latent $`L = (I, \pi, q)`$ for $`p`$ is a finite label set
$`I`$, a prior $`\pi`$ on $`I`$, and component laws $`q_v`$ with
$`\sum_v \pi_v q_v = p`$; this is the type $`\mathrm{Latent} p`$. The library
proves, for every such latent, the component decomposition of the score ([Lemma
6.2 of the factor-nine proof](binary-factor-nine.md#the-score-decomposition),
`latent_score_eq`
in [Bridge](../StochasticToDeterministicLatents/Bridge.lean)):

```math
\mathrm{score}_p(L) = \Psi(p) - \sum_{v \in I} \pi_v\,\Phi(q_v). \qquad \text{(1.1)}
```

Two consequences are used throughout.

- The constant latent, with the single component $`p`$, has score
$`\Psi(p) - \Phi(p) = H(p_X) + H(p_Y) - H(p) = I_p(X;Y)`$.
- The score depends on the latent only through the measure
$`\sum_v \pi_v\,\delta_{q_v}`$ on the simplex, called here the component
measure. Merging labels with equal component laws, or deleting labels with zero
weight, changes neither the mixture nor the score.

The library also proves that the stochastic optimum is attained: for every
probability law there is a latent with $`\mathrm{score}_p(L) = \tau(p)`$
(`exists_optimalLatent`). The deterministic optimum satisfies
$`\tau(p) \le T(p) \le I_p(X;Y)`$: every code defines a latent of equal score
(`ofFunction_score_eq_detScore`), $`\tau(p)`$ is at most every latent score
(`tau_le_score`), and the constant code has score
$`I(X;Y \mid \mathrm{const}) + H(\mathrm{const} \mid X) + H(\mathrm{const} \mid Y) =
I_p(X;Y)`$. Hence

```math
\tau(p) = I_p(X;Y) \implies \tau(p) = T(p) = I_p(X;Y). \qquad \text{(1.2)}
```

Relabeling either observed variable is a bijection of cells. It transports
latents, preserves every entropy in (1.1), and therefore preserves $`\tau`$.
Exchanging the two $`Y`$ labels sends $`(a,b,c,d)`$ to $`(b,a,d,c)`$ and
changes the sign of $`\Delta`$; exchanging the two diagonal cells is not a
relabeling and is used below only as an operation on component laws.

## 2. The support face and the concave envelope

Let $`S = \mathrm{supp} p`$ and let $`\Delta_S`$ be the set of laws supported
in $`S`$. It is a simplex of dimension $`\lvert S \rvert - 1`$, and $`p`$ lies
in its relative interior.

**Lemma 2.1 (components live on the support face).** If $`L = (I, \pi, q)`$ is
a latent for $`p`$ and $`\pi_v > 0`$, then $`\mathrm{supp} q_v`$ is contained
in $`S`$.

*Proof.* For a cell $`z`$ outside $`S`$, $`0 = p_z = \sum_v \pi_v q_v(z)`$ is a
sum of nonnegative terms, so $`q_v(z) = 0`$ whenever $`\pi_v > 0`$.

Define the concave envelope of $`\Phi`$ on the face as

```math
(\mathrm{conc}_S \Phi)(m) = \sup\{ \sum_v \pi_v\,\Phi(q_v) : m = \sum_v \pi_v\,q_v \text{ is a finite decomposition}, \ q_v \in \Delta_S \}. \qquad \text{(2.1)}
```

$`\Phi`$ is bounded on the simplex, so this is finite. The trivial
decomposition gives $`\mathrm{conc}_S \Phi \ge \Phi`$, and combining
decompositions of two laws gives a decomposition of any mixture, so
$`\mathrm{conc}_S \Phi`$ is concave on $`\Delta_S`$.

**Lemma 2.2 (envelope form of the optimum).**
$`\tau(p) = \Psi(p) - (\mathrm{conc}_S \Phi)(p)`$, and the supremum in (2.1) at
$`m = p`$ is attained.

*Proof.* By (1.1) and Lemma 2.1, the scores of latents for $`p`$ are exactly
the numbers $`\Psi(p) - \sum_v \pi_v\,\Phi(q_v)`$ over decompositions of $`p`$
with components in $`\Delta_S`$; conversely every such decomposition is a
latent. Taking the infimum gives the formula, and `exists_optimalLatent`
gives attainment.

**Lemma 2.3 (supporting affine majorant).** There is an affine function
$`\ell`$ on the affine hull of $`\Delta_S`$ with
$`\ell \ge \mathrm{conc}_S \Phi`$ on $`\Delta_S`$ and
$`\ell(p) = (\mathrm{conc}_S \Phi)(p)`$.

*Proof.* $`\mathrm{conc}_S \Phi`$ is a finite concave function on the convex
set $`\Delta_S`$, and $`p`$ is in its relative interior. A finite concave
function on a convex set has a supergradient at every relative-interior point
(Rockafellar, *Convex Analysis*, Theorem 23.4, applied to the convex function
$`-\mathrm{conc}_S \Phi`$). The affine function through $`(p, (\mathrm{conc}_S \Phi)(p))`$
with that slope is $`\ell`$.

Fix one such $`\ell`$ for the rest of the argument, and call

```math
C(\ell) = \{ q \in \Delta_S : \Phi(q) = \ell(q) \} \qquad \text{(2.2)}
```

its contact set. Since $`\ell \ge \mathrm{conc}_S \Phi \ge \Phi`$, a contact is
a point where the majorant touches $`\Phi`$ itself.

**Lemma 2.4 (every optimizer lives on the contact set).** Let
$`L = (I, \pi, q)`$ be any latent for $`p`$ with
$`\mathrm{score}_p(L) = \tau(p)`$. Then $`q_v`$ is a contact of $`\ell`$ for
every label with $`\pi_v > 0`$.

*Proof.* Drop the zero-weight labels. By Lemma 2.2 and optimality,
$`\sum_v \pi_v\,\Phi(q_v) = (\mathrm{conc}_S \Phi)(p) = \ell(p)`$. Since
$`\ell`$ is affine and $`\sum_v \pi_v q_v = p`$,

```math
\sum_v \pi_v\,[ \ell(q_v) - \Phi(q_v) ] = \ell(p) - \ell(p) = 0.
```

Every summand is nonnegative and every $`\pi_v`$ is positive, so every
summand vanishes.

Lemma 2.4 applies to every optimizer, not only to a selected one, because
$`\ell`$ was chosen before the optimizer. Bounding $`C(\ell)`$ therefore bounds
the component set of every optimal latent at once. The rest of the page
bounds it.

## 3. The deficit and the tangent test

Let $`p`$ have support $`S`$. Its tangent affine function is

```math
\ell_p(q) = \sum_{z=(x,y) \in S} q_z\,\log_2( \mu_x^2\,\nu_y^2 / p_z^3 ), \qquad \text{(3.1)}
```

a linear function of $`q \in \Delta_S`$ with finite coefficients. Direct
substitution gives $`\ell_p(p) = \Phi(p)`$. The deficit of a law
$`q \in \Delta_S`$ relative to $`p`$ is

```math
\begin{aligned}
\delta_p(q) &= \ell_p(q) - \Phi(q) \\
&= 3\,D(q \| p) - 2\,D(q_X \| \mu) - 2\,D(q_Y \| \nu). \qquad \text{(3.2)}
\end{aligned}
```

The second line is the first with the entropies of (3.1) expanded; every
divergence is finite because $`q`$ is supported in $`S`$. In particular
$`\delta_p(p) = 0`$.

The notation $`\delta_p`$ is chosen to avoid $`D_p(g)`$, which the blueprint
reserves for the deterministic score.

**Lemma 3.1 (derivative of $`\Phi`$).** $`\Phi`$ is differentiable at every
relative-interior point $`p`$ of $`\Delta_S`$, and for every tangent vector
$`h`$ (supported in $`S`$, with $`\sum_z h_z = 0`$) its derivative
is $`\ell_p(h)`$.

*Proof.* Each entropy in $`\Phi`$ is a finite sum of $`-t\log_2(t)`$, which is
smooth on $`t > 0`$; at $`p`$ every cell of $`S`$ is positive, hence so is
every marginal that meets $`S`$, and a marginal that misses $`S`$ vanishes at
every law in $`\Delta_S`$, so its entropy term is constant along every tangent
vector and contributes nothing. The derivative of $`-t\log_2(t)`$ is
$`-\log_2(t) - 1/\ln(2)`$, and the constant $`-1/\ln(2)`$ cancels against
$`\sum_z h_z = 0`$, and likewise against $`\sum_x h_X(x) = 0`$ and
$`\sum_y h_Y(y) = 0`$ in the marginal terms. What remains is
$`-3\,\sum_z h_z\,\log_2(p_z) + 2\,\sum_x h_X(x)\,\log_2(\mu_x) + 2\,\sum_y h_Y(y)\,\log_2(\nu_y) = \ell_p(h)`$.

**Theorem 3.2 (tangent test).** For a binary law $`p`$ with support $`S`$, the
following are equivalent:

1. $`\tau(p) = I_p(X;Y)`$;
2. $`\delta_p(q) \ge 0`$ for every $`q \in \Delta_S`$;
3. $`\Phi \le \ell_p`$ on $`\Delta_S`$.

When they hold, $`\tau(p) = T(p) = I_p(X;Y)`$.

*Proof.* Items 2 and 3 are the same statement by (3.2).

(2 implies 1.) For any latent $`L = (I, \pi, q)`$ for $`p`$, Lemma 2.1 puts
every positive-weight component in $`\Delta_S`$, so
$`\Phi(q_v) \le \ell_p(q_v)`$; summing with the weights and using linearity,
$`\sum_v \pi_v\,\Phi(q_v) \le \ell_p(p) = \Phi(p)`$. By (1.1),
$`\mathrm{score}_p(L) \ge \Psi(p) - \Phi(p) = I_p(X;Y)`$. The constant latent
attains this.

(1 implies 2.) Suppose $`\delta_p(q) < 0`$ for some $`q \in \Delta_S`$. For
small $`\epsilon > 0`$ the law

```math
r = (p - \epsilon q) / (1 - \epsilon)
```

is in $`\Delta_S`$ (every cell of $`p`$ in $`S`$ is positive, and $`q`$
vanishes off $`S`$), and $`p = \epsilon q + (1-\epsilon)\,r`$ is a two-label
latent for $`p`$. Since $`r - p = \epsilon\,(p - q)/(1-\epsilon)`$ is a tangent
vector of size $`O(\epsilon)`$, Lemma 3.1 gives
$`\Phi(r) = \Phi(p) + \ell_p(r - p) + o(\epsilon)`$, hence

```math
\begin{aligned}
&\epsilon\,\Phi(q) + (1-\epsilon)\,\Phi(r) \\
&= \epsilon\,\Phi(q) + (1-\epsilon)\,\Phi(p) + \epsilon\,\ell_p(p - q) + o(\epsilon) \\
&= \Phi(p) + \epsilon\,[ \Phi(q) - \ell_p(q) ] + o(\epsilon) \\
&= \Phi(p) - \epsilon\,\delta_p(q) + o(\epsilon),
\end{aligned}
```

using $`\ell_p(p) = \Phi(p)`$. By (1.1) the two-label latent has score
$`I_p(X;Y) + \epsilon\,\delta_p(q) + o(\epsilon)`$, which is below $`I_p(X;Y)`$
for small $`\epsilon`$. So $`\tau(p) < I_p(X;Y)`$.

The last sentence of the theorem is (1.2).

## 4. The rational constant-optimality test

Throughout this section $`p`$ has nondegenerate marginals: all four of
$`\mu_0, \mu_1, \nu_0, \nu_1`$ are positive. Cells of $`p`$ may vanish. Define

```math
\begin{aligned}
A &= \nu_0^2 - a^3/\mu_0^2 - c^3/\mu_1^2, \\
E &= \nu_1^2 - b^3/\mu_0^2 - d^3/\mu_1^2, \\
V &= (ad - bc)^2 / (\mu_0\,\mu_1), \\
M &= \nu_0\,\nu_1. \qquad \text{(4.1)}
\end{aligned}
```

**Theorem 4.1 (rational test).** For a binary law $`p`$ with nondegenerate
marginals, $`\tau(p) = I_p(X;Y)`$ if and only if

```math
A \ge 0, E \ge 0, V^3 \le AEM. \qquad \text{(C)}
```

When (C) holds, $`\tau(p) = T(p) = I_p(X;Y)`$. When $`p`$ has a degenerate
marginal, $`\tau(p) = T(p) = I_p(X;Y) = 0`$ directly: one observed variable is
constant, and the constant latent has score $`I_p(X;Y) = 0`$.

The proof passes through five equivalent conditions. Norms are weighted: for a
nonnegative function $`f`$ on $`\{0,1\}`$ and a positive law $`m`$ there,

```math
\begin{aligned}
\|f\|_{3/2,m} &= ( m_0\,f_0^{3/2} + m_1\,f_1^{3/2} )^{2/3}, \\
\|f\|_{3,m} &= ( m_0\,f_0^3 + m_1\,f_1^3 )^{1/3}.
\end{aligned}
```

### Step 1: a finite Gibbs identity

**Lemma 4.2.** Let $`\pi`$ be a positive law on a finite set $`J`$ and $`h`$ a
real function on $`J`$. Then

```math
\log_2( \sum_j \pi_j\,2^{h_j} ) = \max_u \{ E_u[h] - D(u \| \pi) \}, \qquad \text{(4.2)}
```

the maximum over laws $`u`$ on $`J`$, attained at $`u_j = \pi_j\,2^{h_j}/Z`$ with
$`Z`$ the sum on the left.

*Proof.* With that $`u^h`$, direct expansion gives
$`D(u \| u^h) = D(u \| \pi) - E_u[h] + \log_2(Z)`$ for every law $`u`$ on
$`J`$. The left side is nonnegative and vanishes at $`u = u^h`$.

### Step 2: deficit and a bilinear inequality

**Lemma 4.3.** Condition 2 of Theorem 3.2 holds for $`p`$ if and only if

```math
E_p[ f(X)\,g(Y) ] \le \|f\|_{3/2,\mu} \cdot \|g\|_{3/2,\nu} \qquad \text{(B)}
```

for all nonnegative $`f`$ and $`g`$ on $`\{0,1\}`$.

*Proof.* (2 implies (B).) Take $`f, g`$ strictly positive first. Apply (4.2) on
$`J = S`$ with $`\pi = p`$ and $`h_z = \log_2 f_x + \log_2 g_y`$ for
$`z = (x,y)`$:

```math
\log_2 E_p[fg] = \max_{q \in \Delta_S} \{ E_{q_X}[\log_2 f] + E_{q_Y}[\log_2 g] - D(q \| p) \}.
```

By condition 2, $`D(q \| p) \ge (2/3)\,D(q_X \| \mu) + (2/3)\,D(q_Y \| \nu)`$, so
each bracket is at most

```math
\begin{aligned}
&(2/3)\,\{ E_{q_X}[\log_2 f^{3/2}] - D(q_X \| \mu) \} \\
&+ (2/3)\,\{ E_{q_Y}[\log_2 g^{3/2}] - D(q_Y \| \nu) \}.
\end{aligned}
```

Relaxing the marginal pair $`(q_X, q_Y)`$ to arbitrary laws on $`\{0,1\}`$ and
applying (4.2) once on each factor bounds this by
$`(2/3)\,\log_2 E_\mu[f^{3/2}] + (2/3)\,\log_2 E_\nu[g^{3/2}] = \log_2( \|f\|_{3/2,\mu} \cdot \|g\|_{3/2,\nu} )`$.
Exponentiate. For nonnegative $`f, g`$, apply this to $`f + \epsilon`$,
$`g + \epsilon`$ and let $`\epsilon`$ decrease to zero; both sides
are continuous.

((B) implies 2.) Fix $`q \in \Delta_S`$ and set

```math
f_x = ( q_X(x)/\mu_x )^{2/3}, g_y = ( q_Y(y)/\nu_y )^{2/3}.
```

Then $`\|f\|_{3/2,\mu}^{3/2} = \sum_x \mu_x\,(q_X(x)/\mu_x) = 1`$, and likewise for
$`g`$, so (B) gives $`W = E_p[fg] \le 1`$. Also $`W > 0`$: some cell
$`z = (x,y)`$ has $`q_z > 0`$, hence $`p_z > 0`$, $`q_X(x) > 0`$,
$`q_Y(y) > 0`$. Define on $`S`$ the law $`w_z = p_z\,f_x\,g_y / W`$; it is positive
wherever $`q`$ is. On the cells with $`q_z > 0`$,

```math
\begin{aligned}
\log_2(q_z/w_z) &= \log_2(q_z/p_z) - (2/3)\,\log_2(q_X(x)/\mu_x) \\
&- (2/3)\,\log_2(q_Y(y)/\nu_y) + \log_2 W,
\end{aligned}
```

and summing with weights $`q_z`$ gives the exact identity

```math
\delta_p(q) = 3\,[ D(q \| w) - \log_2 W ]. \qquad \text{(4.3)}
```

Both terms in the bracket are nonnegative, so $`\delta_p(q) \ge 0`$.

### Step 3: the conditional kernel

Let $`K`$ be the kernel of $`Y`$ given $`X`$, $`K_{xy} = p_{xy}/\mu_x`$; its rows
sum to one, and $`E_p[f(X)\,g(Y)] = E_\mu[ f\,(K g) ]`$ with
$`(K g)_x = \sum_y K_{xy}\,g_y`$.

**Lemma 4.4 (weighted Hoelder with equality case).** For nonnegative $`f, h`$
on $`\{0,1\}`$ and a positive law $`m`$,
$`E_m[f\,h] \le \|f\|_{3/2,m} \cdot \|h\|_{3,m}`$. If $`f`$ and $`h`$ are nonzero,
equality holds exactly when $`f`$ is proportional to $`h^2`$ pointwise.

*Proof.* Normalize both norms to one. Young's inequality
$`uv \le (2/3)\,u^{3/2} + (1/3)\,v^3`$ for $`u, v \ge 0`$, with equality exactly
when $`u = v^2`$, averages under $`m`$ to $`E_m[f\,h] \le 2/3 + 1/3 = 1`$, with
equality exactly when $`f_x = h_x^2`$ at both points (both have
positive weight).

**Lemma 4.5.** (B) holds if and only if

```math
\|K g\|_{3,\mu} \le \|g\|_{3/2,\nu} \qquad \text{for every nonnegative } g. \qquad \text{(N)}
```

*Proof.* (N) implies (B) by Lemma 4.4 applied to $`f`$ and $`h = K g`$. For the
converse, given $`g`$ with $`h = K g`$ nonzero, take $`f = h^2/\|h\|_{3,\mu}^2`$;
then $`\|f\|_{3/2,\mu} = 1`$ and $`E_\mu[f\,h] = \|h\|_{3,\mu}`$, so (B) gives (N). If
$`K g = 0`$ there is nothing to prove.

### Step 4: a polynomial on a half-line

For $`x \ge 0`$ put $`g = (x^2, 1)`$. Then

```math
\begin{aligned}
\|g\|_{3/2,\nu}^3 &= (\nu_0 x^3 + \nu_1)^2, \\
\|K g\|_{3,\mu}^3 &= (ax^2 + b)^3/\mu_0^2 + (cx^2 + d)^3/\mu_1^2,
\end{aligned}
```

and their difference is

```math
P(x) = (\nu_0 x^3 + \nu_1)^2 - (ax^2 + b)^3/\mu_0^2 - (cx^2 + d)^3/\mu_1^2. \qquad \text{(4.4)}
```

**Lemma 4.6.** (N) holds if and only if $`P(x) \ge 0`$ for every $`x \ge 0`$.

*Proof.* Both sides of (N) are positively homogeneous in $`g`$. A nonnegative
$`g`$ with $`g_1 > 0`$ is a positive multiple of $`(x^2, 1)`$ with
$`x = \sqrt{g_0/g_1} \ge 0`$, and its cubed slack is a positive multiple of
$`P(x)`$. The ray $`g = (g_0, 0)`$ has cubed slack $`g_0^3 A`$, and $`A`$ is
the leading coefficient of $`P`$, which is the limit of $`x^{-6}\,P(x)`$; so
$`P \ge 0`$ on the half-line forces $`A \ge 0`$ and covers this ray. The zero
vector is trivial.

### Step 5: the factorization

**Lemma 4.7.** With $`A, E, V`$ as in (4.1),

```math
\begin{aligned}
P(x) &= (x - 1)^2\,Q(x), \\
Q(x) &= Ax^4 + 2Ax^3 - 3Vx^2 + 2Ex + E, \qquad \text{(4.5)}
\end{aligned}
```

and

```math
A + E = M - 3V. \qquad \text{(4.6)}
```

*Proof.* Let $`k`$ be the two-valued random variable $`P(Y=0 \mid X)`$, taking
the values $`a/\mu_0`$ and $`c/\mu_1`$ with weights $`\mu_0, \mu_1`$, and write
$`m_j = E_\mu[k^j]`$. Then $`m_1 = \nu_0`$, and the variance identity
gives $`m_2 - \nu_0^2 = \mu_0\,\mu_1\,(a/\mu_0 - c/\mu_1)^2 = V`$. Expanding (4.4) row by
row, $`(ax^2+b)^3/\mu_0^2 = \mu_0\,(k_0 x^2 + (1-k_0))^3`$ with $`k_0 = a/\mu_0`$, and
similarly for the second row, so

```math
\begin{aligned}
P(x) &= Ax^6 - 3\,(m_2 - m_3)\,x^4 + 2\,\nu_0\,\nu_1 x^3 \\
&- 3\,(\nu_0 - 2m_2 + m_3)\,x^2 + E,
\end{aligned}
```

with $`A = \nu_0^2 - m_3`$ and
$`E = \nu_1^2 - E_\mu[(1-k)^3] = \nu_1^2 - (1 - 3\,\nu_0 + 3m_2 - m_3)`$.
Expanding $`(x-1)^2\,Q(x)`$ gives the coefficients
$`A, 0, -3A - 3V, 2A + 2E + 6V, -3E - 3V, 0, E`$ in decreasing degree. These
agree with the expansion of $`P`$: for $`x^4`$, $`-3A - 3V = -3\,(m_2 - m_3)`$;
for $`x^2`$, $`-3E - 3V = -3\,(\nu_0 - 2m_2 + m_3)`$ after substituting
$`\nu_1 = 1 - \nu_0`$; for $`x^3`$, $`2A + 2E + 6V = 2\,\nu_0\,\nu_1`$, which
is (4.6). The identity (4.6) itself is
$`A + E = \nu_0^2 + \nu_1^2 - E_\mu[k^3 + (1-k)^3] = \nu_0^2 + \nu_1^2 - 1 + 3\,\nu_0 - 3m_2 = \nu_0 - \nu_0^2 - 3V = M - 3V`$.

**Lemma 4.8.** $`P \ge 0`$ on $`[0, \infty)`$ if and only if $`Q \ge 0`$ there.

*Proof.* One direction is (4.5). Conversely, if $`P \ge 0`$ on the half-line,
division by $`(x-1)^2`$ gives $`Q \ge 0`$ at every $`x \ne 1`$, and continuity
gives $`Q(1) \ge 0`$.

### Step 6: eliminating the last variable

**Lemma 4.9.** $`Q \ge 0`$ on $`[0, \infty)`$ if and only if (C) holds.

*Proof.* $`Q(0) = E`$, so $`E \ge 0`$ is necessary. If $`A < 0`$, $`Q`$ is
negative for large $`x`$; so $`A \ge 0`$ is necessary.

Suppose $`A > 0`$ and $`E > 0`$. For $`x > 0`$,

```math
\begin{aligned}
Q(x)/x^2 &= A\,(x^2 + 2x) + E\,(2/x + 1/x^2) - 3V =: G(x), \\
G'(x) &= 2\,(x+1)\,(A - E/x^3).
\end{aligned}
```

So $`G`$ decreases on $`(0, t]`$ and increases on $`[t, \infty)`$ with
$`t = (E/A)^{1/3}`$, and its minimum is

```math
\begin{aligned}
G(t) &= 3At^2 + 3At - 3V = 3\,(\sigma - V), \\
\sigma &= At\,(t + 1) = A^{2/3}\,E^{1/3} + A^{1/3}\,E^{2/3}.
\end{aligned}
```

Hence $`Q \ge 0`$ on the half-line exactly when $`V \le \sigma`$. Now
$`\sigma^3 = AE\,(A + E + 3\,\sigma)`$, by expanding the cube. The cubic
$`F(y) = y^3 - 3AEy - AE\,(A+E)`$ has $`F(0) < 0`$, decreases on
$`[0, \sqrt{AE}]`$, and increases afterwards, so $`\sigma`$ is its only
nonnegative root and $`F(V) \le 0`$ exactly when $`V \le \sigma`$. Finally
$`F(V) \le 0`$ reads $`V^3 \le AE\,(A + E + 3V) = AEM`$ by (4.6). This is (C)
in the case $`A, E > 0`$.

If $`A = 0`$ and $`E \ge 0`$, then $`Q(x) = -3Vx^2 + 2Ex + E`$, which is
nonnegative on the half-line exactly when $`V = 0`$; (C) reads $`V^3 \le 0`$,
the same condition. If $`E = 0`$ and $`A \ge 0`$, then
$`Q(x) = x^2\,(Ax^2 + 2Ax - 3V)`$, which is negative for small positive $`x`$
unless $`V = 0`$, and nonnegative when $`V = 0`$; again (C) reads $`V = 0`$.
This covers $`A = E = 0`$ as well.

*Proof of Theorem 4.1.* Theorem 3.2, Lemma 4.3, Lemma 4.5, Lemma 4.6, Lemma
4.8, and Lemma 4.9 chain the equivalences $`\tau(p) = I_p(X;Y)`$ iff condition
2 iff (B) iff (N) iff $`P \ge 0`$ iff $`Q \ge 0`$ iff (C). The deterministic
statement is (1.2).

**Example 4.10 (uniform marginals).** For
$`p = ((1+r)/4, (1-r)/4, (1-r)/4, (1+r)/4)`$ with $`-1 < r < 1`$,

```math
\begin{aligned}
A &= E = (1 - 3r^2)/8, V = r^2/4, M = 1/4, \\
AEM - V^3 &= (1 - r^2)^2\,(1 - 4r^2) / 256.
\end{aligned}
```

The condition $`V^3 \le AEM`$ is $`\lvert r \rvert \le 1/2`$, and it implies $`A = E \ge 0`$.
So the constant latent is optimal exactly when $`\lvert r \rvert \le 1/2`$.

**Example 4.11 (a law with a zero cell).** For $`p = (1/3, 1/3, 1/3, 0)`$,
$`A = E = 1/36`$, $`V = 1/18`$, $`M = 2/9`$, and $`AEM = V^3 = 1/5832`$. (C)
holds with equality, so $`\tau(p) = T(p) = I_p(X;Y) = \log_2(3) - 4/3`$.

**Example 4.12 (a full-support law).** For $`p = (1/2, 1/5, 1/10, 1/5)`$,
$`A = 1034/11025`$, $`E = 604/11025`$, $`V = 16/525`$, $`M = 6/25`$, and
$`AEM - V^3 = 1808/1500625 > 0`$. The constant latent is optimal, and it
stays optimal on an open neighbourhood, since all three inequalities are
strict and the quantities are continuous.

## 5. At most two component laws

**Theorem 5.1.** Let $`p`$ be a binary law and $`L`$ any $`\tau`$-optimal
finite latent for $`p`$. Then the positive-weight labels of $`L`$ carry at most
two distinct component laws. In particular, merging equal components gives a
$`\tau`$-optimal latent with at most two labels.

*Proof.* Let $`S = \mathrm{supp} p`$ and fix $`\ell`$ as in Lemma 2.3. By Lemma
2.4 every positive-weight component of $`L`$ lies in $`C(\ell)`$, so it
suffices to show $`\lvert C(\ell) \rvert \le 2`$. The cases are by the size
of $`S`$.

**Small supports.** If $`\lvert S \rvert = 1`$, then $`\Delta_S = \{p\}`$ and
$`C(\ell) = \{p\}`$. If $`\lvert S \rvert = 2`$ and the two cells share a row
(the column case is symmetric), a law $`q = (t, 1-t)`$ on the edge has
$`H(q_X) = 0`$ and $`H(q_Y) = H(q)`$, so
$`\Phi(q) = 3\,H(q) - 2\,H(q) = H(q)`$, a strictly concave function of $`t`$.
Then $`\mathrm{conc}_S \Phi = \Phi`$, and $`\ell`$ is a supporting line of a
strictly concave function at $`p`$. Such a line touches the function only at
$`p`$: if $`\ell(q) = \Phi(q)`$ for some $`q \ne p`$, strict concavity puts
$`\Phi`$ strictly above the chord from $`(p, \Phi(p))`$ to $`(q, \Phi(q))`$,
which is $`\ell`$, between them, contradicting $`\ell \ge \Phi`$. So
$`C(\ell) = \{p\}`$. If $`\lvert S \rvert = 2`$ and the cells are opposite,
$`H(q_X) = H(q_Y) = H(q)`$, so $`\Phi(q) = -H(q)`$, strictly convex on the
edge, zero at the two vertices and negative between them. The least concave
majorant of a convex function on a segment is the chord between its endpoint
values, so $`\mathrm{conc}_S \Phi = 0`$. Then $`\ell \ge 0`$ on the segment
with $`\ell(p) = 0`$ at an interior point, which forces $`\ell = 0`$, and
$`C(\ell)`$ is the set where $`\Phi = 0`$: the two vertices. In all three cases
$`\lvert C(\ell) \rvert \le 2`$.

**Connected supports, $`\lvert S \rvert \ge 3`$.** Any three or four cells of a
$`2 \times 2`$ table are connected: every pair is joined by a chain of cells of
$`S`$ with consecutive cells in a common row or column. Every row and every
column meets $`S`$.

*(a) Contacts are positive on `S`.* Let $`q \in \Delta_S`$ have a zero cell in
$`S`$ and a positive cell. Walking along a chain from a positive cell to a zero
cell, the first zero cell $`z'`$ is adjacent to a positive cell $`z`$. For
$`0 < \epsilon < q_z`$ put $`q^\epsilon = q + \epsilon\,(\delta_{z'} - \delta_z)`$, which
is in $`\Delta_S`$. Say $`z`$ and $`z'`$ share a row (the other case swaps rows
and columns). Then every row marginal is unchanged. The cell $`z'`$ acquires
mass $`\epsilon`$, contributing $`\epsilon\,\log_2(1/\epsilon)`$ to $`H(q^\epsilon) - H(q)`$;
the cell $`z`$ and the column of $`z`$, both positive at $`q`$, change by
$`O(\epsilon)`$; the column of $`z'`$ contributes
$`\epsilon\,\log_2(1/\epsilon) + O(\epsilon)`$ to $`H((q^\epsilon)_Y) - H(q_Y)`$ if it had zero
mass at $`q`$, and $`O(\epsilon)`$ otherwise. Let $`k \in \{0,1\}`$ count that
case. Then

```math
\Phi(q^\epsilon) - \Phi(q) = (3 - 2k)\,\epsilon\,\log_2(1/\epsilon) + O(\epsilon),
```

with $`3 - 2k \ge 1`$, while $`\ell(q^\epsilon) - \ell(q) = O(\epsilon)`$. If $`q`$ were
a contact, $`\ell(q^\epsilon) - \Phi(q^\epsilon)`$ would be negative for small $`\epsilon`$,
contradicting $`\ell \ge \Phi`$ on $`\Delta_S`$. So every contact is positive
on every cell of $`S`$; in particular it has nondegenerate marginals.

*(b) The majorant is the tangent at any contact.* Let $`q \in C(\ell)`$. By (a)
$`q`$ is a relative-interior point of $`\Delta_S`$, and $`\ell - \Phi`$ is
nonnegative on $`\Delta_S`$ and zero at $`q`$. For every tangent vector $`h`$,
the function $`t \to (\ell - \Phi)(q + th)`$ is nonnegative for small
$`\lvert t \rvert`$, zero at $`t = 0`$, and differentiable there by Lemma 3.1;
so its derivative vanishes, that is, the linear part of $`\ell`$ agrees with
$`\ell_q`$ on tangent vectors. Since also $`\ell(q) = \Phi(q) = \ell_q(q)`$,
the two affine functions agree on $`\Delta_S`$: $`\ell = \ell_q`$. Consequently

```math
\ell(r) - \Phi(r) = \delta_q(r) \qquad \text{for every } r \in \Delta_S,
```

so $`\delta_q \ge 0`$ on $`\Delta_S`$, $`q`$ passes the tangent test of Theorem
3.2 (with $`q`$ in the role of $`p`$), and by Theorem 4.1 the quantities
$`A_q, E_q, V_q, M_q`$ of (4.1) computed at $`q`$ satisfy (C); by Lemma 4.9 the
quartic $`Q_q`$ is nonnegative on the half-line. The contacts of $`\ell`$ are
exactly the laws $`r \in \Delta_S`$ with $`\delta_q(r) = 0`$.

*(c) `A_q` and `E_q` are positive.* If $`A_q = 0`$ or $`E_q = 0`$, (C) forces
$`V_q = 0`$, hence $`\det q = 0`$. A $`2 \times 2`$ law with zero determinant
is the product of its marginals, because
$`q_{00} - q_X(0)\,q_Y(0) = q_{00}\,q_{11} - q_{01}\,q_{10}`$ after expanding
with $`\sum q = 1`$. For a product law with nondegenerate marginals, (4.1)
gives $`A_q = \nu_0^2 - \nu_0^3\,(\mu_0 + \mu_1) = \nu_0^2\,\nu_1 > 0`$ and
$`E_q = \nu_1^2\,\nu_0 > 0`$, a contradiction.

*(d) At most two equality rays, and one contact per ray.* Let
$`r \in C(\ell)`$, so $`\delta_q(r) = 0`$. Apply the construction of Lemma 4.3
with $`q`$ as the reference law: $`f_x = (r_X(x)/q_X(x))^{2/3}`$,
$`g_y = (r_Y(y)/q_Y(y))^{2/3}`$, $`W = E_q[fg]`$, $`w = q\,f\,g/W`$. By (4.3),
$`\delta_q(r) = 0`$ forces $`D(r \| w) = 0`$ and $`\log_2 W = 0`$: $`r = w`$
and $`W = 1`$. With $`K`$ the kernel of $`q`$,

```math
\begin{aligned}
1 = W &= E_{q_X}[ f\,(K g) ] \\
&\le \|f\|_{3/2,q_X} \cdot \|K g\|_{3,q_X} \\
&\le \|f\|_{3/2,q_X} \cdot \|g\|_{3/2,q_Y} = 1,
\end{aligned}
```

so both inequalities are equalities. In particular $`g`$ is a nonzero equality
vector of (N) for $`q`$. Neither coordinate of $`g`$ vanishes: the ray
$`(g_0, 0)`$ has cubed slack $`g_0^3 A_q > 0`$ and the ray $`(0, g_1)`$ has
cubed slack $`g_1^3 E_q > 0`$. So $`g = \gamma\,(x^2, 1)`$ with $`\gamma > 0`$,
$`x > 0`$, and its cubed slack $`\gamma^3 P_q(x)`$ vanishes: $`P_q(x) = 0`$.

Write $`t = (E_q/A_q)^{1/3}`$ and $`\sigma = A_q t\,(t+1)`$ as in Lemma 4.9. A
direct expansion, using $`E_q = A_q t^3`$, gives

```math
Q_q(x) = A_q\,(x - t)^2\,[ x^2 + 2\,(1+t)\,x + t ] + 3\,(\sigma - V_q)\,x^2. \qquad \text{(5.1)}
```

The bracket is positive for $`x \ge 0`$, and $`\sigma - V_q \ge 0`$ by Lemma
4.9. So $`Q_q(x) = 0`$ with $`x > 0`$ forces $`x = t`$ and $`\sigma = V_q`$.
Since $`P_q = (x-1)^2 Q_q`$, the zeros of $`P_q`$ on $`x > 0`$ lie in
$`\{1, t\}`$. There are at most two rays.

Each ray yields at most one contact. The unit norm $`\|g\|_{3/2,q_Y} = 1`$ fixes
$`\gamma`$. The vector $`h = K g`$ is strictly positive, because $`K`$ has
nonnegative entries, unit row sums, and $`g`$ is positive. Equality in Lemma
4.4 with $`\|f\|_{3/2,q_X} = \|h\|_{3,q_X} = 1`$ forces $`f = h^2`$. Then
$`r = w = qfg`$ is determined. The ray $`x = 1`$ gives $`g = (1,1)`$,
$`f = (1,1)`$, and $`r = q`$ itself.

Hence $`\lvert C(\ell) \rvert \le 2`$ on every connected support, which proves
the theorem.

**Remark 5.2 (what the library proves).** The kernel-verified normal form
covers a special case of Theorem 5.1 in its own formulation. In
[TransposeNormalForm](../StochasticToDeterministicLatents/Binary/TransposeNormalForm.lean),
the proposition `Binary.ContactClassification` states that any three
full-support contacts of a common feasible binary kernel contain a
duplicate, and `transposeNormalFormInputs_hold` proves it; passing to the
duplicate quotient of the library's seed setup then yields, for a selected
optimizer on a full-support law, a quotient latent with at most two distinct
component laws (the library does not show that the two-class branch ever
occurs). That statement is about the dual
kernel of the upstream duality module and about a selected optimizer.
Theorem 5.1 is about the affine majorant of the concave envelope, every
optimizer, and every support. This page does not identify the two contact
notions; the Lean result is cited as corroboration on full support, not as
an input.

## 6. The cubic

For a binary law $`p = (a,b,c,d)`$ put $`s = a+d`$, $`v = b+c`$, $`w =
bc`$, and

```math
f_p(u) = u^3 - vu^2 - wu - ws. \qquad \text{(6.1)}
```

**Lemma 6.1 (the root).** If $`w > 0`$ and $`s > 0`$, then $`f_p`$ has exactly
one positive root $`u_0`$; $`f_p < 0`$ on $`[0, u_0)`$ and $`f_p > 0`$ on
$`(u_0, \infty)`$. Moreover $`u_0 > v`$. If $`w = 0`$, then
$`f_p(u) = u^2\,(u - v)`$, its largest nonnegative root is $`u_0 = v`$, and
$`f_p > 0`$ exactly on $`(v, \infty)`$.

*Proof.* For $`w > 0`$ and $`u > 0`$, $`f_p(u)/u^2 = u - v - w/u - ws/u^2`$ has
derivative $`1 + w/u^2 + 2ws/u^3 > 0`$, tends to $`-\infty`$ at $`0`$ and to
$`+\infty`$ at $`\infty`$, so it has exactly one zero and the stated signs;
$`f_p(0) = -ws < 0`$ completes the sign on $`[0, u_0)`$. Also
$`f_p(v) = -wv - ws = -w\,(v + s) = -w < 0`$, so $`u_0 > v`$. The case
$`w = 0`$ is direct.

**Lemma 6.2 (the norm margin factors).** For a law $`q = (a,b,c,d)`$ with
nondegenerate marginals, let $`\xi = ad`$, $`\eta = bc`$, and
$`\Lambda = abc + abd + acd + bcd`$. Then, with $`A, E, V, M`$ of (4.1)
computed at $`q`$,

```math
\begin{aligned}
&AEM - V^3 \\
&= [ \Lambda^2 - \xi\,(\xi - \eta)^2 ]\,[ \Lambda^2 - \eta\,(\xi - \eta)^2 ] / (\mu_0^4\,\mu_1^4). \qquad \text{(6.2)}
\end{aligned}
```

*Proof.* This is a polynomial identity. For unnormalized nonnegative cells with
total $`z = a+b+c+d`$, row sums $`m_0 = a+b`$, $`m_1 = c+d`$, and column sums
$`n_0 = a+c`$, $`n_1 = b+d`$, put

```math
\begin{aligned}
\mathrm{An} &= n_0^2\,m_0^2\,m_1^2 - z\,(a^3\,m_1^2 + c^3\,m_0^2), \\
\mathrm{En} &= n_1^2\,m_0^2\,m_1^2 - z\,(b^3\,m_1^2 + d^3\,m_0^2).
\end{aligned}
```

Then $`A = \mathrm{An}/(z^2 m_0^2 m_1^2)`$, $`E = \mathrm{En}/(z^2 m_0^2 m_1^2)`$,
$`V = (\xi - \eta)^2/(z^2 m_0 m_1)`$, $`M = n_0 n_1/z^2`$, and expanding both sides
gives

```math
\mathrm{An}\,\mathrm{En}\,n_0\,n_1 - (\xi - \eta)^6\,m_0\,m_1 = z^2\,[ \Lambda^2 - \xi\,(\xi-\eta)^2 ]\,[ \Lambda^2 - \eta\,(\xi-\eta)^2 ],
```

an identity of polynomials in the four cells. Dividing by $`z^6\,m_0^4\,m_1^4`$
and setting $`z = 1`$ gives (6.2). The expansion is reproduced by
[`scripts/check_stochastic_optimum_identities.py`](../scripts/check_stochastic_optimum_identities.py),
which also checks (4.5), (4.6), (5.1), and (6.3) below; the script is a
convenience for the reader, not part of the proof.

**Lemma 6.3 (sign of the margin).** Let $`q`$ be positive on a support $`S`$
with $`\lvert S \rvert \ge 3`$, and suppose $`\det q = \xi - \eta > 0`$. Then
the second factor of (6.2) is positive, and with
$`u = \sqrt{\xi} = \sqrt{ad}`$,

```math
\Lambda - u\,(\xi - \eta) = -f_q(u). \qquad \text{(6.3)}
```

Consequently $`AEM - V^3`$ has the sign of $`-f_q(\sqrt{ad})`$; in particular it
vanishes exactly when $`f_q(\sqrt{ad}) = 0`$.

*Proof.* If $`\eta > 0`$, then
$`\Lambda = \xi\,(b+c) + \eta\,(a+d) \ge 2\,\xi\,\sqrt{\eta} > \sqrt{\eta}\,(\xi - \eta)`$
(the first step is $`b + c \ge 2\,\sqrt{bc}`$), so
$`\Lambda^2 > \eta\,(\xi-\eta)^2`$. If $`\eta = 0`$, then $`b+c > 0`$ since
$`\lvert S \rvert \ge 3`$ and $`ad > 0`$, so $`\Lambda = \xi\,(b+c) > 0`$ and
$`\Lambda^2 > 0 = \eta\,(\xi-\eta)^2`$. For (6.3), substitute $`ad = u^2`$,
$`bc = w`$, $`a+d = s`$, $`b+c = v`$: $`\Lambda = u^2 v + ws`$ and
$`u\,(\xi - \eta) = u^3 - uw`$, so
$`\Lambda - u\,(\xi-\eta) = -(u^3 - vu^2 - wu - ws)`$. Since
$`\Lambda + u\,(\xi - \eta) > 0`$, the first factor
$`\Lambda^2 - \xi\,(\xi-\eta)^2 = (\Lambda - u\,(\xi-\eta))\,(\Lambda + u\,(\xi-\eta))`$
has the sign of $`-f_q(u)`$.

**Lemma 6.4 (a second contact is a diagonal swap).** Let $`q`$ be positive on a
support $`S`$ with $`\lvert S \rvert \ge 3`$, suppose $`\delta_q \ge 0`$ on
$`\Delta_S`$, and suppose the tangent majorant $`\ell_q`$ has a contact
$`r \ne q`$ in $`\Delta_S`$. Then $`\det q \ne 0`$. If $`\det q > 0`$, then
$`f_q(\sqrt{ad}) = 0`$, $`a \ne d`$, and $`r = (d, b, c, a)`$. If
$`\det q < 0`$, the same holds after exchanging the $`Y`$ labels: $`b \ne c`$
and $`r = (a, c, b, d)`$.

*Proof.* By step (d) of Theorem 5.1, a second contact requires the two rays
$`1`$ and $`t`$ to be distinct zeros of $`P_q = (x-1)^2 Q_q`$ on the half-line;
$`x = 1`$ is always one, and $`x = t`$ is one exactly when $`Q_q(t) = 0`$, that
is $`\sigma = V_q`$, which by the computation in Lemma 4.9 is
$`V_q^3 = A_q E_q M_q`$. A product law has $`V_q = 0`$ and $`A_q, E_q > 0`$ by
step (c), so $`\sigma > 0 = V_q`$ and only the ray $`x = 1`$ exists; hence
$`\det q \ne 0`$.

Take $`\det q > 0`$. Lemma 6.3 turns $`V_q^3 = A_q E_q M_q`$ into
$`f_q(u) = 0`$ with $`u = \sqrt{ad}`$. Let $`q' = (d, b, c, a)`$; it has
support $`S`$. Compare the coefficients (3.1) of $`\ell_q`$ and $`\ell_{q'}`$
cell by cell. At the off-diagonal cell $`(0,1)`$ the coefficient is
$`\log_2( (a+b)^2 (b+d)^2 / b^3 )`$ for $`q`$ and $`\log_2( (d+b)^2 (a+b)^2 / b^3 )`$
for $`q'`$: equal. The cell $`(1,0)`$ is the same. At the diagonal cell
$`(0,0)`$ the two coefficients are $`\log_2( (a+b)^2 (a+c)^2 / a^3 )`$ and
$`\log_2( (d+b)^2 (d+c)^2 / d^3 )`$, and they agree exactly when
$`a^{3/2} (d+b)(d+c) = d^{3/2} (a+b)(a+c)`$. With $`\alpha = \sqrt{a}`$,
$`\beta = \sqrt{d}`$, $`u = \alpha\,\beta`$, direct expansion gives

```math
\begin{aligned}
&a^{3/2}\,(d+b)\,(d+c) - d^{3/2}\,(a+b)\,(a+c) \\
&= (\alpha - \beta)\,[ -u^3 + (b+c)\,u^2 + bc\,(a + d + u) ] = -(\alpha - \beta)\,f_q(u),
\end{aligned}
```

which vanishes. The cell $`(1,1)`$ agrees by the same computation with the
roles of the two diagonal cells exchanged. Hence $`\ell_q = \ell_{q'}`$ on
$`\Delta_S`$. Since $`\ell_q \ge \Phi`$ on $`\Delta_S`$ and
$`\ell_{q'}(q') = \Phi(q')`$, the law $`q'`$ is a contact of $`\ell_q`$.

If $`a = d`$, then $`u = a`$, $`X = a^2`$, and $`f_q(a) = 0`$ reads
$`a^2\,(b+c) + 2abc = a\,(a^2 - bc)`$, that is, $`3bc = a\,(a - b - c)`$. A
direct computation then gives $`\mu_0\,\mu_1 = \nu_0\,\nu_1 = 2\,(ad - bc)`$,
so $`M_q = 4V_q`$, and by (4.5) and (4.6),
$`Q_q(1) = 3\,(A_q + E_q) - 3V_q = 3\,(M_q - 4V_q) = 0`$. By (5.1) the only
possible positive zero of $`Q_q`$ is $`t`$, so $`t = 1`$: the two rays
coincide, and $`\ell_q`$ has a single contact, contrary to hypothesis. So
$`a \ne d`$, $`q' \ne q`$, and since $`\lvert C(\ell_q) \rvert \le 2`$, the
second contact is $`q'`$.

For $`\det q < 0`$, exchange the $`Y`$ labels, apply the positive case, and
exchange back: the pair is $`q`$ and $`(a, c, b, d)`$.

**Lemma 6.5 (mixing a swap pair raises the determinant).** If
$`q^+ = (A', b, c, D')`$ and $`q^- = (D', b, c, A')`$ with $`A' \ne D'`$, and
$`p = \lambda q^+ + (1-\lambda)\,q^-`$ with $`0 < \lambda < 1`$, then

```math
p_{00}\,p_{11} = A'\,D' + \lambda\,(1-\lambda)\,(A' - D')^2 > A'\,D',
```

so $`\det p > \det q^+ = \det q^-`$. Symmetrically, mixing an off-diagonal swap
pair strictly lowers the determinant.

*Proof.* Expand
$`(\lambda A' + (1-\lambda)\,D')\,(\lambda D' + (1-\lambda)\,A')`$.

**Theorem 6.6 (the cubic decides, and locates, the optimum).** Let $`p`$ be a
binary law with $`\Delta > 0`$ and $`u_0`$ the largest nonnegative root of
(6.1). Then $`\tau(p) < I_p(X;Y)`$ if and only if $`\sqrt{ad} > u_0`$. In that
case the contact set of the majorant of Lemma 2.3 is $`\{q^+, q^-\}`$ with
$`q^+`$, $`q^-`$, $`\lambda`$ as in the theorem at the head of this page, and

```math
\tau(p) = \Psi(p) - \Phi(q^+) = \Psi(p) - \Phi(q^-).
```

*Proof.* Since $`\Delta > 0`$, both diagonal cells are positive and $`s > 0`$.
If $`b = c = 0`$, then $`S`$ is the opposite edge: as computed in Theorem 5.1,
$`\mathrm{conc}_S \Phi = 0`$ there, so
$`\tau(p) = \Psi(p) = H(X \mid Y) + H(Y \mid X) = 0`$, attained by revealing
the cell; the cubic has $`v = w = 0`$, $`u_0 = 0 < \sqrt{ad}`$,
$`\rho = s = 1`$, $`q^+ = (1,0,0,0)`$, $`q^- = (0,0,0,1)`$, $`\lambda = a`$,
and $`\Psi(p) - \Phi(q^+) = 0`$, in agreement with the statement. Assume from
now on that $`\lvert S \rvert \ge 3`$; then $`p`$ has nondegenerate marginals.

(If $`\tau(p) < I_p(X;Y)`$ then $`\sqrt{ad} > u_0`$.) Take an attained
optimizer (`exists_optimalLatent`) and fix $`\ell`$ as in Lemma 2.3. By Lemma
2.4 its positive-weight components are contacts of $`\ell`$. If they were all
equal to $`p`$, the score would be $`I_p(X;Y)`$; so some component differs from
$`p`$, and since the components average to $`p`$, there are at least two
distinct contacts. By Theorem 5.1 there are exactly two, $`q`$ and $`r`$, both
positive on $`S`$ by step (a), and by step (b) $`\ell = \ell_q`$ with
$`\delta_q \ge 0`$. Lemma 6.4 applies: the pair is a diagonal swap if
$`\det q > 0`$ and an off-diagonal swap if $`\det q < 0`$. The law $`p`$ is a
strict mixture of the pair (if $`p`$ were one of them, the barycentric equation
would give the other weight zero and the score $`I_p(X;Y)`$). An off-diagonal
pair would give $`\det p < \det q < 0`$ by Lemma 6.5, contradicting
$`\Delta > 0`$. So $`\det q > 0`$, the pair is $`(A', b, c, D')`$ and
$`(D', b, c, A')`$ with the same off-diagonal cells as $`p`$, and
$`A' + D' = s`$. By Lemma 6.4 the product $`A'\,D' = u^2`$ satisfies
$`f_q(u) = 0`$, and $`f_q = f_p`$ because $`q`$ and $`p`$ share $`b`$, $`c`$,
and $`s`$. Since $`u > 0`$, Lemma 6.1 gives $`u = u_0`$ in both cases $`w > 0`$
and $`w = 0`$. Finally Lemma 6.5 gives $`ad > A'\,D' = u_0^2`$.

(If $`\sqrt{ad} > u_0`$ then $`\tau(p) < I_p(X;Y)`$.) By Lemma 6.1,
$`f_p(\sqrt{ad}) > 0`$. By Lemma 6.3 at $`q = p`$, $`AEM - V^3 < 0`$, so (C)
fails and Theorem 4.1 gives $`\tau(p) \ne I_p(X;Y)`$; since always
$`\tau(p) \le I_p(X;Y)`$, the inequality is strict.

(The optimum.) In the mixed case the contacts are the diagonal-swap pair with
off-diagonal cells $`b, c`$, diagonal sum $`s`$, and diagonal product
$`u_0^2`$, so the diagonal entries are the roots of $`y^2 - sy + u_0^2`$,
namely $`(s \pm \rho)/2`$ with $`\rho = \sqrt{s^2 - 4u_0^2}`$. This is real and
positive because $`u_0 < \sqrt{ad} \le s/2`$. Both laws have nonnegative entries.
The weight is fixed by the first cell:
$`a = \lambda\,(s+\rho)/2 + (1-\lambda)\,(s-\rho)/2`$, giving the displayed
$`\lambda`$, and $`0 < \lambda < 1`$ because
$`ad > u_0^2 = ((s+\rho)/2)\,((s-\rho)/2)`$ with $`a + d = s`$ places $`a`$
strictly between the two roots. Swapping the diagonal entries preserves
$`H(q)`$ and exchanges $`H(q_X)`$ with $`H(q_Y)`$, so $`\Phi(q^+) = \Phi(q^-)`$
and (1.1) gives $`\tau(p) = \Psi(p) - \Phi(q^+)`$.

**Theorem 6.7 (uniqueness of the component measure).** For every binary law
$`p`$, all $`\tau`$-optimal finite latents have the same component measure
after merging equal components and discarding zero weights: the point mass at
$`p`$ when $`\tau(p) = I_p(X;Y)`$, and
$`\lambda\,\delta_{q^+} + (1-\lambda)\,\delta_{q^-}`$ otherwise.

*Proof.* Fix $`\ell`$ as in Lemma 2.3. Every optimizer's positive-weight
components lie in $`C(\ell)`$ (Lemma 2.4), which has at most two elements
(Theorem 5.1). If the components of an optimizer are all equal, they equal
$`p`$. If $`C(\ell) = \{q, r\}`$ with $`q \ne r`$, the barycentric equation
$`p = \lambda q + (1-\lambda)\,r`$ determines $`\lambda`$, since
$`q - r \ne 0`$. In the constant-optimal case $`p`$ is itself a contact
($`\ell(p) = (\mathrm{conc}_S \Phi)(p) = \Phi(p)`$); if $`C(\ell) = \{p, r\}`$
with $`r \ne p`$, the barycentric equation forces $`\lambda = 1`$, so $`r`$
carries zero weight, and any optimizer has all components equal to $`p`$. In
the mixed case Theorem 6.6 identifies the pair and the weight, after the $`Y`$
relabeling when $`\Delta < 0`$; the relabeling transports component measures
bijectively, so uniqueness transfers.

*Proof of the theorem at the head of the page.* Case 1: a law with
$`\Delta = 0`$ is the product of its marginals, so $`I_p(X;Y) = 0`$, and
$`0 \le \tau(p) \le T(p) \le I_p(X;Y)`$. Case 2: relabeling preserves $`\tau`$,
and the optimal component measure transports along the relabeling. Case 3:
Theorems 6.6 and 6.7.

## 7. Consequences

**Corollary 7.1 (the disagreement band).** Let $`v = b + c = P(X \ne Y)`$. If
$`1/3 \le v \le 2/3`$, then $`\tau(p) = T(p) = I_p(X;Y)`$. The band is sharp as a
condition on $`v`$ alone: for every $`v`$ outside $`[1/3, 2/3]`$ there is a law
with that disagreement mass and $`\tau(p) < I_p(X;Y)`$.

*Proof.* If $`\Delta > 0`$ and $`\tau(p) < I_p(X;Y)`$, Theorem 6.6 gives
$`\sqrt{ad} > u_0 \ge v`$ (Lemma 6.1), while $`\sqrt{ad} \le (a+d)/2 = (1-v)/2`$;
so $`v < (1-v)/2`$, that is, $`v < 1/3`$. If $`\Delta < 0`$, exchange the $`Y`$
labels: the disagreement mass becomes $`1 - v`$, and the same argument gives
$`1 - v < 1/3`$. If $`\Delta = 0`$, $`\tau = I = 0`$. Contraposition proves the
band, and (1.2) the deterministic equality. For sharpness, take
$`p = ((1-v)/2, v, 0, (1-v)/2)`$ with $`0 < v < 1/3`$: $`\Delta > 0`$, $`w = 0`$,
$`u_0 = v`$, and $`\sqrt{ad} = (1-v)/2 > v`$, so $`\tau(p) < I_p(X;Y)`$ by
Theorem 6.6. At $`v = 0`$, the law $`(1/2, 0, 0, 1/2)`$ has $`\tau = 0 < 1 = I`$.
A column exchange gives examples for $`v > 2/3`$.

The band has normalized volume $`13/27`$ in the simplex of binary laws: in the
coordinates $`(a, b, v)`$, reached from $`(a, b, c)`$ by a map of unit
Jacobian, the section at fixed $`v`$ is the rectangle $`0 \le a \le 1-v`$,
$`0 \le b \le v`$, of area $`v\,(1-v)`$; the whole simplex has volume $`1/6`$,
and $`6 \int_{1/3}^{2/3} v\,(1-v)\,dv = 13/27`$. This is a region on which
the answer is known, not a count of anything else.

**Corollary 7.2 (an optimal latent is blind to agreement).** For every binary
law $`p`$ and every $`\tau`$-optimal finite latent $`L`$, the latent is
independent of the event $`\{X = Y\}`$; reading both observables as
$`\{0,1\}`$-valued, $`I(L; X \,\mathrm{xor}\, Y) = 0`$.

*Proof.* By Theorem 6.7 every positive-weight component is $`p`$, or one of
$`q^+`$, $`q^-`$, which share the off-diagonal cells $`b, c`$ (when
$`\Delta < 0`$, the pair in the original labels is $`q`$ and $`(a, c, b, d)`$,
which shares the diagonal cells $`a, d`$ instead, and the disagreement mass
$`b + c`$ is again common). So every positive-weight label has the same
conditional probability of $`\{X \ne Y\}`$, which is independence.

**Example 7.3 (the uniform-marginal family, again).** For
$`p = ((1+r)/4, (1-r)/4, (1-r)/4, (1+r)/4)`$ with $`0 < r < 1`$, $`\Delta = r/4`$,
$`s = (1+r)/2`$, $`v = (1-r)/2`$, $`w = (1-r)^2/16`$, and $`\sqrt{ad} = (1+r)/4`$.
Direct substitution gives $`f_p((1+r)/4) = (1+r)\,(2r - 1)/16`$. So the constant
latent is optimal exactly when $`r \le 1/2`$, in agreement with Example 4.10, and
for $`r > 1/2`$ the optimum is the diagonal-swap pair with $`u_0`$ the positive
root of $`f_p`$.

**Example 7.4 (a law with a nonconstant optimum).** For
$`p = (3/5, 1/20, 1/20, 3/10)`$, $`\Delta = 71/400 > 0`$, $`s = 9/10`$, $`v = 1/10`$,
$`w = 1/400`$, and $`ad = 9/50`$. Then

```math
f_p(\sqrt{9/50}) = (71/400)\,\sqrt{9/50} - 81/4000 > 0,
```

since $`\sqrt{9/50} > 81/710`$. So $`\sqrt{ad} > u_0`$, the constant latent is not
optimal, and the optimal components swap the diagonal entries around the root
$`u_0`$ of $`u^3 - u^2/10 - u/400 - 9/4000`$.

**Example 7.5 (Example 4.12 through the cubic).** For
$`p = (1/2, 1/5, 1/10, 1/5)`$, $`s = 7/10`$, $`v = 3/10`$, $`w = 1/50`$, and
$`ad = 1/10`$. Then $`f_p(1/\sqrt{10}) = (2/25)/\sqrt{10} - 11/250 < 0`$, since
$`(2/25)/\sqrt{10} < 2/75 < 11/250`$. So $`\sqrt{ad} < u_0`$ and the constant
latent is optimal, as the rational test found.

## 8. Scope and formalization

**What is proved here.** Everything above is a complete prose derivation
from the definitions in [section 1](#1-setting-and-public-inputs), the two
library facts quoted there (the score decomposition and attainment), and
standard finite-dimensional analysis (the supporting-hyperplane theorem, the
Gibbs variational identity, Young's inequality). It is `paper proof` in the
ledger's sense. The ledger rows are `BIN-CONSTANT-TEST` (Theorem 4.1),
`BIN-TWO-COMPONENTS` (Theorem 5.1), `BIN-TAU-EXACT` (Theorems 6.6 and 6.7),
and `BIN-DISAGREEMENT-BAND` (Corollary 7.1).

**What is not proved here.** No inequality between $`T(p)`$ and $`\tau(p)`$
beyond $`\tau(p) \le T(p)`$ is stated. `BIN-C2` remains a conjecture. Nothing
is claimed about which laws maximize $`T(p)/\tau(p)`$, about alphabets larger than
$`2 \times 2`$, or about latents that are not finite mixtures.

**What changes for `BIN-C2`.** The conjecture $`T(p) \le 2\,\tau(p)`$ now
reads, for a full-support law with $`\Delta > 0`$ and $`\sqrt{ad} > u_0`$,

```math
\min_g D_p(g) \le 2\,[ \Psi(p) - \Phi(q^+) ],
```

with the minimum over the fifteen partitions of four cells and $`q^+`$ given by
one cubic root. The constant-optimal region needs nothing: there
$`T(p) = \tau(p)`$. Zero-cell laws reduce, by Theorem 6.6 on a three-cell
support, to the same comparison with $`w = 0`$. The
[open-problems page](open-problems.md#21-the-binary-constant-2-bin-c2) records
this standing.

**Formalization.** The public Lean already contains the ingredients of a
special case: the two-contact chart of
[NormalForm](../StochasticToDeterministicLatents/Binary/NormalForm.lean)
parametrizes a full-support contact pair by chart coordinates, and its
`contact_root_identity` is the cubic (6.1) written in those coordinates, after
the `Y`-label exchange that orients the chart's determinant. The
target declarations for the four rows are listed in the
[Lean contracts](lean-contracts.md#binary-stochastic-optimum). The natural
order is the rational test (a finite algebraic statement once Theorem 3.2
is formalized), then the two-component bound, then the cubic.
