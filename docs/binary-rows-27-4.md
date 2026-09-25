# Binary rows: factor seven

This page proves $`T(p) \le (27\text/4)\,\tau(p)`$ for every law $`p`$ of a binary
$`X`$ and a $`Y`$ with values in any finite nonempty set, and, by exchanging the
coordinates, for every law of a finite $`X`$ and a binary $`Y`$. Since
$`27\text/4 < 7`$, the result is called factor seven. This page completes the
structural half proved on
[Binary rows: the optimal latent and the replica](binary-rows-replica.md). The
derivation here is at `paper proof` in the sense of the
[claim ledger](claims.md#status-vocabulary). The theorem itself, including the
code clause on full support, is `kernel-verified` in this repository; see
[section 7](#7-scope-and-formalization).

The symbols of the companion page's [section 1](binary-rows-replica.md#1-setting)
are used without restatement, and everything is in natural logarithms
([section 1](#1-setting)).

> **Binary-row theorem (factor seven).** For every finite nonempty set $`Y`$ and
> every law $`p`$ on $`\{0,1\} \times Y`$,
>
> ```math
> T(p) \le (27\text/4)\,\tau(p).
> ```
>
> The same holds for every law on $`X \times \{0,1\}`$ with $`X`$ finite and
> nonempty. If a law $`p`$ on $`\{0,1\} \times Y`$ has full support, then the constant code, the row code
> $`g(x,y) = x`$, or a purified code of a $`\tau`$-optimal latent with positive
> weights and distinct components has $`D_p(g) \le (27\text/4)\,\tau(p)`$.

The proof splits on the separation $`k = t\text/s`$ of the two contacts. For
$`1 < k \le 16`$ the constant code or the row code works: a variance identity
and a second look at $`X`$ (the replica) bound $`\tau(p)`$ from below, and six
closed bands of $`k`$ each reduce the comparison to one rational inequality. For
$`k \ge 16`$ a purified code works: given the replica, at most the fraction
$`4\text/25 + 4\text/13`$ of $`H(W \mid X)`$ remains, plus a remainder that
$`I(X;Y \mid W)`$ pays. The one-label case needs only the constant code,
and laws with a zero cell follow from the full-support case by a transfer that
gives the bound on $`T`$ and nothing more.

| Step | Sections |
|---|---|
| Units, standing notation and public inputs | [1](#1-setting) |
| The variance split and the replica variance bound | [2](#2-the-replica-variance-bound) |
| Band constants and four band bounds | [3](#3-four-band-bounds) |
| The scalar balance on six bands, $`1 < k \le 16`$ | [4](#4-the-scalar-balance) |
| Large separation, $`k \ge 16`$ | [5](#5-large-separation) |
| Full support, every law, and binary columns | [6](#6-assembly) |
| Scope and formalization | [7](#7-scope-and-formalization) |
| Finite constants | [Appendix](#appendix-finite-constants) |

## 1. Setting

**Units.** Everything on this page is in natural logarithms, as on the
companion page: information quantities, scores, $`\tau(p)`$ and $`T(p)`$ are
$`\ln 2`$ times their bit values. The band constants $`P`$, $`Q`$, $`r`$ and
$`\Omega`$ of section 3, the cap $`149\text/1000`$ of Lemma 5.2, and the comparison
$`\ln 15 > 27\text/10`$ are specific to nats: each appears only in an inequality
whose other side is a nat quantity of the same kind, such as
$`I(W;X) \le P u`$, and in bits it would carry a factor $`1\text/\ln 2`$. The band
inequality of Lemma 4.1 is homogeneous of degree two in $`(P,\Upsilon,r,\Omega)`$, so it
is unit-free, and every theorem of sections 4 to 6 compares information
quantities only, so it holds verbatim in bits.

**Standing notation.** In sections 2 to 5, $`p`$ is a full-support law on
$`\{0,1\} \times Y`$ in case 2 of the
[structure theorem](binary-rows-replica.md#binary-rows-the-optimal-latent-and-the-replica),
with the latent $`W`$, the weight $`w \in (0,1)`$ and the coordinates
$`k, \ell, e_0, e_1, \kappa`$ of its
[section 6](binary-rows-replica.md#6-contact-coordinates), and
$`J = I(X;Y \mid W)`$, $`U = H(X \mid W)`$, $`V = H(W \mid X)`$. Put

```math
\delta = 1 - e_0 - e_1, \qquad u = w(1-w)\,\delta^2, \qquad v = (1-w)\, e_0(1-e_0) + w\, e_1(1-e_1).
```

Here $`\delta > 0`$ by [Lemma 6.2](binary-rows-replica.md#6-contact-coordinates),
and $`v > 0`$ because $`0 < e_i < 1`$. The two row means are
$`\Pr(X=1 \mid W=0) = e_0`$ and $`\Pr(X=1 \mid W=1) = 1 - e_1`$, whose difference is
$`\delta`$.

**Public inputs.** From the companion page, whose derivations are at
`paper proof` (Lemma 4.1 is also `kernel-verified`; see its
[section 9](binary-rows-replica.md#9-scope-and-formalization)): the structure
theorem, the three codes ([Lemma 2.1](binary-rows-replica.md#2-codes-and-interfaces)), the purification lemma
([Lemma 4.1](binary-rows-replica.md#4-the-purification-lemma)), the parameter
range, posterior variance and replica cells
([Lemmas 6.2 to 6.4](binary-rows-replica.md#6-contact-coordinates)), and Pinsker,
the function $`\omega`$, Ordentlich-Weinberger and the bound on $`J`$
([Lemmas 7.1 to 7.4](binary-rows-replica.md#7-the-bernoulli-layer)). The
integral form of divided differences (Hermite-Genocchi) is cited for the name
only; the case used is derived in Lemma 3.4. The one `kernel-verified` declaration used as an input here is
the transfer theorem of
[SparseLimit](../StochasticToDeterministicLatents/SparseLimit.lean), generic in
the alphabets and the constant, quoted in Theorem 6.2.

## 2. The replica variance bound

**Lemma 2.1 (variance split).** Let $`\vartheta_x = \Pr(W=1 \mid X=x)`$. Then

```math
p_X(1)\,(1 - p_X(1)) = u + v, \qquad
E\left[ \vartheta_X (1-\vartheta_X) \right] = \frac{w(1-w)\,v}{u+v}.
```

*Proof.* The first identity is the law of total variance for $`X`$: the
conditional variances average to $`v`$, and the conditional means $`e_0`$ and
$`1-e_1`$, with weights $`1-w`$ and $`w`$, have variance $`w(1-w)\delta^2 = u`$.
For the second, write $`\bar\xi = p_X(1) = e_0 + w\delta`$. By Bayes' rule,
$`\vartheta_1(1-\vartheta_1) = w(1-w)(1-e_1)e_0\text/\bar\xi^2`$ and
$`\vartheta_0(1-\vartheta_0) = w(1-w)\, e_1(1-e_0)\text/(1-\bar\xi)^2`$, so

```math
\frac{\bar\xi(1-\bar\xi)}{w(1-w)}\, E\left[ \vartheta_X(1-\vartheta_X) \right]
= (1-e_1)\, e_0\, (1-\bar\xi) + e_1 (1-e_0)\, \bar\xi .
```

Substituting $`\bar\xi = e_0 + w\delta`$ and using
$`e_1(1-e_0) - e_0(1-e_1) = e_1 - e_0`$, the right side is
$`e_0(1-e_0) + w\delta\,(e_1 - e_0)`$. Its difference from $`v`$ is $`w`$ times

```math
e_0 - e_0^2 - e_1 + e_1^2 + (1 - e_0 - e_1)(e_1 - e_0)
= (e_0 - e_1)\left( 1 - (e_0 + e_1) \right) - (e_0 - e_1)(1 - e_0 - e_1) = 0,
```

so the right side is $`v`$, and $`\bar\xi(1-\bar\xi) = u + v`$ finishes the proof.

**Lemma 2.2 (the replica variance bound).** For every $`w \in (0,1)`$,

```math
I(W;X' \mid X) \ge 2(1-\kappa)^2\, \frac{uv}{u+v}.
```

*Proof.* By the replica cells of
[Lemma 6.4](binary-rows-replica.md#6-contact-coordinates),

```math
\begin{aligned}
\Pr(X'=1 \mid X=0, W=0) &= (1-\kappa)\, e_0, & \Pr(X'=1 \mid X=0, W=1) &= (1-\kappa)(1-e_1), \\
\Pr(X'=1 \mid X=1, W=0) &= e_0 + \kappa(1-e_0), & \Pr(X'=1 \mid X=1, W=1) &= 1 - e_1 + \kappa e_1,
\end{aligned}
```

so for either value $`x`$ the two conditional means of $`X'`$ differ by
$`(1-\kappa)\delta`$. Given $`X = x`$, $`W`$ is Bernoulli with parameter
$`\vartheta_x`$, and

```math
I(W;X' \mid X=x) = \sum_i \Pr(W=i \mid X=x)\, \mathrm{kl}\left( \Pr(X'=1 \mid x,i) \Vert \Pr(X'=1 \mid x) \right).
```

By Pinsker ([Lemma 7.1](binary-rows-replica.md#7-the-bernoulli-layer)) this is
at least twice the variance of the conditional mean over $`W`$, a two-point
variable with gap $`(1-\kappa)\delta`$, which is
$`2\,\vartheta_x(1-\vartheta_x)(1-\kappa)^2\delta^2`$. Averaging over $`X`$ with Lemma
2.1 gives $`2(1-\kappa)^2\delta^2\,w(1-w)\,v\text/(u+v)`$, which is the claim.

## 3. Four band bounds

A *band* is a closed interval $`[A,B]`$ of the separation $`k`$ with
$`1 \le A < B`$. Write $`\kappa(x) = x\text/(x+1)^2`$, so that $`\kappa = \kappa(k)`$,
and $`\varphi(\xi) = h(\xi)\text/(\xi(1-\xi))`$. The band constants are

```math
\begin{aligned}
\epsilon &= \frac{1}{B^2+B+1}, \qquad \bar q = \frac{A+1}{A^2+A+1}, \qquad
P = \frac{\mathrm{kl}(1-\bar q \Vert \epsilon)}{(1-\bar q-\epsilon)^2}, \qquad Q = \varphi(\epsilon), \\
r &= \kappa(B)\, \omega\left( \min\{\bar q, 1\text/2\} \right), \qquad \Omega = 2\,(1-\kappa(A))^2 .
\end{aligned}
```

When $`\bar q \ge 1\text/2`$, $`r = 2\,\kappa(B)`$.

**Lemma 3.1 (band endpoints).** If $`1 \le A < B`$, then $`\epsilon < 1\text/3`$,
$`\bar q \le 2\text/3`$, and $`\epsilon < \bar q < 1 - \epsilon`$. For every
$`k \in [A,B]`$, $`\epsilon \le 1\text/N`$ and $`(k+1)\text/N \le \bar q`$, so
$`e_0, e_1 \in [\epsilon, \bar q]`$, and $`\kappa(B) \le \kappa(k) \le \kappa(A)`$.

*Proof.* $`B > 1`$ gives $`B^2 + B + 1 > 3`$. The map
$`x \to (x+1)\text/(x^2+x+1)`$ has derivative $`-(x^2+2x)\text/(x^2+x+1)^2 < 0`$, so
it decreases on $`[1,\infty)`$ from $`2\text/3`$; with $`1\text/(x^2+x+1)`$ also
decreasing, $`k \in [A,B]`$ gives $`1\text/N \ge \epsilon`$ and
$`(k+1)\text/N \le \bar q`$. Next,
$`\epsilon < 1\text/(A^2+A+1) < \bar q`$ and $`\bar q \le 2\text/3 < 1 - \epsilon`$.
[Lemma 6.2](binary-rows-replica.md#6-contact-coordinates) places $`e_0, e_1`$
in $`[1\text/N, (k+1)\text/N]`$. Finally $`\kappa'(x) = (1-x)\text/(x+1)^3 \le 0`$ for
$`x \ge 1`$.

For $`\xi, \zeta \in (0,1)`$,
$`\mathrm{kl}(\xi \Vert \zeta) = (-h)(\xi) - (-h)(\zeta) - (-h)'(\zeta)\,(\xi - \zeta)`$,
and Taylor's formula for $`-h`$ about $`\zeta`$, whose
second derivative is $`-h''(x) = 1\text/(x(1-x))`$, gives

```math
\mathrm{kl}(\xi \Vert \zeta) = (\xi - \zeta)^2\, K(\xi,\zeta), \qquad
K(\xi,\zeta) = \int_0^1 (1-\nu)\,(-h'')\left( \zeta + \nu(\xi - \zeta) \right) d\nu . \qquad \text{(3.1)}
```

The Bregman quotient $`K`$ is continuous on $`(0,1)^2`$, equal to
$`1\text/(2\zeta(1-\zeta))`$ on the diagonal, unchanged under
$`(\xi,\zeta) \to (1-\xi,1-\zeta)`$, and $`K(1-\zeta,\zeta) = \omega(\zeta)`$,
because $`\mathrm{kl}(1-\zeta \Vert \zeta) = (1-2\zeta)\ln((1-\zeta)\text/\zeta)`$.

**Lemma 3.2 (pairing).** For $`0 < \epsilon < \xi \le 1-\epsilon`$,
$`\mathrm{kl}(\xi \Vert \epsilon) \ge \mathrm{kl}(\epsilon \Vert \xi)`$, with
equality only at $`\xi = 1-\epsilon`$.

*Proof.* By (3.1), and the substitution $`\nu \to 1-\nu`$ in the formula for
$`\mathrm{kl}(\epsilon \Vert \xi)`$, with $`x_\nu = \epsilon + \nu(\xi - \epsilon)`$,

```math
\mathrm{kl}(\xi \Vert \epsilon) - \mathrm{kl}(\epsilon \Vert \xi)
= (\xi-\epsilon)^2 \int_0^1 (1-2\nu)\, (-h'')(x_\nu)\, d\nu
= (\xi-\epsilon)^2 \int_0^{1\text/2} (1-2\nu) \left( (-h'')(x_\nu) - (-h'')(x_{1-\nu}) \right) d\nu .
```

For $`\nu < 1\text/2`$ put $`x = x_\nu`$ and $`y = x_{1-\nu}`$. Then
$`\epsilon \le x < y \le \xi`$ and $`x + y = \epsilon + \xi \le 1`$, so
$`y(1-y) - x(1-x) = (y-x)(1-x-y) \ge 0`$ and $`(-h'')(x) \ge (-h'')(y)`$. The
integrand is nonnegative, and it vanishes throughout only when
$`x + y = 1`$, that is $`\xi = 1-\epsilon`$.

**Lemma 3.3 (two lower bounds).** For every $`k \in [A,B]`$ and $`w \in (0,1)`$,

```math
J \ge r\, v, \qquad I(W;X' \mid X) \ge \Omega\, \frac{uv}{u+v}.
```

Both are non-strict; on the band $`[1,4]`$, $`r = 2\kappa(4) = 8\text/25`$ exactly.

*Proof.* [Lemma 7.4](binary-rows-replica.md#7-the-bernoulli-layer) gives
$`J \ge \kappa\left( (1-w) e_0(1-e_0)\omega(e_0) + w\, e_1(1-e_1)\omega(e_1) \right)`$.
By Lemma 3.1, $`\kappa \ge \kappa(B)`$ and $`e_i \in [\epsilon,\bar q]`$, and on
that interval the least value of $`\omega`$, which decreases up to $`1\text/2`$ and
increases after it ([Lemma 7.2](binary-rows-replica.md#7-the-bernoulli-layer)),
is $`\omega(\min\{\bar q,1\text/2\})`$. So $`J \ge r v`$. For the second bound,
Lemma 2.2 and $`0 \le \kappa \le \kappa(A) \le 1\text/4`$ give
$`2(1-\kappa)^2 \ge \Omega`$.

**Lemma 3.4 (the normalized Jensen-gap bound).** For every $`k \in [A,B]`$ and
$`w \in (0,1)`$, $`I(W;X) \le P u`$.

*Proof.* Put $`\xi_0 = e_0`$, $`\xi_1 = 1 - e_1`$ and
$`\bar\xi = (1-w)\xi_0 + w\xi_1 = p_X(1)`$, so $`\xi_1 - \xi_0 = \delta`$. With
$`\bar h = -h`$, so that $`\bar h'' = -h''`$,

```math
I(W;X) = h(\bar\xi) - (1-w)\,h(\xi_0) - w\,h(\xi_1) = (1-w)\,\bar h(\xi_0) + w\,\bar h(\xi_1) - \bar h(\bar\xi).
```

*Step 1: the normalized gap is an integral.* Write
$`\bar h[a,b] = (\bar h(b)-\bar h(a))\text/(b-a) = \int_0^1 \bar h'(a + \nu(b-a))\, d\nu`$. Since
$`\bar\xi - \xi_0 = w\delta`$ and $`\xi_1 - \bar\xi = (1-w)\delta`$,

```math
\frac{I(W;X)}{u} = \frac{\bar h[\xi_0,\xi_1] - \bar h[\xi_0,\bar\xi]}{\xi_1 - \bar\xi} .
```

The numerator is
$`\int_0^1 \left( \bar h'((1-\nu)\xi_0 + \nu\xi_1) - \bar h'((1-\nu)\xi_0 + \nu\bar\xi) \right) d\nu`$,
and the fundamental theorem of calculus along the segment from $`\bar\xi`$ to
$`\xi_1`$ in the second point gives

```math
\frac{I(W;X)}{u} = \int_0^1 \int_0^1 \nu\, (-h'')\left( (1-\nu)\,\xi_0 + \nu\,( (1-\nu')\,\bar\xi + \nu'\,\xi_1 ) \right) d\nu'\, d\nu .
```

This is the Hermite-Genocchi formula for a second divided difference, after the
substitution $`(\nu(1-\nu'), \nu\nu')`$ onto the simplex.

*Step 2: convexity in the weight.* The argument of $`-h''`$ is affine in $`w`$
and stays in $`[\xi_0,\xi_1] \subset (0,1)`$, and $`-h''`$ is convex, since
$`(-h'')'' = 2\text/x^3 + 2\text/(1-x)^3 > 0`$. So the right side is a convex,
continuous function of $`w \in [0,1]`$, and at most the larger of its values at
$`w = 0`$ and $`w = 1`$. The normalized gap $`I(W;X)\text/u`$ is convex in $`w`$;
$`I(W;X)`$ itself is concave in $`w`$. At $`w = 0`$ the inner argument is
$`\xi_0 + \nu\nu'\delta`$; substituting $`c = \nu\nu'`$ in the inner integral and
exchanging the order gives $`\int_0^1 (1-c)(-h'')(\xi_0 + c\,\delta)\, dc = K(\xi_1,\xi_0)`$.
At $`w = 1`$ it is $`\int_0^1 \nu\,(-h'')(\xi_0 + \nu\delta)\, d\nu = K(\xi_0,\xi_1)`$.
Hence

```math
I(W;X) \le u \max\{ K(\xi_1,\xi_0),\ K(\xi_0,\xi_1) \}.
```

*Step 3: four corners.* By (3.1), $`K`$ is an average of the convex function
$`-h''`$ at points linear in $`(\xi,\zeta)`$, so $`K`$ is jointly convex on
$`(0,1)^2`$. By Lemma 3.1, $`(\xi_0,\xi_1)`$ lies in the rectangle
$`[\epsilon,\bar q] \times [1-\bar q, 1-\epsilon]`$, and both
$`K(\xi_1,\xi_0)`$ and $`K(\xi_0,\xi_1)`$ are convex there, so each is at most
its largest value at the four corners. No order between $`\bar q`$ and
$`1-\bar q`$ is assumed; on $`[1,4]`$ the rectangle crosses the diagonal. Using
$`K(\xi,\zeta) = K(1-\xi,1-\zeta)`$, the eight corner values are

| Corner $`(\xi_0,\xi_1)`$ | $`K(\xi_1,\xi_0)`$ | $`K(\xi_0,\xi_1)`$ |
|---|---|---|
| $`(\epsilon, 1-\bar q)`$ | $`P`$ | $`K(\epsilon, 1-\bar q)`$ |
| $`(\epsilon, 1-\epsilon)`$ | $`\omega(\epsilon)`$ | $`\omega(\epsilon)`$ |
| $`(\bar q, 1-\bar q)`$ | $`\omega(\bar q)`$ | $`\omega(\bar q)`$ |
| $`(\bar q, 1-\epsilon)`$ | $`K(\epsilon, 1-\bar q)`$ | $`P`$ |

*Step 4: three comparisons.* Each value is at most $`P`$, for three separate
reasons. By Lemma 3.1, $`\epsilon < 1-\bar q \le 1-\epsilon`$.

1. $`K(\epsilon,1-\bar q) \le P`$: the two share the denominator
   $`(1-\bar q-\epsilon)^2`$, and Lemma 3.2 at $`\xi = 1-\bar q`$ compares the
   numerators.
2. $`\omega(\epsilon) \le P`$: for $`\epsilon < \xi \le 1-\epsilon`$,
   using $`\partial_\xi \mathrm{kl}(\xi \Vert \epsilon) = \bar h'(\xi) - \bar h'(\epsilon)`$
   and $`\mathrm{kl}(\xi \Vert \epsilon) + \mathrm{kl}(\epsilon \Vert \xi) = (\bar h'(\xi) - \bar h'(\epsilon))(\xi - \epsilon)`$,

   ```math
   \partial_\xi K(\xi,\epsilon) = \frac{\mathrm{kl}(\epsilon \Vert \xi) - \mathrm{kl}(\xi \Vert \epsilon)}{(\xi - \epsilon)^3} \le 0
   ```

   by Lemma 3.2. So $`K(\cdot,\epsilon)`$ does not increase on
   $`(\epsilon, 1-\epsilon]`$, and
   $`\omega(\epsilon) = K(1-\epsilon,\epsilon) \le K(1-\bar q,\epsilon) = P`$.
3. $`\omega(\bar q) \le \omega(\epsilon)`$: $`\omega`$ is symmetric about
   $`1\text/2`$ and decreasing on $`(0,1\text/2]`$, and both $`\bar q`$ and
   $`1-\bar q`$ lie in $`(\epsilon, 1-\epsilon)`$.

**Lemma 3.5 (the entropy-to-variance bound).** The function $`\varphi`$ is
symmetric about $`1\text/2`$ and decreasing on $`(0,1\text/2]`$. Hence, for every
$`k \in [A,B]`$ and $`w \in (0,1)`$, $`U \le Q v`$.

*Proof.* The derivative of $`\varphi`$ has the sign of
$`(1-\xi)^2 \ln(1-\xi) - \xi^2 \ln \xi`$. With $`y = (1-\xi)\text/\xi \ge 1`$
for $`\xi \le 1\text/2`$, this sign is that of
$`\ln(1+y) - y^2 \ln(1 + 1\text/y)`$. The function
$`\varrho(y) = y^2 \ln(1+1\text/y) - \ln(1+y)`$ vanishes at $`y = 1`$, and

```math
\varrho'(y) = 2y \ln\left( 1 + \frac{1}{y} \right) - 1 \ge \frac{2y}{y+1} - 1 = \frac{y - 1}{y + 1} \ge 0,
```

using $`\ln(1 + 1\text/y) \ge 1\text/(y+1)`$. So $`\varphi' \le 0`$ on $`(0,1\text/2]`$;
symmetry is clear. Then
$`U = (1-w)\,h(e_0) + w\,h(e_1) = (1-w)\,e_0(1-e_0)\varphi(e_0) + w\,e_1(1-e_1)\varphi(e_1)`$,
and on $`[\epsilon,\bar q] \subset [\epsilon, 1-\epsilon]`$ the largest value of
$`\varphi`$ is $`\varphi(\epsilon) = Q`$. On the band $`[1,4]`$, where
$`\bar q = 2\text/3 > 1\text/2`$, this uses the symmetry.

## 4. The scalar balance

**Lemma 4.1 (scalar balance).** Let $`P, \Upsilon, r, \Omega > 0`$ satisfy

```math
\Upsilon\,(P+\Upsilon) \le \frac{23}{4} \left( r\,(P+\Upsilon) + \Omega \Upsilon \right). \qquad \text{(4.1)}
```

Then $`\min\{P z, \Upsilon\} \le (23\text/4)\left( r + \Omega z\text/(1+z) \right)`$ for every
$`z \ge 0`$.

*Proof.* Put $`z_* = \Upsilon\text/P`$, so $`z_*\text/(1+z_*) = \Upsilon\text/(P+\Upsilon)`$. For
$`z \ge z_*`$ the minimum is at most $`\Upsilon`$, and the right side increases in
$`z`$; at $`z_*`$ the claim $`\Upsilon \le (23\text/4)(r + \Omega \Upsilon\text/(P+\Upsilon))`$ is
(4.1) divided by $`P+\Upsilon`$. For $`0 \le z \le z_*`$ the minimum is at most
$`Pz`$, and $`Pz \le (23\text/4)(r + \Omega z\text/(1+z))`$ is equivalent to

```math
\Theta(z) = P z(1+z) - \frac{23}{4}\left( r\,(1+z) + \Omega z \right) \le 0 .
```

$`\Theta`$ is a convex quadratic, so on $`[0,z_*]`$ it is at most
$`\max\{\Theta(0),\Theta(z_*)\}`$. Here $`\Theta(0) = -(23\text/4)\,r < 0`$, and
$`P\,\Theta(z_*) = \Upsilon(P+\Upsilon) - (23\text/4)(r(P+\Upsilon) + \Omega \Upsilon) \le 0`$ by (4.1).

**Theorem 4.2 (moderate separation).** If $`1 < k \le 16`$, then

```math
\min\{ I_p(X;Y),\ H(X \mid Y) \} \le (27\text/4)\,\tau(p).
```

*Proof.* The six closed bands $`[1,4]`$, $`[4,8]`$, $`[8,12]`$, $`[12,14]`$,
$`[14,76\text/5]`$ and $`[76\text/5,16]`$ have union $`[1,16]`$; take one containing
$`k`$. The appendix proves the directed bounds $`\hat P \ge P`$,
$`\hat Q \ge Q`$ and $`\hat r \le r`$ of Table 2, so Lemmas 3.3 to 3.5 give
$`I(W;X) \le \hat P u`$, $`U \le \hat Q v`$ and $`J \ge \hat r v`$; replacing a
constant by a weaker one only weakens each bound. Put
$`\hat\Upsilon = \hat Q - 2\hat r > 0`$ and $`z = u\text/v \ge 0`$. The structure
theorem and $`\mathrm{score}_p(W) = \tau(p)`$ give

```math
\begin{aligned}
\min\{ I_p(X;Y),\ H(X \mid Y) \} &\le \tau(p) + \min\{ I(W;X),\ U - 2J \} \le \tau(p) + v \min\{ \hat P z,\ \hat\Upsilon \}, \\
\tau(p) &\ge J + I(W;X' \mid X) \ge v \left( \hat r + \Omega z\text/(1+z) \right),
\end{aligned}
```

using Lemma 3.3 for the second line. Table 2 checks (4.1) for
$`(\hat P, \hat\Upsilon, \hat r, \Omega)`$ in each band, so Lemma 4.1 and $`v > 0`$ give
$`\min\{ I_p(X;Y), H(X \mid Y) \} \le \tau(p) + (23\text/4)\,\tau(p)`$.

**Table 1. Exact band data.**

| Band $`[A,B]`$ | $`\epsilon`$ | $`\bar q`$ | $`\Omega`$ |
|---|---|---|---|
| $`[1,4]`$ | $`1\text/21`$ | $`2\text/3`$ | $`9\text/8`$ |
| $`[4,8]`$ | $`1\text/73`$ | $`5\text/21`$ | $`882\text/625`$ |
| $`[8,12]`$ | $`1\text/157`$ | $`9\text/73`$ | $`10658\text/6561`$ |
| $`[12,14]`$ | $`1\text/211`$ | $`13\text/157`$ | $`49298\text/28561`$ |
| $`[14,76\text/5]`$ | $`25\text/6181`$ | $`15\text/211`$ | $`89042\text/50625`$ |
| $`[76\text/5,16]`$ | $`1\text/273`$ | $`405\text/6181`$ | $`76409522\text/43046721`$ |

**Table 2. Directed constants and the band inequality (4.1).** $`\hat P`$ and
$`\hat Q`$ are upper bounds, $`\hat r`$ a lower bound, all exact terminating
decimals; the last column gives the left side of (4.1) rounded up and the right
side rounded down, both evaluated at $`(\hat P, \hat\Upsilon, \hat r, \Omega)`$.

| Band | $`\hat P`$ | $`\hat Q`$ | $`\hat r`$ | $`\hat\Upsilon`$ | (4.1) |
|---|---|---|---|---|---|
| $`[1,4]`$ | 5.03296 | 4.22135 | 0.32000 | 3.58135 | 30.8509 ≤ 39.0171 |
| $`[4,8]`$ | 4.86473 | 5.35697 | 0.21931 | 4.91835 | 48.1167 ≤ 52.2462 |
| $`[8,12]`$ | 5.36008 | 6.09186 | 0.18487 | 5.72212 | 63.4137 ≤ 65.2282 |
| $`[12,14]`$ | 5.55328 | 6.37973 | 0.17933 | 6.02107 | 69.6900 ≤ 71.6930 |
| $`[14,76\text/5]`$ | 5.68460 | 6.53477 | 0.17352 | 6.18773 | 73.4628 ≤ 74.4245 |
| $`[76\text/5,16]`$ | 5.77122 | 6.63194 | 0.16932 | 6.29330 | 75.9257 ≤ 75.9782 |

On $`[1,4]`$ the entry $`\hat r = 0.32000`$ equals $`r = 8\text/25`$. In
coefficient form, each row gives the bound of Theorem 4.2 with $`27\text/4`$
replaced by $`1 + \hat\Upsilon(\hat P+\hat\Upsilon)\text/(\hat r(\hat P+\hat\Upsilon) + \Omega\hat\Upsilon)`$,
a rational; the smallest of the six differences from $`27\text/4`$ is at
$`[76\text/5,16]`$ and equals exactly
$`435300959146709\text/109385069122930372`$.

## 5. Large separation

For $`\xi, \zeta > 0`$ let

```math
F(\xi,\zeta) = \xi \ln\left( 1 + \frac{\zeta}{\xi} \right) + \zeta \ln\left( 1 + \frac{\xi}{\zeta} \right),
\qquad f(\zeta) = F(1,\zeta),
```

the function $`F`$ of the [factor-two page](binary-factor-two.md#1-setting),
extended by $`F(\xi,0) = 0`$. It is symmetric, homogeneous of degree one, and
increasing in each argument, since $`\partial_\zeta F(\xi,\zeta) = \ln(1+\xi\text/\zeta) > 0`$.
Also $`f'(\zeta) = \ln(1+1\text/\zeta)`$ and $`f''(\zeta) = -1\text/(\zeta(1+\zeta))`$.
For a finite variable $`Z`$ observed with $`W`$,
$`H(W \mid Z) = \sum_z F(\Pr(W=0,Z=z), \Pr(W=1,Z=z))`$, since $`F(n,n') = (n+n')\,h(n'\text/(n+n'))`$.
With the cell masses $`n_{ix} = \Pr(W=i, X=x)`$,

```math
n_{00} = (1-w)(1-e_0), \quad n_{01} = (1-w)\,e_0, \quad n_{10} = w\,e_1, \quad n_{11} = w(1-e_1),
\qquad V = F(n_{00},n_{10}) + F(n_{01},n_{11}).
```

**Lemma 5.1 (separation).** Let $`\lambda_0, \lambda_1 \ge 15`$ with
$`\lambda_0\lambda_1 \ge 4096`$. For all $`\xi, \zeta > 0`$,

```math
F(\lambda_0 \xi, \zeta) + F(\xi, \lambda_1 \zeta) \ge (13\text/2)\, F(\xi,\zeta).
```

*Proof.* Since $`F`$ is symmetric, the claim is unchanged under
$`(\xi,\zeta,\lambda_0,\lambda_1) \to (\zeta,\xi,\lambda_1,\lambda_0)`$, and so are the
hypotheses; so let $`\zeta \ge \xi`$, and by homogeneity $`\xi = 1`$ and
$`\zeta \ge 1`$. The claim is $`F(\lambda_0,\zeta) + F(1,\lambda_1\zeta) \ge (13\text/2) f(\zeta)`$, in
three ranges of $`\zeta`$, $`[1,4]`$, $`[4,8]`$ and $`[8,\infty)`$, the second resting on the first.

*The first two ranges.* For $`1 \le \zeta \le 8`$, by $`\ln(1+y) \ge y\text/(1+y)`$,
$`F(\lambda_0,\zeta) - \zeta \ln(\lambda_0\text/\zeta) = (\lambda_0+\zeta)\ln(1 + \zeta\text/\lambda_0) \ge \zeta`$,
and in the same way $`F(1,\lambda_1\zeta) = F(\lambda_1\zeta,1) \ge \ln(\lambda_1\zeta) + 1`$. Since
$`\zeta \ge 1`$, $`\zeta\ln\lambda_0 + \ln\lambda_1 = (\zeta-1)\ln\lambda_0 + \ln(\lambda_0\lambda_1) \ge (\zeta-1)\ln 15 + 12\ln 2`$.
So the left side minus $`(13\text/2)f(\zeta)`$ is at least

```math
G(\zeta) = 12 \ln 2 + (\zeta - 1)\ln 15 - (\zeta - 1)\ln\zeta + 1 + \zeta - \frac{13}{2} f(\zeta),
```

with

```math
G'(\zeta) = \ln 15 + \frac{11}{2}\ln\zeta + \frac{1}{\zeta} - \frac{13}{2}\ln(1+\zeta), \qquad
G''(\zeta) = \frac{-\zeta^2 + (9\text/2)\,\zeta - 1}{\zeta^2 (1+\zeta)} .
```

*The first range.* The numerator of $`G''`$ is a concave quadratic, equal to $`5\text/2`$ at
$`\zeta = 1`$ and $`1`$ at $`\zeta = 4`$, so $`G`$ is convex on $`[1,4]`$. Since
$`G'(2) < 0`$ (appendix), the tangent at $`2`$ gives, for $`1 \le \zeta \le 4`$,
$`G(\zeta) \ge G(2) + G'(2)(\zeta - 2) \ge G(2) + 2G'(2) > 0`$.

*The second range.* On $`[4,8]`$ the
numerator of $`G''`$ changes sign once, from positive to negative, so $`G'`$
increases and then decreases; as $`G'(4) > 0`$, $`G'`$ is positive and then
possibly negative, and $`G`$ is at least $`\min\{G(4),G(8)\}`$. Here
$`G(4) > 0`$ by the range $`[1,4]`$ and $`G(8) > 0`$ (appendix).

*The third range.* For $`\zeta \ge 8`$, by monotonicity in $`\lambda_0`$ and
$`\lambda_1`$, the left side minus $`(13\text/2)f(\zeta)`$ is at least

```math
G_\infty(\zeta) = 15\, f(\zeta\text/15) + f(15\zeta) - \frac{13}{2} f(\zeta).
```

From the formula for $`f''`$,

```math
G_\infty''(\zeta) = \left( \Xi(\zeta) - \frac{13}{2} \right) f''(\zeta), \qquad
\Xi(\zeta) = 15\,(1+\zeta) \left( \frac{1}{15+\zeta} + \frac{1}{1+15\zeta} \right).
```

$`\Xi'(\zeta) = 210\left( (15+\zeta)^{-2} - (1+15\zeta)^{-2} \right) \ge 0`$ for
$`\zeta \ge 1`$, and $`\Xi(8) = 19440\text/2783 > 13\text/2`$, so with $`f'' < 0`$,
$`G_\infty`$ is concave on $`[8,\infty)`$. Its derivative

```math
G_\infty'(\zeta) = \ln\left( 1 + \frac{15}{\zeta} \right) + 15 \ln\left( 1 + \frac{1}{15\zeta} \right) - \frac{13}{2} \ln\left( 1 + \frac{1}{\zeta} \right)
```

tends to $`0`$ as $`\zeta \to \infty`$ and does not increase, so it is
nonnegative. Hence $`G_\infty(\zeta) \ge G_\infty(8) > 0`$ (appendix).

**Lemma 5.2 (scaling).** Let $`\eta_0 = 33\text/289`$ and, for $`\eta > 0`$,

```math
\Gamma(\eta) = \sup_{\zeta \ge 0} \left( F(\eta,\zeta) - \frac{4}{25} F(1,\zeta) \right).
```

For $`0 < \eta \le \eta_0`$, $`\Gamma(\eta) \le (\eta\text/\eta_0)(149\text/1000)`$ nats, and for all
$`\xi, \zeta > 0`$

```math
F(\eta\xi, \zeta) \le \frac{4}{25}\, F(\xi,\zeta) + \Gamma(\eta)\, \xi \le \frac{4}{25}\, F(\xi,\zeta) + \frac{\eta}{\eta_0} \cdot \frac{149}{1000}\, \xi .
```

*Proof.* Let $`\varrho_0(\zeta) = F(\eta_0,\zeta) - (4\text/25)F(1,\zeta)`$. Then
$`\varrho_0'(\zeta) = \ln(1+\eta_0 y) - (4\text/25)\ln(1+y)`$ with $`y = 1\text/\zeta`$. The
function $`\psi(y) = (1+y)^{4\text/25} - 1 - \eta_0 y`$ is strictly concave, with
$`\psi(0) = 0`$, $`\psi'(0) = 4\text/25 - 33\text/289 = 331\text/7225 > 0`$, and
$`\psi \to -\infty`$, so it has exactly one positive zero, positive before it and
negative after. As $`\varrho_0' > 0`$ exactly where $`\psi(y) < 0`$, $`\varrho_0`$ increases and
then decreases, with its maximum at the one critical point $`\zeta_*`$. The
exact comparisons

```math
\left( \frac{29021}{25721} \right)^{25} > \left( \frac{189}{89} \right)^4, \qquad
\left( \frac{977}{867} \right)^{25} < \left( \frac{19}{9} \right)^4
```

say $`\varrho_0'(89\text/100) > 0 > \varrho_0'(9\text/10)`$, since
$`1 + \eta_0\text/(89\text/100) = 29021\text/25721`$ and
$`1 + \eta_0\text/(9\text/10) = 977\text/867`$. So $`89\text/100 < \zeta_* < 9\text/10`$, and by
monotonicity of $`F`$ in its second argument

```math
\Gamma(\eta_0) = \varrho_0(\zeta_*) \le F(\eta_0, 9\text/10) - \frac{4}{25}\, F(1, 89\text/100) < \frac{149}{1000}
```

(appendix). For $`\eta = c\,\eta_0`$ with $`0 < c \le 1`$ and $`\zeta = c\,\zeta'`$,
homogeneity and $`F(1\text/c,\zeta') \ge F(1,\zeta')`$ give
$`F(\eta,\zeta) - (4\text/25)F(1,\zeta) = c\left( F(\eta_0,\zeta') - (4\text/25)F(1\text/c,\zeta') \right) \le c\,\varrho_0(\zeta')`$,
so $`\Gamma(\eta) \le c\,\Gamma(\eta_0)`$. The last display follows from
$`F(\eta\xi,\zeta) = \xi F(\eta,\zeta\text/\xi)`$.

**Theorem 5.3 (large separation).** If $`k \ge 16`$, then

```math
\tau(p) \ge \frac{173}{325}\, V, \qquad
\tau(p) + 3\,H(W \mid X,Y) \le \frac{1148}{173}\, \tau(p) < \frac{27}{4}\,\tau(p) .
```

*Proof.* Put $`\eta_k = \kappa + (1-\kappa)(k+1)\text/N = (2k+1)\text/(k+1)^2`$. It
decreases in $`k`$ and $`\eta_{16} = 33\text/289 = \eta_0`$, so $`\eta_k \le \eta_0`$;
and $`\eta_k\text/\kappa = 2 + 1\text/k \le 33\text/16`$.

*The eight masses.* By [Lemma 6.4](binary-rows-replica.md#6-contact-coordinates),
the masses of $`W = 0`$ and $`W = 1`$ on the cell $`(x,x')`$ of $`(X,X')`$ are
bounded as follows. On $`(0,0)`$: $`(1-w)\left( (1-e_0)^2 + \kappa e_0(1-e_0) \right) \le n_{00}`$
and $`w\, e_1\left( e_1 + \kappa(1-e_1) \right) \le \eta_k\, n_{10}`$. On $`(1,1)`$:
$`(1-w)\, e_0\left( e_0 + \kappa(1-e_0) \right) \le \eta_k\, n_{01}`$ and
$`w\left( (1-e_1)^2 + \kappa e_1(1-e_1) \right) \le n_{11}`$. On each of $`(0,1)`$ and
$`(1,0)`$: $`(1-\kappa)(1-w)\, e_0(1-e_0) \le n_{01}`$ and
$`(1-\kappa)\, w\, e_1(1-e_1) \le n_{10}`$. Six of these are trivial. The two with
$`\eta_k`$ read $`e_i + \kappa(1-e_i) \le \kappa + (1-\kappa)(k+1)\text/N`$, that is
$`e_i \le (k+1)\text/N`$, which is Lemma 6.2. Since $`F`$ increases in each
argument,

```math
V_2 = H(W \mid X,X') \le F(n_{00}, \eta_k n_{10}) + F(\eta_k n_{01}, n_{11}) + 2\,F(n_{01}, n_{10}).
```

*Scaling.* By symmetry of $`F`$, $`F(n_{00},\eta_k n_{10}) = F(\eta_k n_{10}, n_{00})`$.
Lemma 5.2 with $`\eta = \eta_k`$, applied to the first two terms, and
$`\bar e = n_{01} + n_{10} = (1-w)e_0 + w e_1 > 0`$, give
$`F(n_{00},\eta_k n_{10}) + F(\eta_k n_{01}, n_{11}) \le (4\text/25)\,V + \Gamma(\eta_k)\,\bar e`$.

*Separation.* Put $`\lambda_0 = n_{00}\text/n_{01} = 1\text/\ell`$ and
$`\lambda_1 = n_{11}\text/n_{10} = k^3\ell`$. By Lemma 6.2 both exceed
$`k^2\text/(k+1) \ge 256\text/17 > 15`$, and $`\lambda_0\lambda_1 = k^3 \ge 4096`$. Lemma
5.1 at $`(\xi,\zeta) = (n_{01}, n_{10})`$ gives $`V \ge (13\text/2)F(n_{01},n_{10})`$, so
$`2F(n_{01},n_{10}) \le (4\text/13)\,V`$.

*Payment by the component information.* Since $`e_i < (k+1)\text/N < 1\text/2`$,
$`(1-e_i)\text/(1-2e_i) \ge 1`$, and $`(1-e_0)\text/e_0 = \lambda_0`$ and
$`(1-e_1)\text/e_1 = \lambda_1`$ exceed $`15`$,
[Lemma 7.4](binary-rows-replica.md#7-the-bernoulli-layer) gives

```math
J \ge \kappa\left( (1-w)\, e_0 \ln\lambda_0 + w\, e_1 \ln\lambda_1 \right) \ge \kappa\,\bar e \ln 15 > \frac{27}{10}\, \kappa\,\bar e ,
```

while Lemma 5.2 and $`\eta_k \le (33\text/16)\kappa`$ give

```math
\Gamma(\eta_k)\,\bar e \le \frac{149}{1000} \cdot \frac{289}{33} \cdot \frac{33}{16}\, \kappa\,\bar e = \frac{43061}{16000}\, \kappa\,\bar e < \frac{27}{10}\, \kappa\,\bar e < J .
```

*Conclusion.* $`I(W;X' \mid X) = H(W \mid X) - H(W \mid X,X') = V - V_2`$, so by the
replica bound of the structure theorem

```math
\tau(p) \ge J + V - V_2 \ge J + \left( 1 - \frac{4}{25} - \frac{4}{13} \right) V - \Gamma(\eta_k)\,\bar e \ge \frac{173}{325}\, V .
```

The structure theorem also gives $`\tau(p) + 3H(W \mid X,Y) \le \tau(p) + 3V`$,
and $`3V \le (975\text/173)\,\tau(p)`$, so the sum is at most
$`(1148\text/173)\,\tau(p)`$. Finally $`27\text/4 - 1148\text/173 = 79\text/692 > 0`$ and
$`\tau(p) \ge (173\text/325)\,V > 0`$, since all four masses $`n_{ix}`$ are positive. The argument holds for every $`w \in (0,1)`$.

## 6. Assembly

**Theorem 6.1 (full support).** Let $`p`$ be a full-support law on
$`\{0,1\} \times Y`$. Then the constant code, the row code, or a purified code
of a $`\tau`$-optimal latent with positive weights and distinct components has
$`D_p(g) \le (27\text/4)\,\tau(p)`$, and so
$`T(p) \le (27\text/4)\,\tau(p)`$.

*Proof.* In case 1 of the structure theorem the constant code has
$`D_p = \tau(p) \le (27\text/4)\,\tau(p)`$, since $`\tau(p) \ge 0`$. In case 2,
$`k > 1`$. If $`k \le 16`$, Theorem 4.2 bounds the score of the constant code,
$`I_p(X;Y)`$, or of the row code, $`H(X \mid Y)`$. If $`k \ge 16`$, a purified code
of $`W`$ has $`D_p \le \tau(p) + 3H(W \mid X,Y)`$
([Lemma 4.1](binary-rows-replica.md#4-the-purification-lemma)), and Theorem 5.3
bounds this. The two ranges meet at $`k = 16`$, where both apply. In each case
$`T(p) \le D_p(g)`$ ([Lemma 2.1](binary-rows-replica.md#2-codes-and-interfaces)).

**Theorem 6.2 (every law).** $`T(p) \le (27\text/4)\,\tau(p)`$ for every law on
$`\{0,1\} \times Y`$.

*Proof.* Theorem 6.1 holds verbatim in bits, and it supplies the hypothesis of
the `kernel-verified` transfer theorem

```lean
theorem T_le_mul_tau_of_forall_fullSupport
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    {C : ℝ} (hC : 0 ≤ C)
    (hfull : ∀ p : α × β → ℝ, IsPMF p → (∀ z, 0 < p z) → T p ≤ C * tau p)
    (p : α × β → ℝ) (hp : IsPMF p) :
    T p ≤ C * tau p
```

with the rows as `α`, $`Y`$ as `β`, and $`C = 27\text/4`$.

**Theorem 6.3 (binary columns).** $`T(p) \le (27\text/4)\,\tau(p)`$ for every law on
$`X \times \{0,1\}`$ with $`X`$ finite and nonempty.

*Proof.* Exchanging the two coordinates is a bijection of the cells that maps
rows to columns and columns to rows. Latents and codes transport along it, and
$`\mathrm{score}_p(L)`$ and $`D_p(g)`$ are unchanged, because
$`I(X;Y \mid L)`$ is symmetric and the other two terms of each score exchange. So
$`\tau`$ and $`T`$ are unchanged, and Theorem 6.2 applies to the exchanged law.

**What the transfer gives, and what it does not.** For a law with a zero cell,
Theorem 6.2 bounds $`T(p)`$ and nothing else. It supplies no optimal latent of
the sparse law with the structure of the companion page, and no named code: the
three-code clause of Theorem 6.1 is not claimed there. `exists_optimalCode`
attaches some code to $`T(p)`$, but no rule selects it.

## 7. Scope and formalization

**What is proved here.** The binary-row theorem, by complete prose derivations
from the companion page, the transfer theorem, one-variable calculus, and
finitely many rational comparisons after the logarithm enclosures of the
appendix. Apart from the six bands of Theorem 4.2, which share one argument and
differ only in constants, no step splits into more than three cases; the most are the three
ranges of one variable in the separation lemma.

**What is not proved here.** Nothing is claimed about the sharpness of
$`27\text/4`$, about laws that maximize $`T(p)\text/\tau(p)`$, or about equality
cases. The coefficient that the six bands give is a bound from this relaxation,
not a maximum over laws. Nothing is claimed for $`\lvert X \rvert > 2`$ with
$`\lvert Y \rvert > 2`$, and the arbitrary-alphabet constant $`C_*`$ keeps its
standing on the [open problems](open-problems.md) page. The three-code clause
says which codes stay within the bound on full support; it does not say which
code attains $`T(p)`$.

**Formalization.** The derivation on this page is at `paper proof`. The
binary-row theorem is `kernel-verified` in this repository: the bound as
`BinaryRow.T_le_twentySevenQuarters_mul_tau` for laws on `Bit × Y`, where `Bit`
is `Fin 2`, and `BinaryRow.T_le_twentySevenQuarters_mul_tau_col` for laws on
`Y × Bit`, and the code clause on full support as
`BinaryRow.exists_rowWitnessCode`. The Lean proves these statements; the
[admission record](../verification/admissions.md#binaryrow) describes its
route. The [claim ledger](claims.md#ledger) records the standing of the
binary-row theorem, and the [Lean contracts](lean-contracts.md) list its
modules.

## Appendix: finite constants

Every finite fact above is a rational comparison after enclosing logarithms of
primes. For $`0 < \zeta < 1`$ and $`n \ge 1`$
([Lemma 1.3 of the factor-two page](binary-factor-two.md#1-setting)),

```math
2 \sum_{j=0}^{n-1} \frac{\zeta^{2j+1}}{2j+1} \le \ln \frac{1+\zeta}{1-\zeta}
\le 2 \sum_{j=0}^{n-1} \frac{\zeta^{2j+1}}{2j+1} + \frac{2\,\zeta^{2n+1}}{(2n+1)(1-\zeta^2)} .
```

For a prime $`\mathfrak p`$ write $`\mathfrak p = 2^m \mathfrak u`$ with $`1 < \mathfrak u \le 2`$, take
$`\zeta = (\mathfrak u-1)\text/(\mathfrak u+1) \le 1\text/3`$ and $`n = 12`$, and add $`m`$ times the
interval for $`\ln 2`$. The resulting rational intervals, rounded outward to
twelve decimals, are:

| Prime | $`\mathfrak u`$ | Interval for the logarithm |
|---|---|---|
| 2 | $`2`$ | [0.693147180559, 0.693147180560] |
| 3 | $`3\text/2`$ | [1.098612288668, 1.098612288669] |
| 5 | $`5\text/4`$ | [1.609437912433, 1.609437912435] |
| 7 | $`7\text/4`$ | [1.945910149055, 1.945910149056] |
| 11 | $`11\text/8`$ | [2.397895272798, 2.397895272799] |
| 13 | $`13\text/8`$ | [2.564949357461, 2.564949357462] |
| 17 | $`17\text/16`$ | [2.833213344055, 2.833213344057] |
| 19 | $`19\text/16`$ | [2.944438979166, 2.944438979167] |
| 23 | $`23\text/16`$ | [3.135494215928, 3.135494215930] |
| 73 | $`73\text/64`$ | [4.290459441147, 4.290459441149] |
| 89 | $`89\text/64`$ | [4.488636369731, 4.488636369733] |
| 157 | $`157\text/128`$ | [5.056245805347, 5.056245805349] |
| 211 | $`211\text/128`$ | [5.351858133475, 5.351858133477] |
| 883 | $`883\text/512`$ | [6.783325200603, 6.783325200604] |
| 977 | $`977\text/512`$ | [6.884486652041, 6.884486652043] |

Each quantity below is a rational constant plus a rational combination of these
logarithms. Replacing each logarithm by the endpoint that moves the quantity in
the required direction gives a rational bound.

**Band constants (Table 2).** $`P`$, $`Q`$ and $`r`$ are rational combinations of
$`\ln\epsilon`$, $`\ln(1-\epsilon)`$, $`\ln\bar q`$ and $`\ln(1-\bar q)`$. Factored,
the numbers of Table 1 involve the primes 2, 3, 5, 7, 13, 17, 19, 73, 157, 211 and
883; for example $`1 - 25\text/6181 = 2^2\, 3^4\, 19\text/(7 \cdot 883)`$. The
directed bounds clear each entry of Table 2 by more than $`10^{-6}`$, except
$`\hat r = 8\text/25`$ on $`[1,4]`$, which is exact. The six band inequalities
(4.1) are then comparisons of rationals.

**The signs used in Lemma 5.1**, in the primes 2, 3, 5, 11 and 23:

```math
\begin{aligned}
G'(2) &= \frac{11}{2}\ln 2 + \ln 5 - \frac{11}{2}\ln 3 + \frac{1}{2} \in [-0.120620183, -0.120620182], \\
G(2) + 2G'(2) &= 35 \ln 2 + 3 \ln 5 - \frac{59}{2}\ln 3 + 4 \in [0.679402541, 0.679402542], \\
G'(4) &= 11 \ln 2 + \ln 3 - \frac{11}{2}\ln 5 + \frac{1}{4} \in [0.121322756, 0.121322757], \\
G(8) &= 147 \ln 2 - 110 \ln 3 + 7 \ln 5 + 9 \in [1.311349175, 1.311349176], \\
G_\infty(8) &= 23 \ln 23 + 242 \ln 11 - 228 \ln 2 - 252 \ln 3 - 135 \ln 5 \in [0.245050892, 0.245050894].
\end{aligned}
```

**The cap of Lemma 5.2**, in the primes 2, 3, 5, 7, 11, 17, 89 and 977, since
$`\eta_0 + 9\text/10 = 2931\text/2890 = 3 \cdot 977\text/(2 \cdot 5 \cdot 17^2)`$:

```math
F(\eta_0, 9\text/10) - \frac{4}{25}\, F(1, 89\text/100) \in [0.147792460, 0.147792461], \qquad \text{below } 149\text/1000 .
```

**The comparison of Theorem 5.3:** $`\ln 15 > 27\text/10`$, since $`\ln 3 + \ln 5 \ge 2.708050201101`$.

**Pure rationals.** The values of $`\Omega`$ in Table 1; $`\Xi(8) = 19440\text/2783 > 13\text/2`$;
$`\psi'(0) = 331\text/7225`$; $`\eta_{16} = 33\text/289`$; $`256\text/17 > 15`$;
$`1 - 4\text/25 - 4\text/13 = 173\text/325`$; $`(149\text/1000)(289\text/16) = 43061\text/16000 < 27\text/10`$;
$`27\text/4 - 1148\text/173 = 79\text/692`$; and the two twenty-fifth powers of Lemma
5.2, which compare the integers $`29021^{25} \cdot 89^4`$ with
$`189^4 \cdot 25721^{25}`$, and $`977^{25} \cdot 9^4`$ with $`19^4 \cdot 867^{25}`$.
