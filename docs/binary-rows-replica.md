# Binary rows: the optimal latent and the replica

This page proves the structural half of the bound $`T(p) \le (27\text/4)\,\tau(p)`$
on laws $`p`$ of a binary $`X`$ and a $`Y`$ with values in any finite nonempty
set: for a full-support law, an optimal latent with at most two labels, three
code bounds, and the replica bound that pays for them. Laws of a finite $`X`$
and a binary $`Y`$ follow by exchanging the coordinates
([Theorem 6.3](binary-rows-27-4.md#6-assembly) of the companion page).
The derivations here are at `paper proof` in the sense of the
[claim ledger](claims.md#status-vocabulary). The purification lemma and the
bound this page serves are also `kernel-verified` in this repository
([section 9](#9-scope-and-formalization)), and the estimate that completes
the proof is on the companion page [Binary rows: factor seven](binary-rows-27-4.md).
Section 7, the Bernoulli layer, serves that page; the structure theorem does not use it.

The constant $`27\text/4`$ lies between the constant $`2`$ that
[binary factor two](binary-factor-two.md) proves for $`2 \times 2`$ laws and the
$`9`$ of [binary factor nine](binary-factor-nine.md); on $`2 \times 2`$ laws it
adds nothing to the constant $`2`$. It is the first bound proved in this repository for
alphabets beyond $`2 \times 2`$. It leaves the arbitrary-alphabet constant
$`C_*`$ of the [claim ledger](claims.md#ledger) unchanged, since a bound on one
family of alphabets says nothing about all of them.

Write $`p(x,y)`$ for the law, with $`X \in \{0,1\}`$ the row and $`Y`$ the
column; scores, codes, $`\tau`$ and $`T`$ are those of the
[blueprint](blueprint.md#1-laws-entropy-and-codes), and the other symbols are
listed in [section 1](#1-setting).

> **Structure theorem (the optimal latent and three codes).** Let $`p`$ be a full-support
> law on $`\{0,1\} \times Y`$. Then one of the following holds.
>
> 1. $`\tau(p) = I_p(X;Y)`$, the constant code has $`D_p = \tau(p)`$, and so
>    $`T(p) \le \tau(p)`$.
> 2. There is a $`\tau`$-optimal latent $`W`$ with values in $`\{0,1\}`$, both
>    weights positive and distinct component laws.
>
> In case 2, with $`J = I(X;Y \mid W)`$ and $`X'`$ the replica of
> [section 3](#3-the-replica-bound),
>
> ```math
> \begin{aligned}
> T(p) &\le \min\{ I_p(X;Y),\ H(X \mid Y),\ \tau(p) + 3\,H(W \mid X,Y) \}, \\
> I_p(X;Y) &\le \tau(p) + I(W;X), \\
> H(X \mid Y) &\le \tau(p) + H(X \mid W) - 2J, \\
> H(W \mid X,Y) &\le H(W \mid X), \\
> \tau(p) &\ge J + I(W;X' \mid X),
> \end{aligned}
> ```
>
> and the joint law of $`(W,X,X')`$ is fixed by three parameters $`k > 1`$,
> $`\ell > 0`$ and $`w \in (0,1)`$ (Lemma 6.4).

The three terms of the minimum are upper bounds on the scores of three codes:
the constant code, the row code $`g(x,y) = x`$, and a purified code of $`W`$
(Lemma 4.1). The theorem does not say that the latent $`W`$ is unique.

| Step | Sections |
|---|---|
| Units, notation and public inputs | [1](#1-setting) |
| Three codes and three interfaces | [2](#2-codes-and-interfaces) |
| The replica bound | [3](#3-the-replica-bound) |
| The purification lemma | [4](#4-the-purification-lemma) |
| At most two component laws | [5](#5-at-most-two-component-laws) |
| Contact coordinates | [6](#6-contact-coordinates) |
| The Bernoulli layer | [7](#7-the-bernoulli-layer) |
| Proof of the structure theorem | [8](#8-proof-of-the-structure-theorem) |
| Scope and formalization | [9](#9-scope-and-formalization) |

## 1. Setting

**Units.** Everything on this page is in natural logarithms. The entropies, the
information quantities, the functionals $`\Psi`$ and $`\Phi`$, the scores
$`\mathrm{score}_p(L)`$ and $`D_p(g)`$, and the optima $`\tau(p)`$ and $`T(p)`$
all denote $`\ln 2`$ times the bit-valued quantities used elsewhere in this
repository. An inequality proved here holds verbatim in bits when every term in
it is such a quantity, which is the case for the structure theorem and every lemma of
sections 2 to 6. Two constants are specific to nats: Pinsker's constant $`2`$ in
Lemma 7.1 and the function $`\omega`$ of Lemma 7.2, so Lemmas 7.1, 7.3 and 7.4
hold as written only with divergences and $`J`$ in nats (in bits their right
sides carry a factor $`1\text/\ln 2`$). The declarations quoted below are stated in
bits.

**Notation.** For $`\xi \in [0,1]`$ and $`\zeta \in (0,1)`$, with $`0 \ln 0 = 0`$,

```math
h(\xi) = -\xi \ln \xi - (1-\xi) \ln(1-\xi), \qquad
\mathrm{kl}(\xi \Vert \zeta) = \xi \ln \frac{\xi}{\zeta} + (1-\xi) \ln \frac{1-\xi}{1-\zeta}.
```

For a law $`m`$ on a product of finite sets, with marginals $`m_X`$ and $`m_Y`$,
$`\Phi(m) = 3\,H(m) - 2\,H(m_X) - 2\,H(m_Y)`$ as in the blueprint, and
$`\Psi(m) = 2\,H(m) - H(m_X) - H(m_Y)`$ as in the
[score decomposition](binary-factor-nine.md#the-score-decomposition), so that
$`\Psi(p) - \Phi(p) = I_p(X;Y)`$. The symbols below are fixed on this page and
used without restatement on the companion page.

| Symbol | Meaning | Defined in |
|---|---|---|
| $`W`$, $`w`$, $`q_0`$, $`q_1`$ | the two-label optimal latent, $`w = \Pr(W=1)`$, its component laws | [6](#6-contact-coordinates) |
| $`X'`$ | the replica of $`X`$ given $`(W,Y)`$ | [3](#3-the-replica-bound) |
| $`\gamma`$ | the kernel | [1](#1-setting) |
| $`m_y`$, $`\rho_y`$, $`\mu_j`$ | the kernel's column weights and ratios, and their moments | [5](#5-at-most-two-component-laws) |
| $`s < t`$, $`k`$, $`\ell`$, $`N`$, $`\kappa`$ | contact parameters, $`k = t\text/s`$, $`\ell = s^3`$, $`N = k^2+k+1`$, $`\kappa = k\text/(k+1)^2`$ | [6](#6-contact-coordinates) |
| $`e_0`$, $`e_1`$ | $`\Pr(X=1 \mid W=0)`$, $`\Pr(X=0 \mid W=1)`$ | [6](#6-contact-coordinates) |
| $`\chi_i(y)`$ | $`\Pr(X=1 \mid Y=y, W=i)`$ | [6](#6-contact-coordinates) |
| $`\omega(\zeta)`$ | the Ordentlich-Weinberger function | [7](#7-the-bernoulli-layer) |

**Contacts.** Let $`S`$ be a set of cells and $`\gamma`$ a kernel on $`S`$.
For probability vectors $`\alpha'`$ on the rows and $`\beta'`$ on the columns put
$`\Lambda_\gamma(\alpha',\beta') = \sum_{(x,y) \in S} \gamma(x,y)\, {\alpha'_x}^{2\text/3}\, {\beta'_y}^{2\text/3}`$.
The kernel is *feasible* when it is positive on $`S`$ and $`\Lambda_\gamma(\alpha',\beta') \le 1`$ for all such $`\alpha'`$
and $`\beta'`$, and a law $`q`$ supported in $`S`$ is a *contact* of $`\gamma`$ when

```math
q(x,y) = \gamma(x,y)\, q_X(x)^{2\text/3}\, q_Y(y)^{2\text/3} \qquad \text{for every } (x,y) \in S.
```

These are the library's `Lambda`, `Feasible` and `IsContact`. The contacts of
the [binary stochastic optimum](binary-stochastic-optimum.md#5-at-most-two-component-laws)
page are defined differently, and nothing here identifies the two notions.

**Public inputs.** The proof uses the definitions of the blueprint and the
following `kernel-verified` declarations of
[Deterministic](../StochasticToDeterministicLatents/Deterministic.lean) and
[Bridge](../StochasticToDeterministicLatents/Bridge.lean), for arbitrary finite
alphabets `α` and `β`:

```lean
theorem exists_optimalCode (p : α × β → ℝ) :
    ∃ g : Code α β, detScore p g = T p

theorem T_le_detScore (p : α × β → ℝ) (g : Code α β) :
    T p ≤ detScore p g

theorem latent_score_eq {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) :
    L.score = Psi p - ∑ v, L.prior v * Phi (L.comp v)

theorem exists_seedSetup {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) : Nonempty (SeedSetup p)

theorem contact_support_eq {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q : α × β → ℝ} (hq : IsContact S w q) :
    support q = S

-- in namespace SeedSetup
theorem optimal (D : SeedSetup p) : D.L.score = tau p

theorem contact (D : SeedSetup p) :
    ∀ v, D.L.prior v ≠ 0 → IsContact (support p) D.w (D.L.comp v)

theorem feasible (D : SeedSetup p) : Feasible (support p) D.w

theorem prior_pos (D : SeedSetup p) : ∀ v, 0 < D.L.prior v
```

In words: $`T(p)`$ is attained and is at most every code's score; a latent's
score is $`\Psi(p) - \sum_l \pi_l\,\Phi(q_l)`$; and a law with connected support
(any two cells of the support are joined by a chain of cells of the support,
consecutive cells sharing a row or a column)
has a $`\tau`$-optimal latent `D.L` with positive weights whose components are all
contacts of one feasible kernel `D.w`, each with support equal to that of $`p`$.
The kernel `D.w` is the $`\gamma`$ of the contacts above, not the weight $`w`$ of
section 6. The
Bernoulli form of the Ordentlich-Weinberger inequality is attributed to
E. Ordentlich and M. J. Weinberger, "A distribution dependent refinement of
Pinsker's inequality", IEEE Transactions on Information Theory 51 (2005),
1836-1840; Lemma 7.3 proves the form used here.

## 2. Codes and interfaces

Sections 2 to 4 hold for a law $`p`$ on any finite $`\alpha \times \beta`$ and
any finite latent $`L`$ of $`p`$, with prior $`\pi`$ and components $`q_l`$.

**Lemma 2.1 (three codes).**

1. The constant code has $`D_p = I_p(X;Y)`$.
2. The row code $`g(x,y) = x`$ has $`D_p(g) = H(X \mid Y)`$.
3. For every function $`f`$ from $`\alpha \times \beta`$ to a finite set,
   $`T(p) \le D_p(f) = I(X;Y \mid f) + H(f \mid X) + H(f \mid Y)`$.

*Proof.* (1) Conditioning on a constant changes nothing, and a constant has zero
entropy given anything. (2) $`I(X;Y \mid X) = 0`$ and $`H(X \mid X) = 0`$, which
leaves $`H(X \mid Y)`$. (3) The image of $`f`$ has at most
$`\lvert \alpha \times \beta \rvert`$ points; an injection of it into the canonical
alphabet gives a code $`g`$ with the same classes as $`f`$. Every entropy in
$`D_p`$ depends only on the partition into classes, so $`D_p(g) = D_p(f)`$, and
`T_le_detScore` gives $`T(p) \le D_p(g)`$.

**Lemma 2.2 (three interfaces).** With $`J_L = I(X;Y \mid L)`$,

```math
\begin{aligned}
I_p(X;Y) &\le \mathrm{score}_p(L) + I(L;X), \\
H(X \mid Y) &\le \mathrm{score}_p(L) + H(X \mid L) - 2J_L, \\
H(L \mid X,Y) &\le H(L \mid X).
\end{aligned}
```

*Proof.* Expanding $`I(X;L,Y)`$ in two orders and $`H(X \mid Y)`$ through $`L`$,

```math
\begin{aligned}
I_p(X;Y) &= J_L + I(L;X) - I(L;X \mid Y), \\
H(X \mid Y) &= H(X \mid L,Y) + I(L;X \mid Y) = H(X \mid L) - J_L + I(L;X \mid Y), \\
\mathrm{score}_p(L) &= J_L + I(L;X \mid Y) + I(L;Y \mid X) \ge J_L + I(L;X \mid Y).
\end{aligned}
```

The first line with $`I(L;X \mid Y) \ge 0`$ and $`J_L \le \mathrm{score}_p(L)`$
gives the first bound. The third line gives
$`I(L;X \mid Y) \le \mathrm{score}_p(L) - J_L`$, and substituting it into the
second gives the second bound. Conditioning does not increase entropy, which is
the third.

Every inequality here is additive: nothing is divided by $`\tau(p)`$ or by a
score, so $`\tau(p) = 0`$ needs no separate treatment.

## 3. The replica bound

**The replica.** Draw $`X'`$ from the law of $`X`$ given $`(L,Y)`$,
independently of $`X`$. That is, on the labels times $`\alpha \times \beta \times \alpha`$,

```math
\Pr(L=l,\, X=x,\, Y=y,\, X'=x') = \pi_l\, q_l(x,y)\, \frac{q_l(x',y)}{q_{l,Y}(y)},
```

and zero where $`q_{l,Y}(y) = 0`$. Summing over $`x'`$ returns the law of
$`(L,X,Y)`$; summing over $`x`$ shows that $`(L,X',Y)`$ has the same law as
$`(L,X,Y)`$; and the product form makes $`X`$ and $`X'`$ independent given
$`(L,Y)`$.

**Lemma 3.1 (the replica bound).**

```math
I(X;Y \mid L) + I(L;X' \mid X) \le \mathrm{score}_p(L).
```

*Proof.* By the chain rule,

```math
I(L;X' \mid X) \le I(L;Y,X' \mid X) = I(L;Y \mid X) + I(L;X' \mid X,Y).
```

Expanding $`I(L,X;X' \mid Y)`$ in two orders,

```math
I(X;X' \mid Y) + I(L;X' \mid X,Y) = I(L;X' \mid Y) + I(X;X' \mid L,Y).
```

The last term is zero by conditional independence, and $`I(L;X' \mid Y) = I(L;X \mid Y)`$
because $`(L,X',Y)`$ and $`(L,X,Y)`$ have the same law. Hence
$`I(L;X' \mid X,Y) = I(L;X \mid Y) - I(X;X' \mid Y) \le I(L;X \mid Y)`$, so
$`I(L;X' \mid X) \le I(L;Y \mid X) + I(L;X \mid Y)`$. Adding
$`I(X;Y \mid L)`$ gives the score.

No positivity is assumed; a pair $`(l,y)`$ of zero mass contributes nothing to
either side.

## 4. The purification lemma

For a label $`l`$ and a cell $`z = (x,y)`$ with $`p(z) > 0`$ put
$`\theta_l(z) = \pi_l\, q_l(z)\text/p(z)`$, the posterior of $`l`$, and call $`l`$
*available* at $`z`$ when $`\theta_l(z) > 0`$. Where $`q_l(z) > 0`$ put

```math
\phi_l(z) = 3 \ln q_l(z) - 2 \ln q_{l,X}(x) - 2 \ln q_{l,Y}(y).
```

**Lemma 4.1 (purification).** Let $`f`$ choose, at each cell with
$`p(z) > 0`$, any available label minimizing $`\phi_l(z) - 3 \ln \theta_l(z)`$,
and any label at cells with $`p(z) = 0`$. Then

```math
D_p(f) \le \mathrm{score}_p(L) + 3\,H(L \mid X,Y),
```

and so $`T(p) \le \mathrm{score}_p(L) + 3\,H(L \mid X,Y)`$ by Lemma 2.1. Call
$`f`$ a *purified code* of $`L`$.

*Proof.* Labels of zero weight are discarded first; this changes neither side.
The code $`f`$ is itself a latent of $`p`$ whose components are its blocks: block
$`l`$ has mass $`\pi'_l = \Pr(f = l)`$ and law $`r_l`$, and blocks of mass zero are
dropped. Since $`H(f \mid X,Y) = 0`$, the score of this latent is
$`I(X;Y \mid f) + H(f \mid Y) + H(f \mid X) = D_p(f)`$, and the score
decomposition gives $`D_p(f) = \Psi(p) - \sum_l \pi'_l\,\Phi(r_l)`$.

Two exact identities are used. First, for a law $`r`$ supported where
$`q_l > 0`$, expanding the entropies of $`\Phi(r)`$ against $`\phi_l`$ gives

```math
-\Phi(r) = \sum_z r(z)\, \phi_l(z) + 3\,\mathrm{KL}(r \Vert q_l) - 2\,\mathrm{KL}(r_X \Vert q_{l,X}) - 2\,\mathrm{KL}(r_Y \Vert q_{l,Y}),
```

with $`\mathrm{KL}`$ the relative entropy. Block $`l`$ lives on cells where $`l`$ is
available, so $`r_l`$ qualifies. Second, since $`\pi'_l\, r_l(z) = p(z)`$ on block
$`l`$ and $`p(z)\text/q_l(z) = \pi_l\text/\theta_l(z)`$,

```math
\sum_l \pi'_l\, \mathrm{KL}(r_l \Vert q_l) = -\sum_z p(z) \ln \theta_{f(z)}(z) - \mathrm{KL}(\pi' \Vert \pi).
```

Substitute the first identity at $`r = r_l`$ into the score decomposition of
$`f`$, then the second into the $`\mathrm{KL}(r_l \Vert q_l)`$ terms. What remains
beyond the display below is the two marginal divergences, with coefficient
$`-2`$, and $`\mathrm{KL}(\pi' \Vert \pi)`$, with coefficient $`-3`$; dropping them,

```math
D_p(f) \le \Psi(p) + \sum_z p(z) \left( \phi_{f(z)}(z) - 3 \ln \theta_{f(z)}(z) \right).
```

At each cell the chosen value is at most the average of
$`\phi_l(z) - 3 \ln \theta_l(z)`$ with weights $`\theta_l(z)`$, which sum to $`1`$
over the available labels. Since $`p(z)\,\theta_l(z) = \pi_l\, q_l(z)`$, the averages sum to

```math
\sum_l \pi_l \sum_z q_l(z)\, \phi_l(z) - 3 \sum_z p(z) \sum_l \theta_l(z) \ln \theta_l(z)
= -\sum_l \pi_l\,\Phi(q_l) + 3\,H(L \mid X,Y),
```

and $`\Psi(p) - \sum_l \pi_l\,\Phi(q_l) = \mathrm{score}_p(L)`$.

Nothing about optimality or support is used. The label set of $`f`$ is that of
$`L`$; Lemma 2.1(3) relabels it into the canonical alphabet.

## 5. At most two component laws

From here to the end of the page $`p`$ is a full-support law on
$`\{0,1\} \times Y`$.

**Lemma 5.1 (the form of a contact).** Let $`\gamma > 0`$ be a kernel on all of
$`\{0,1\} \times Y`$ and $`q`$ a full-support contact of $`\gamma`$. Put

```math
m_y = \gamma(0,y)^3, \qquad \rho_y = \frac{\gamma(1,y)}{\gamma(0,y)}, \qquad
t = \left( \frac{q_X(1)}{q_X(0)} \right)^{1\text/3} > 0.
```

Then

```math
q(0,y) = \frac{m_y\,(1 + \rho_y t^2)^2}{(1+t^3)^2}, \qquad q(1,y) = \rho_y t^2\, q(0,y). \qquad \text{(5.1)}
```

In particular $`q`$ is determined by $`t`$.

*Proof.* Here $`q_X(0) = 1\text/(1+t^3)`$ and $`q_X(1)^{2\text/3} = t^2\,q_X(0)^{2\text/3}`$.
Summing the contact equation over the two rows of column $`y`$ and dividing by
$`q_Y(y)^{2\text/3}`$,

```math
q_Y(y)^{1\text/3} = \gamma(0,y)\, q_X(0)^{2\text/3} + \gamma(1,y)\, q_X(1)^{2\text/3}
= \gamma(0,y)\, q_X(0)^{2\text/3} (1 + \rho_y t^2).
```

Substituting $`q_Y(y)^{2\text/3} = \gamma(0,y)^2\, q_X(0)^{4\text/3} (1+\rho_y t^2)^2`$
into the contact equation at $`(0,y)`$ gives
$`q(0,y) = \gamma(0,y)^3\, q_X(0)^2\, (1 + \rho_y t^2)^2`$, which is (5.1); at
$`(1,y)`$ the factor $`\gamma(1,y)\, q_X(1)^{2\text/3}`$ replaces
$`\gamma(0,y)\, q_X(0)^{2\text/3}`$, a ratio of $`\rho_y t^2`$.

**The contact polynomial.** For the kernel $`\gamma`$ put
$`\mu_j = \sum_y m_y \rho_y^j`$ for $`j = 0,1,2,3`$ and

```math
R(z) = (1+z^3)^2 - \sum_y m_y (1 + \rho_y z^2)^3
= (1-\mu_0) - 3\mu_1 z^2 + 2z^3 - 3\mu_2 z^4 + (1-\mu_3) z^6. \qquad \text{(5.2)}
```

**Lemma 5.2 (contacts are double roots).** If $`q`$ is a full-support contact of
$`\gamma`$ with parameter $`t`$, then $`R(t) = R'(t) = 0`$. Distinct contacts
have distinct parameters, and $`\gamma`$ has at most two distinct full-support
contacts.

*Proof.* By (5.1), the total mass of $`q`$ is
$`\sum_y m_y (1+\rho_y t^2)^3\text/(1+t^3)^2`$, and it equals $`1`$: that is
$`R(t) = 0`$. The mass of row $`1`$ is
$`t^2 \sum_y m_y \rho_y (1+\rho_y t^2)^2\text/(1+t^3)^2`$, and it equals
$`q_X(1) = t^3\text/(1+t^3)`$, so $`\sum_y m_y \rho_y (1+\rho_y t^2)^2 = t\,(1+t^3)`$.
Differentiating (5.2),

```math
R'(z) = 6z^2 (1+z^3) - 6z \sum_y m_y \rho_y (1 + \rho_y z^2)^2,
```

which vanishes at $`z = t`$. Distinct contacts have distinct $`t`$ by Lemma 5.1.

Suppose three distinct contacts had parameters $`t_1 < t_2 < t_3`$. The
polynomial $`R`$ is not zero, since its $`z^3`$ coefficient is $`2`$, and it has
degree at most six, so the three double roots force
$`R(z) = (1-\mu_3) \prod_{i=1}^3 (z-t_i)^2`$ with $`1 - \mu_3 \ne 0`$. The
$`z^5`$ coefficient of the right side is $`-2(1-\mu_3)(t_1+t_2+t_3) \ne 0`$,
while that of (5.2) is zero. So there are at most two contacts.

**Theorem 5.3 (at most two component laws).** There is a $`\tau`$-optimal
latent of $`p`$ whose labels have positive weight and pairwise distinct
component laws, all contacts of one feasible kernel $`\gamma > 0`$ with full
support. It has one or two labels, and with one label
$`\tau(p) = I_p(X;Y)`$.

*Proof.* Full support makes the support connected: the cells $`(x,y)`$ and
$`(x',y')`$ are joined through $`(x,y')`$, which shares a row with the first
and a column with the second. So `exists_seedSetup` supplies a latent with
score $`\tau(p)`$ and positive weights whose components are contacts of a
feasible kernel $`\gamma`$ on all cells, each of full support by
`contact_support_eq`.

Merge labels with equal component laws, adding their weights. The mixture is
unchanged, so the result is a latent of $`p`$; its components are among the old
ones, hence still contacts; and its score is unchanged, because
$`\Psi(p) - \sum_l \pi_l\,\Phi(q_l)`$ depends only on the total weight carried by
each distinct law. Lemma 5.2 leaves at most two labels. With one label the
component is the mixture $`p`$ itself, and its score is
$`\Psi(p) - \Phi(p) = I_p(X;Y)`$.

## 6. Contact coordinates

In this section the latent of Theorem 5.3 has two labels. Their contacts have
distinct parameters; label them $`0`$ and $`1`$ so that the parameter $`s`$ of
label $`0`$ is smaller than the parameter $`t`$ of label $`1`$, and call the
result $`W`$, with components $`q_0`$, $`q_1`$ and weight $`w = \Pr(W=1) \in (0,1)`$.
Put

```math
k = \frac{t}{s} > 1, \qquad \ell = s^3, \qquad N = k^2+k+1, \qquad \kappa = \frac{k}{(k+1)^2},
```

and let $`e_0 = \Pr(X=1 \mid W=0)`$ and $`e_1 = \Pr(X=0 \mid W=1)`$. By (5.1) the
row masses of the two contacts give

```math
e_0 = \frac{s^3}{1+s^3} = \frac{\ell}{1+\ell}, \qquad e_1 = \frac{1}{1+t^3} = \frac{1}{1+k^3 \ell}.
```

**Lemma 6.1 (the moments).** With $`\sigma_1 = s+t`$ and $`\sigma_2 = st`$,

```math
R(z) = \frac{(z-s)^2 (z-t)^2 (z^2 + 2\sigma_1 z + \sigma_2)}{\sigma_1^3},
```

```math
\mu_0 = 1 - \frac{\sigma_2^3}{\sigma_1^3}, \qquad
\mu_1 = \frac{\sigma_2 (\sigma_1^2 - \sigma_2)}{\sigma_1^3}, \qquad
\mu_2 = \frac{\sigma_1^2 - \sigma_2}{\sigma_1^3}, \qquad
\mu_3 = 1 - \frac{1}{\sigma_1^3}.
```

*Proof.* By Lemma 5.2, $`(z-s)^2(z-t)^2 = (z^2 - \sigma_1 z + \sigma_2)^2`$
divides $`R`$, which has degree at most six; write the quotient as
$`a_2 z^2 + a_1 z + a_0`$. Expanding,

```math
(z^2 - \sigma_1 z + \sigma_2)^2 = z^4 - 2\sigma_1 z^3 + (\sigma_1^2 + 2\sigma_2) z^2 - 2\sigma_1\sigma_2 z + \sigma_2^2 .
```

The coefficients of $`z^5`$, $`z`$ and $`z^3`$ in (5.2) are $`0`$, $`0`$ and
$`2`$:

```math
\begin{aligned}
a_1 - 2\sigma_1 a_2 &= 0, \\
\sigma_2^2 a_1 - 2\sigma_1\sigma_2 a_0 &= 0, \\
-2\sigma_1 a_0 + (\sigma_1^2 + 2\sigma_2)\, a_1 - 2\sigma_1\sigma_2\, a_2 &= 2.
\end{aligned}
```

The first two give $`a_1 = 2\sigma_1 a_2`$ and $`a_0 = \sigma_2 a_2`$, and then
the third reads $`2\sigma_1^3 a_2 = 2`$, so $`a_2 = \sigma_1^{-3}`$. The
coefficients of $`z^6`$, $`z^4`$, $`z^2`$ and $`1`$ then give

```math
\begin{aligned}
1 - \mu_3 &= a_2, \\
-3\mu_2 &= a_0 - 2\sigma_1 a_1 + (\sigma_1^2 + 2\sigma_2)\, a_2 = 3\,(\sigma_2 - \sigma_1^2)\, a_2, \\
-3\mu_1 &= (\sigma_1^2 + 2\sigma_2)\, a_0 - 2\sigma_1\sigma_2\, a_1 + \sigma_2^2\, a_2 = 3\,\sigma_2 (\sigma_2 - \sigma_1^2)\, a_2, \\
1 - \mu_0 &= \sigma_2^2\, a_0 = \sigma_2^3\, a_2,
\end{aligned}
```

which are the four moments.

**Lemma 6.2 (the open parameter range).** The two moment determinants are
positive:

```math
\mu_0\mu_2 - \mu_1^2 = \frac{(\sigma_1^2 - \sigma_2)(\sigma_1 - \sigma_2^2)}{\sigma_1^4} > 0, \qquad
\mu_1\mu_3 - \mu_2^2 = \frac{(\sigma_1^2 - \sigma_2)(\sigma_1\sigma_2 - 1)}{\sigma_1^4} > 0.
```

Consequently, strictly,

```math
\frac{1}{k(k+1)} < \ell < \frac{k+1}{k^2}, \qquad
\frac{1}{N} < e_0,\, e_1 < \frac{k+1}{N}, \qquad
e_0 + e_1 < 1,
```

and $`Y`$ has at least two elements.

*Proof.* Substituting Lemma 6.1 and factoring out $`\sigma_1^2 - \sigma_2`$,

```math
\begin{aligned}
\sigma_1^6\,(\mu_0\mu_2 - \mu_1^2) &= (\sigma_1^2 - \sigma_2)\left( \sigma_1^3 - \sigma_2^3 - \sigma_2^2(\sigma_1^2 - \sigma_2) \right) = (\sigma_1^2 - \sigma_2)\,\sigma_1^2\,(\sigma_1 - \sigma_2^2), \\
\sigma_1^6\,(\mu_1\mu_3 - \mu_2^2) &= (\sigma_1^2 - \sigma_2)\left( \sigma_2(\sigma_1^3 - 1) - (\sigma_1^2 - \sigma_2) \right) = (\sigma_1^2 - \sigma_2)\,\sigma_1^2\,(\sigma_1\sigma_2 - 1).
\end{aligned}
```

As weighted variances,
$`\mu_0\mu_2 - \mu_1^2 = \mu_0 \sum_y m_y (\rho_y - \mu_1\text/\mu_0)^2`$ and
$`\mu_1\mu_3 - \mu_2^2 = \mu_1 \sum_y m_y \rho_y (\rho_y - \mu_2\text/\mu_1)^2`$,
with $`m_y > 0`$ and $`\rho_y > 0`$. Both are nonnegative, and each vanishes exactly
when all $`\rho_y`$ are equal. If both vanished, the identities (with
$`\sigma_1^2 - \sigma_2 = s^2 + st + t^2 > 0`$) would give
$`\sigma_1 = \sigma_2^2`$ and $`\sigma_1\sigma_2 = 1`$, hence
$`\sigma_1 = \sigma_2 = 1`$, contradicting $`\sigma_1 \ge 2\sqrt{\smash[b]{\sigma_2}}`$. So
both are positive, not all $`\rho_y`$ are equal, and $`\lvert Y \rvert \ge 2`$.

With $`s = \ell^{1\text/3}`$ and $`t = k s`$, $`\sigma_1 > \sigma_2^2`$ reads
$`s(1+k) > s^4 k^2`$, that is $`\ell < (k+1)\text/k^2`$, and
$`\sigma_1\sigma_2 > 1`$ reads $`\ell\, k(k+1) > 1`$. Next, $`e_0`$ increases and
$`e_1`$ decreases in $`\ell`$; at $`\ell = 1\text/(k(k+1))`$ they are $`1\text/N`$ and
$`(k+1)\text/N`$, and at $`\ell = (k+1)\text/k^2`$ they are $`(k+1)\text/N`$ and
$`1\text/N`$. Finally,

```math
1 - e_0 - e_1 = \frac{1}{1+\ell} - \frac{1}{1+k^3\ell} = \frac{\ell\,(k^3-1)}{(1+\ell)(1+k^3\ell)} > 0.
```

The bound $`e_0 + e_1 < 1`$ does not follow from the upper bounds
$`e_0, e_1 < (k+1)\text/N`$ alone, since $`(k+1)\text/N < 1\text/2`$ only when
$`k > (1+\sqrt 5)\text/2`$.

**Lemma 6.3 (the posterior variance).** Let $`\chi_i(y) = \Pr(X=1 \mid Y=y, W=i)`$,
a random variable of $`y`$ drawn from $`q_{i,Y}`$. Then
$`E\,\chi_0 = e_0`$, $`E\,\chi_1 = 1 - e_1`$, and

```math
\mathrm{Var}\,\chi_i = \kappa\, e_i (1-e_i), \qquad i = 0,1.
```

*Proof.* Write $`t_0 = s`$ and $`t_1 = t`$. By (5.1),
$`q_{i,Y}(y) = m_y (1+\rho_y t_i^2)^3\text/(1+t_i^3)^2`$ and
$`\chi_i(y) = \rho_y t_i^2\text/(1+\rho_y t_i^2)`$. The mean is the row mass
$`t_i^3\text/(1+t_i^3)`$, which is $`e_0`$ for $`i = 0`$ and $`1-e_1`$ for $`i = 1`$.
The second moment is

```math
E\,\chi_i^2 = \frac{t_i^4 \sum_y m_y \rho_y^2 (1 + \rho_y t_i^2)}{(1+t_i^3)^2}
= \frac{t_i^4 (\mu_2 + t_i^2 \mu_3)}{(1+t_i^3)^2},
```

so

```math
\mathrm{Var}\,\chi_i = \frac{t_i^3 \left( t_i \mu_2 + t_i^3 (\mu_3 - 1) \right)}{(1+t_i^3)^2}.
```

By Lemma 6.1,
$`t_i \mu_2 + t_i^3(\mu_3 - 1) = t_i (s^2 + st + t^2 - t_i^2)\text/(s+t)^3`$, which
is $`st\text/(s+t)^2 = \kappa`$ for both $`t_i = s`$ and $`t_i = t`$. Since
$`t_i^3\text/(1+t_i^3)^2`$ is the product of the two row masses, it equals
$`e_i(1-e_i)`$.

**Lemma 6.4 (the replica cells).** The replica $`X'`$ of section 3, built from
$`W`$, gives the conditional laws of $`(X,X')`$

| Cell $`(x,x')`$ | given $`W=0`$ | given $`W=1`$ |
|---|---|---|
| $`(0,0)`$ | $`(1-e_0)^2 + \kappa e_0(1-e_0)`$ | $`e_1^2 + \kappa e_1(1-e_1)`$ |
| $`(0,1)`$, and also $`(1,0)`$ | $`(1-\kappa)\, e_0(1-e_0)`$ | $`(1-\kappa)\, e_1(1-e_1)`$ |
| $`(1,1)`$ | $`e_0^2 + \kappa e_0(1-e_0)`$ | $`(1-e_1)^2 + \kappa e_1(1-e_1)`$ |

So the joint law of $`(W,X,X')`$ depends only on $`(k,\ell,w)`$.

*Proof.* Given $`W = i`$ and $`Y = y`$, $`X`$ and $`X'`$ are conditionally independent Bernoulli
variables with parameter $`\chi_i(y)`$. Averaging over $`y`$,
$`\Pr(X = X' = 1 \mid W = i) = E\,\chi_i^2`$,
$`\Pr(X = 1, X' = 0 \mid W = i) = E\,\chi_i - E\,\chi_i^2`$, and
$`\Pr(X = X' = 0 \mid W = i) = 1 - 2E\,\chi_i + E\,\chi_i^2`$. Lemma 6.3 gives
$`E\,\chi_i^2 = (E\,\chi_i)^2 + \kappa e_i(1-e_i)`$, and the table follows.

## 7. The Bernoulli layer

**Lemma 7.1 (Pinsker).** For $`\xi \in [0,1]`$ and $`\zeta \in (0,1)`$,
$`\mathrm{kl}(\xi \Vert \zeta) \ge 2(\xi - \zeta)^2`$.

*Proof.* As a function of $`\xi`$ on $`(0,1)`$, the difference vanishes with its
derivative at $`\xi = \zeta`$, and its second derivative is
$`1\text/(\xi(1-\xi)) - 4 \ge 0`$. So it is convex and nonnegative on
$`(0,1)`$, and by continuity at $`\xi \in \{0,1\}`$.

**Lemma 7.2 (the Ordentlich-Weinberger function).** For $`\zeta \in (0,1)`$ put

```math
\omega(\zeta) = \frac{1}{1-2\zeta} \ln \frac{1-\zeta}{\zeta}, \qquad \omega(1\text/2) = 2.
```

With $`y = 1 - 2\zeta`$,

```math
\omega(\zeta) = \frac{2\,\mathrm{atanh}(y)}{y} = 2 \sum_{j \ge 0} \frac{y^{2j}}{2j+1}.
```

Hence $`\omega`$ is continuous, symmetric about $`1\text/2`$, decreasing on
$`(0,1\text/2]`$, increasing on $`[1\text/2,1)`$, and $`\omega(\zeta) > 2`$ for
$`\zeta \ne 1\text/2`$. Moreover $`1\text/(\zeta(1-\zeta)) > 2\,\omega(\zeta)`$ for
$`\zeta \ne 1\text/2`$.

*Proof.* $`(1-\zeta)\text/\zeta = (1+y)\text/(1-y)`$, and
$`\ln \frac{1+y}{1-y} = 2\,\mathrm{atanh}(y) = 2 \sum_{j \ge 0} y^{2j+1}\text/(2j+1)`$
for $`\lvert y \rvert < 1`$. Every term of the series for $`\omega`$ is a
nonnegative even power of $`y`$, which gives the shape and $`\omega > 2`$ for
$`y \ne 0`$. For the last claim, $`\zeta(1-\zeta) = (1-y^2)\text/4`$, and for
$`0 < y < 1`$

```math
\frac{\omega(\zeta)}{2} = \frac{\mathrm{atanh}(y)}{y} < \frac{1}{y} \sum_{j \ge 0} y^{2j+1} = \frac{1}{1-y^2} = \frac{1}{4\,\zeta(1-\zeta)};
```

negative $`y`$ follows by symmetry.

**Lemma 7.3 (Ordentlich-Weinberger).** For $`\xi \in [0,1]`$ and
$`\zeta \in (0,1)`$,

```math
\mathrm{kl}(\xi \Vert \zeta) \ge \omega(\zeta)\, (\xi - \zeta)^2 .
```

*Proof.* At $`\zeta = 1\text/2`$ this is Lemma 7.1. Both sides are unchanged by
$`(\xi,\zeta) \to (1-\xi,1-\zeta)`$, so let $`\zeta < 1\text/2`$ and put
$`G(\xi) = \mathrm{kl}(\xi \Vert \zeta) - \omega(\zeta)(\xi-\zeta)^2`$ on
$`(0,1)`$. Then

```math
G'(\xi) = \ln \frac{\xi\,(1-\zeta)}{(1-\xi)\,\zeta} - 2\,\omega(\zeta)\,(\xi - \zeta), \qquad
G''(\xi) = \frac{1}{\xi(1-\xi)} - 2\,\omega(\zeta).
```

$`G'`$ vanishes at $`\xi = \zeta`$, at $`\xi = 1\text/2`$ (where the logarithm is
$`\ln((1-\zeta)\text/\zeta) = \omega(\zeta)(1-2\zeta)`$), and at $`\xi = 1-\zeta`$
(where it is twice that). Since $`1\text/(\xi(1-\xi))`$ is convex and symmetric
with minimum $`4 < 2\,\omega(\zeta)`$ at $`1\text/2`$, $`G''`$ is negative exactly on
an interval $`(\xi_-,\xi_+)`$ symmetric about $`1\text/2`$, and positive outside it.
By Lemma 7.2, $`G''(\zeta) > 0`$, so $`\zeta < \xi_-`$ and
$`1 - \zeta > \xi_+`$. Hence $`G'`$ increases through its zero $`\zeta`$,
decreases through $`1\text/2`$, and increases through $`1-\zeta`$: $`G`$ decreases
on $`(0,\zeta]`$, increases on $`[\zeta,1\text/2]`$, decreases on
$`[1\text/2,1-\zeta]`$ and increases on $`[1-\zeta,1)`$. Its minima are
$`G(\zeta) = 0`$ and

```math
G(1-\zeta) = (1-2\zeta) \ln \frac{1-\zeta}{\zeta} - \omega(\zeta)(1-2\zeta)^2 = 0 .
```

So $`G \ge 0`$ on $`(0,1)`$, and on $`[0,1]`$ by continuity.

**Lemma 7.4 (the component information).** For the latent $`W`$ of section 6,

```math
J = I(X;Y \mid W) \ge \kappa \left( (1-w)\, e_0(1-e_0)\, \omega(e_0) + w\, e_1(1-e_1)\, \omega(e_1) \right).
```

*Proof.* For each label,
$`I(X;Y \mid W=i) = \sum_y q_{i,Y}(y)\, \mathrm{kl}(\chi_i(y) \Vert E\,\chi_i)`$.
By Lemma 7.3 each term is at least
$`\omega(E\,\chi_i)\,(\chi_i(y) - E\,\chi_i)^2`$, and the average of the square is
$`\mathrm{Var}\,\chi_i = \kappa e_i(1-e_i)`$ (Lemma 6.3). Here
$`\omega(E\,\chi_0) = \omega(e_0)`$ and $`\omega(E\,\chi_1) = \omega(1-e_1) = \omega(e_1)`$.
Weight by $`1-w`$ and $`w`$.

## 8. Proof of the structure theorem

Theorem 5.3 gives a $`\tau`$-optimal latent with one or two labels. With one
label, $`\tau(p) = I_p(X;Y)`$, which is the score of the constant code (Lemma
2.1), so $`T(p) \le \tau(p)`$: case 1. With two labels, section 6 names it
$`W`$, with values in $`\{0,1\}`$, positive weights and distinct components, and
$`\mathrm{score}_p(W) = \tau(p)`$. Lemma 2.1 bounds $`T(p)`$ by the scores of the
constant and row codes, and Lemma 4.1 by $`\tau(p) + 3\,H(W \mid X,Y)`$; Lemma 2.2
at $`L = W`$ gives the three interfaces; Lemma 3.1 gives the replica bound; and
Lemma 6.4 gives the law of $`(W,X,X')`$: case 2.

## 9. Scope and formalization

**What is proved here.** The structure theorem and the lemmas above are complete prose
derivations from the public inputs of [section 1](#1-setting), Shannon's chain
rules, and one-variable calculus. Sections 2 to 4 hold for every finite law and
every finite latent. Sections 5 to 8 need full support on
$`\{0,1\} \times Y`$. The companion page
[Binary rows: factor seven](binary-rows-27-4.md) uses the structure theorem,
Lemmas 2.1 and 4.1, Lemmas 6.2 to 6.4, and Lemmas 7.1 to 7.4.

**What is not proved here.** The structure theorem is an existence statement: it does not say
that the optimal latent, or its two-label form, is unique, and it does not
compare its contacts with those of the binary stochastic optimum page. Nothing
here concerns laws with a zero cell; the companion page reaches them through the
sparse transfer, which says nothing about their optimal latents. Nothing is
claimed for $`\lvert X \rvert > 2`$ with $`\lvert Y \rvert > 2`$.

**Formalization.** The derivations on this page are at `paper proof`; the
`kernel-verified` inputs of [section 1](#1-setting) are cited by name. Lemma 4.1
is `kernel-verified` in this repository, in bits, as
`BinaryRow.IsPurifiedCode.score_le`, for every purified code in the sense of
`BinaryRow.IsPurifiedCode`; its per-cell objective `BinaryRow.purifyObjective`
is the page's minus $`3 \ln p(z)`$, a term constant in the label, so the two
definitions admit the same codes. The bound this page serves is `kernel-verified` as
`BinaryRow.T_le_twentySevenQuarters_mul_tau` and
`BinaryRow.T_le_twentySevenQuarters_mul_tau_col`, and the code clause on full
support as `BinaryRow.exists_rowWitnessCode`. The Lean proves these statements;
the [admission record](../verification/admissions.md#binaryrow) describes its
route. The [claim ledger](claims.md#ledger) records the standing of the
binary-row bound, and the [Lean contracts](lean-contracts.md) list its modules.
