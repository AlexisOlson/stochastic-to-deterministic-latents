# Constructive blueprint

This is the canonical notation and mechanism guide. The certificate-free binary
factor-nine theorem is kernel-verified in this repository. The
arbitrary-alphabet factor-nine statement remains open.

The [claim ledger](claims.md) records exact evidence status. Start with the
[definitions](#1-laws-entropy-and-codes) and [pricing rule](#2-price-the-act-of-determinizing),
or go directly to the [law-only selector](#5-recover-the-code-from-the-law).
The [factor-nine proof](binary-factor-nine.md) gives the complete verified
argument.

## 1. Laws, entropy, and codes

Let $`X`$ and $`Y`$ take values in finite alphabets $`\alpha`$ and $`\beta`$,
and let $`p`$ be their joint law. All entropies and information quantities are
measured in bits. A zero-probability event contributes zero to entropy.

A finite stochastic latent $`L`$, coupled to $`(X,Y)`$, has score

```math
\mathrm{score}_p(L) = I(X;Y \mid L) + I(L;X \mid Y) + I(L;Y \mid X).
```

The stochastic optimum is

```math
\tau(p) = \inf_L \mathrm{score}_p(L),
```

where the infimum ranges over finite stochastic latents.

A canonical deterministic code has type

```math
\mathrm{Code}(\alpha,\beta) = (\alpha \times \beta) \to \mathrm{Fin}(\mathrm{card}(\alpha \times \beta)).
```

There is one available label for every observation cell, which is enough to
encode every partition of the finite observation space. Any finite-valued
deterministic code can therefore be relabeled into this canonical alphabet
without changing its partition. The score of a canonical code $`g`$ is

```math
D_p(g) = I(X;Y \mid g) + H(g \mid X) + H(g \mid Y).
```

The Lean definition of this score is named `detScore`; $`D_p(g)`$ is the
reader-facing notation used throughout the exposition.

Notation is deliberately typed by role. $`\mathrm{score}_p(L)`$ always means
the score of a supplied stochastic latent, $`\tau(p)`$ only the stochastic
optimum, $`D_p(g)`$ the score of a supplied deterministic code, and $`T(p)`$
only the deterministic optimum. A proof may select a latent attaining
$`\tau(p)`$, but it never renames that latent's score as a new objective.

The optimizer normal form also uses the component functional

```math
\Phi(q) = 3 H(q) - 2 H(q_X) - 2 H(q_Y).
```

$`\Phi(q)`$ is not a latent score. A latent decomposition uses the
prior-weighted sum $`\sum_l \pi_l\,\Phi(q_l)`$, with the weights always written
explicitly. For binary laws the stochastic optimum is computed exactly in the
[binary stochastic optimum](binary-stochastic-optimum.md) page, at
`paper proof`.

The deterministic optimum is the attained finite minimum

```math
T(p) = \min_{g : \mathrm{Code}(\alpha,\beta)} D_p(g).
```

Only the partition of the positive support induced by $`g`$ matters: relabeling
code values changes no information quantity, and distinctions confined to
zero-mass cells are ignored when codes are canonicalized.

The target statements are inequalities rather than bounds on $`T(p) \text{/} \tau(p)`$.
This keeps the product-law boundary $`\tau(p) = 0`$ meaningful. For a binary
product law, the constant code has score zero, so
$`D_p(c) = T(p) = \tau(p) = 0`$.

## 2. Price the act of determinizing

For a supplied stochastic latent $`L`$ and deterministic code $`g`$, define

```math
\begin{aligned}
\mathrm{W3Cost}_L(g) &= I(L;(X,Y) \mid g) + 3 H(g \mid L), \\[1ex]
\mathrm{W3}(L) &= \min_{g : \mathrm{Code}(\alpha,\beta)} \mathrm{W3Cost}_L(g).
\end{aligned}
```

Lean names these definitions `w3Cost` and `w3`; the exposition keeps the
mathematical capitalization.

There is an exact score identity

```math
D_p(g) = \mathrm{score}_p(L) + \mathrm{W3Cost}_L(g) - 2 R_L(g),
```

where $`R_L(g)`$ is an explicit sum of four conditional mutual informations and
is therefore nonnegative. Dropping this rebate gives

```math
D_p(g) \le \mathrm{score}_p(L) + \mathrm{W3Cost}_L(g).
```

When $`L`$ attains $`\tau(p)`$, minimizing over $`g`$ yields the reusable
pricing rule

```math
\mathrm{W3}(L) \le c\,\tau(p) \implies T(p) \le (1+c)\,\tau(p).
```

This is the common seam between the binary bound and the open
arbitrary-alphabet factor-nine conjecture.

## 3. Why the binary search collapses

On the positive, full-support $`2 \times 2`$ two-contact chart, relabeling puts
the two conditional laws into a transposed form. Their likelihood ratios take
three levels: neutral on the diagonal, low on one off-diagonal cell, and high
on the other.

Writing

```math
\mathrm{reward}_L(g) = H(g) - 4 H(g \mid L),
```

gives

```math
\mathrm{W3Cost}_L(g) = I(L;(X,Y)) - \mathrm{reward}_L(g).
```

The finite-code geometry shows that no deterministic partition beats both of the
following candidates:

1. the constant code; and
2. the singleton code isolating the high likelihood-ratio cell.

The reduction merges neutral mass to an endpoint, compares the low and high tails,
and then merges the remaining three-level case. This reduces the search over
deterministic partitions to one two-candidate decision.

## 4. The binary estimate

### Certificate-free factor eight

For a full-support binary law, choose the attained optimizer from the
normal-form argument. In the two-contact case, orient its chart so that the
high likelihood-ratio cell is fixed. Write

```math
\begin{aligned}
K &= I(L;(X,Y)), \\
R_H &= H(\mathrm{high}) - 4 H(\mathrm{high} \mid L).
\end{aligned}
```

Choose $`g_{\mathrm{chart}}`$ to be the high singleton when $`R_H \ge 0`$, and
the constant otherwise. The exact fixed-code identity gives

```math
\mathrm{W3Cost}_L(g_{\mathrm{chart}}) = K - \max(0,R_H).
```

The analytic proof separates the two signs of `R_H`. In the nonpositive phase,
integral comparisons bound $`K`$ by eight times the between-component part of
the latent score. In the positive phase, an exact loss split and two seam
endpoint estimates give the corresponding bound for $`K-R_H`$. Both
phases yield

```math
\mathrm{W3}(L) \le \mathrm{W3Cost}_L(g_{\mathrm{chart}}) \le 8\,\tau(p).
```

The one-component case has zero cost. In the two-contact case, catalog recovery
transports the selected chart code to a member of the catalog defined from
$`p`$. Pricing gives that member deterministic score at most $`9\,\tau(p)`$,
and the law-only selector minimizes deterministic score over the catalog. Thus

```math
T(p) \le D_p(g_p) \le 9\,\tau(p)
```

for every full-support binary law. Explicit smoothing extends the bound on
$`T`$ to every binary law, and finite attainment supplies a deterministic
witness. The sparse transfer provides neither a selected-latent $`\mathrm{W3}`$
bound nor a bound for $`g_p`$ at the boundary.

These conclusions are kernel-verified in
[`Binary/FactorNine.lean`](../StochasticToDeterministicLatents/Binary/FactorNine.lean).
The generic transfer theorem `T_le_mul_tau_of_forall_fullSupport` remains
conditional on a full-support bound; the binary theorem supplies its premise
at constant nine. See the [binary factor-nine proof](binary-factor-nine.md).

## 5. Recover the code from the law

Although the proof may select an attained optimal latent, the final deterministic
code does not receive that latent as input. For a binary table

```math
p = \begin{pmatrix} p_{00} & p_{01} \\ p_{10} & p_{11} \end{pmatrix},
```

define the law-only selector $`g_p`$ as follows:

1. Compute $`\Delta = p_{00}\,p_{11} - p_{01}\,p_{10}`$. If it is zero, return the constant code.
2. If $`\Delta > 0`$, use the diagonal pair $`\{00,11\}`$. If $`\Delta < 0`$, use the
off-diagonal pair $`\{01,10\}`$.
3. Choose the lower-mass cell in that pair. On an exact mass tie, use the first
cell in row-major order $`00 < 01 < 10 < 11`$.
4. Form the singleton code separating that cell from the other cells, and
   canonicalize its labels on positive support.
5. Compare its exact $`D_p`$ score with the constant code's. Return the singleton
   only when its score is strictly smaller; the constant wins a final score tie.

Codes are canonicalized on positive support so that zero-mass cells do not create
spurious distinctions. On count or rational input every decision is exact and
finite. On arbitrary exact real input the same mathematical function is defined
classically; no total oracle-free comparison procedure is claimed.

For full-support laws, this mathematical selector has the locally verified
factor-nine guarantee. The count and rational implementations still need the
refinement theorems connecting their outputs to this selector.

### A final-score tie

Let $`q`$ be the count table

```math
q = \begin{pmatrix} 14 & 1 \\ 1 & 4 \end{pmatrix}, \qquad p = q\text{/}20.
```

The checkerboard products are `56` and `1`, so the active pair is
$`\{00,11\}`$. Cell `11` has the lower mass. Its singleton and the constant
code have equal deterministic scores, so the selector returns the constant
partition $`\{00,01,10,11\}`$.

The [exact calculation](../examples/README.md#final-score-tie) gives the two
identical integer score keys. The examples page also covers a product law,
sparse support, an endpoint-mass tie, and a strict singleton win. These are
branch specifications; the score-key theorem and count/rational refinement
remain unproved in the public Lean library.

## 6. The open arbitrary-alphabet factor-nine route

The same pricing rule would prove the arbitrary-finite bound from the following
selected estimate:

```text
for every finite law p,
select an attained tau-optimal L with W3(L) <= 8 * tau(p).
```

Unlike the binary estimate proved above, this arbitrary-alphabet estimate
remains a `conjecture`. Hence $`T(p) \le 9\,\tau(p)`$ for arbitrary finite
alphabets also remains a conjecture. The goal is a deterministic construction
whose low cost follows from a readable structural argument and whose behavior
at exact ties and zero-mass boundaries is explicit.
