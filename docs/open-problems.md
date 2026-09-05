# Open problems

This page maps what is proved, what is conjectured, and where a contribution
would land, so that a reader can pick a problem and know its standing before
starting. Tiers are those of the [claim ledger](claims.md#status-vocabulary):
`kernel-verified`, `paper proof`, `conjecture`. The ledger is authoritative;
this page restates nothing at a stronger tier than the ledger gives it.

## 1. The targets

Let `C_*` be the infimum of constants `C` with `T(p) <= C*tau(p)` for every
law on arbitrary finite alphabets, and `C_2` the same infimum over binary
`2 x 2` laws only, so `C_2 <= C_*`.

| Fact | Status |
|---|---|
| `C_* >= 1.960073002187`, witnessed by a `12 x 12` law | external `native_decide` certificate ([`LOWER-1960`](claims.md#ledger)); not reproduced here |
| `C_* <= 1771` | `kernel-verified` upstream in [`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det) at the pinned revision |
| `C_2 <= 9` | `kernel-verified` here, certificate-free ([`BIN-C9`](claims.md#ledger)) |
| `C_* <= 9` | `conjecture` ([`GEN-C9`](claims.md#ledger)) |
| `C_2 <= 2` | `conjecture` ([`BIN-C2`](claims.md#ledger)) |

Two constants are interesting. A universal constant of `2` would sit within
two percent of the general lower bound. For binary laws the conjectured
constant is also `2`; the `12 x 12` witness says nothing about `C_2`, and
this repository holds no binary lower bound above the trivial `1`.

## 2. Problems with a precise statement

### 2.1 The binary constant `2` (`BIN-C2`)

**Statement.** `T(p) <= 2*tau(p)` for every binary `2 x 2` law `p`.

**What is known.** `C_2 <= 9` by the certificate-free proof in this
repository. The factor-nine route does not approach `2`: its constant is
`1 + 8` from the pricing rule, where `8` is the ratio between two chart
quantities in the scalar phases. Harwood and Gillen report numerical
experiments on binary variables and a partial argument for the equal-marginal
case in their
[LessWrong post](https://www.lesswrong.com/posts/4q3kMfJHB4rxr3Z8m/small-steps-towards-proving-stochastic-deterministic-natural);
those are literature claims here, with no tier.

**A public lower bound is cheap to certify.** For any law `p` and any
explicit latent `L`, `T(p)/tau(p) >= T(p)/score_p(L)`, because
`tau(p) <= score_p(L)`. On a `2 x 2` law, `T(p)` is a minimum over finitely
many codes, and both sides are finite sums of rational-logarithm terms, so a
binary lower bound needs one explicit law, one explicit latent, and exact
bounds on a handful of logarithms of the kind already proved throughout
[`ScalarEstimates`](../StochasticToDeterministicLatents/Binary/ScalarEstimates.lean).
No such certificate is in the library yet. The one-parameter family of
symmetric laws `p00 = p11`, `p01 = p10` is the natural place to start.

**What would close the upper bound.** Any route that prices a selected
optimal latent at `W3(L) <= tau(p)`, or a direct argument on the finite code
space that does not pass through `W3`. Sharper binary constants are in
progress and are not part of this release.

**Tier.** `conjecture`.

### 2.2 The general factor-eight estimate (`GEN-W3-8`)

**Statement.** Every finite law `p` admits an attained `tau`-optimal latent
`L` with `W3(L) <= 8*tau(p)`.

**What is known.** The binary case is proved here through the two-contact
normal form and the two scalar phase arguments ([`BIN-W3-8`](claims.md#ledger),
full support). The pricing rule [`PRICE(c)`](claims.md#ledger) is generic, so
this estimate alone would give [`GEN-C9`](claims.md#ledger).

**What would close it.** A normal form for optimal latents beyond two
observation symbols, or a different witness whose cost is bounded without
one. See the
[general construction problem](blueprint.md#6-the-open-arbitrary-alphabet-factor-nine-route).

**Tier.** `conjecture`.

### 2.3 The universal constant `2`

**Statement.** `T(p) <= 2*tau(p)` for every finite law.

**What is known.** Only the bounds in section 1. Any proof would need to
handle laws like the `12 x 12` witness, where the ratio exceeds `1.96`.

**Tier.** `conjecture`.

### 2.4 Executable refinement of the binary selector (`BIN-LAW-SELECTOR`)

**Statement.** The count and rational implementations of the law-only
selector agree with the mathematical selector `Binary.selector`. The target
signatures are `Binary.CountTable.selector_eq_realSelector` and
`Binary.RationalTable.selector_eq_realSelector` in the
[Lean contracts](lean-contracts.md#bin-law-selector).

**What is known.** The score-key identity
`N * log(2) * (D_p(singleton) - D_p(constant)) = log(A/B)` is stated with
exact integer keys in the [worked examples](../examples/README.md#exact-score-comparison);
its Lean proof is missing, as are positive-total normalization and support
agreement.

**Why it matters.** It is the smallest self-contained Lean contribution in
the repository, and it turns the verified full-support selector bound into a
bound for a program.

**Tier.** `paper proof` for the mathematical rule; the refinement is open.

### 2.5 Sparse laws and the named selector

**Statement.** `D_p(g_p) <= 9*tau(p)` for the law-only selector `g_p` on
binary laws with a zero cell.

**What is known.** The all-law bound on `T` is proved by smoothing, which
carries no selection rule across the limit
([proof section 6](binary-factor-nine.md#6-sparse-and-degenerate-laws)). A
direct argument on the boundary would need the selector's deterministic
score on product and sparse laws; those statements are not in the library.

**Tier.** `conjecture`.

### 2.6 The label count of an optimal latent

**Statement.** Every binary law has a `tau`-optimal latent with at most `k`
labels, for an explicit `k`.

**What is known.** The normal form bounds the number of distinct active
component laws (two), not the label count of the ambient optimizer; the
duplicate quotient is what the library works with.

**Tier.** `conjecture`.

## 3. Where a contribution lands

Every problem above has a fixed statement. A contribution is one of:

- a Lean proof of an existing target signature, admitted through the
  [verification procedure](../verification/README.md#admitting-a-change),
  which pins the new theorem in `Verify.lean` and promotes its ledger row;
- a paper proof with a fixed statement, which enters the ledger at that tier
  and becomes a node of the
  [dependency blueprint](https://alexisolson.github.io/stochastic-to-deterministic-latents/)
  with no Lean declaration, ready for formalization;
- an explicit witness, for a lower bound, with exact arithmetic that the
  library can replay.

The blueprint site marks a node "ready" when every node it depends on is
formalized. That is a statement about dependencies, not about the existence
of a proof; the conjecture rows above are "ready" in that sense and remain
conjectures. This page is the human priority list.

## 4. Asking for more

A larger private workspace behind this repository holds explored routes
toward the constant `2`, some closed with a recorded reason, some partial.
Curated notes on a route are available on request: open an issue or a
discussion naming the problem above that it bears on. Shared material
carries the tier stated with it and no more.
