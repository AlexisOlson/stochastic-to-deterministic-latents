# Stochastic-to-Deterministic Latents

Replace a finite stochastic latent variable by a deterministic function of the
observations at bounded information cost. For every binary $`2 \times 2`$ law,
this repository proves

```math
T(p) \le 2\,\tau(p),
```

where $`T`$ is the deterministic optimum and $`\tau`$ is the stochastic
optimum. On full support, one of five explicit codes, the constant code or one
of the four singleton codes, has score at most $`2\,\tau(p)`$; the Lean
statement does not say which. The weaker
$`T(p) \le 9\,\tau(p)`$ is proved by an independent route. Beyond
$`2 \times 2`$, when one observation is binary and the other takes values in
any finite set, the repository proves $`T(p) \le (27\text/4)\,\tau(p)`$; on
full support, with the binary observation as the row, the constant code, the
row code, or a purified code of an optimal latent meets that bound. All three
proofs are kernel-verified in the public Lean library and certificate-free:
every numerical comparison is an exact rational bound on logarithms proved in
Lean, with nothing delegated to an interval certificate. No constant is
claimed to be sharp.

Here $`p`$ is the joint law of two observations $`(X,Y)`$. A finite stochastic
latent $`L`$ coupled to them has score
$`I(X;Y \mid L) + I(L;X \mid Y) + I(L;Y \mid X)`$, and $`\tau(p)`$ is the
infimum of that score over all such latents. A deterministic code $`g`$ is a
function of $`(X,Y)`$; its score is
$`D_p(g) = I(X;Y \mid g) + H(g \mid X) + H(g \mid Y)`$, and $`T(p)`$ is the
minimum over the finitely many codes. Both are in bits. The blueprint fixes
the notation.

| To begin | Read |
|---|---|
| Understand the construction | [Constructive blueprint](docs/blueprint.md), including the [selector recipe](docs/blueprint.md#5-recover-the-code-from-the-law) |
| Follow the headline proof | [Binary factor two](docs/binary-factor-two.md) |
| Follow the independent factor-nine proof and the law-only selector | [Binary factor nine](docs/binary-factor-nine.md) |
| Follow the proof for one binary alphabet | [Binary rows: the optimal latent and the replica](docs/binary-rows-replica.md), then [Binary rows: factor 27/4](docs/binary-rows-27-4.md) |
| Inspect the Lean statements | [Existing endpoints and target contracts](docs/lean-contracts.md) |
| Check the verification | [Verification procedure](verification/README.md) |
| Pick a problem | [Open problems](docs/open-problems.md), with the standing of each target and where a contribution lands |
| Explore the declaration graph | [Verso dependency blueprint](https://AlexisOlson.github.io/stochastic-to-deterministic-latents/) |

## Results and targets

| Scope | Bound | Construction | Current evidence |
|---|---:|---|---|
| Binary $`2 \times 2`$ | $`T(p) \le 2\,\tau(p)`$ | [Binary factor two](docs/binary-factor-two.md): on full support, the constant code or a singleton code, compared with the exact optimum along each contact chord; sparse laws by the kernel-verified transfer | `kernel-verified` in this repository; certificate-free |
| Binary $`2 \times 2`$ | $`T(p) \le 9\,\tau(p)`$ | Law-only selector on full support; attained code on sparse laws | `kernel-verified` in this repository; certificate-free |
| $`\{0,1\} \times Y`$ or $`Y \times \{0,1\}`$, with $`Y`$ finite | $`T(p) \le (27\text/4)\,\tau(p)`$ | [Binary rows](docs/binary-rows-27-4.md): on full support over $`\{0,1\} \times Y`$, the constant code, the row code, or a purified code of an optimal latent, against a lower bound on the optimum from a replica of the row; sparse laws by the kernel-verified transfer, and columns by transposition | `kernel-verified` in this repository; certificate-free |
| Binary $`2 \times 2`$ | $`\tau(p)`$ exactly, from one cubic root; every optimal latent has at most two component laws | [Binary stochastic optimum](docs/binary-stochastic-optimum.md) | `paper proof`; the value on full support with nonnegative determinant is also `kernel-verified` |
| Arbitrary finite alphabets | $`T(p) \le 9\,\tau(p)`$ | Open | `conjecture` |

For a full-support binary law, the deterministic witness can be chosen from the
law alone. Compare the constant code with the singleton selected by the
determinant and endpoint-mass rule, then return the one with smaller
deterministic score. This selector satisfies $`D_p(g_p) \le 9\,\tau(p)`$.

For a law with a zero cell, smoothing transfers the bound on $`T`$. Finite
attainment then supplies a code with $`D_p(g) = T(p) \le 9\,\tau(p)`$. The
sparse transfer supplies neither a $`\mathrm{W3}`$ estimate for a sparse
optimizer nor a bound for the named selector at the boundary.

The [claim ledger](docs/claims.md) records each statement's exact quantifiers,
dependencies, and evidence tier.

## Mechanism

For an attained stochastic optimizer, a bound $`\mathrm{W3} \le c\,\tau`$
yields $`T \le (1+c)\,\tau`$. On full support, the binary proof selects an
optimal latent $`L`$ and bounds the cost of its constant or
high-likelihood-ratio singleton code by $`8\,\tau(p)`$. This gives
$`\mathrm{W3}(L) \le 8\,\tau(p)`$. Catalog recovery transfers that witness to
the law-defined catalog, and pricing gives factor nine for the catalog's
deterministic-score minimizer.

The separate binary reduction theorem proves that the better chart code also
minimizes cost over the canonical code space. Its minimality is not needed for
the factor-nine upper bound. The [blueprint](docs/blueprint.md) defines the
costs and derives the pricing rule.

Count and rational selector implementations are available, but their agreement
with the real-valued selector remains unproved here. On arbitrary exact real
input, the mathematical selector uses classical exact comparisons. The
[worked examples](examples/README.md) show the branch and tie rules without
claiming this missing refinement.

## Related bounds

On binary product laws, the constant code is exactly optimal and
$`D_p(c) = T(p) = \tau(p) = 0`$.

Let $`C_*`$ be the infimum of constants $`C`$ for which
$`T(p) \le C\,\tau(p)`$ holds for every finite law. An
[external compiler-backed Lean certificate](https://github.com/satchlj/stoch-to-det-lower)
exhibits a $`12 \times 12`$ law with ratio at least $`1.960073002187`$, so
$`C_* \ge 1.960073002187`$. That certificate uses `native_decide`; it is not a
local verification claim and is not `kernel-verified` under this repository's
terminology. The universal constant and the arbitrary-alphabet factor-nine
conjecture remain open.

## Verify it yourself

With Lean's `elan` installed, from the repository root:

```sh
lake exe cache get
lake build StochasticToDeterministicLatents
lake env lean -DrelaxedAutoImplicit=false Verify.lean
```

The first command fetches the Mathlib cache on a fresh clone. The build ends
with "Build completed successfully", and the audit prints nothing and exits 0
on success.

`Verify.lean` carries, for each of the 947 public theorem endpoints, an
`assert_no_sorry` check and a `#print axioms` result pinned with `#guard_msgs`.
Every pinned set was discovered by running `#print axioms` after compilation;
the headline theorems, factor two, factor nine and the binary-row factor
alike, each report
`[propext, Classical.choice, Quot.sound]`. A
root build after a single module changes takes a minute or two, and the audit
about twenty seconds once the root is built; both take considerably longer from
a cold cache, and either may exceed ten minutes there. The [verification guide](verification/README.md) gives the trust
scan, the single-module check, and the admission procedure.

## Contributing

The [open problems](docs/open-problems.md) page is the priority list. Each
problem there has a fixed statement, its current evidence tier, and what would
close it. A contribution takes one of three shapes: a Lean proof of a target
signature in the [contracts](docs/lean-contracts.md), admitted through the
[verification procedure](verification/README.md#admitting-a-change); a paper
proof with a fixed statement, which enters the ledger at that tier; or an
explicit witness with exact arithmetic the library can replay. Open an issue
naming the problem before starting anything large.

## Reference

- [Blueprint](docs/blueprint.md): notation, pricing, and the selector recipe.
- [Binary factor nine](docs/binary-factor-nine.md): the independent factor-nine proof, which also bounds the law-only selector.
- [Binary stochastic optimum](docs/binary-stochastic-optimum.md): $`\tau(p)`$ in closed form for every binary law, at `paper proof`.
- [Binary factor two](docs/binary-factor-two.md): the binary constant two, from two deterministic scores compared with the exact stochastic optimum along each contact chord. The page gives the prose derivation at `paper proof`; the theorem itself is `kernel-verified`.
- [Binary rows: the optimal latent and the replica](docs/binary-rows-replica.md) and [Binary rows: factor 27/4](docs/binary-rows-27-4.md): the constant $`27\text/4`$ when one alphabet is binary, from an optimal latent with at most two labels, three codes, and a replica of the binary observation. The pages give the prose derivation at `paper proof`; the theorem itself is `kernel-verified`.
- [Claim ledger](docs/claims.md) and [Lean contracts](docs/lean-contracts.md): statements, scope, and existing or proposed signatures.
- [Verification](verification/README.md): commands, trust model, and admission requirements.
- [Examples](examples/README.md): exact inputs, branch calculations, and selected partitions.
- [Provenance](docs/provenance.md) and [transfer manifest](docs/transfer-manifest.md): attribution and publication decisions.

## Upstream

This project descends from and credits
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), which introduced
the Lean formalization and the finite-alphabet theorem developed here. This is a
fresh distillation of that work and the reviewed follow-on material. See
[NOTICE](NOTICE) and [docs/provenance.md](docs/provenance.md).

## License

Licensed under the [Apache License, Version 2.0](LICENSE). This repository
derives from [`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det),
also Apache-2.0; attribution and change notices are in [NOTICE](NOTICE).
