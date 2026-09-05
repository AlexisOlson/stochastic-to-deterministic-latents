# Stochastic-to-Deterministic Latents

Replace a finite stochastic latent variable by a deterministic function of the
observations at bounded information cost. For every binary `2 x 2` law, this
repository proves

```text
T(p) <= 9*tau(p),
```

where `T` is the deterministic optimum and `tau` is the stochastic optimum.
The proof is kernel-verified in the public Lean library and certificate-free:
every analytic step is an exact rational-logarithm bound proved in Lean, with
nothing delegated to a numerical certificate.

Here `p` is the joint law of two observations `(X,Y)`. A finite stochastic
latent `L` coupled to them has score `I(X;Y | L) + I(L;X | Y) + I(L;Y | X)`,
and `tau(p)` is the infimum of that score over all such latents. A
deterministic code `g` is a function of `(X,Y)`; its score is
`D_p(g) = I(X;Y | g) + H(g | X) + H(g | Y)`, and `T(p)` is the minimum over
the finitely many codes. Both are in bits. The blueprint fixes the notation.

| To begin | Read |
|---|---|
| Understand the construction | [Constructive blueprint](docs/blueprint.md), including the [selector recipe](docs/blueprint.md#5-recover-the-code-from-the-law) |
| Follow the complete proof | [Binary factor nine](docs/binary-factor-nine.md) |
| Inspect the Lean statements | [Existing endpoints and target contracts](docs/lean-contracts.md) |
| Check the verification | [Verification procedure](verification/README.md) |

## Results and targets

| Scope | Bound | Construction | Current evidence |
|---|---:|---|---|
| Binary `2 x 2` | `T(p) <= 9*tau(p)` | Law-only selector on full support; attained code on sparse laws | `kernel-verified` in this repository; certificate-free |
| Arbitrary finite alphabets | `T(p) <= 9*tau(p)` | Open | `conjecture` |

For a full-support binary law, the deterministic witness can be chosen from the
law alone. Compare the constant code with the singleton selected by the
determinant and endpoint-mass rule, then return the one with smaller
deterministic score. This selector satisfies `D_p(g_p) <= 9*tau(p)`.

For a law with a zero cell, smoothing transfers the bound on `T`. Finite
attainment then supplies a code with `D_p(g) = T(p) <= 9*tau(p)`. The sparse
transfer supplies neither a `W3` estimate for a sparse optimizer nor a bound
for the named selector at the boundary.

The [claim ledger](docs/claims.md) records each statement's exact quantifiers,
dependencies, and evidence tier.

## Mechanism

For an attained stochastic optimizer, a bound `W3 <= c*tau` yields
`T <= (1+c)*tau`. On full support, the binary proof selects an optimal latent
`L` and bounds the cost of its constant or high-likelihood-ratio singleton
code by `8*tau(p)`. This gives `W3(L) <= 8*tau(p)`. Catalog recovery transfers
that witness to the law-defined catalog, and pricing gives factor nine for
the catalog's deterministic-score minimizer.

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
`D_p(c) = T(p) = tau(p) = 0`.

Let `C_*` be the infimum of constants `C` for which
`T(p) <= C*tau(p)` holds for every finite law. An
[external compiler-backed Lean certificate](https://github.com/satchlj/stoch-to-det-lower)
exhibits a `12 x 12` law with ratio at least `1.960073002187`, so
`C_* >= 1.960073002187`. That certificate uses `native_decide`; it is not a
local verification claim and is not `kernel-verified` under this repository's
terminology. The universal constant and the arbitrary-alphabet factor-nine
conjecture remain open.

## Verify it yourself

With Lean's `elan` installed, from the repository root:

```sh
lake exe cache get          # fresh clone only: fetch the Mathlib oleans
lake build                  # the root library; ends with "Build completed successfully"
lake env lean Verify.lean   # the audit; prints nothing and exits 0 on success
```

`Verify.lean` carries, for each of the 495 public theorem endpoints, an
`assert_no_sorry` check and a `#print axioms` result pinned with `#guard_msgs`.
Every pinned set was discovered by running `#print axioms` after compilation;
the four headlines each report `[propext, Classical.choice, Quot.sound]`. The
root build takes about eleven minutes with a warm cache, and the audit can
exceed ten. The [verification guide](verification/README.md) gives the trust
scan, the single-module check, and the admission procedure.

## Ways to contribute

- Prove that the count and rational backends agree with the mathematical
  selector, including support canonicalization and exact score ties.
- Produce an independent exact checker for the rational-log ledgers.
- Prove the arbitrary-finite `W3 <= 8*tau` estimate, or develop deterministic
  constructions beyond the binary case.

## Reference

- [Blueprint](docs/blueprint.md): notation, pricing, and the selector recipe.
- [Binary factor nine](docs/binary-factor-nine.md): the complete proof, with every analytic step an exact rational-logarithm bound.
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
