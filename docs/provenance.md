# Provenance and attribution

## Public foundation

The primary code and mathematical ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det). It supplies
the initial Lean formalization, finite-law and latent interfaces, stochastic
and deterministic objectives, and the first universal finite bound. Its code
is distributed under the Apache License, Version 2.0; this repository retains
the attribution and change notices described in [NOTICE](../NOTICE).

The finite-information layer is reused through a Lake dependency pinned to
`299c75264b07db05eab8e6d232ef88e0988f4790`. The local `Information.lean` and
`Latent.lean` expose descriptive aliases and theorem wrappers without copying
the upstream implementations. `Deterministic.lean` rewrites the deterministic
objective over a canonical code alphabet. `Bridge.lean` is the only public
import point for the upstream envelope, duality, seed, and quotient machinery.

The foundation files map to the pinned upstream source as follows:

| Public file | Upstream source at the pinned revision | Treatment |
|---|---|---|
| `Information.lean` | `stoch_to_det/Entropy.lean`, including `H`, `Hvar`, `condH`, `MI`, and `condMI` | Reducible public aliases and small theorem wrappers. |
| `Latent.lean` | `stoch_to_det/Functionals.lean`, including `Latent`, `Latent.score`, and `tau` | Reducible public aliases and small theorem wrappers. |
| `Deterministic.lean` | The deterministic objective `detScore` and `T` in `stoch_to_det/Functionals.lean` | Local code-first rewrite over one canonical finite code alphabet. |
| `Bridge.lean` | `stoch_to_det/Envelope.lean` (`Latent.score_eq`, `Latent.ofFunction`, `Latent.ofFunction_isDet`, `Latent.ofFunction_score_eq_detScore`, `exists_tau_optimal_latent`, `T_eq_iInf_detScore_codes`, `continuousEntropy`, `H_eq_continuousEntropy`, `continuous_continuousEntropy`, `continuous_push_map`), `stoch_to_det/Duality.lean` (`Lambda`, `Feasible`, `IsContact`, `contact_support_eq`), `stoch_to_det/Seed.lean` (`SeedSetup`, `exists_seedSetup`), `stoch_to_det/Quotient.lean` (`Clustering`, `Clustering.Q`, `Clustering.s`, `Clustering.Q_injective`, `Clustering.Q_isContact`, `exists_clustering`), `stoch_to_det/Functionals.lean` (`support`, `IsConnected`, `Latent.IsDet`, `detScore`, `T`), and `stoch_to_det/Entropy.lean` (`Psi`, `Phi`) | Reducible public aliases and exact restatements; the two bridge theorems identify the local `detScore` with upstream's unconditionally and the local `T` with upstream's on probability laws. This is the only public import point for the upstream `Envelope`, `Duality`, `Seed`, and `Quotient` modules. |
| `Pricing.lean` | The score, `detScore`, and `tau` foundations of `stoch_to_det/Functionals.lean`; the pinned revision has no `W3` declarations | Cost, rebate identity, and pricing theorem written for this repository. |

Every other Lean module reaches upstream only through these files. The pinned
revision contains no declarations matching the binary geometry, normal forms,
scalar estimates, phase arguments, or sparse transfer; those are adapted from
the reviewed working material described below. The [claim ledger](claims.md)
states current result scopes and evidence tiers; [verification](../verification/README.md)
describes their local audit.

## File-level attribution

Every adapted Lean file carries a concise header identifying its origin and
license and stating that the rest is adapted from unpublished working
material with public names and module boundaries. That material supplies
attribution, not public verification evidence, and is not a dependency. Its
internal module and declaration names are meaningless to a public reader and
are kept in a private per-file record outside this repository, together with
the merge, specialization, and private-helper accounting for each module;
public declarations use mathematical names only. Headers must not contain
private workspace paths or directory names.

## Reviewed working material

Reviewed follow-on material informed the mathematical proofs and Lean
adaptations. Its structure is not a template for the public library, and no
verification status is inherited from it. Every admitted public theorem must
be proved and audited in this checkout under the
[admission contract](../verification/README.md).

The mathematical proofs and the Lean library in this repository were produced
with language models used as drafting, proof-search, and coding agents, under
the direction and review of the repository owner, who decided what entered
the tree. The research proof this library distils was produced the same way.
No statement inherits verification status from that process. Every Lean
declaration admitted here was compiled and audited in this checkout:
[Verify.lean](../Verify.lean) records the `assert_no_sorry` check and the
discovered axiom set of every public theorem, and the [claim ledger](claims.md)
records the evidence tier of every prose claim. Model session logs,
transcripts, and research reports are not part of the source tree.

Raw reports, transcripts, review conversations, orchestration records,
abandoned branches, and exploratory output remain outside this repository.
The [selective transfer manifest](transfer-manifest.md) records the permitted
treatment by material category.

| Artifact | Required source record |
|---|---|
| Rewritten mathematical proof | Identify the reviewed material's role and make each public lemma self-contained. Private reports are not evidence. |
| Adapted Lean declaration | Retain the file-level notice and linked source inventory, describe changes, and establish verification status locally. |
| Rewritten example | Give exact input and expected result. Exploratory runs confer no theorem status. |

## External comparison result

The lower bound `C_* >= 1.960073002187` is credited to
[`satchlj/stoch-to-det-lower`](https://github.com/satchlj/stoch-to-det-lower).
Its theorem `StochToDet1960.exists_lower_bound_1960073002187` exhibits a
`12 x 12` witness and is checked there by a compiler-backed Lean certificate
using `native_decide`. No part of that certificate is transferred here. The
claim ledger records its external verification model; it is not a locally
kernel-verified result.

## Contribution and evidence

This repository provides a constructive explanation, a claim ledger, and a
Lean library organized by mathematical dependency. Its certificate-free
binary factor-nine proof gives an all-law deterministic bound, together with
full-support selector and selected-latent guarantees. The four public
headlines and their dependencies are locally audited; the general-alphabet
conjectures retain their separate evidence tier.

Attribution must distinguish rewrites, adaptations, and exact imports, and
identify the repository in which a claim was verified. A report, numerical
experiment, compiled proposition, or uninhabited Lean interface is not a proof
of the proposition it describes.
