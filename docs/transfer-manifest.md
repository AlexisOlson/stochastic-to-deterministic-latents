# Selective transfer manifest

This manifest records publication decisions by material category. Unpublished
workspace identifiers are not evidence: every public claim must stand on the
exposition, source, and verification artifacts actually included here.

The decision words are normative:

- **rewrite**: restate the mathematics for this repository;
- **adapt**: retain selected proof or code structure with attribution and cleanup;
- **import**: preserve exact bytes when reproducibility requires them;
- **cite**: attribute without transferring content;
- **defer**: reconsider only when a current public claim needs the material; and
- **exclude**: keep the material outside the public repository.

## Decisions

| Decision | Material category | Public treatment | Gate |
|---|---|---|---|
| **rewrite** | Mathematical overview, binary factor-nine argument, and law-only selector | Present one mechanism-first narrative using the notation in [`blueprint.md`](blueprint.md). | State every analytic and formal input at its actual evidence tier. |
| **cite** | Finite probability, entropy, and stochastic-latent foundations | Reuse the exact upstream package through a pinned Lake dependency and expose thin descriptive facades; do not copy its implementation. | Pin a public commit, retain Apache-2.0 attribution, and verify every local theorem wrapper. |
| **rewrite** | Deterministic codes and objective | Define `T` directly over one fixed finite code space rather than bundled deterministic latents. | Prove nonnegativity, the pointwise upper bound, and finite attainment locally. |
| **cite** | Upstream envelope, duality, seed-setup, and clustering layer (`Envelope`, `Duality`, `Seed`, `Quotient`) | Reach it only through `Bridge.lean`: reducible aliases, exact restatements, and the two theorems identifying the local `detScore` and `T` with upstream's. No other public module imports those four upstream modules. | Every theorem in the bridge is audited in `Verify.lean`; its header retains the origin and modification notice, and `provenance.md` names each upstream declaration it descends from. |
| **adapt** | Exact `W3` identity, nonnegative rebate, minimizer, and pricing rule | Organize by mathematical dependency rather than source layout. | Re-run local no-`sorry` and axiom checks before changing claim status. |
| **adapt** | Exact binary geometry and finite-code reduction | Transfer one theorem dependency at a time with neutral public names. | Keep chart hypotheses and boundary scope explicit. |
| **rewrite** | Certificate-free binary factor-eight estimate | Present the two phase arguments and their exact finite rational-log ledgers without the research chronology. | Keep the selected-latent estimate restricted to full support. State the locally verified full-support selector bound separately from the all-law `T` bound and finite-code witness. |
| **rewrite** | Exact binary stochastic optimum: the rational constant-optimality test, the two-component bound on every support, the cubic locating the optimal pair, and the disagreement band | Present as one `paper proof` page under the public `Phi`, with every display re-derived rather than transcribed; ledger rows at `paper proof`; Lean targets in the contracts page. | Independent read against the source proofs and a cold read of the public tree before commit; the sympy replay script is not evidence; no row compares `tau` with `T`. |
| **adapt** | Exact count/rational selector core | Expose the determinant, endpoint-mass, support, and final-score tie rules. | Do not publish uninhabited interfaces as results. |
| **defer** | Sharper binary factor-five argument, its factor-four interval-certificate verifier, the certificate contract, and any immutable certificate inputs | Held for a later release; nothing from this route appears in this one. | Reconsider only with a standalone verifier having explicit directed rounding, complete domain coverage, deterministic fingerprints, and mutations that exercise every essential coefficient, orientation, and domain edge; exact input bytes only after provenance and license review, with SHA-256 values and generation origin recorded beside each input. |
| **rewrite** | Small exact worked cases | Add an example only when it exercises a public definition or theorem boundary. | Include exact input, selected code, and intended comparison. |
| **cite** | [`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det) | Credit the primary mathematical and Lean ancestor in the README, NOTICE, and adapted files. | Do not mirror its historical module layout. |
| **cite** | [`satchlj/stoch-to-det-lower`](https://github.com/satchlj/stoch-to-det-lower) | Cite the exact `1.960073002187` lower-bound theorem as external context for the universal constant. | State its compiler-backed `native_decide` verification model; do not vendor its certificate or call it locally kernel-verified. |
| **defer** | Local $`5 \times 5`$ lower-bound witness and support-subset certificate | Reconsider as a standalone public lower-bound artifact after the theorem-facing upper-bound release. | Require a clean verifier, exact witness data, provenance, and an independent replay before stating its numerical bound publicly. |
| **defer** | General-alphabet proof routes and large regression families | Add only a stable route or witness that clarifies a live public claim. | `GEN-W3-8` remains a conjecture. |
| **exclude** | Raw reports, transcripts, review conversations, orchestration records, abandoned branches, bulk exploratory output, and machine metadata | Do not transfer these artifacts. Rewrite only the mathematical fact that survives review. | Relevant facts must enter through a claim, proof, example, or provenance note. |

## Release sequence

A public release may present several results with different constants,
construction guarantees, and evidence tiers. The README and claim ledger must
keep those differences visible.

The certificate-free binary factor-nine theorem requires a self-contained paper
proof, an accurate claim ledger, and the audited public Lean theorem and its
admitted dependencies. The exact binary stochastic optimum is presented at
`paper proof`, with its Lean targets stated and unproved. The sharper
factor-five argument and its interval certificate are deferred to a later
release and do not appear in this one.

## Artifact status and remaining work

The table lists the admitted library and the deferred artifacts of the held
sharper route. Local audits are in the
[admission record](../verification/admissions.md).

| Public artifact | Current role | Remaining work |
|---|---|---|
| `docs/blueprint.md`, `docs/binary-factor-nine.md` | Construction and complete certificate-free C9 proof | Keep the full-support selector and selected-latent guarantees distinct from the all-law bound on `T`. |
| `docs/binary-stochastic-optimum.md`, `scripts/check_stochastic_optimum_identities.py` | Paper-proof exposition of the exact binary stochastic optimum, with a sympy replay of its identities | Blueprint nodes for its four rows; Lean proofs of the target signatures in the contracts page. |
| `Pricing.lean` | Audited pricing identity, rebate, minimizer, and conditional theorem | Supplies the factor $`1+c`$ when an optimal latent's cost bound is given. |
| `Binary/Table.lean`, `Binary/Selector.lean` | Audited table, support, catalog, and mathematical-selector interfaces | General support-partition canonicalization and executable refinement remain target contracts. |
| `Binary/CountSelector.lean` | Executable count/rational definitions and audited structural lemmas | Prove normalization, score-key, support, and count/rational-to-real refinement. |
| `Binary/Reduction.lean` | Audited cost dominance over canonical `BinaryCode` | Preserve its supplied-chart and output-alphabet scope. |
| `Binary/FactorNine.lean` | Four audited numerical endpoints | All-law `T` and existential-code C9; full-support selector C9 and selected-latent W3 factor eight. |
| `docs/binary-theorem.md`, `docs/factor-four.md` | Deferred: factor-five proof decomposition and analytic certificate contract, held for a later release; absent | Publish only with the completed factor-four lemmas, finite ledgers, and public certificate replay. |
| `Binary/FactorFive.lean` | Deferred with the route; absent | Any conditional composition must retain its supplied factor-four premise. |
| `verification/factor_four/README.md` | Deferred: certificate contract, held with the route; absent | Directed arithmetic and exhaustive coverage with pinned MPFR/GMP behavior. |
| `verification/factor_four/src/compact_interface.c`, `replay.py`, `mutations.py` | Deferred verifier and replay artifacts; absent | Deterministic failure and fingerprints, immutable-input hashes, normal/optimized comparisons, and mutations reaching every theorem-relevant coefficient, orientation, and boundary check. |
| `examples/README.md` | Exact selector branch examples | Keep examples distinct from numerical-bound evidence and executable-refinement proofs. |

## Transfer rule

Each adapted source file retains a concise origin, license, and modification
notice. The per-file record of adapted source declarations, local adaptations,
and private-helper accounting is kept privately, outside the public tree, and
must be reconciled against the source whenever a file changes. Each imported verification input
requires its hash and generation origin. Material outside the current proof
dependencies remains deferred or excluded.

Before a public release, every outward mathematical rewrite must receive an
independent source check against the underlying artifacts. The release review must
also confirm that the README and claim ledger agree, notation follows
[`blueprint.md`](blueprint.md), all public links resolve, no private workspace path
appears in tracked files, and no report, transcript, audit bundle, campaign record,
or generated build artifact has entered the tree.
