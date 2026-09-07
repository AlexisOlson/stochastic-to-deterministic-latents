# Admission record

The root imports every module listed below. All of each module's public
theorems were checked with `assert_no_sorry` and individually discovered axiom
sets in [Verify.lean](../Verify.lean). Thirty public `lemma` declarations in
TransposeNormalForm are not pinned separately; each is used only inside
audited proofs, where the audit covers it transitively. Pinning or
privatizing them is pending. The [verification guide](README.md)
gives the current procedure; the [claim ledger](../docs/claims.md) states
exact result scopes.

## Module coverage

Module names are relative to `StochasticToDeterministicLatents`. The table
contains 27 modules and 547 theorem endpoints. Definitions, including
proposition-valued definitions, are not counted as theorem evidence.

| Module | Admitted | Public theorems | Verified role |
|---|---|---:|---|
| [Information](../StochasticToDeterministicLatents/Information.lean) | 2026-09-01 | 8 | Finite probability and entropy |
| [Latent](../StochasticToDeterministicLatents/Latent.lean) | 2026-09-01 | 4 | Latent score and stochastic optimum |
| [Deterministic](../StochasticToDeterministicLatents/Deterministic.lean) | 2026-09-01 | 4 | Deterministic score and finite attainment |
| [Binary.Table](../StochasticToDeterministicLatents/Binary/Table.lean) | 2026-09-01 | 2 | Binary codes and support canonicalization |
| [Binary.Selector](../StochasticToDeterministicLatents/Binary/Selector.lean) | 2026-09-01 | 6 | Mathematical catalog and score-minimizing selector |
| [Binary.CountSelector](../StochasticToDeterministicLatents/Binary/CountSelector.lean) | 2026-09-01 | 4 | Structural count-selector lemmas |
| [Pricing](../StochasticToDeterministicLatents/Pricing.lean) | 2026-09-01 | 6 | Fixed-code identity, rebate, and PRICE(c) |
| [Bridge](../StochasticToDeterministicLatents/Bridge.lean) | 2026-09-02 | 23 | Upstream objective, contact, seed, and quotient interfaces |
| [Binary.Symmetry](../StochasticToDeterministicLatents/Binary/Symmetry.lean) | 2026-09-02 | 37 | Cell, code, and latent transport |
| [Binary.Chart](../StochasticToDeterministicLatents/Binary/Chart.lean) | 2026-09-03 | 15 | Transpose-chart law and two-arm cost identity |
| [Binary.ContactChart](../StochasticToDeterministicLatents/Binary/ContactChart.lean) | 2026-09-03 | 61 | Contact geometry, scalar ledgers, and bit conversions |
| [Binary.TransposeNormalForm](../StochasticToDeterministicLatents/Binary/TransposeNormalForm.lean) | 2026-09-03 | 56 | Selected optimizer quotient normal form |
| [Binary.CatalogRecovery](../StochasticToDeterministicLatents/Binary/CatalogRecovery.lean) | 2026-09-03 | 17 | Full-support equal-cost catalog recovery |
| [Binary.NormalForm](../StochasticToDeterministicLatents/Binary/NormalForm.lean) | 2026-09-03 | 32 | Selected one-class or contact-chart presentation |
| [SparseLimit](../StochasticToDeterministicLatents/SparseLimit.lean) | 2026-09-03 | 1 | Conditional transfer from full support to all laws |
| [Binary.ScalarEstimates](../StochasticToDeterministicLatents/Binary/ScalarEstimates.lean) | 2026-09-03 | 71 | Logarithm, mixing, proxy, and seam tools |
| [Binary.Reduction](../StochasticToDeterministicLatents/Binary/Reduction.lean) | 2026-09-03 | 3 | Cost dominance over the canonical BinaryCode space |
| [Binary.FactorNine.NonpositivePhase](../StochasticToDeterministicLatents/Binary/FactorNine/NonpositivePhase.lean) | 2026-09-03 | 37 | Nonpositive scalar arm |
| [Binary.FactorNine.PositivePhase](../StochasticToDeterministicLatents/Binary/FactorNine/PositivePhase.lean) | 2026-09-04 | 64 | Positive scalar arm and chart cost under seam hypotheses |
| [Binary.FactorNine.SeamEndpoints](../StochasticToDeterministicLatents/Binary/FactorNine/SeamEndpoints.lean) | 2026-09-04 | 41 | Both seam estimates and unconditional chart cost |
| [Binary.FactorNine](../StochasticToDeterministicLatents/Binary/FactorNine.lean) | 2026-09-04 | 4 | All-law C9 and full-support latent/selector headlines |
| [Binary.FactorTwo.Shape](../StochasticToDeterministicLatents/Binary/FactorTwo/Shape.lean) | 2026-09-07 | 6 | Scalar curvature and shape lemmas for the chord margins |
| [Binary.FactorTwo.Defs](../StochasticToDeterministicLatents/Binary/FactorTwo/Defs.lean) | 2026-09-07 | 18 | Binary cubic, its top root, and the diagonal contact pair |
| [Binary.FactorTwo.Contact](../StochasticToDeterministicLatents/Binary/FactorTwo/Contact.lean) | 2026-09-07 | 11 | Affine majorants of $`\Phi`$ and the optimum at a contact pair |
| [Binary.FactorTwo.Touch](../StochasticToDeterministicLatents/Binary/FactorTwo/Touch.lean) | 2026-09-07 | 10 | Contact cells, the swap invariance, and the touching identity |
| [Binary.FactorTwo.RationalTest](../StochasticToDeterministicLatents/Binary/FactorTwo/RationalTest.lean) | 2026-09-07 | 4 | The positivity gate at a contact and at a constant optimum |
| [Binary.FactorTwo.NormBound](../StochasticToDeterministicLatents/Binary/FactorTwo/NormBound.lean) | 2026-09-07 | 2 | The norm bound from the positivity gate |

## Axiom sets

All audited theorems report `[propext, Classical.choice, Quot.sound]` except:

| Theorem | Discovered set |
|---|---|
| `Binary.CountTable.activeCell?_eq_none_iff` | `[propext]` |
| `Binary.transportCode_transportCode` | `[propext, Quot.sound]` |

The namespace prefix is `StochasticToDeterministicLatents`. Verify pins each
set beside its theorem. In particular, each of the four FactorNine headlines
uses exactly `[propext, Classical.choice, Quot.sound]`.

Some public definitions use smaller sets too. For example, NormalForm's
`antiDiagonalSymmetry` uses no axioms and `chartTableSymmetry` uses `[propext]`.
They are definitions, so neither is included in the theorem count. The same
principle applies to the `StrictProxy*` and `SmallCatalogFactorEightWitness`
propositions: evidence comes from the theorems proving or using them.

## Claim promotions

The foundation queue was completed on 2026-09-01 in the order Binary.Table,
Binary.Selector, Binary.CountSelector, then Pricing. That admission promoted
`PRICE(c)` through `T_le_one_add_mul_tau_of_w3`.

On 2026-09-03, Reduction promoted `BIN-REDUCE`, restricted to the canonical
four-label `BinaryCode` space. The arbitrary-output reward argument remains
private and is not an audited cost theorem for another label type. The
infimum identity stated in the mathematical exposition is not a separate
public declaration.

On 2026-09-04, FactorNine promoted `BIN-W3-8` for full-support binary laws and
`BIN-C9` for every binary law. It also proves the mathematical selector's
factor-nine bound on full support. All other admissions in the table changed
no ledger tier. The count/rational refinement and the general-alphabet
conjectures retain their stated evidence tiers. The `BIN-CATALOG-RECOVERY`
row was narrowed on 2026-09-04 to the supplied-presentation recovery that
`CatalogRecovery`'s two audited theorems state, and reads `kernel-verified`
through them; it was not re-audited, and no declaration changed.

## How the binary admissions compose

TransposeNormalForm supplies a selected optimizer whose duplicate quotient
has one or two classes. NormalForm constructs a contact-chart presentation on
the two-class branch; the selected latent used downstream is the quotient.
These results do not assert a bound on the ambient optimizer's label count.

Chart identifies the cost of a supplied code. ContactChart expresses that cost
and the latent score in the scalar coordinates, with conversions between
natural-log quantities and bits. CatalogRecovery transports the selected chart
code to a literal member of the observable law's catalog on full support, using
equal $`\mathrm{W3Cost}`$ at a balanced tie. This does not require the
row-major representative itself to be equivariant.

ScalarEstimates provides the analytic tools. NonpositivePhase proves one
scalar arm. PositivePhase proves the other under two seam-positivity inputs,
and combines the arms into a conditional chart-cost bound. SeamEndpoints
proves both seam estimates and discharges those inputs. No scalar arm alone
establishes the selected-latent theorem.

FactorNine applies the chart bound to the selected optimizer and uses catalog
recovery and pricing. SparseLimit is a generic conditional theorem; supplying
its binary full-support premise at nine extends the `T` bound to all laws.
Finite deterministic attainment then supplies the existential code. This
composition gives neither a sparse selected-latent $`\mathrm{W3}`$ estimate nor
a sparse bound for the named selector.

## Factor-two admission checks

The factor-two modules are a separate lane and prove no headline yet. Shape
supplies the scalar curvature and shape lemmas the chord margins consume. Defs
fixes the binary cubic, proves its top root exists and is unique, and builds the
diagonal contact pair and its mixture. Contact supplies both sides of the
optimum at a contact pair: a two-point latent bounds $`\tau`$ above, and an
affine majorant of $`\Phi`$ bounds it below. Touch names the two diagonal cells
of the contact pair, proves that the two contacts carry the same $`\Phi`$
because the diagonal swap only relabels cells, and proves that at a root of the
cubic the tangent certificate at one contact is tight at the other as well.

RationalTest verifies the positivity gate in the two places the factor-two
argument needs it. Clearing the denominators turns the three gate quantities
into polynomials in the cells, and the gap between the two sides of the gate
then factors as a product of two balance forms. At the upper contact of a law
whose cubic has the root $`u`$ the contact relation $`AD = u^2`$ makes the
first balance form vanish, so the gate holds there with equality; at a law
whose top root has reached $`\sqrt{ad}`$, so that the stochastic optimum is
constant, both forms are only nonnegative and the gate holds as an inequality.
Every step is a `ring` identity in named indeterminates or a positivity
argument from the cells; the module introduces no analytic fact.

NormBound closes the certificate side. The gate expressions are the
coefficients of the norm-gate quartic, which Shape already proves nonnegative
on the half line from the gate inequality alone. That quartic is $`(x-1)^2`$
times the norm-gate polynomial of the law, so the polynomial is nonnegative
too, and weighted Hölder at the conjugate exponents $`3\text/2`$ and $`3`$
turns the resulting cube bound into `Binary.NormBound`. Hölder is the one
inequality the factor-two lane uses that is not a polynomial fact about the
cells. The two marginal positivity lemmas of Contact become public here,
because this module is their first consumer.

The lower bound is proved from `exists_optimalLatent` and `latent_score_eq`
alone, with no duality vocabulary in the statement; the majorant property is
carried as the explicit inequality `Binary.Majorizes`. The single duality fact
consumed, `phi_le_logCertificate_of_feasible`, was added to Bridge in its own
commit; it is the forward direction of an upstream equivalence, restated with
the upstream validity predicate unfolded.

The module states no unproved analytic fact. `Binary.majorizes_tangentCert_of_normBound`
takes the norm bound as a hypothesis; `Binary.PositivityGate` and the four gate
expressions are stated here without a consumer in this module, because the two
modules that reduce the gate to the norm bound and verify it on a chart both
import this one and neither imports the other. No claim in the ledger changes
status here.

## Factor-nine admission checks

The final three modules passed individual Lake builds, complete public-theorem
axiom discovery, trust scans, and adversarial source/prose review. Their
imports were tested by removal from external copies. PositivePhase needs
NonpositivePhase. SeamEndpoints needs PositivePhase; its redundant explicit
Mathlib integral import was removed. FactorNine needs SeamEndpoints,
NormalForm, and SparseLimit.

Each admission also passed the full root build and Verify. The audit contained
450 endpoints after PositivePhase, 491 after SeamEndpoints, and 495 after
FactorNine. Their source inventories and reconciliation counts are kept in
the private attribution record described in
[provenance](../docs/provenance.md#file-level-attribution).
