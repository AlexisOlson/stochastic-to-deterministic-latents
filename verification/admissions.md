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
contains 72 modules and 754 theorem endpoints. Definitions, including
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
| [Binary.ScalarEstimates](../StochasticToDeterministicLatents/Binary/ScalarEstimates.lean) | 2026-09-03 | 70 | Logarithm, mixing, proxy, and seam tools |
| [Binary.Reduction](../StochasticToDeterministicLatents/Binary/Reduction.lean) | 2026-09-03 | 3 | Cost dominance over the canonical BinaryCode space |
| [Binary.FactorNine.NonpositivePhase](../StochasticToDeterministicLatents/Binary/FactorNine/NonpositivePhase.lean) | 2026-09-03 | 37 | Nonpositive scalar arm |
| [Binary.FactorNine.PositivePhase](../StochasticToDeterministicLatents/Binary/FactorNine/PositivePhase.lean) | 2026-09-04 | 64 | Positive scalar arm and chart cost under seam hypotheses |
| [Binary.FactorNine.SeamEndpoints](../StochasticToDeterministicLatents/Binary/FactorNine/SeamEndpoints.lean) | 2026-09-04 | 41 | Both seam estimates and unconditional chart cost |
| [Binary.FactorNine](../StochasticToDeterministicLatents/Binary/FactorNine.lean) | 2026-09-04 | 4 | All-law C9 and full-support latent/selector headlines |
| [Binary.FactorTwo.Shape](../StochasticToDeterministicLatents/Binary/FactorTwo/Shape.lean) | 2026-09-07 | 6 | Scalar curvature and shape lemmas for the chord margins |
| [Binary.FactorTwo.Defs](../StochasticToDeterministicLatents/Binary/FactorTwo/Defs.lean) | 2026-09-07 | 21 | Binary cubic, its top root, and the diagonal contact pair |
| [Binary.FactorTwo.Contact](../StochasticToDeterministicLatents/Binary/FactorTwo/Contact.lean) | 2026-09-07 | 12 | Affine majorants of $`\Phi`$ and the optimum at a contact pair |
| [Binary.FactorTwo.Touch](../StochasticToDeterministicLatents/Binary/FactorTwo/Touch.lean) | 2026-09-07 | 10 | Contact cells, the swap invariance, and the touching identity |
| [Binary.FactorTwo.RationalTest](../StochasticToDeterministicLatents/Binary/FactorTwo/RationalTest.lean) | 2026-09-07 | 4 | The positivity gate at a contact and at a constant optimum |
| [Binary.FactorTwo.NormBound](../StochasticToDeterministicLatents/Binary/FactorTwo/NormBound.lean) | 2026-09-07 | 2 | The norm bound from the positivity gate |
| [Binary.FactorTwo.Optimum](../StochasticToDeterministicLatents/Binary/FactorTwo/Optimum.lean) | 2026-09-07 | 3 | The stochastic optimum of a fully supported binary law |
| [Binary.FactorTwo.Orientation](../StochasticToDeterministicLatents/Binary/FactorTwo/Orientation.lean) | 2026-09-07 | 4 | Deterministic-score transport and the oriented region |
| [Binary.FactorTwo.Chord](../StochasticToDeterministicLatents/Binary/FactorTwo/Chord.lean) | 2026-09-07 | 38 | The diagonal chord, its two competitor margins, and their identification with the stochastic optimum at the chord point |
| [Binary.FactorTwo.ChordScalars](../StochasticToDeterministicLatents/Binary/FactorTwo/ChordScalars.lean) | 2026-09-07 | 6 | The chord's entropies as scalar expressions |
| [Binary.FactorTwo.SingletonScore](../StochasticToDeterministicLatents/Binary/FactorTwo/SingletonScore.lean) | 2026-09-07 | 2 | The isolating code's score and margin along the chord |
| [Binary.FactorTwo.Margins](../StochasticToDeterministicLatents/Binary/FactorTwo/Margins.lean) | 2026-09-07 | 11 | The two margins as scalar functions, and their two derivatives |
| [Binary.FactorTwo.Gates](../StochasticToDeterministicLatents/Binary/FactorTwo/Gates.lean) | 2026-09-07 | 8 | Three sufficient conditions for the chord margin, and the bounds from them |
| [Binary.FactorTwo.Strip](../StochasticToDeterministicLatents/Binary/FactorTwo/Strip.lean) | 2026-09-07 | 6 | The fixed cut, the root sign test, and the corner information |
| [Binary.FactorTwo.LogSeries](../StochasticToDeterministicLatents/Binary/FactorTwo/LogSeries.lean) | 2026-09-07 | 2 | The odd logarithm series with two error terms |
| [Binary.FactorTwo.LogValues](../StochasticToDeterministicLatents/Binary/FactorTwo/LogValues.lean) | 2026-09-07 | 5 | Decimal enclosures of `log 3`, `log 5`, `log 7`, `log 11` and `log 13` |
| [Binary.FactorTwo.ConstantRatio](../StochasticToDeterministicLatents/Binary/FactorTwo/ConstantRatio.lean) | 2026-09-07 | 1 | The constant margin's ratio term at the fixed cut, and its lower bound |
| [Binary.FactorTwo.SingletonRatio](../StochasticToDeterministicLatents/Binary/FactorTwo/SingletonRatio.lean) | 2026-09-07 | 1 | The singleton margin's ratio term at the fixed cut, and its pair bound |
| [Binary.FactorTwo.SingletonMass](../StochasticToDeterministicLatents/Binary/FactorTwo/SingletonMass.lean) | 2026-09-07 | 1 | The singleton margin's mass term, and the lower bound on its three scalar terms together |
| [Binary.FactorTwo.FixedCutConstant](../StochasticToDeterministicLatents/Binary/FactorTwo/FixedCutConstant.lean) | 2026-09-07 | 7 | The chord potential, its remainder at the fixed cut, and the entry to the constant scalar |
| [Binary.FactorTwo.ConstantBound](../StochasticToDeterministicLatents/Binary/FactorTwo/ConstantBound.lean) | 2026-09-07 | 1 | The constant margin's strict lower bound at the fixed cut, below an eighth of off-diagonal mass |
| [Binary.FactorTwo.SingletonBound](../StochasticToDeterministicLatents/Binary/FactorTwo/SingletonBound.lean) | 2026-09-07 | 1 | The singleton margin's strict lower bound at the fixed cut, below an eighth of off-diagonal mass |
| [Binary.FactorTwo.Center](../StochasticToDeterministicLatents/Binary/FactorTwo/Center.lean) | 2026-09-07 | 3 | The chord's midpoint law and the two margins' closed forms there |
| [Binary.FactorTwo.CertValues](../StochasticToDeterministicLatents/Binary/FactorTwo/CertValues.lean) | 2026-09-07 | 2 | The tangent certificate's four values at a contact law, and `Phi` there |
| [Binary.FactorTwo.CenterMajorant](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterMajorant.lean) | 2026-09-07 | 1 | A contact plane evaluated at the centre of a chord |
| [Binary.FactorTwo.Planes](../StochasticToDeterministicLatents/Binary/FactorTwo/Planes.lean) | 2026-09-07 | 2 | Four explicit reference laws and their planes in closed form |
| [Binary.FactorTwo.PlaneBound](../StochasticToDeterministicLatents/Binary/FactorTwo/PlaneBound.lean) | 2026-09-07 | 1 | The plane bound is concave in the imbalance |
| [Binary.FactorTwo.CenterLogValues](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterLogValues.lean) | 2026-09-07 | 8 | Decimal enclosures of eight more logarithms |
| [Binary.FactorTwo.PlaneEndpoints](../StochasticToDeterministicLatents/Binary/FactorTwo/PlaneEndpoints.lean) | 2026-09-07 | 4 | The plane bound exceeds one hundredth at eight endpoints |
| [Binary.FactorTwo.CenterSeam](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterSeam.lean) | 2026-09-07 | 1 | The constant margin at the centre, on the seam |
| [Binary.FactorTwo.CenterChart](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterChart.lean) | 2026-09-07 | 4 | The contact chart, its identities and its positivity |
| [Binary.FactorTwo.CenterFractions](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterFractions.lean) | 2026-09-07 | 9 | The chart's radial derivatives in closed form |
| [Binary.FactorTwo.CenterCurvature](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterCurvature.lean) | 2026-09-07 | 5 | The chart's second-order expressions along a ray |
| [Binary.FactorTwo.CenterRay](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterRay.lean) | 2026-09-07 | 4 | The ray of fixed imbalance and its critical radius |
| [Binary.FactorTwo.CenterLaws](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterLaws.lean) | 2026-09-07 | 7 | The chart and the laws it describes |
| [Binary.FactorTwo.CenterDerivatives](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterDerivatives.lean) | 2026-09-07 | 3 | Derivatives along a path in the chart |
| [Binary.FactorTwo.CenterDictionary](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterDictionary.lean) | 2026-09-07 | 3 | A chord law in the ray's coordinates |
| [Binary.FactorTwo.CenterSeamChart](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterSeamChart.lean) | 2026-09-07 | 3 | The seam, in the chart's radius |
| [Binary.FactorTwo.CenterSeamPositivity](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterSeamPositivity.lean) | 2026-09-07 | 3 | Signs on the seam |
| [Binary.FactorTwo.CenterSeamDerivative](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterSeamDerivative.lean) | 2026-09-07 | 4 | The seam's derivative |
| [Binary.FactorTwo.CenterSeamMargin](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterSeamMargin.lean) | 2026-09-07 | 2 | The margin along the seam |
| [Binary.FactorTwo.CenterRayMass](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterRayMass.lean) | 2026-09-07 | 5 | The mass along the ray |
| [Binary.FactorTwo.CenterRayMargins](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterRayMargins.lean) | 2026-09-07 | 7 | The margins along the ray |
| [Binary.FactorTwo.CenterEndpointMin](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterEndpointMin.lean) | 2026-09-07 | 2 | An endpoint minimum principle |
| [Binary.FactorTwo.CenterRayEnds](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterRayEnds.lean) | 2026-09-07 | 6 | The ray out to its ends |
| [Binary.FactorTwo.CenterRayBoundary](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterRayBoundary.lean) | 2026-09-08 | 3 | The ray's law at the critical radius |
| [Binary.FactorTwo.CenterRaySeam](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterRaySeam.lean) | 2026-09-08 | 5 | The seam radius on a ray |
| [Binary.FactorTwo.CenterEndpoints](../StochasticToDeterministicLatents/Binary/FactorTwo/CenterEndpoints.lean) | 2026-09-08 | 4 | The centre theorem |
| [Binary.FactorTwo.ContactPositive](../StochasticToDeterministicLatents/Binary/FactorTwo/ContactPositive.lean) | 2026-09-08 | 2 | A positive mutual information at the contact |
| [Binary.FactorTwo.Witness](../StochasticToDeterministicLatents/Binary/FactorTwo/Witness.lean) | 2026-09-08 | 2 | Five codes suffice for the factor-two bound |
| [Binary.FactorTwo](../StochasticToDeterministicLatents/Binary/FactorTwo.lean) | 2026-09-08 | 2 | The factor-two theorem |

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

The factor-two modules are a separate lane, and since 2026-09-08 they prove
two headline endpoints of their own, `T_le_two_mul_tau` and
`exists_witnessCode`. Shape
supplies the scalar curvature and shape lemmas the chord margins consume. Defs
fixes the binary cubic, proves its top root exists and is unique, and builds the
diagonal contact pair and its mixture. Contact supplies both sides of the
optimum at a contact pair: a two-point latent bounds $`\tau`$ above, and an
affine majorant of $`\Phi`$ bounds it below. Touch names the two diagonal cells
of the contact pair, proves that the two contacts carry the same $`\Phi`$
because the diagonal swap only relabels cells, and proves that at a root of the
cubic the tangent certificate at one contact is tight at the other as well.

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

Optimum closes the squeeze. Contact bounds $`\tau`$ above by a latent
built from the contact pair and below by any affine majorant of $`\Phi`$;
RationalTest verifies the gate at the contact and at a constant optimum;
NormBound turns the gate into the norm bound, which makes the tangent
certificate a majorant. What is left is to pair the certificate at one contact
with $`p`$, which the mixture and the equality of the two contact values of
$`\Phi`$ supply. The result is exact in both branches: below the geometric mean
of the diagonal, $`\tau(p) = \Psi(p) - \Phi(q_+)`$ at the upper contact
$`q_+`$; at it, $`\tau(p) = \Psi(p) - \Phi(p)`$. This is the exact stochastic
optimum for a fully supported binary law with nonnegative determinant, with no
gate hypothesis remaining, and it is the input the deterministic comparison
needs. It is not itself a bound on $`T`$, and no claim in the ledger changes
status here.

Orientation supplies the piece the symmetry module was missing.
`Binary.Symmetry` already carried $`\tau`$ across the group generated by the
row swap, the column swap, and the transpose, but not $`T`$; the transported
code makes the deterministic score invariant, and the finite code infimum then
transports by antisymmetry. With both optima invariant, three of the eight
symmetries carry an arbitrary fully supported law to one whose determinant is
nonnegative and whose diagonal and off-diagonal entries are each ordered, so a
multiplicative bound has only to be proved there. The last theorem removes the
orientation and, through `T_le_mul_tau_of_forall_fullSupport`, the
full-support hypothesis as well; it is a reduction, not a bound, and no claim
in the ledger changes status here.

Chord is where the deterministic side of the factor-two argument
begins. Sliding mass along the diagonal, holding the off-diagonal and the
diagonal total fixed, leaves the cubic unchanged, so `contactAt_chordAt` says
the contact pair -- and with it the value of $`\Phi`$ that module 7 subtracts
-- is the same at every point of the chord. The chord runs from the midpoint
of the diagonal to the upper contact; its ends are ordered, and a law with an
ordered diagonal lies on it. Two named deterministic competitors are measured
against the chord's budget: the constant code, whose score is $`\Psi - \Phi`$,
and the code isolating the last cell. If either margin is nonnegative
everywhere on the chord, then $`T(p) \le 2\,\tau(p)`$ at the law itself. That
is a reduction of the factor-two bound to a one-dimensional inequality, not a
proof of it, and no claim in the ledger changes status here.

Two facts are needed from outside the chord. `T_le_psi_sub_phi` bounds the
deterministic optimum by the mutual information, through the upstream bound and
`T_eq_upstream`; it is the deterministic counterpart of `tau_le_psi_sub_phi`.
`determinant_pos_of_nonconstant` shows that a fully supported law whose top
root falls below the geometric mean of its diagonal has a strictly positive
determinant, because at a vanishing determinant the cubic is negative at that
geometric mean. That is what lets the oriented region of the previous module be
taken at a nonnegative determinant while every chord statement asks for a
positive one.

ChordScalars makes the chord's entropies visible as scalar
expressions, which is what the one-dimensional argument downstream of it
differentiates. For a probability law the entropy is minus the sum of `xLogX`
over its values, so along the chord the law contributes four terms in the
moving coordinate and each marginal two. Since
$`\Psi(q) + \Phi(q) = 5\,H(q) - 3\,H(q_X) - 3\,H(q_Y)`$, the constant margin
is eight such terms together with the value of $`\Phi`$ at the fixed contact.
The library's information quantities are in bits and `xLogX` is in natural-log
units, so every statement here carries its explicit factor of `Real.log 2`
rather than absorbing the conversion. Nothing is proved about the sign of any
margin, and no claim in the ledger changes status here.

SingletonScore measures the chord's second competitor, the code that
gives the last cell its own label. Its labels are drawn from the canonical
label type, so two of the four labels carry no mass and contribute nothing;
three pushforwards are computed, the cell together with its label is the law
itself because the label is a function of the cell, and the two reversed pairs
are equivalences of the computed ones. The resulting score, and the margin it
leaves against the chord's budget, are sums of `xLogX` terms in the moving
coordinate. As in the previous module the statements are in natural-log units
with an explicit factor of `Real.log 2`. Nothing is proved about the sign of
the margin, and no claim in the ledger changes status here.

Margins names the two margins as functions of the diagonal mass, the
two off-diagonal cells, the contact's $`\Phi`$ and the moving coordinate, and
differentiates them twice. Because the library's scalar ledger is in
natural-log units, the second derivatives are exactly the expressions
`Shape.lean` already analyses: the constant margin's curvature is the left side
of `constantCurvature_eq_numerator_div`, and the isolating margin's is
`singletonCurvature_neg` at the complementary diagonal cell. The module also
records that the constant margin is stationary at the midpoint of the diagonal,
which is the hypothesis the endpoint comparison downstream needs, and that
every argument the derivatives are taken at is positive on the chord. No
inequality between the margins and zero is proved here, and no claim in the
ledger changes status.

Gates supplies three sufficient conditions for the chord reduction's
hypothesis, each checkable at one or two points. The constant margin has no
interior minimum, because its curvature changes sign at most once on the upper
half of the diagonal and its slope vanishes at the midpoint; so a nonnegative
value at the midpoint carries the whole segment, the upper end being the
contact's own mutual information. The isolating margin is concave, because its
curvature is negative throughout; so nonnegative values at the two ends carry
the segment, and a nonnegative value at the midpoint together with an interior
point where both margins are nonnegative covers it in two pieces.

`T_le_two_tau_of_gates` assembles those with the orientation and the constant
branch of the stochastic optimum: it proves $`T(p) \le 2\,\tau(p)`$ for every
probability law, from a hypothesis that is entirely one-dimensional. It is a
conditional theorem, not a proof of `BIN-C2`: the hypothesis compares explicit
scalar functions with zero at named points of an arbitrary chord domain, and
nothing here proves that comparison. No claim in the ledger changes status.

Three one-line positivity facts about a fully supported law -- that its
diagonal mass, its off-diagonal mass, and its off-diagonal product are positive
-- had been re-proved privately in four modules. They are public in
`FactorTwo.Defs` now and the copies are gone, which is why that module's
endpoint count rises by three without any new mathematics.

Strip supplies three things the quantitative estimates need. Below an
eighth of off-diagonal mass the smaller cell of the contact pair is below half
that mass -- `contactMass_lt_half_disagreement`, the first of the contract
page's five quantitative rows to be proved -- and therefore the point that
leaves three times that cell below it lies strictly inside the segment. A point
where the cubic is already positive lies beyond the top root, which is the
converse of the top root's defining property. And `cornerInfo`, the
unnormalized mutual information of a law with one zero corner, is squeezed
between $`bc\text/(a+b+c)`$ and $`bc\text/a`$.

None of these compares a margin with zero, so no gate is discharged and no
claim in the ledger changes status.

LogSeries banks the one tool every quantitative estimate uses: the odd
part of the series for $`\log((1+t)\text/(1-t))`$, truncated at any length,
with two error terms -- Mathlib's logarithm remainder and the geometric bound
on the omitted terms. `logRatioSeries_enclosure` brackets the logarithm by the
first; `logRatio_mem_of_side` says a short truncation brackets it as soon as a
longer one is seen to fall inside the short one's tail, which is the shape a
consumer wants: it names its own two lengths and its own rational point, and
discharges both hypotheses by `norm_num`. The module mentions no probability
law and imports nothing from this library.

LogValues turns that tool into the five numbers the estimates need.
Mathlib gives `Real.log 2` to nine places; each of `Real.log 3`, `Real.log 5`,
`Real.log 7`, `Real.log 11` and `Real.log 13` follows to eight from one
rational point, by writing the number as a power of two times
$`(1+t)\text/(1-t)`$ and bracketing that ratio. The arithmetic is `norm_num`
over finite sums of rationals: no `native_decide`, and the audit records the
standard three axioms for all five.

ConstantRatio is the first of the three scalar families under the
fixed-cut estimates. The constant margin at the fixed cut is bounded below by
`constantRatioTerm` at each of the two off-diagonal cells over the contact
cell, less explicit constants, and the only fact the estimate needs is
$`19\text/2 < V(x)`$ for every positive $`x`$. Below $`x = 1`$ that is the
tangent at $`1\text/2`$, whose intercept exceeds $`19\text/2`$ by about
$`0.0087`$; above it, monotonicity from $`V(1) = 14 \log 2`$. The two
constants of the tangent are settled here from the enclosures of `Real.log 3`
and `Real.log 7`, so the public theorem carries no numerical hypothesis. Like
Shape and LogSeries the module mentions no probability law, no code and no
information quantity.

SingletonRatio is the second family. The singleton margin's two
ratio terms are bounded together, not one at a time: at the fixed cut the two
ratios sum to at least $`2`$, and on that half plane
$`8 \log 2 - 6 \log 3 \le \psi(x) + \psi(y)`$. The proof restricts to the
symmetric slice $`x + y = 2`$, where the sum is stationary at $`x = 1`$ by
symmetry and has positive second derivative -- a cubic in $`(x-1)^2`$ after
clearing denominators -- and then carries the bound off the slice by strict
monotonicity of $`\psi`$ above $`1`$. The bound is exact: no decimal
enclosure enters it.

SingletonMass closes the three scalar families. Its own function is
concave in the contact cell on the fixed cut's box, so it is least at one of
the two ends; each end is antitone in the off-diagonal mass, so each is least
at $`v = 1\text/8`$, where it is an explicit combination of logarithms of
$`2`$, $`3`$, $`5`$, $`7`$, $`11`$ and $`13`$. What the module exports is not
that bound alone but `singletonTerms_gt`, the sum with the two ratio terms of
SingletonRatio, which the singleton estimate consumes directly: on the box the
three terms exceed $`1\text/100`$. Stating it that way keeps the two corner
values private, as the tangent constants are private in ConstantRatio.

FixedCutConstant carries the constant margin from the chord to that
scalar. The chord's potential $`\log 2 \cdot \Phi`$ is written as eight
`xLogX` terms in the small diagonal mass; its derivative vanishes at the
contact mass, which is Strip's root identity, and its second derivative is
bounded below on the small half of the chord. So the potential's decrease
from the contact mass to the fixed cut is at most a signed combination of
three elementary remainders, taken at the shifts zero and the two off-diagonal
cells, which is `chordPotential_remainder`.
The mutual information at the cut is written in the same terms, and
`constantRatioTerm_affine` divides the cell part by the contact mass to leave
exactly `constantRatioTerm` at the two ratios. The estimate itself is not
proved here; the module supplies the three identities and the three
inequalities a later assembly needs.

ConstantBound closes the constant arm. It rearranges Strip's contact identity
into the cell ratios at the two ends of the chord, adds those three
inequalities, and divides by the contact mass, which leaves two
copies of `constantRatioTerm` at the two ratios. Each exceeds
$`19\text/2`$ by ConstantRatio, and the terms they are set against are small
because the contact mass is: below an eighth of off-diagonal mass the contact
mass is under a sixteenth, so the upper contact is above thirteen sixteenths
and the two ratios there sum to less than $`2\text/13`$. What survives is
`fixedCut_constantMargin_gt`, a strict lower bound proportional to the contact
mass. It is stated multiplied through by $`\log 2`$, so no public statement
divides by that constant. This is one hypothesis of
`T_le_two_mul_tau_of_cutGates`, not the theorem; the singleton arm and the
midpoint hypothesis are separate.

SingletonBound is the other arm, and it is longer, because the singleton
margin does not reduce to its scalar by an identity alone. The margin at the
cut is written out against the chord potential at the contact mass, and
dividing by that mass leaves two copies of `singletonRatioTerm` and a
correction. Four estimates bound the correction below by `singletonMassTerm`:
the corner information at the upper contact is at least half the one at the
cut, the entropy of the contact mass has a quadratic tangent, `pairInfo` grows
over an interval by at most the slope at its left end times its length, and
two cell logarithms are dominated by twice the one at their mean.
`singletonTerms_gt` then bounds the three scalar terms together and leaves
`fixedCut_singletonMargin_gt`, in the same multiplied-through units as the
constant arm. With it and `fixedCut_constantMargin_gt`, two of the three
hypotheses of `T_le_two_mul_tau_of_cutGates` are supplied; the singleton
margin at the midpoint is not, and no declaration here proves the bound.

Chord gained the identification the two margins are named for. A point of the
chord strictly below the upper contact carries the same chord domain and the
same top root -- the determinant stays positive because the top root exceeds
the geometric mean of the off-diagonal, and the diagonal product stays above
$`u^2`$ -- so `tau_eq_chord`, public when this was written and privatized on
2026-09-08 as recorded below, applies at that point and the chord budget there
is twice its own stochastic optimum. Hence
`constantMargin_eq_two_mul_tau_sub` and `singletonMargin_eq_two_mul_tau_sub`:
the two margins are $`2\,\tau - I`$ and $`2\,\tau - S_{11}`$ at the chord
point, which is what the ledger's factor-two rows mean by them. The upper
contact is excluded, where the diagonal product falls to $`u^2`$ and the law
is constant-optimal; `constantMargin_chordTop` covers that end separately.

Center names the chord's midpoint law and says what the two margins are there.
Both marginals coincide at the midpoint, so the row and column entropies of
Margins collapse to one number and the four cells are fixed by two: the
off-diagonal mass $`v`$ and the imbalance $`z = (b - c)\text/v`$.
`centerConstantScalar` and `centerSingletonScalar` are the two margins written
in those coordinates, and `log_two_mul_constantMargin_center` and
`log_two_mul_singletonMargin_center` identify them with the margins at
`chordMidpoint p`, in natural-log units. `chordDomain_center` is the midpoint
case of `chordDomain_chordAt`, which this module's use makes public. Nothing
here bounds either margin; the module supplies the coordinates in which the
centre's estimates are stated.

CertValues evaluates the tangent certificate of
[Contact.lean](../StochasticToDeterministicLatents/Binary/FactorTwo/Contact.lean)
at a contact law, where the diagonal cells multiply to $`u^2`$ and the cubic
vanishes at $`u`$. Under those two hypotheses each of its four values is the
logarithm of a rational function of the cells: the two diagonal values are
`certDiagonal` of the diagonal mass and $`u`$, equal to one another, and the two
off-diagonal values are `certOffDiagonal` in the two orders. Pairing that
certificate with the law it was built at gives `Phi` there, so
`log_two_mul_phi_contact` states `Phi` in the same three logarithms, in
natural-log units. Nothing here is a bound; the module makes an explicit
reference law's certificate computable in closed form, which is what a later
module needs in order to use one as an affine minorant.

CenterMajorant turns a contact plane into a bound at a chord's midpoint, for two
independent laws: the plane may come from one chord domain's contact and be
evaluated at another's centre. The mechanism is that a contact plane does not
distinguish the two diagonal cells, which is the first two components of
`tangentCert_contact_values`; the chord moves mass only between those cells and
holds their sum fixed, so the pairing is constant along the chord, and the
contact is one of its points. The majorant itself is the route
`tau_eq_contact` already takes, through `positivityGate_contactAt`,
`normBound_of_positivityGate`, and `majorizes_tangentCert_of_normBound`. The
module supplies no number; it says where a plane may be evaluated.

Planes supplies four explicit rational laws for `CenterMajorant` to draw a plane
from. `chordDomain_referencePlane` checks all seven chord-domain conditions on
each, and `tangentCert_referencePlane` evaluates each plane at its contact
through `CertValues`: three rational numbers per plane, the two diagonal cells
sharing one. Every step is `fin_cases` over the four followed by `norm_num` on
explicit rationals. Nothing here says which plane applies to which imbalance,
and no bound is stated.

The first plane's contact is the reference law
$`q_{\mathrm{r}} = (112, 8, 8, 7)\text{/}135`$ of the factor-two page, with the
page's constants $`K = 375\text{/}343`$ and $`P_b^2\text{/}b^3 = 375\text{/}8`$;
the plane's own law is the midpoint of that contact's chord, which carries the
same plane.

PlaneBound fixes the off-diagonal mass at $`1\text{/}8`$ and the split between
the two off-diagonal cells at $`(1 \pm z)\text{/}16`$, pairs a reference plane
against that law, and feeds the result to `centerConstantScalar`, giving a
function of the imbalance $`z`$ alone. `centerPlaneBound_concaveOn` proves that
function concave on $`[0, 1]`$ from a nonpositive second derivative, through
`concaveOn_Icc_of_hasDerivAt2_nonpos`. The second derivative,
$`-5\text{/}(8(1 - z^2)) + 6\text{/}(64 - z^2)`$, does not mention the plane at
all: a plane contributes only a term linear in $`z`$. So no positivity of a
plane's three values is needed, and the same concavity serves all four.

The constant fed to `centerConstantScalar` carries the sign the certificate
gives it, $`(7\text{/}8)\log K - ((1+z)\text{/}16)\log L_b -
((1-z)\text{/}16)\log L_c`$, which is `Real.log 2` times the pairing of
`tangentCert_referencePlane` against `cellTable` at those weights;
`centerConstantScalar` subtracts twice its argument because that argument is
the contact's $`\Phi`$ in natural-log units. No bound on a margin is stated
here: that step needs the pairing inequality.

CenterLogValues adds $`\mathrm{log}`$ at 17, 19, 23, 47, 173, 179, 313 and 3581,
each to eight places except 3581, which is to three units in that place. It is
a second module rather than an extension of
[LogValues](../StochasticToDeterministicLatents/Binary/FactorTwo/LogValues.lean)
because that one is admitted and its five endpoints are recorded above; the two
are the same four-step proof at different points. Every one of the centre's
numeric comparisons is against a ratio of products of these eight primes and
the earlier six, so an integer combination of the thirteen enclosures and
Mathlib's $`\mathrm{log}\,2`$ replaces a separate series estimate at each
ratio. The points here are coarser -- 3581 needs $`t`$ near $`0.27`$ where 11
needed $`3\text{/}19`$ -- and six series terms still suffice at every one of
them: the widest tail is $`7.6 \times 10^{-9}`$. No law, code or margin appears
in this module, and it states no comparison.

PlaneEndpoints evaluates the plane bound at the two ends of the interval each
reference plane governs and shows it exceeds $`1\text{/}100`$ there. The four
intervals $`[0, 1\text{/}3]`$, $`[1\text{/}3, 2\text{/}3]`$,
$`[2\text{/}3, 19\text{/}20]`$ and $`[19\text{/}20, 1]`$ cover $`[0, 1]`$, so
with `centerPlaneBound_concaveOn` these eight numbers are what a lower bound
over the whole range of the imbalance would rest on. That step is not taken
here: no law, code or margin appears in the module, and no bound on a margin is
stated.

Unfolding the definitions at a rational $`z`$ leaves a rational combination of
logarithms of rationals -- the two diagonal cells give
$`\mathrm{log}\,(7\text{/}16)`$, the off-diagonal cells
$`\mathrm{log}\,((1 \pm z)\text{/}16)`$, the two marginals
$`\mathrm{log}\,((8 \pm z)\text{/}16)`$, and the plane its three values.
Twenty-eight such rationals occur across the eight, and every one factors over
the fourteen primes enclosed by LogValues and CenterLogValues; all fourteen are
used and no other prime occurs. A private table of twenty-eight equations
rewrites each logarithm into that basis exactly, and `linarith` applies the
enclosures once, at the end. That is why the table holds equations rather than
enclosures: bounding each of eight terms separately would compound the
enclosure error eight times over. The smallest slack over $`1\text{/}100`$ is
about $`2.6 \times 10^{-3}`$, against an accumulated enclosure error near
$`3 \times 10^{-7}`$.

CenterSeam is the first module of this route to bound a margin. For a chord
domain whose off-diagonal mass is exactly $`1\text{/}8`$,
`seam_constantMargin_center_gt` puts the constant margin above
$`1\text{/}100`$ nats at the centre of the contact chord. As with the fixed
cut, the bound is stated multiplied through by $`\log 2`$, so no public
statement divides by it.

Three steps join. The contact's $`\Phi`$ is at most its pairing against any
reference plane's certificate; the two diagonal cells of the chord at any
parameter sum to its diagonal mass, so that pairing collapses to three
terms and the step needs no hypothesis on the off-diagonal mass. On the seam
those three terms are exactly the constant fed to `centerPlaneBound`, because
the diagonal mass is $`7\text{/}8`$ and the two off-diagonal cells are
$`(1 \pm z)\text{/}16`$. Since `centerConstantScalar` **subtracts** twice its
argument, the plane bound then lies below the margin. Finally the four
intervals cover $`[0, 1]`$ and concavity puts the plane bound above
$`1\text{/}100`$ on each. The certificate is in bits and the scalar in nats;
the one multiplication by $`\log 2`$ is where they meet.

The plane index is produced existentially rather than by a nested conditional,
which is possible because the step from a plane's bound to the margin holds for
every one of the four.

CenterChart opens the centre's other arm and states nothing about a law. Along
the contact chord the cubic's positive root rescales the two off-diagonal
cells, and everything above this module depends on the rescaled pair only
through its sum $`r`$ and product $`\omega`$. `ChartDomain` is the resulting
parameter set and the six scalars are the chart's normalizer, the cubic's root,
the off-diagonal mass, the diagonal mass, the off-diagonal product and the
discriminant.

Two of the four theorems say what the chart is. `chartRoot_cubic` shows the
root solves the cubic by construction: the polynomial collapses to
$`u^2 (u \cdot n - \omega)`$, which vanishes because $`u = \omega\text{/}n`$.
The page proves the same identity in the other direction, dividing the cubic to
reach $`u_0 n = \omega`$; here that equation is the definition and the cubic's
vanishing is the consequence, which is the page's converse paragraph.
`chartDiscriminant_eq` identifies the curvature input with the cubic's
discriminant $`v^2 - 4w`$. Both were run as a scratch `example` against
[Defs](../StochasticToDeterministicLatents/Binary/FactorTwo/Defs.lean) before
the module was written, and they are what fixed the public names: these are the
library's own three quantities and its cubic root, in coordinates.

`chart_identities` proves the three entries of the page's display (3.4) that
are not definitional here, and `chart_pos` collects the positivity every
consumer needs, so that no module above this one re-derives it. The private
source proves that positivity and then never uses it, three later modules
re-deriving what they need; six of its declarations, a pair of two-variable
polynomials with their positivity and a pair of denominators with theirs, are
consumed by nothing in the whole transfer closure and were dropped.

CenterFractions carries the radial derivatives the page computes from the
cubic, in that chart and in closed form: the cubic's own derivative at the
root, the quantity $`u^2 - w`$, the root's radial derivative, the part of the
two contact masses' derivatives that does not depend on the cell, and the
radial derivative of $`\log K`$. Each is proved equal to an explicit ratio of
polynomials in $`r`$ and $`\omega`$.

`chartLogKDeriv_eq` is the right side of the page's display (3.7).
`chartFactors_pos` is the page's own list of positive factors, and every
denominator in the module is one of them.

CenterCurvature carries the three second-order expressions the page's
Lemma 3.4 and Lemma 4.3 use, in the same chart. `chartContactSecondOrder` is
the right side of display (3.9), and `chartContactSecondOrder_eq_logKDeriv`
proves it equal to the radial derivative of $`\log K`$, which is the page's own
step from (3.9) to (3.7) reached by carrying both sides to one closed form
rather than by its cancellation of a factor $`v + s`$.
`chartContactSecondOrder_lt` is display (3.8), and
`chartConstantSecondOrder_neg` and `chartSingletonSecondOrder_neg` put the two
expressions of display (4.3) below zero on the chart domain.

**No module here differentiates anything.** That these expressions are the two
margins' second radial derivatives is the analytic half of Lemma 4.3; it is
stated in CenterRayMargins below, not here. The concavity along a ray that it
and the two negativity results give together is stated nowhere. Nothing in the
three modules bounds a margin, and none of them mentions a law.

CenterRay is the first module of this apparatus that does mention a law. It
defines the ray of fixed imbalance the centre argument runs along, on the
public `tableOfEntries`, and proves that every law on the closed ray is a
probability law with full support at positive radius; that the critical radius
lies in $`(0, 1)`$ with its mass in $`[1\text/4, 1\text/3)`$ and the chart's
interior condition vanishing there; the test for a radius being below it; and
the mass and root at it. The private cell constructor is not ported:
`tableOfEntries` is the same map with the same row-major order, checked cell by
cell.

This ties the chart's parameters to laws -- radius $`r`$ and product
$`\kappa(z)\,r^2`$ -- and does no more. No declaration in it bounds a margin
or differentiates anything.

CenterLaws supplies the correspondence between the chart and the laws, in both
directions. `chartDomain_of_chordDomain` is the forward direction of the
correspondence in the page's Lemma 3.3:
a chord domain's two off-diagonal cells, rescaled by its top root, are positive
and ordered, they satisfy `ChartDomain`, and that root is the chart's root.
`chart_certValues` is display (3.5), stated through the two public certificate
values rather than the page's contact masses. `log_two_mul_phi_contact_chart`
evaluates $`\log 2 \cdot \Phi`$ at a chord domain's contact as minus the new
definition `chartHeight` at those coordinates, in nats. `chartDomain_ray` and
`chordDomain_rayLaw` run the other way: a radius strictly inside the critical
one puts the ray's parameters in the chart domain and makes the law there a
chord domain. `rayLaw_chartCoordinates` and `rayRoot_eq_chartRoot` identify
that law's own chart coordinates with the radius and the ray's product, which
is what makes the two directions compose. Nothing in the module differentiates
anything.

CenterDerivatives is the first module of this group that does.  It moves along
a path in the chart -- the two rescaled cells are differentiable functions of a
real parameter -- and differentiates three things along it.
`hasDerivAt_chartRoot` gives the root's derivative, the quotient rule's value;
`hasDerivAt_log_certDiagonal` gives the diagonal certificate value's logarithm;
and `hasDerivAt_chartHeight` gives the height, whose derivative is the page's
display (3.3) contracted against the path's velocity in the contact's two
off-diagonal cells: the first cell's coefficient uses `certOffDiagonal b c u`
and the second's uses `certOffDiagonal c b u`, that value not being symmetric
in its first two arguments.  The path's root derivative is a hypothesis of the last
two, discharged by the first.  These are derivatives along an **arbitrary**
path, and nothing in this module connects them to the radial expressions of
`CenterFractions`.  CenterRayMargins below connects `chartRootDeriv`;
`chartCommonDeriv` is still not shown to be a derivative of anything, and
`chartLogKDeriv` is reached there only through its equality with
`chartContactSecondOrder`, never as the derivative of `log K` that its name
claims.

CenterDictionary joins the chart apparatus to the two margins.
`chordDomain_rayCoordinates` reads a chord law in the ray's coordinates: its
imbalance lies in `[0, 1)`, its off-diagonal mass over its top root lies
strictly between zero and the critical radius, and at that pair the ray's root,
off-diagonal mass and law are the chord law's own root, its own off-diagonal
mass, and the chord law recentred at its midpoint.  `rayConstantScalar` and
`raySingletonScalar` then write `Center`'s two centre scalars as functions of
the imbalance and the radius alone, and `rayConstantScalar_eq` and
`raySingletonScalar_eq` say that at a chord law's own coordinates they are that
law's two margins at the midpoint.  Nothing in the module bounds a margin or
differentiates anything.

CenterSeamChart collapses the chart to one parameter on the seam, that is,
on the locus of off-diagonal mass exactly `1 / 8`.  Six definitions carry
it: `seamProduct` is the product parameter forced by the radius,
`seamImbalanceSq` the square of the imbalance, `seamCellB` and `seamCellC`
the two rescaled off-diagonal cells, `seamSingletonScalar` the isolating
code's margin at the midpoint as a function of the radius alone, and
`seamLaw` the centre law of mass `1 / 8` and a given imbalance.
`chordDomain_seamCoordinates` reads a chord law of that mass in the radius:
the radius lies in `(1 / 2, 1)`, the seam's product parameter there is the
law's own off-diagonal product over the square of its root, the seam's
squared imbalance is the square of the law's own, and the seam's singleton
scalar is the law's isolating-code margin at the chord's midpoint.
`rayValues_of_seamRadius` runs the other way, taking a radius in that
interval at which the squared imbalance is nonnegative -- not every radius
there is -- and putting its chart parameters in `ChartDomain`, with the root,
the mass and the law there.  `exists_balanced_seamRadius` finds a radius carrying a balanced seam
law, which the page does not need because it parametrises the seam by the
difference of the two off-diagonal cells rather than by the radius.
`seam_topRoot_lt_quarter` is private: its content is the lower end of the
radius interval above.  The two foundation facts consumed, the converse of
the top root's defining property and the arithmetic-geometric bound on the
off-diagonal product, were already public in `Strip`.  Nothing in the module
bounds a margin or differentiates anything.

CenterSeamPositivity supplies every sign the seam's derivative calculation
needs.  `seamCells_pos` puts the two rescaled cells positive, strictly
ordered and below one, and both seam denominators positive, at any radius in
`(1 / 2, 1)` whose squared imbalance is strictly positive.
`seam_log_identity` collapses the combination of logarithms the derivative
produces into a single logarithm of a ratio; it is an identity in two
positive reals and mentions no seam quantity and no law.
`seam_logRatio_pos` puts that ratio above one.  Its proof factors the
difference of the two weighted cells through a quartic in their sum and
product, and shows that quartic positive by the substitution
`t = (2 r - 1) / (1 - r)`, under which it becomes a ratio of polynomials with
positive coefficients.  The quartic and its three lemmas are private here.
**This route is not the page's**: Proposition 4.6 bounds the isolating code's
seam derivative in the difference of the two off-diagonal cells through an
integral remainder inequality, and nothing in this module corresponds to a
display.  Nothing here bounds a margin or differentiates anything.

The module is slow: **five minutes and thirty-nine seconds**, against
twenty to fifty seconds for every other module of this lane.  The cost is one
`field_simp` and `ring` on a degree-seven rational identity.

CenterSeamDerivative differentiates the isolating code's margin along the
seam.  `hasDerivAt_seamImbalanceSq` gives the squared imbalance's derivative,
the new definition `seamImbalanceSqDeriv`, at every radius of `(1 / 2, 1)`,
and `seamImbalanceSq_strictMonoOn` puts the squared imbalance strictly
increasing there.  `hasDerivAt_seamSingletonScalar` is the margin's own
derivative: the squared imbalance's derivative, over thirty-two times the
imbalance, times the logarithm `seam_logRatio_pos` puts above zero.  It
carries the extra hypothesis that the squared imbalance is strictly
positive, which **excludes the balanced radius**, the imbalance in its
denominator being zero there.
**No declaration here concludes that the margin increases**, and none bounds
it; that is the next module's work.  The route runs through a closed form for
the height at the seam's two cells, then through two identities -- a
cancellation of every rational term and a collapse of every logarithm -- both
private, as are the eleven intermediate derivative lemmas.  The closed form
itself, `seamHeight_eq`, is public: it holds wherever the squared imbalance
is nonnegative, which includes the balanced radius, where the derivative
does not exist and the seam's bound is evaluated.  One theorem of the
private source, the derivative of half the imbalance, is dropped: nothing in
the transfer closure consumes it.  **This is not the page's route**, which
differentiates in the difference of the two off-diagonal cells rather than in
the radius.

CenterSeamMargin closes the seam.  `seamSingletonScalar_monotoneOn` says the
isolating code's margin is monotone on any interval running from a balanced
radius up, which is the conclusion CenterSeamDerivative supplied a derivative
for and did not draw; `seam_singletonMargin_gt` bounds the margin below by
`1 / (250 * Real.log 2)` bits at the chord's midpoint, for every chord domain
whose off-diagonal mass is one eighth.  The route is: the squared imbalance is
a square, so no law on the seam has a radius below the balanced one; the
margin's derivative is nonnegative above it; the margin is continuous down to
it; and at it a single reference plane, the first of the four, bounds the
margin below by a rational combination of six logarithms.  That combination is
resolved over the prime basis inside this module rather than by reopening
PlaneEndpoints, which holds the same six identities privately: what repeats is
proof text, and no logarithm enclosure is duplicated.  **Only the bound half of
the page's Proposition 4.6 is claimed.**  Its quadratic growth in the imbalance
appears nowhere; monotonicity in the radius stands in its place and is a
different statement.  Two theorems of the private source are kept private here:
the value at the balanced radius and the continuity that carries it.

CenterRayMass differentiates the ray's two rational coordinates in the
radius.  `hasDerivAt_rayRoot` and `hasDerivAt_rayMass` give the derivatives of
the chart's root and of the off-diagonal mass on the open interval from the
centre to the critical radius, the second through the new definition
`rayMassDeriv`; `rayMassDeriv_pos` puts that derivative above zero there, and
`rayMass_strictMonoOn` puts the mass strictly increasing on the closed
interval.  All four are consumed by modules still to come, so all four are
public.  **Nothing here is analytic**: no logarithm, no law, and no margin
appears, so the module crosses no unit or sign convention.  The one private
lemma is the positivity of the chart normalizer's two factors.

CenterRayMargins differentiates the two centre margins along the ray, twice.
**Its count rose from seven to eight on 2026-09-08 and fell back the same
day.**  A private `rayChartDomain` was promoted so that the next module
could use it -- and `CenterLaws` already had `chartDomain_ray`, the same
statement with the same proof, public and in scope, which the promotion
had not found.  The duplicate is gone and every use here and in
`CenterRaySeam` now calls `chartDomain_ray`, which had until then been
exported and used by nothing.
The page's radial derivative is in the off-diagonal mass, with the operator
`D = v d/dv`; Lean differentiates in the radius, so every value here carries
the factor `rayMassDeriv`, which is `dv/dr` and which `CenterRayMass` puts
above zero strictly inside the ray.  Dividing it out is the change of
variable.

`hasDerivAt_rayHeight` differentiates the contact height along the ray,
exhibiting the new definition `rayHeightSlope` as `dk/dv`.
`hasDerivAt_rayConstantScalar` and `hasDerivAt_raySingletonScalar` do the
same for the two margins already defined in `CenterDictionary`, exhibiting
the new definitions `rayConstantSlope` and `raySingletonSlope`.
`hasDerivAt_rayHeightSlope`, `hasDerivAt_rayConstantSlope` and
`hasDerivAt_raySingletonSlope` differentiate the three slopes again, with
values the chart's second-order expressions over the mass squared.  Dividing
by `rayMassDeriv` twice, these are the page's display (3.7) for the height
and the two equalities of display (4.3) for the margins.

`chartRootDeriv_mul_rayMassDeriv` is the seventh: `chartRootDeriv` times the
mass's derivative is the mass times the root's derivative, so that expression
is `v du/dv`.  It is the first declaration in the tree that ties any of
`CenterFractions`' radial expressions to a derivative, and it is exported
under the ledger clause of the admission rule rather than because a later
module consumes it: the claim ledger named `chartRootDeriv` as an expression
no declaration exhibited, and the ledger paragraph is rewritten in the same
commit.

**No sign, monotonicity or bound is claimed.**  Display (4.3) is two chains:
each expression is bounded by an explicit negative quantity, and that
quantity by zero.  Only the conclusions are stated in this tree.
`chartConstantSecondOrder_neg` and `chartSingletonSecondOrder_neg`, admitted
earlier, say that the two expressions are negative; the intermediate bounds
`-3v/(1+v)` and `-v(1-2v)/(1-v^2)` the display passes through appear only as
steps inside those proofs, fused by `linarith`, and no declaration states
them.  Nothing composes that negativity with the equalities proved here into
concavity, and the composition is not immediate, since these derivatives are
in the radius and the page's concavity is in the mass.

CenterEndpointMin is the centre arm's counterpart of Shape: pure real
analysis, every statement quantifying over arbitrary real functions, with no
law, code, chart, margin or information quantity anywhere in the module and
nothing from this library imported.  It states one principle in two forms.
A function continuous on a closed interval whose derivative there is a
positive weight times an antitone factor rises and then falls, so it takes no
interior value below both endpoint values; that is the private
`min_endpoints_le_of_antitoneSlope`.  Its public form
`min_endpoints_le_of_antitoneSlope_affine` subtracts an affine function of a
second function `V` whose derivative is the same weight, which shifts the
antitone factor by a constant and leaves it antitone.  The wrapper
`antitoneOn_Ioo_of_hasDerivAt_nonpos` turns a nonpositive derivative on an
open interval into antitonicity on it; it is the twin of Shape's private
`antitoneOn_of_hasDerivAt_nonpos`, which is stated on a closed interval and
so needs the continuity hypothesis this one derives, and neither serves for
the other.  **No claim status changes.**  Nothing in the module is evidence
for any display of the page. **Amended 2026-09-08**: it was applied by no
declaration when admitted, and `CenterRaySeam` applies it now.

CenterRayEnds carries the ray to the closed interval `[0, r_c]`.  Every
derivative of this arm is taken strictly inside, because that is where the
chart's interior condition holds, though the mass's strict monotonicity and
the chart normalizer's positivity already hold on the closed interval; what
the endpoint arguments still need is the height and the two margins at the
ends themselves.  `rayNorm_pos` puts the chart's normalizer positive
there, `continuousOn_rayMass` puts the off-diagonal mass continuous,
`rayHeight_eq` rewrites the contact height into the ray's coordinates, and
`continuousOn_rayConstantScalar` and `continuousOn_raySingletonScalar` put
both margins continuous on the closed interval.  One private lemma of an
admitted module, `rayNorm_factors_pos`, is lifted to public in CenterRayMass
in the same commit, since `chartFactors_pos` cannot serve, its `ChartDomain`
hypothesis failing at the centre.

`raySingletonScalar_zero` is the isolating code's margin at radius zero, and
it is `0`.  **That value is the `0 log 0 = 0` convention, not a limit**: the
mass and the root both vanish there, so every entropy term that carries
either of them is `xLogX 0` and vanishes by the convention, while those
that remain have argument `1 / 2` and cancel, their coefficients summing to
zero.  It
is the pair -- that value together with continuity on the closed interval --
that gives the page's part (1) of Lemma 4.4, and even then only in the
radius: **no declaration in this tree states a limit**, and the page's
statement is a limit in the off-diagonal mass.  Of part (2), only the
continuity is here.  That the constant margin at the critical radius
equals the centre law's mutual information is proved in CenterRayBoundary,
the next module admitted below; **that it is positive there is still not
stated anywhere in this tree**.

**No bound is proved and nothing is differentiated.**

CenterRayBoundary is the far end of that same ray.  At the critical radius
the diagonal product `entryA * entryD` is exactly the square of the ray's
root, so the geometric mean of the diagonal is that root.  **No
`ChordDomain` holds there, at any top root**: such a domain's `nonconstant`
field would put its own root strictly below that mean and so strictly
below the ray's root, its `topRoot` field would then make the cubic
strictly positive at every larger point, and `rayLaw_cubic` says the cubic
vanishes at the ray's root.  Everything taking one --
`rayConstantScalar_eq` and `log_two_mul_phi_contact_chart` among them --
is unavailable; the route that would have supplied one is closed for the
matching reason, `chordDomain_rayLaw` asking for the chart's interior
condition `0 < 1 - r - 3 omega`, which degenerates to an equality at that
radius.  The module reaches `Phi` instead through
`log_two_mul_phi_contact`, which asks only for a fully supported probability
law, a positive root, and the two cubic conditions.  `rayLaw_coalesces` is the page's
`rho = 0` and `q^+ = p^o`: the contact radius vanishes and the upper contact
is the law itself.  `rayConstantScalar_boundary_eq` is then the
identification in part (2) of the page's Lemma 4.4: the constant code's
margin at the critical radius is
`Real.log 2` times the law's mutual information `Psi - Phi`.  **The module
mixes the two unit conventions on purpose** -- the margin is in nats and the
mutual information in bits -- and the factor of `Real.log 2` is what carries
the conversion, as in ChordScalars.

**The page's strict inequality is not proved.**  Lemma 4.4(2) states that
the mutual information there is *positive*, with a reason: the law is not a
product law.  `rayConstantScalar_boundary_nonneg` gives only `0 <= `, from
`psi_sub_phi_nonneg`.  The endpoint comparison still to come consumes only
the nonnegativity.  **Amended 2026-09-08**: the general strict inequality
is now proved, as `psi_sub_phi_pos` in ContactPositive, so the sentence
that once stood here -- that it was proved nowhere in this tree -- is no
longer true.  What is still missing is its hypothesis at this particular
law: nothing here computes the determinant of the law at the critical
radius, so this endpoint keeps its nonnegative form.

CenterRaySeam collects what a single ray of fixed imbalance contributes to
the endpoint comparison.  `exists_raySeamRadius` puts a radius strictly
inside every ray at off-diagonal mass exactly `1 / 8`: the mass is `0` at
the centre, at least `1 / 4` at the critical radius by
`criticalRadius_spec`, and continuous between them by
`continuousOn_rayMass`, so the intermediate value theorem applies.  This is
the page's remark that `1/8 < 1/4 <= v_c(z)` puts the seam inside every ray.

`rayConstantSlope_antitoneOn` and `raySingletonSlope_antitoneOn` put the two
margin slopes antitone on the open ray.  Each slope's derivative was
admitted in CenterRayMargins as the mass's derivative times a chart
second-order expression over the mass squared; `rayMassDeriv_pos` puts the
first factor above zero and `chartConstantSecondOrder_neg` and
`chartSingletonSecondOrder_neg` put the second below it, so the product is
nonpositive and `antitoneOn_Ioo_of_hasDerivAt_nonpos` concludes.

**These are stated in the radius, not in the off-diagonal mass.**  The
page's Lemma 4.3 is concavity of the two margins in the mass.  The mass is
strictly increasing in the radius -- `rayMass_strictMonoOn`, admitted in
CenterRayMass -- so the change of variable is available, but **no
declaration in this tree carries it out and none states the concavity**.

`rayConstantScalar_gt_of_seam` and `raySeam_margins_gt` read the two seam
bounds at the ray's own law.  `chordDomain_rayLaw` turns the chart domain
into a chord domain, three private lemmas recover the ray's coordinates
from that law, and `rayConstantScalar_eq` and `raySingletonScalar_eq`
transfer the admitted bounds.  **The two admitted bounds are stated in
different units in this tree**: `seam_constantMargin_center_gt` is already
in natural-log units, so the constant arm converts nothing, while
`seam_singletonMargin_gt` is in bits, so the isolating arm carries an
explicit `Real.log 2`.  Both crossings were checked as scratch examples
before the module was written.  The isolating arm's own statement is
private: it does not escape, and `raySeam_margins_gt` is what the endpoint
comparison consumes.

**No endpoint comparison is made here**, and nothing about a law off its
own ray is claimed.

CenterEndpoints closes the centre arm.  Both halves run the same way: a
chord domain sits at one radius on one ray of fixed imbalance, the seam
sits at another radius on that ray, the margin's slope is antitone
between them, and `min_endpoints_le_of_antitoneSlope_affine` therefore
bounds the margin, corrected by an affine function of the mass, below by
the smaller of its two endpoint values.  Both endpoint values are already
admitted.

`center_singletonMargin_ge` is the small-mass half.  Between the centre of
the ray and the seam the correction is `4/125` times the mass; at the
centre `raySingletonScalar_zero` makes both terms vanish, and at the seam
`raySeam_margins_gt` puts the margin above `1/250`, which is exactly what
the correction takes there.  `center_singletonMargin_nonneg` weakens it to
the form the gate assembly consumes.

`center_constantMargin_ge` is the large-mass half, between the seam and
the critical radius, with the affine function through the two known
endpoint values: `rayConstantScalar_gt_of_seam` at the seam and
`rayConstantScalar_boundary_nonneg` at the critical radius, where that
function is zero.  `center_constantMargin_pos` is strict, and **the
strictness does not come from the far endpoint**: it comes from the
bound's numerator, the mass at a radius strictly inside the ray being
strictly below its value at the critical radius by
`rayMass_strictMonoOn`.  So the positivity the page states at that
endpoint is still not proved in this tree and is still not needed.

**This is a different route from the page's.**  The page's step (2) argues
that a concave function with positive values at both ends is positive
throughout, which needs the far endpoint to be positive.  The affine
correction needs it only to be nonnegative.

**Units.**  `constantMargin` and `singletonMargin` are in bits and the ray
scalars are in natural-log units, so each bound carries a `Real.log 2` in
its denominator.  The ledger states the same bound in nats.

**The two gate wrappers of the private source are dropped.**  They inhabit
`Prop` abbreviations that have no counterpart here: `Gates.lean` takes the
inequalities directly.

Binary.FactorTwo is the top of the chain.  `gates_of_chordDomain` splits
on the off-diagonal mass and supplies, at every chord domain, the
disjunction `T_le_two_tau_of_gates` quantifies over: above an eighth
`center_constantMargin_pos` gives the first branch; at or below an eighth
the fixed cut is an interior point of the chord by `fixedCut_mem_chord`,
both margins are positive there by `fixedCut_constantMargin_gt` and
`fixedCut_singletonMargin_gt`, and `center_singletonMargin_nonneg` gives
the margin at the midpoint, which together are the third branch.  The two
cases overlap at an eighth, where either applies.

`T_le_two_mul_tau` is then `T p <= 2 * tau p` for every `IsPMF p`.

**The two fixed-cut bounds are in natural-log units** and against a
positive multiple of `chordBottom`, while the margins are in bits; each
conversion is one step against `Real.log_pos` and `chordBottom_pos`, and
all three conversions were checked as scratch examples before the module
was written.

**Five gate `Prop`s and six theorems parametrised by them are dropped.**
The private assembly declares `CenterSmallGate` and four siblings so that
the gate proofs can be supplied separately; `Gates.lean` took the other
route and takes the disjunction directly.  A duplicate of the endpoint
under a second name is dropped as well.

**What is not proved here.**  Nothing in this module exhibits a latent or a
code meeting the bound.  Amended 2026-09-08: the full-support witness
clause is proved in `Witness`, below, in its unlocated form; nothing in
this tree locates the singleton from the law, and nothing exhibits a law
and a code whose score *equals* twice the optimum.

**Chord's count fell from 42 to 36 on 2026-09-08.**  Six theorems --
`cubic_offDiagonalMass`, `determinant_ne_zero_of_nonconstant`,
`entryA_mem_chord`, `tau_eq_chord`, `constantMargin_entryA` and
`singletonMargin_entryA` -- were public but used only inside their own
module, so they are now private and their pins are gone.  **Nothing else
changed**: the module was rebuilt and the whole audit re-run.  This is
the privatizing rule applied to the six declarations that were carried
for it; a seventh candidate, `singletonRatioTerm_pair`, turned out to be
consumed by `SingletonRatio` and stays public.

**Two duplicates removed on 2026-09-08.**  `CenterRayMargins` held a
private copy of `rayRoot_eq_chartRoot`, identical to the public one in
`CenterLaws` in statement and proof, and reachable from it; the copy is
gone.  `CenterRayEnds` and `CenterSeamMargin` each held an identical
private continuity lemma for `xLogX` composed with a continuous
function; both are gone and one public `continuousOn_xLogX` sits beside
`xLogX` in ContactChart, whose count rises from 61 to 62.  **A third
candidate was not a duplicate**: `Shape`'s private
`antitoneOn_of_hasDerivAt_nonpos` is stated on a closed interval and
takes a continuity hypothesis, where `CenterEndpointMin`'s public
`antitoneOn_Ioo_of_hasDerivAt_nonpos` is stated on an open one and
derives it.

**Two redundant public theorems removed on 2026-09-08**, found by the
statement scan of the cleanup pass.  ContactChart's
`two_mul_highInformationLoss_le_offDiagonalLoss_of_information_order`
was an alias whose whole proof was one application of
`..._of_orientation` in the same file, used once and named in no
document; the one use now calls the original.  ScalarEstimates'
`mixtureMass_sum_eq_one_add_r` re-proved ContactChart's `e_add_ell`,
which it imports; its one use now calls that.  ContactChart falls from
62 to 61 and ScalarEstimates from 71 to 70.

**Two further duplicates were left in place, deliberately.**
`w3Cost_constantCode_eq_zero_of_subsingleton` is private in both
ContactChart and FactorNine, so removing the duplication would mean
**adding** public surface to delete a private copy, which is the wrong
direction for this tree.  `mixingKernel_rectangle_integrable` is private
in ScalarEstimates and public in NonpositivePhase, and merging them
would delete a long proof from an admitted module of the other arm
without changing the endpoint count at all.

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

## ContactPositive

**Admitted 2026-09-08.  An original argument for this tree, not a
transfer of adapted working material**, and the module carries no
adaptation notice for that reason.  The stronger claim that no proof of
this statement existed anywhere in the source workspace is **not** made:
that workspace was searched only narrowly, and it holds an information
floor of a different kind in a different setting.

Every earlier module in the lane stops at a *nonnegative* mutual
information, which is all `psi_sub_phi_nonneg` gives.  The chord-cut
argument's statement of the constant margin at the upper contact asks for
the strict inequality, and `BIN-CHORD-CUT` was held at `paper proof` for
exactly that one conjunct.

`psi_sub_phi_pos` supplies it in general: mutual information is the
divergence of a law from the product of its marginals, `log x <= x - 1`
bounds each of the four cells below by `q z - mX * mY`, those four bounds
sum to `1 - 1 = 0`, and `log x < x - 1` away from `x = 1` makes the sum
strict as soon as one cell differs from its marginal product.  On a binary
table the first cell differs exactly when the determinant does not vanish,
since `a - (a + b)(a + c) = ad - bc` for a law of total mass one.

`constantMargin_chordTop_pos` applies it at the upper contact.  The
contact's diagonal product is `u ^ 2`, so its determinant is `u ^ 2` less
the off-diagonal product, and the top root of a chord domain exceeds the
geometric mean of the off-diagonal.  That last fact was already proved and
private in Chord; it is promoted here rather than restated, as is
`sum_mul_logb_self` in Contact, which the cell-by-cell expansion of
`Psi - Phi` needs for the table and for both of its marginals.  Those two
promotions are the only changes of *interface* to admitted modules; the
statement scan was run first, and it is what found the Chord lemma. The
docstrings of CenterRayBoundary were also amended in the same commit,
where they described the strict inequality as unavailable anywhere in the
tree.

The endpoints move from 746 to 750: two promotions and the module's own
two.

## Witness

**Admitted 2026-09-08.  An original argument for this tree, not a
transfer**, like ContactPositive: no adapted working material supplied the
clause.  The two helper lemmas are not new mathematics; the private
per-file source record names their counterparts.  **Amended 2026-09-08**:
the module does carry an adaptation notice, added after this entry was
first written.  Its statement and argument are this tree's own, but two of
its short proof scripts follow the upstream repository's, one of them
restated here without the probability hypothesis it carries there, and the
notice credits that.

`T_le_two_mul_tau` bounds an infimum over the whole code space.  The
factor-two claim says more: on full support one of five named codes -- the
constant code or one of the four singletons -- already meets the bound.
That clause is `exists_witnessCode`, and the five codes are
`IsWitnessCode`.  It is not a sharpness claim.

Most of it was already present.  Bounding an infimum from above meant
exhibiting a competitor, and the chord argument's competitors are the
constant code and the code isolating the last cell; `chordMargin_witness`
in Chord is that step with the codes kept rather than dropped into the
infimum, and `T_le_two_tau_of_chordMargin` is now derived from it, so its
statement is unchanged.  Two things had to be added.

**The constant code's score.**  `T_le_psi_sub_phi` bounds `T` by the
mutual information through the constant *latent*, upstream, which names no
code.  `detScore_constantCode` computes the constant *code* directly:
conditioning on a constant changes no entropy, so both conditional entropy
terms vanish and the conditional mutual information is the plain one.

**Carrying a code through the orientation.**  `exists_oriented` recorded
only that the oriented law has the same two optima, which is all a bound
on `T` and `tau` needs; a named code needs the symmetry itself.  The three
orientation steps are therefore restated for an arbitrary property that
descends along one pushforward, as `of_oriented`, and the three previous
private helpers are **replaced** by it rather than duplicated:
`T_le_mul_tau_of_oriented` is re-derived as the instance where the
property is the bound itself, and its statement and axioms are unchanged.

Pulling a code back along a relabelling of the cells fixes the constant
code and sends the singleton at a cell to the singleton at its preimage,
so the five-code set is closed under the group.  **That is why the clause
names four singletons and not one.**

The full-support hypothesis is the clause's own and is not removed: the
sparse-law transfer preserves the two optima but not a code.

With this and ContactPositive, `BIN-C2` is `kernel-verified` in both of
its clauses.  The endpoints move from 750 to 754: `chordMargin_witness`,
`of_oriented`, and the module's own two.
