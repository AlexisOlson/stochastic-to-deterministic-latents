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
contains 43 modules and 649 theorem endpoints. Definitions, including
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
| [Binary.FactorTwo.Defs](../StochasticToDeterministicLatents/Binary/FactorTwo/Defs.lean) | 2026-09-07 | 21 | Binary cubic, its top root, and the diagonal contact pair |
| [Binary.FactorTwo.Contact](../StochasticToDeterministicLatents/Binary/FactorTwo/Contact.lean) | 2026-09-07 | 11 | Affine majorants of $`\Phi`$ and the optimum at a contact pair |
| [Binary.FactorTwo.Touch](../StochasticToDeterministicLatents/Binary/FactorTwo/Touch.lean) | 2026-09-07 | 10 | Contact cells, the swap invariance, and the touching identity |
| [Binary.FactorTwo.RationalTest](../StochasticToDeterministicLatents/Binary/FactorTwo/RationalTest.lean) | 2026-09-07 | 4 | The positivity gate at a contact and at a constant optimum |
| [Binary.FactorTwo.NormBound](../StochasticToDeterministicLatents/Binary/FactorTwo/NormBound.lean) | 2026-09-07 | 2 | The norm bound from the positivity gate |
| [Binary.FactorTwo.Optimum](../StochasticToDeterministicLatents/Binary/FactorTwo/Optimum.lean) | 2026-09-07 | 3 | The stochastic optimum of a fully supported binary law |
| [Binary.FactorTwo.Orientation](../StochasticToDeterministicLatents/Binary/FactorTwo/Orientation.lean) | 2026-09-07 | 3 | Deterministic-score transport and the oriented region |
| [Binary.FactorTwo.Chord](../StochasticToDeterministicLatents/Binary/FactorTwo/Chord.lean) | 2026-09-07 | 41 | The diagonal chord, its two competitor margins, and their identification with the stochastic optimum at the chord point |
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
$`u^2`$ -- so `tau_eq_chord` applies at that point and the chord budget there
is twice its own stochastic optimum. Hence
`constantMargin_eq_two_mul_tau_sub` and `singletonMargin_eq_two_mul_tau_sub`:
the two margins are $`2\,\tau - I`$ and $`2\,\tau - S_{11}`$ at the chord
point, which is what the ledger's factor-two rows mean by them. The upper
contact is excluded, where the diagonal product falls to $`u^2`$ and the law
is constant-optimal; `constantMargin_chordTop` covers that end separately.

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
