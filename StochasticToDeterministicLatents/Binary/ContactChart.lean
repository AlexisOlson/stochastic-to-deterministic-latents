import StochasticToDeterministicLatents.Binary.Symmetry
import StochasticToDeterministicLatents.Binary.Chart
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Binary contact charts and their scalar ledger

This module adds the strict common-contact geometry to a transpose chart,
extracts its four-scalar analytic chart, and records the exact homogeneous
natural-log ledger used by later estimates.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents.Binary

noncomputable section

/-! ## Bundled contact geometry -/

/-- A transpose chart equipped with a feasible common-contact kernel and strict
contact geometry.

Every field is a hypothesis, not a result. In particular `attained` assumes
that the chart's latent achieves the stochastic optimum: nothing in this module
constructs such a chart or proves one exists, and no theorem below establishes
optimality. The `ratio` field is the homogeneous coordinate `x ^ 4`, and is a
different quantity from `ScalarContactChart.ratio`. -/
structure ContactChart extends TransposeChart where
  kernel : Cell → ℝ
  lowMass : ℝ
  ratio : ℝ
  highMass : ℝ
  norm : ℝ
  lowMass_pos : 0 < lowMass
  ratio_pos : 0 < ratio
  highMass_pos : 0 < highMass
  norm_pos : 0 < norm
  norm_eq : norm = lowMass + 1 + ratio + highMass
  a_eq : toTransposeChart.a = lowMass / norm
  b_eq : toTransposeChart.b = 1 / norm
  c_eq : toTransposeChart.c = ratio / norm
  d_eq : toTransposeChart.d = highMass / norm
  ratio_lt_one : ratio < 1
  contactGap : lowMass * highMass < ratio
  strictOrder : toTransposeChart.c < toTransposeChart.b
  feasible : Feasible (Finset.univ : Finset Cell) kernel
  firstComponent_contact :
    IsContact (Finset.univ : Finset Cell) kernel toTransposeChart.firstComponent
  secondComponent_contact :
    IsContact (Finset.univ : Finset Cell) kernel toTransposeChart.secondComponent
  attained : toTransposeChart.latent.score = tau toTransposeChart.law

/-- An attained optimizer whose latent alphabet has one element. -/
structure UnaryOptimalLatent (p : RealTable) where
  latent : Latent p
  attained : latent.score = tau p
  unary : Nonempty (latent.ι ≃ Unit)

/-- A contact chart presented over an original law through a binary table
symmetry. -/
structure ContactPresentation (p : RealTable) where
  chart : ContactChart
  relabel : TableSymmetry
  oriented_law : pushforward relabel.equiv p = chart.toTransposeChart.law

/-! ## Four-scalar contact chart -/

/-- The closed four-scalar contact chart used by the analytic estimates. -/
structure ScalarContactChart where
  x : ℝ
  pi : ℝ
  lowMass : ℝ
  highMass : ℝ
  x_pos : 0 < x
  x_le_one : x ≤ 1
  pi_nonneg : 0 ≤ pi
  pi_le_half : pi ≤ 1 / 2
  lowMass_nonneg : 0 ≤ lowMass
  lowMass_le_highMass : lowMass ≤ highMass
  contact : (1 + x ^ 2 + x ^ 4) * lowMass * highMass =
    x ^ 4 * (x ^ 2 - (lowMass + highMass))

namespace ScalarContactChart

/-- The square chart coordinate. -/
def y (C : ScalarContactChart) : ℝ := C.x ^ 2

/-- The fourth-power chart coordinate. -/
def r (C : ScalarContactChart) : ℝ := C.x ^ 4

/-- The sum of the ordered diagonal masses. -/
def s (C : ScalarContactChart) : ℝ := C.lowMass + C.highMass

/-- The homogeneous mass normalization. -/
def norm (C : ScalarContactChart) : ℝ := 1 + C.r + C.s

/-- The shift parameter in the contact hyperbola, `r / (1 + y + r)`.

This is not the same quantity as `ContactChart.ratio`, which is the
homogeneous coordinate `x ^ 4`; `toScalarChart_coordinates` sends the latter to
`r`, not to this. The two share a name because each is the natural ratio of its
own chart. -/
def ratio (C : ScalarContactChart) : ℝ :=
  C.r / (1 + C.y + C.r)

/-- The lower off-diagonal mixture mass in the canonical prior orientation. -/
def e (C : ScalarContactChart) : ℝ :=
  C.pi + (1 - C.pi) * C.r

/-- The upper off-diagonal mixture mass in the canonical prior orientation. -/
def ell (C : ScalarContactChart) : ℝ :=
  1 - C.pi + C.pi * C.r

theorem y_pos (C : ScalarContactChart) : 0 < C.y := by
  exact sq_pos_of_pos C.x_pos

theorem r_pos (C : ScalarContactChart) : 0 < C.r := by
  exact pow_pos C.x_pos 4

theorem r_le_one (C : ScalarContactChart) : C.r ≤ 1 := by
  dsimp only [r]
  exact pow_le_one₀ C.x_pos.le C.x_le_one

theorem highMass_nonneg (C : ScalarContactChart) : 0 ≤ C.highMass :=
  C.lowMass_nonneg.trans C.lowMass_le_highMass

theorem s_nonneg (C : ScalarContactChart) : 0 ≤ C.s := by
  exact add_nonneg C.lowMass_nonneg C.highMass_nonneg

theorem norm_pos (C : ScalarContactChart) : 0 < C.norm := by
  dsimp only [norm]
  linarith [C.r_pos, C.s_nonneg]

theorem denominator_pos (C : ScalarContactChart) :
    0 < 1 + C.y + C.r := by
  linarith [C.y_pos, C.r_pos]

theorem ratio_pos (C : ScalarContactChart) : 0 < C.ratio := by
  exact div_pos C.r_pos C.denominator_pos

theorem contact_eq (C : ScalarContactChart) :
    C.lowMass * C.highMass = C.ratio * (C.y - C.s) := by
  have hden : 1 + C.y + C.r ≠ 0 := C.denominator_pos.ne'
  dsimp only [ratio, r, y, s]
  field_simp [hden]
  nlinarith [C.contact]

theorem s_le_y (C : ScalarContactChart) : C.s ≤ C.y := by
  have hleft : 0 ≤ (1 + C.y + C.r) * C.lowMass * C.highMass := by
    exact mul_nonneg
      (mul_nonneg C.denominator_pos.le C.lowMass_nonneg) C.highMass_nonneg
  have hright : 0 ≤ C.r * (C.y - C.s) := by
    simpa only [y, r, s] using C.contact ▸ hleft
  by_contra h
  have hneg : C.y - C.s < 0 := sub_neg.mpr (lt_of_not_ge h)
  exact (not_lt_of_ge hright) (mul_neg_of_pos_of_neg C.r_pos hneg)

theorem contact_shifted (C : ScalarContactChart) :
    (C.lowMass + C.ratio) * (C.highMass + C.ratio) =
      C.ratio * C.y + C.ratio ^ 2 := by
  calc
    (C.lowMass + C.ratio) * (C.highMass + C.ratio) =
        C.lowMass * C.highMass + C.ratio * (C.lowMass + C.highMass) +
          C.ratio ^ 2 := by ring
    _ = C.ratio * (C.y - C.s) + C.ratio * C.s + C.ratio ^ 2 := by
      rw [C.contact_eq]
      rfl
    _ = C.ratio * C.y + C.ratio ^ 2 := by ring

theorem e_add_ell (C : ScalarContactChart) :
    C.e + C.ell = 1 + C.r := by
  dsimp only [e, ell]
  ring

theorem e_add_ell_add_s (C : ScalarContactChart) :
    C.e + C.ell + C.s = C.norm := by
  rw [C.e_add_ell]
  rfl

theorem norm_sub_e (C : ScalarContactChart) :
    C.norm - C.e = C.ell + C.s := by
  linarith [C.e_add_ell_add_s]

theorem norm_sub_r (C : ScalarContactChart) :
    C.norm - C.r = 1 + C.s := by
  unfold norm
  ring

theorem norm_sub_one (C : ScalarContactChart) :
    C.norm - 1 = C.r + C.s := by
  unfold norm
  ring

theorem e_pos (C : ScalarContactChart) : 0 < C.e := by
  have hcoef : 0 < 1 - C.pi := by linarith [C.pi_le_half]
  have hterm : 0 < (1 - C.pi) * C.r := mul_pos hcoef C.r_pos
  dsimp only [e]
  linarith [C.pi_nonneg]

theorem ell_pos (C : ScalarContactChart) : 0 < C.ell := by
  have hfirst : 0 < 1 - C.pi := by linarith [C.pi_le_half]
  have hterm : 0 ≤ C.pi * C.r := mul_nonneg C.pi_nonneg C.r_pos.le
  dsimp only [ell]
  linarith

theorem e_le_ell (C : ScalarContactChart) : C.e ≤ C.ell := by
  have hprior : 0 ≤ 1 - 2 * C.pi := by linarith [C.pi_le_half]
  have hr : 0 ≤ 1 - C.r := sub_nonneg.mpr C.r_le_one
  have hprod : 0 ≤ (1 - 2 * C.pi) * (1 - C.r) := mul_nonneg hprior hr
  dsimp only [e, ell]
  nlinarith

theorem e_lt_norm (C : ScalarContactChart) : C.e < C.norm := by
  have h : 0 < C.ell + C.s := add_pos_of_pos_of_nonneg C.ell_pos C.s_nonneg
  linarith [C.norm_sub_e]

theorem r_lt_norm (C : ScalarContactChart) : C.r < C.norm := by
  linarith [C.norm_sub_r, C.s_nonneg]

theorem one_lt_norm (C : ScalarContactChart) : 1 < C.norm := by
  linarith [C.norm_sub_one, C.r_pos, C.s_nonneg]

/-- The strict scalar domain used by the analytic phase estimates. -/
def StrictInterior (C : ScalarContactChart) : Prop :=
  C.x < 1 ∧
    0 < C.pi ∧
    2 * (C.x ^ 3 / (1 + C.x + C.x ^ 2)) ≤ C.s ∧
    C.s < C.y ∧
    C.lowMass * C.highMass < C.r

end ScalarContactChart

/-! ## Homogeneous natural-log entropy -/

/-- The continuous extension of `z * log z`, including `xLogX 0 = 0`. -/
def xLogX (z : ℝ) : ℝ := z * Real.log z

/-- One-homogeneous two-point entropy in natural-log units. -/
def pairEntropy (a b : ℝ) : ℝ :=
  xLogX (a + b) - xLogX a - xLogX b

/-- The homogeneous entropy of a split `z + (Q-z) = Q`, in natural-log
units. -/
def splitEntropy (Q z : ℝ) : ℝ :=
  xLogX Q - xLogX z - xLogX (Q - z)

@[simp] theorem xLogX_zero : xLogX 0 = 0 := by
  simp [xLogX]

@[simp] theorem xLogX_one : xLogX 1 = 0 := by
  simp [xLogX]

theorem continuous_xLogX : Continuous xLogX := by
  change Continuous fun z : ℝ => z * Real.log z
  exact Real.continuous_mul_log

@[simp] theorem pairEntropy_zero_left (b : ℝ) : pairEntropy 0 b = 0 := by
  simp [pairEntropy]

@[simp] theorem pairEntropy_zero_right (a : ℝ) : pairEntropy a 0 = 0 := by
  simp [pairEntropy]

theorem pairEntropy_comm (a b : ℝ) : pairEntropy a b = pairEntropy b a := by
  simp only [pairEntropy]
  rw [add_comm]
  ring

theorem continuous_pairEntropy :
    Continuous fun p : ℝ × ℝ => pairEntropy p.1 p.2 := by
  unfold pairEntropy
  exact
    ((continuous_xLogX.comp (continuous_fst.add continuous_snd)).sub
      (continuous_xLogX.comp continuous_fst)).sub
        (continuous_xLogX.comp continuous_snd)

theorem splitEntropy_eq_pairEntropy (Q z : ℝ) :
    splitEntropy Q z = pairEntropy z (Q - z) := by
  unfold splitEntropy pairEntropy
  have hsum : z + (Q - z) = Q := by ring
  rw [hsum]

@[simp] theorem splitEntropy_zero (Q : ℝ) : splitEntropy Q 0 = 0 := by
  simp [splitEntropy]

@[simp] theorem splitEntropy_self (Q : ℝ) : splitEntropy Q Q = 0 := by
  simp [splitEntropy]

theorem splitEntropy_symm (Q z : ℝ) :
    splitEntropy Q (Q - z) = splitEntropy Q z := by
  unfold splitEntropy
  have hsub : Q - (Q - z) = z := by ring
  rw [hsub]
  ring

theorem continuous_splitEntropy :
    Continuous fun p : ℝ × ℝ => splitEntropy p.1 p.2 := by
  unfold splitEntropy
  exact
    ((continuous_xLogX.comp continuous_fst).sub
      (continuous_xLogX.comp continuous_snd)).sub
        (continuous_xLogX.comp (continuous_fst.sub continuous_snd))

theorem hasDerivAt_xLogX {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt xLogX (Real.log z + 1) z := by
  unfold xLogX
  exact Real.hasDerivAt_mul_log hz

theorem hasDerivAt_pairEntropy_left {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (fun z => pairEntropy z v) (Real.log ((u + v) / u)) u := by
  unfold pairEntropy xLogX
  have hsum := (Real.hasDerivAt_mul_log (add_pos hu hv).ne').comp u
    ((hasDerivAt_id u).add_const v)
  have hu' := Real.hasDerivAt_mul_log hu.ne'
  simpa only [Function.comp_apply, id_eq, Pi.sub_apply, mul_one,
    Real.log_div (add_pos hu hv).ne' hu.ne', add_sub_add_right_eq_sub] using
      (hsum.sub hu').sub_const (v * Real.log v)

theorem hasDerivAt_pairEntropy_right {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (fun z => pairEntropy u z) (Real.log ((u + v) / v)) v := by
  unfold pairEntropy xLogX
  have hsum := (Real.hasDerivAt_mul_log (add_pos hu hv).ne').comp v
    ((hasDerivAt_const v u).add (hasDerivAt_id v))
  have hv' := Real.hasDerivAt_mul_log hv.ne'
  have hraw := (hsum.sub_const (u * Real.log u)).sub hv'
  have hraw' : HasDerivAt
      (((fun x : ℝ => ((fun t : ℝ => t * Real.log t) (u + x)) - u * Real.log u) -
        fun x : ℝ => x * Real.log x))
      (Real.log (u + v) - Real.log v) v := by
    simpa only [Function.comp_apply, Pi.sub_apply, Pi.add_apply, zero_add, mul_one,
      add_sub_add_right_eq_sub] using hraw
  have hder : Real.log ((u + v) / v) = Real.log (u + v) - Real.log v :=
    Real.log_div (add_pos hu hv).ne' hv.ne'
  rw [hder]
  apply hraw'.congr_of_eventuallyEq
  filter_upwards [] with z
  simp only [Pi.sub_apply]

/-! ## Scalar entropy ledger -/

namespace ScalarContactChart

/-- Homogeneous latent-to-cell mutual information in natural-log units. -/
def observableInfo (C : ScalarContactChart) : ℝ :=
  pairEntropy C.e C.ell - pairEntropy C.r 1

/-- Homogeneous conditional mutual-information component in natural-log units. -/
def contactEntropyGap (C : ScalarContactChart) : ℝ :=
  pairEntropy (C.lowMass + C.r) (1 + C.highMass) -
    pairEntropy C.lowMass 1 - pairEntropy C.r C.highMass

/-- One diagonal mass's homogeneous bridge contribution in natural-log units. -/
def mixingTerm (C : ScalarContactChart) (z : ℝ) : ℝ :=
  pairEntropy z C.e + pairEntropy z C.ell -
    pairEntropy z C.r - pairEntropy z 1

/-- The sum of the two diagonal bridge contributions in natural-log units. -/
def mixingSum (C : ScalarContactChart) : ℝ :=
  C.mixingTerm C.lowMass + C.mixingTerm C.highMass

/-- The homogeneous reward of the canonically oriented high singleton, in
natural-log units. -/
def phaseReward (C : ScalarContactChart) : ℝ :=
  pairEntropy C.e (C.ell + C.s) -
    4 * ((1 - C.pi) * pairEntropy C.r (1 + C.s) +
      C.pi * pairEntropy 1 (C.r + C.s))

theorem observableInfo_expand (C : ScalarContactChart) :
    C.observableInfo = xLogX C.r - xLogX C.e - xLogX C.ell := by
  simp [observableInfo, pairEntropy, C.e_add_ell]
  ring_nf

theorem contactEntropyGap_expand (C : ScalarContactChart) :
    C.contactEntropyGap =
      xLogX C.norm + xLogX C.lowMass + xLogX C.highMass + xLogX C.r -
      xLogX (C.lowMass + C.r) - xLogX (C.lowMass + 1) -
      xLogX (C.highMass + C.r) - xLogX (C.highMass + 1) := by
  unfold contactEntropyGap pairEntropy
  rw [xLogX_one]
  have htotal : C.lowMass + C.r + (1 + C.highMass) = C.norm := by
    unfold norm s
    ring
  rw [htotal, add_comm 1 C.highMass, add_comm C.r C.highMass]
  ring

theorem mixingTerm_expand (C : ScalarContactChart) (z : ℝ) :
    C.mixingTerm z =
      xLogX (z + C.e) + xLogX (z + C.ell) -
      xLogX (z + C.r) - xLogX (z + 1) +
      xLogX C.r - xLogX C.e - xLogX C.ell := by
  simp [mixingTerm, pairEntropy]
  ring

theorem mixingSum_expand (C : ScalarContactChart) :
    C.mixingSum =
      xLogX (C.lowMass + C.e) + xLogX (C.lowMass + C.ell) +
      xLogX (C.highMass + C.e) + xLogX (C.highMass + C.ell) -
      xLogX (C.lowMass + C.r) - xLogX (C.lowMass + 1) -
      xLogX (C.highMass + C.r) - xLogX (C.highMass + 1) +
      2 * (xLogX C.r - xLogX C.e - xLogX C.ell) := by
  rw [mixingSum, mixingTerm_expand, mixingTerm_expand]
  ring

theorem phaseReward_eq_splitEntropy (C : ScalarContactChart) :
    C.phaseReward =
      splitEntropy C.norm C.e -
        4 * ((1 - C.pi) * splitEntropy C.norm C.r +
          C.pi * splitEntropy C.norm 1) := by
  unfold phaseReward splitEntropy pairEntropy
  have heq : C.e + (C.ell + C.s) = C.norm := by
    rw [← add_assoc, C.e_add_ell_add_s]
  have hrq : C.r + (1 + C.s) = C.norm := by
    unfold norm
    ring
  have honeq : 1 + (C.r + C.s) = C.norm := by
    unfold norm
    ring
  rw [heq, hrq, honeq, C.norm_sub_e, C.norm_sub_r, C.norm_sub_one]

end ScalarContactChart

/-! ## Contact equation and scalar extraction -/

namespace ContactChart

/-- The scalar contact equation at a proposed positive fourth root. -/
def ContactEquation (C : ContactChart) (x : ℝ) : Prop :=
  (1 + x ^ 2 + x ^ 4) * C.lowMass * C.highMass =
    x ^ 4 * (x ^ 2 - (C.lowMass + C.highMass))

/-- The contact equation forces the three nontrivial strict-domain gates. -/
theorem strictInterior_gates_of_contactEquation
    (C : ContactChart) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (h : C.ContactEquation x) :
    C.lowMass + C.highMass < x ^ 2 ∧
      2 * (x ^ 3 / (1 + x + x ^ 2)) ≤ C.lowMass + C.highMass ∧
      C.lowMass * C.highMass < x ^ 4 := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
  have hx3 : 0 < x ^ 3 := pow_pos hx0 3
  have hx4 : 0 < x ^ 4 := pow_pos hx0 4
  have hcoef : 0 < 1 + x ^ 2 + x ^ 4 := by positivity
  have had : 0 < C.lowMass * C.highMass :=
    mul_pos C.lowMass_pos C.highMass_pos
  have hfirst : C.lowMass + C.highMass < x ^ 2 := by
    unfold ContactEquation at h
    nlinarith [mul_pos hcoef had]
  have hspos : 0 < C.lowMass + C.highMass :=
    add_pos C.lowMass_pos C.highMass_pos
  have hamgm :
      4 * (C.lowMass * C.highMass) ≤ (C.lowMass + C.highMass) ^ 2 := by
    nlinarith [sq_nonneg (C.lowMass - C.highMass)]
  have hf :
      0 ≤ (1 + x ^ 2 + x ^ 4) * (C.lowMass + C.highMass) ^ 2 +
        4 * x ^ 4 * (C.lowMass + C.highMass) - 4 * x ^ 6 := by
    unfold ContactEquation at h
    nlinarith [h, hamgm]
  have hden : 0 < 1 + x + x ^ 2 := by positivity
  have hroot :
      (1 + x ^ 2 + x ^ 4) *
          ((C.lowMass + C.highMass) - 2 * x ^ 3 / (1 + x + x ^ 2)) *
          ((C.lowMass + C.highMass) +
            2 * x ^ 3 * (1 + x + x ^ 2) / (1 + x ^ 2 + x ^ 4)) =
        (1 + x ^ 2 + x ^ 4) * (C.lowMass + C.highMass) ^ 2 +
          4 * x ^ 4 * (C.lowMass + C.highMass) - 4 * x ^ 6 := by
    field_simp
    ring
  have hsecondFactor :
      0 < (C.lowMass + C.highMass) +
        2 * x ^ 3 * (1 + x + x ^ 2) / (1 + x ^ 2 + x ^ 4) := by
    positivity
  have hsecond :
      2 * (x ^ 3 / (1 + x + x ^ 2)) ≤ C.lowMass + C.highMass := by
    rw [← hroot] at hf
    by_contra hn
    have hdiff :
        C.lowMass + C.highMass - 2 * x ^ 3 / (1 + x + x ^ 2) < 0 := by
      push Not at hn
      apply sub_neg.mpr
      simpa [mul_div_assoc] using hn
    exact (not_lt_of_ge hf)
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hcoef hdiff) hsecondFactor)
  have hthird : C.lowMass * C.highMass < x ^ 4 := by
    have hsquare : (C.lowMass + C.highMass) ^ 2 < 4 * x ^ 4 := by
      nlinarith [sq_nonneg ((C.lowMass + C.highMass) + x ^ 2)]
    nlinarith [sq_nonneg (C.lowMass - C.highMass)]
  exact ⟨hfirst, hsecond, hthird⟩

/-- Extract the closed scalar chart at a supplied positive contact root. -/
def toScalarChart
    (C : ContactChart) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) : ScalarContactChart where
  x := x
  pi := C.toTransposeChart.pi
  lowMass := C.lowMass
  highMass := C.highMass
  x_pos := hx0
  x_le_one := hx1.le
  pi_nonneg := C.toTransposeChart.pi_pos.le
  pi_le_half := C.toTransposeChart.pi_le_half
  lowMass_nonneg := C.lowMass_pos.le
  lowMass_le_highMass := hmass
  contact := heq

/-- The exact homogeneous coordinates represented by scalar extraction. -/
theorem toScalarChart_coordinates
    (C : ContactChart) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hratio : C.ratio = x ^ 4)
    (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    S.r = C.ratio ∧
      S.s = C.lowMass + C.highMass ∧
      S.norm = C.norm ∧
      C.toTransposeChart.a = S.lowMass / S.norm ∧
      C.toTransposeChart.b = 1 / S.norm ∧
      C.toTransposeChart.c = S.r / S.norm ∧
      C.toTransposeChart.d = S.highMass / S.norm := by
  dsimp [toScalarChart, ScalarContactChart.r, ScalarContactChart.s,
    ScalarContactChart.norm]
  have hnorm : 1 + x ^ 4 + (C.lowMass + C.highMass) = C.norm := by
    rw [← hratio, C.norm_eq]
    ring
  rw [hnorm]
  exact ⟨hratio.symm, rfl, rfl, C.a_eq, C.b_eq,
    C.c_eq.trans (congrArg (fun z => z / C.norm) hratio), C.d_eq⟩

/-- Scalar extraction lands in the strict analytic interior. -/
theorem toScalarChart_strictInterior
    (C : ContactChart) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    S.StrictInterior := by
  let S := C.toScalarChart x hx0 hx1 hmass heq
  have hgates := C.strictInterior_gates_of_contactEquation x hx0 hx1 heq
  change S.StrictInterior
  unfold ScalarContactChart.StrictInterior
  refine ⟨hx1, C.toTransposeChart.pi_pos, ?_, ?_, ?_⟩
  · simpa [S, toScalarChart, ScalarContactChart.s] using hgates.2.1
  · simpa [S, toScalarChart, ScalarContactChart.s, ScalarContactChart.y] using hgates.1
  · simpa [S, toScalarChart, ScalarContactChart.r] using hgates.2.2

/-- The observable law cells in the scalar chart's homogeneous coordinates. -/
theorem toScalarChart_law
    (C : ContactChart) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hratio : C.ratio = x ^ 4)
    (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    C.toTransposeChart.law cell00 = S.lowMass / S.norm ∧
      C.toTransposeChart.law cell01 = S.ell / S.norm ∧
      C.toTransposeChart.law cell10 = S.e / S.norm ∧
      C.toTransposeChart.law cell11 = S.highMass / S.norm := by
  let S := C.toScalarChart x hx0 hx1 hmass heq
  have hspec := C.toScalarChart_coordinates x hx0 hx1 hratio hmass heq
  change C.toTransposeChart.law cell00 = S.lowMass / S.norm ∧
    C.toTransposeChart.law cell01 = S.ell / S.norm ∧
    C.toTransposeChart.law cell10 = S.e / S.norm ∧
    C.toTransposeChart.law cell11 = S.highMass / S.norm
  dsimp only [S] at hspec ⊢
  rcases hspec with ⟨hr, hs, hnorm, ha, hb, hc, hd⟩
  have hnorm0 : C.norm ≠ 0 := C.norm_pos.ne'
  rw [hnorm] at ha hb hc hd ⊢
  simp [TransposeChart.law, transposeMixtureLaw, tableOfEntries,
    transposeTableOfEntries, ScalarContactChart.e, ScalarContactChart.ell,
    toScalarChart, ha, hb, hc, hd, cell00, cell01, cell10, cell11]
  all_goals (field_simp; ring_nf; simp)

/-- The proposition that the strict factor-eight inequality holds at every
scalar presentation of a bundled contact chart.

`Binary.FactorNine.SeamEndpoints` proves this proposition as
`ContactChart.strictFactorEight`, using the two scalar phase bounds and the
explicit bit conversions below. `Binary.NormalForm` supplies a contact chart
at the selected optimizer on the two-class branch. -/
def StrictFactorEight : Prop :=
  ∀ (C : ContactChart) (x : ℝ), 0 < x → x < 1 →
    C.ratio = x ^ 4 → C.lowMass ≤ C.highMass → C.ContactEquation x →
    w3Cost C.toTransposeChart.latent (phaseSelector C.toTransposeChart) ≤
      8 * C.toTransposeChart.latent.score

end ContactChart

/-! ## High- and low-arm scalar algebra -/

namespace ScalarContactChart

/-- The conditional-entropy component of the canonically oriented high
singleton. -/
def highConditionalEntropy (C : ScalarContactChart) : ℝ :=
  (1 - C.pi) * pairEntropy C.r (1 + C.s) +
    C.pi * pairEntropy 1 (C.r + C.s)

/-- The information component of the canonically oriented high singleton. -/
def highInformation (C : ScalarContactChart) : ℝ :=
  pairEntropy C.e (C.ell + C.s) - C.highConditionalEntropy

/-- The conditional-entropy component of the oppositely oriented low
singleton. -/
def lowConditionalEntropy (C : ScalarContactChart) : ℝ :=
  (1 - C.pi) * pairEntropy 1 (C.r + C.s) +
    C.pi * pairEntropy C.r (1 + C.s)

/-- The information component of the oppositely oriented low singleton. -/
def lowInformation (C : ScalarContactChart) : ℝ :=
  pairEntropy C.ell (C.e + C.s) - C.lowConditionalEntropy

/-- The mixing contribution at the total diagonal mass. -/
def offDiagonalLoss (C : ScalarContactChart) : ℝ := C.mixingTerm C.s

/-- Information lost by selecting the high singleton. -/
def highInformationLoss (C : ScalarContactChart) : ℝ :=
  C.observableInfo - C.highInformation

/-- Information lost by selecting the low singleton. -/
def lowInformationLoss (C : ScalarContactChart) : ℝ :=
  C.observableInfo - C.lowInformation

theorem phaseReward_eq_highInformation_sub_three_mul_highConditionalEntropy
    (C : ScalarContactChart) :
    C.phaseReward = C.highInformation - 3 * C.highConditionalEntropy := by
  unfold phaseReward highInformation highConditionalEntropy
  ring

theorem offDiagonalLoss_eq_highInformationLoss_add_lowInformationLoss
    (C : ScalarContactChart) :
    C.offDiagonalLoss = C.highInformationLoss + C.lowInformationLoss := by
  unfold offDiagonalLoss highInformationLoss lowInformationLoss highInformation
    lowInformation highConditionalEntropy lowConditionalEntropy observableInfo mixingTerm
  have her : C.e + C.ell = C.r + 1 := by
    rw [C.e_add_ell]
    ring
  have heTotal : C.e + (C.ell + C.s) = C.r + (1 + C.s) := by
    rw [← add_assoc, her]
    ring
  have hellTotal : C.ell + (C.e + C.s) = 1 + (C.r + C.s) := by
    rw [← add_assoc, add_comm C.ell C.e, her]
    ring
  unfold pairEntropy
  rw [add_comm C.s C.e, add_comm C.s C.ell, add_comm C.s C.r,
    her, heTotal, hellTotal]
  ring_nf

theorem two_mul_highInformationLoss_le_offDiagonalLoss_of_orientation
    (C : ScalarContactChart) (horient : C.lowInformation ≤ C.highInformation) :
    2 * C.highInformationLoss ≤ C.offDiagonalLoss := by
  rw [C.offDiagonalLoss_eq_highInformationLoss_add_lowInformationLoss]
  unfold highInformationLoss lowInformationLoss
  linarith

private def orientationDifference (C : ScalarContactChart) (p : ℝ) : ℝ :=
  (pairEntropy (p + (1 - p) * C.r)
      (1 - p + p * C.r + C.s) -
    ((1 - p) * pairEntropy C.r (1 + C.s) +
      p * pairEntropy 1 (C.r + C.s))) -
  (pairEntropy (1 - p + p * C.r)
      (p + (1 - p) * C.r + C.s) -
    ((1 - p) * pairEntropy 1 (C.r + C.s) +
      p * pairEntropy C.r (1 + C.s)))

private theorem orientationDifference_apply (C : ScalarContactChart) :
    orientationDifference C C.pi = C.highInformation - C.lowInformation := by
  rfl

private theorem orientationDifference_zero (C : ScalarContactChart) :
    orientationDifference C 0 = 0 := by
  simp [orientationDifference, pairEntropy]

private theorem orientationDifference_half (C : ScalarContactChart) :
    orientationDifference C (1 / 2) = 0 := by
  unfold orientationDifference
  have heq : (1 / 2 : ℝ) + (1 - 1 / 2) * C.r =
      1 - 1 / 2 + (1 / 2 : ℝ) * C.r := by ring
  rw [heq]
  ring

private def orientationBaseline (C : ScalarContactChart) : ℝ :=
  xLogX C.r + xLogX (1 + C.s) - xLogX (C.r + C.s)

private def orientationDifferenceSlope (C : ScalarContactChart) (p : ℝ) : ℝ :=
  (1 - C.r) * Real.log
    (((p + (1 - p) * C.r + C.s) *
      (1 - p + p * C.r + C.s)) /
      ((p + (1 - p) * C.r) * (1 - p + p * C.r))) -
    2 * orientationBaseline C

private theorem orientationDifference_hasDerivAt
    (C : ScalarContactChart) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    HasDerivAt (orientationDifference C) (orientationDifferenceSlope C p) p := by
  let e := p + (1 - p) * C.r
  let ell := 1 - p + p * C.r
  have he : 0 < e := by
    dsimp [e]
    have hcoef : 0 < 1 - p := by linarith
    nlinarith [mul_pos hcoef C.r_pos]
  have hell : 0 < ell := by
    dsimp [ell]
    have hcoef : 0 < 1 - p := by linarith
    nlinarith [mul_nonneg hp0 C.r_pos.le]
  have hes : 0 < e + C.s := add_pos_of_pos_of_nonneg he C.s_nonneg
  have hells : 0 < ell + C.s := add_pos_of_pos_of_nonneg hell C.s_nonneg
  have heD : HasDerivAt (fun q : ℝ => q + (1 - q) * C.r) (1 - C.r) p := by
    have h := (hasDerivAt_id p).add
      (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul_const C.r)
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun q : ℝ => q + (1 - q) * C.r)
      (Filter.Eventually.of_forall (fun q => by simp))
    exact h'.congr_deriv (by ring)
  have hellD : HasDerivAt (fun q : ℝ => 1 - q + q * C.r) (-(1 - C.r)) p := by
    have h := ((hasDerivAt_const p 1).sub (hasDerivAt_id p)).add
      ((hasDerivAt_id p).mul_const C.r)
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun q : ℝ => 1 - q + q * C.r)
      (Filter.Eventually.of_forall (fun q => by simp))
    exact h'.congr_deriv (by ring)
  have hphi_e := (hasDerivAt_xLogX he.ne').comp p heD
  have hphi_ell := (hasDerivAt_xLogX hell.ne').comp p hellD
  have hphi_es := (hasDerivAt_xLogX hes.ne').comp p (heD.add_const C.s)
  have hphi_ells := (hasDerivAt_xLogX hells.ne').comp p (hellD.add_const C.s)
  have hraw := ((hphi_e.neg.sub hphi_ells).add hphi_ell).add hphi_es
  have hlinear : HasDerivAt (fun q : ℝ => (1 - 2 * q) * orientationBaseline C)
      (-2 * orientationBaseline C) p := by
    have h := (((hasDerivAt_const p 1).sub
      ((hasDerivAt_const p 2).mul (hasDerivAt_id p))).mul_const
        (orientationBaseline C))
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun q : ℝ => (1 - 2 * q) * orientationBaseline C)
      (Filter.Eventually.of_forall (fun q => by simp))
    simpa using h'
  have hall := hraw.add hlinear
  have hfun : orientationDifference C =
      ((((-xLogX ∘ fun q : ℝ => q + (1 - q) * C.r) -
        xLogX ∘ fun q : ℝ => 1 - q + q * C.r + C.s) +
        xLogX ∘ fun q : ℝ => 1 - q + q * C.r) +
        xLogX ∘ fun q : ℝ => q + (1 - q) * C.r + C.s) +
        fun q : ℝ => (1 - 2 * q) * orientationBaseline C := by
    funext q
    unfold orientationDifference pairEntropy
    dsimp [e, ell, orientationBaseline]
    rw [xLogX_one]
    ring_nf
  unfold orientationDifferenceSlope
  rw [hfun]
  have hder :
      (1 - C.r) *
          Real.log
            (((p + (1 - p) * C.r + C.s) * (1 - p + p * C.r + C.s)) /
              ((p + (1 - p) * C.r) * (1 - p + p * C.r))) -
          2 * orientationBaseline C =
        -((Real.log e + 1) * (1 - C.r)) -
            (Real.log (ell + C.s) + 1) * -(1 - C.r) +
            (Real.log ell + 1) * -(1 - C.r) +
            (Real.log (e + C.s) + 1) * (1 - C.r) +
            -2 * orientationBaseline C := by
    rw [Real.log_div (mul_ne_zero hes.ne' hells.ne')
      (mul_ne_zero he.ne' hell.ne'),
      Real.log_mul hes.ne' hells.ne', Real.log_mul he.ne' hell.ne']
    dsimp [e, ell]
    ring
  rw [hder]
  exact hall

private theorem orientationDifferenceSlope_antitone (C : ScalarContactChart) :
    AntitoneOn (orientationDifferenceSlope C) (Set.Icc 0 (1 / 2)) := by
  intro p hp q hq hpq
  simp only [Set.mem_Icc] at hp hq
  let ep := p + (1 - p) * C.r
  let lp := 1 - p + p * C.r
  let eq := q + (1 - q) * C.r
  let lq := 1 - q + q * C.r
  have hep : 0 < ep := by
    dsimp [ep]
    nlinarith [mul_pos (by linarith : 0 < 1 - p) C.r_pos]
  have hlp : 0 < lp := by
    dsimp [lp]
    nlinarith [mul_nonneg hp.1 C.r_pos.le]
  have heq : 0 < eq := by
    dsimp [eq]
    nlinarith [mul_pos (by linarith : 0 < 1 - q) C.r_pos]
  have hlq : 0 < lq := by
    dsimp [lq]
    nlinarith [mul_nonneg hq.1 C.r_pos.le]
  have hUp : 0 < ep * lp := mul_pos hep hlp
  have hUq : 0 < eq * lq := mul_pos heq hlq
  have hprod_p : ep * lp =
      C.r + p * (1 - p) * (1 - C.r) ^ 2 := by
    dsimp [ep, lp]
    ring
  have hprod_q : eq * lq =
      C.r + q * (1 - q) * (1 - C.r) ^ 2 := by
    dsimp [eq, lq]
    ring
  have hpquad : p * (1 - p) ≤ q * (1 - q) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (by linarith : 0 ≤ 1 - p - q)]
  have hU : ep * lp ≤ eq * lq := by
    rw [hprod_p, hprod_q]
    nlinarith [sq_nonneg (1 - C.r)]
  have hnum : 0 ≤ C.s * (1 + C.r + C.s) :=
    mul_nonneg C.s_nonneg (by linarith [C.r_pos, C.s_nonneg])
  have hratio_p :
      ((ep + C.s) * (lp + C.s)) / (ep * lp) =
        1 + C.s * (1 + C.r + C.s) / (ep * lp) := by
    field_simp
    dsimp [ep, lp]
    ring
  have hratio_q :
      ((eq + C.s) * (lq + C.s)) / (eq * lq) =
        1 + C.s * (1 + C.r + C.s) / (eq * lq) := by
    field_simp
    dsimp [eq, lq]
    ring
  have hfrac : C.s * (1 + C.r + C.s) / (eq * lq) ≤
      C.s * (1 + C.r + C.s) / (ep * lp) := by
    exact div_le_div_of_nonneg_left hnum hUp hU
  have hlog : Real.log
        (1 + C.s * (1 + C.r + C.s) / (eq * lq)) ≤
      Real.log (1 + C.s * (1 + C.r + C.s) / (ep * lp)) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; linarith [div_nonneg hnum hUq.le])
      (by simp only [Set.mem_Ioi]; linarith [div_nonneg hnum hUp.le])
      (by linarith)
  unfold orientationDifferenceSlope
  change (1 - C.r) * Real.log (((eq + C.s) * (lq + C.s)) / (eq * lq)) -
      2 * orientationBaseline C ≤
    (1 - C.r) * Real.log (((ep + C.s) * (lp + C.s)) / (ep * lp)) -
      2 * orientationBaseline C
  rw [hratio_p, hratio_q]
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr C.r_le_one)) _

private theorem orientationDifference_concaveOn (C : ScalarContactChart) :
    ConcaveOn ℝ (Set.Icc 0 (1 / 2)) (orientationDifference C) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
  · intro p hp
    exact (orientationDifference_hasDerivAt C hp.1 hp.2).continuousAt.continuousWithinAt
  · intro p hp
    simp only [interior_Icc, Set.mem_Ioo] at hp
    exact (orientationDifference_hasDerivAt C hp.1.le hp.2.le).differentiableAt.differentiableWithinAt
  · intro p hp q hq hpq
    simp only [interior_Icc, Set.mem_Ioo] at hp hq
    rw [(orientationDifference_hasDerivAt C hp.1.le hp.2.le).deriv,
      (orientationDifference_hasDerivAt C hq.1.le hq.2.le).deriv]
    exact orientationDifferenceSlope_antitone C ⟨hp.1.le, hp.2.le⟩
      ⟨hq.1.le, hq.2.le⟩ hpq

/-- The canonically high singleton always has at least as much information as
the oppositely oriented low singleton. -/
theorem lowInformation_le_highInformation (C : ScalarContactChart) :
    C.lowInformation ≤ C.highInformation := by
  have hleft : 0 ≤ 1 - 2 * C.pi := by linarith [C.pi_le_half]
  have hright : 0 ≤ 2 * C.pi := mul_nonneg (by norm_num) C.pi_nonneg
  have hsum : (1 - 2 * C.pi) + 2 * C.pi = 1 := by ring
  have hconc := (orientationDifference_concaveOn C).2
      (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num)
      (show (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num)
      hleft hright hsum
  have hpoint : (1 - 2 * C.pi) • (0 : ℝ) +
      (2 * C.pi) • (1 / 2 : ℝ) = C.pi := by
    simp only [smul_eq_mul]
    ring
  rw [hpoint, orientationDifference_zero, orientationDifference_half] at hconc
  rw [orientationDifference_apply] at hconc
  simp only [smul_eq_mul, mul_zero, add_zero] at hconc
  linarith

/-- A supplied information orientation puts at most half the split loss on the
high arm. -/
theorem two_mul_highInformationLoss_le_offDiagonalLoss_of_information_order
    (C : ScalarContactChart) (horient : C.lowInformation ≤ C.highInformation) :
    2 * C.highInformationLoss ≤ C.offDiagonalLoss := by
  exact C.two_mul_highInformationLoss_le_offDiagonalLoss_of_orientation horient

/-- At most half the split information loss lies on the canonically high arm. -/
theorem two_mul_highInformationLoss_le_offDiagonalLoss
    (C : ScalarContactChart) :
    2 * C.highInformationLoss ≤ C.offDiagonalLoss := by
  exact C.two_mul_highInformationLoss_le_offDiagonalLoss_of_information_order
    C.lowInformation_le_highInformation

end ScalarContactChart

/-! ## Natural-log scaling and singleton reward -/

theorem norm_mul_binEntropy_div
    (Q z : ℝ) (hQ : 0 < Q) (hz : 0 < z) (hzQ : z < Q) :
    Q * Real.binEntropy (z / Q) = splitEntropy Q z := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold Real.negMulLog splitEntropy xLogX
  rw [Real.log_div hz.ne' hQ.ne']
  have hone : 1 - z / Q = (Q - z) / Q := by field_simp
  rw [hone, Real.log_div (sub_pos.mpr hzQ).ne' hQ.ne']
  field_simp
  ring

theorem norm_mul_negMulLog_div
    (Q z : ℝ) (hQ : 0 < Q) (hz : 0 < z) :
    Q * Real.negMulLog (z / Q) = -xLogX z + z * Real.log Q := by
  unfold Real.negMulLog xLogX
  rw [Real.log_div hz.ne' hQ.ne']
  field_simp
  ring

/-- The scalar reward of a singleton with component masses `u` and `v`; the
explicit `Real.log 2` in bridge theorems converts public bit quantities to
these natural-log units. -/
def scalarSingletonReward (pi u v : ℝ) : ℝ :=
  Real.binEntropy ((1 - pi) * u + pi * v) -
    4 * ((1 - pi) * Real.binEntropy u + pi * Real.binEntropy v)

private lemma condEntropy_observable_eq_weighted_components
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : RealTable} (L : Latent p) (g : Cell → γ) :
    stoch_to_det.condH (fun w : L.ι × Cell => g w.2) (fun w => w.1) L.joint =
      ∑ i, L.prior i * stoch_to_det.Hvar g (L.comp i) := by
  have hdecomp := stoch_to_det.Hvar_pair_eq_sum_fibers L.joint_isPMF
    (fun w : L.ι × Cell => g w.2) (fun w => w.1)
  calc
    stoch_to_det.condH (fun w : L.ι × Cell => g w.2) (fun w => w.1) L.joint =
        ∑ i, stoch_to_det.H
          (stoch_to_det.push (fun w : L.ι × Cell => g w.2)
            (fun w => if w.1 = i then L.joint w else 0)) := by
      unfold stoch_to_det.condH
      rw [hdecomp]
      ring
    _ = ∑ i, L.prior i * stoch_to_det.Hvar g (L.comp i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hfiber :
          stoch_to_det.push (fun w : L.ι × Cell => g w.2)
              (fun w => if w.1 = i then L.joint w else 0) =
            fun label => L.prior i * stoch_to_det.push g (L.comp i) label := by
        funext label
        unfold stoch_to_det.push
        rw [Finset.sum_filter, Fintype.sum_prod_type]
        simp only [Latent.joint, stoch_to_det.Latent.joint]
        rw [Finset.sum_comm]
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : g z = label
        · simp only [hz, if_true]
          simp
        · simp [hz]
      rw [hfiber]
      by_cases hi : L.prior i = 0
      · simp [hi, stoch_to_det.Hvar, stoch_to_det.H, stoch_to_det.mass]
      · have hipos : 0 < L.prior i :=
          lt_of_le_of_ne (L.prior_isPMF.nonneg i) (Ne.symm hi)
        simpa [stoch_to_det.Hvar] using stoch_to_det.H_smul
          (stoch_to_det.isFinMeas_push (L.comp_isPMF i).isFinMeas) hipos.le

private lemma log_two_mul_entropyOf_singletonCode
    {p : RealTable} (hp : IsPMF p) (cell : Cell) :
    Real.log 2 * entropyOf (singletonCode cell) p = Real.binEntropy (p cell) := by
  let indicator : Cell → Bool := fun z => decide (z = cell)
  let zeroLabel : Fin (Fintype.card Cell) := ⟨0, by decide⟩
  let oneLabel : Fin (Fintype.card Cell) := ⟨1, by decide⟩
  let encode : Bool → Fin (Fintype.card Cell) :=
    fun b => if b then oneLabel else zeroLabel
  let decode : Fin (Fintype.card Cell) → Bool :=
    fun k => decide (k = oneLabel)
  have hleft : Function.LeftInverse decode encode := by
    intro b
    cases b <;> simp [decode, encode, zeroLabel, oneLabel]
  have hcode : encode ∘ indicator = singletonCode cell := by
    funext z
    by_cases hzc : z = cell <;>
      simp [indicator, encode, zeroLabel, oneLabel, singletonCode, hzc]
  have hEntropy :
      entropyOf (singletonCode cell) p = entropyOf indicator p := by
    rw [← hcode]
    exact stoch_to_det.Hvar_eq_of_leftInverse hp indicator encode decode hleft
  have h := stoch_to_det.H_eq_negMulLog
    (stoch_to_det.isPMF_push (f := indicator) hp).isFinMeas
  have htotal := (stoch_to_det.isPMF_push (f := indicator) hp).total
  rw [htotal, Real.log_one, mul_zero, zero_add] at h
  rw [hEntropy]
  unfold entropyOf stoch_to_det.Hvar
  rw [h]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hsum : ∑ z, p z = 1 := by
    simpa [mass, stoch_to_det.mass] using hp.total
  have hfalse : pushforward indicator p false = 1 - p cell := by
    unfold pushforward stoch_to_det.push
    have hfilter :
        Finset.univ.filter (fun z => indicator z = false) =
          Finset.univ.erase cell := by
      ext z
      by_cases hzc : z = cell <;> simp [indicator, hzc]
    rw [hfilter]
    have herase : ∑ z ∈ (Finset.univ.erase cell), p z = 1 - p cell := by
      have hadd := Finset.sum_erase_add (s := (Finset.univ : Finset Cell))
        (f := p) (Finset.mem_univ cell)
      rw [hsum] at hadd
      linarith
    exact herase
  have htrue : pushforward indicator p true = p cell := by
    unfold pushforward stoch_to_det.push
    have hfilter :
        Finset.univ.filter (fun z => indicator z = true) = {cell} := by
      ext z
      by_cases hzc : z = cell <;> simp [indicator, hzc]
    rw [hfilter]
    simp
  change stoch_to_det.push indicator p false = 1 - p cell at hfalse
  change stoch_to_det.push indicator p true = p cell at htrue
  rw [Fintype.sum_bool, htrue, hfalse]

/-- Exact natural-log formula for the reward of any singleton partition of a
transpose chart. -/
theorem log_two_mul_codeReward_singleton (D : TransposeChart) (cell : Cell) :
    Real.log 2 * codeReward D.latent (singletonCode cell) =
      scalarSingletonReward D.pi (D.firstComponent cell) (D.secondComponent cell) := by
  have hG := log_two_mul_entropyOf_singletonCode D.law_isPMF cell
  have h0 := log_two_mul_entropyOf_singletonCode D.firstComponent_isPMF cell
  have h1 := log_two_mul_entropyOf_singletonCode D.secondComponent_isPMF cell
  have hcond := condEntropy_observable_eq_weighted_components
    D.latent (singletonCode cell)
  have hcondScale :
      Real.log 2 * condEntropy
          (fun w : D.latent.ι × Cell => singletonCode cell w.2)
          (fun w => w.1) D.latent.joint =
        (1 - D.pi) * Real.binEntropy (D.firstComponent cell) +
          D.pi * Real.binEntropy (D.secondComponent cell) := by
    change Real.log 2 * stoch_to_det.condH
        (fun w : D.latent.ι × Cell => singletonCode cell w.2)
        (fun w => w.1) D.latent.joint = _
    rw [hcond]
    change Real.log 2 *
        (∑ i : Bit, D.latent.prior i *
          stoch_to_det.Hvar (singletonCode cell) (D.latent.comp i)) = _
    rw [Fin.sum_univ_two]
    simp only [TransposeChart.latent, TransposeChart.prior, twoPointPrior,
      ↓reduceIte, one_ne_zero]
    calc
      Real.log 2 * ((1 - D.pi) * entropyOf (singletonCode cell) D.firstComponent +
          D.pi * entropyOf (singletonCode cell) D.secondComponent) =
          (1 - D.pi) * (Real.log 2 * entropyOf (singletonCode cell) D.firstComponent) +
            D.pi * (Real.log 2 * entropyOf (singletonCode cell) D.secondComponent) := by
        ring
      _ = _ := by rw [h0, h1]
  calc
    Real.log 2 * codeReward D.latent (singletonCode cell) =
        Real.log 2 * entropyOf (singletonCode cell) D.law -
          4 * (Real.log 2 * condEntropy
            (fun w : D.latent.ι × Cell => singletonCode cell w.2)
            (fun w => w.1) D.latent.joint) := by
      unfold codeReward
      ring
    _ = Real.binEntropy (D.law cell) -
        4 * ((1 - D.pi) * Real.binEntropy (D.firstComponent cell) +
          D.pi * Real.binEntropy (D.secondComponent cell)) := by
      rw [hG, hcondScale]
    _ = scalarSingletonReward D.pi (D.firstComponent cell)
        (D.secondComponent cell) := by
      unfold scalarSingletonReward
      congr 2

private theorem w3Cost_constantCode_eq_zero_of_subsingleton
    {p : RealTable} (L : Latent p) [Subsingleton L.ι] :
    w3Cost L constantCode = 0 := by
  have hlabel : Nonempty L.ι := by
    by_contra h
    let _ : IsEmpty L.ι := not_nonempty_iff.mp h
    have htotal := L.prior_isPMF.total
    simp [stoch_to_det.mass] at htotal
  let i0 : L.ι := Classical.choice hlabel
  let g0 : Fin (Fintype.card Cell) := ⟨0, by decide⟩
  have hcode : constantCode = fun _ => g0 := by rfl
  have hLg : entropyOf (fun a : L.ι × Cell => (a.1, g0)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.1) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.1) (fun x => (x, g0)) Prod.fst (by intro; rfl)
  have hZg : entropyOf (fun a : L.ι × Cell => (a.2, g0)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.2) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.2) (fun x => (x, g0)) Prod.fst (by intro; rfl)
  have hLZg : entropyOf (fun a : L.ι × Cell => (a.1, a.2, g0)) L.joint =
      entropyOf (fun a : L.ι × Cell => (a.1, a.2)) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => (a.1, a.2))
      (fun x => (x.1, x.2, g0)) (fun y => (y.1, y.2.1)) (by intro; rfl)
  have hL : (fun w : L.ι × Cell => w.1) = fun _ => i0 := by
    funext w
    exact Subsingleton.elim _ _
  have hpair : (fun w : L.ι × Cell => (w.1, w.2)) = fun w => (i0, w.2) := by
    funext w
    exact congrArg (fun i => (i, w.2)) (Subsingleton.elim _ _)
  have hLZ : entropyOf (fun a : L.ι × Cell => (a.1, a.2)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.2) L.joint := by
    rw [hpair]
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.2) (fun x => (i0, x)) Prod.snd (by intro; rfl)
  have hgL : entropyOf (fun a : L.ι × Cell => (g0, a.1)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.1) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.1) (fun x => (g0, x)) Prod.snd (by intro; rfl)
  have hsum : ∑ w, L.joint w = 1 := by
    simpa [mass, stoch_to_det.mass] using L.joint_isPMF.total
  have hunit : entropyOf (fun _ : L.ι × Cell => ()) L.joint = 0 := by
    simp [entropyOf, stoch_to_det.Hvar, stoch_to_det.H,
      stoch_to_det.push, stoch_to_det.mass, hsum]
  have hconstL : entropyOf (fun _ : L.ι × Cell => i0) L.joint = 0 := by
    apply le_antisymm
    · exact (stoch_to_det.Hvar_comp_le L.joint_isPMF
        (fun _ : L.ι × Cell => ()) (fun _ => i0)).trans_eq hunit
    · unfold entropyOf stoch_to_det.Hvar
      exact stoch_to_det.H_nonneg_of_isPMF
        (stoch_to_det.isPMF_push L.joint_isPMF)
  have hconstG : entropyOf (fun _ : L.ι × Cell => g0) L.joint = 0 := by
    apply le_antisymm
    · exact (stoch_to_det.Hvar_comp_le L.joint_isPMF
        (fun _ : L.ι × Cell => ()) (fun _ => g0)).trans_eq hunit
    · unfold entropyOf stoch_to_det.Hvar
      exact stoch_to_det.H_nonneg_of_isPMF
        (stoch_to_det.isPMF_push L.joint_isPMF)
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, g0)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.1) L.joint at hLg
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.2, g0)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.2) L.joint at hZg
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, a.2, g0)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, a.2)) L.joint at hLZg
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, a.2)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.2) L.joint at hLZ
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (g0, a.1)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.1) L.joint at hgL
  change stoch_to_det.Hvar (fun _ : L.ι × Cell => i0) L.joint = 0 at hconstL
  change stoch_to_det.Hvar (fun _ : L.ι × Cell => g0) L.joint = 0 at hconstG
  unfold w3Cost condMutualInfo condEntropy
  unfold stoch_to_det.condMI stoch_to_det.condH
  rw [hcode]
  simp only
  rw [hLg, hZg, hLZg, hLZ, hgL, hL, hconstL, hconstG]
  ring

private def twoPointMass (u v : ℝ) : Bit → ℝ
  | 0 => u
  | 1 => v

private theorem scale_entropy_twoPointMass
    (Q u v : ℝ) (hQ : 0 < Q)
    (hu : 0 < u) (hv : 0 < v) (hsum : u + v = Q) :
    Q * Real.log 2 * entropy (twoPointMass (u / Q) (v / Q)) =
      xLogX Q - xLogX u - xLogX v := by
  have hfin : IsFiniteMeasure (twoPointMass (u / Q) (v / Q)) := by
    intro i
    fin_cases i <;> simp [twoPointMass] <;> positivity
  have hm : mass (twoPointMass (u / Q) (v / Q)) = 1 := by
    simp [mass, stoch_to_det.mass, twoPointMass, Fin.sum_univ_two]
    field_simp [hQ.ne']
    linarith
  change Q * Real.log 2 * stoch_to_det.H (twoPointMass (u / Q) (v / Q)) = _
  change stoch_to_det.mass (twoPointMass (u / Q) (v / Q)) = 1 at hm
  rw [mul_assoc, stoch_to_det.H_eq_negMulLog hfin, hm, Real.log_one,
    one_mul, zero_add]
  simp [twoPointMass, Fin.sum_univ_two]
  have hdist :
      Q * (Real.negMulLog (u / Q) + Real.negMulLog (v / Q)) =
        Q * Real.negMulLog (u / Q) + Q * Real.negMulLog (v / Q) := by ring
  rw [hdist, norm_mul_negMulLog_div Q u hQ hu,
    norm_mul_negMulLog_div Q v hQ hv, ← hsum]
  unfold xLogX
  ring

private theorem scale_entropy_table
    (Q A B C D : ℝ) (hQ : 0 < Q)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hsum : A + B + C + D = Q) :
    Q * Real.log 2 * entropy
        (tableOfEntries (A / Q) (B / Q) (C / Q) (D / Q)) =
      xLogX Q - xLogX A - xLogX B - xLogX C - xLogX D := by
  have hfin :
      IsFiniteMeasure (tableOfEntries (A / Q) (B / Q) (C / Q) (D / Q)) := by
    intro z
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [tableOfEntries] <;> positivity
  have hm :
      mass (tableOfEntries (A / Q) (B / Q) (C / Q) (D / Q)) = 1 := by
    simp [mass, stoch_to_det.mass, tableOfEntries,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    field_simp [hQ.ne']
    linarith
  change Q * Real.log 2 * stoch_to_det.H
      (tableOfEntries (A / Q) (B / Q) (C / Q) (D / Q)) = _
  change stoch_to_det.mass
    (tableOfEntries (A / Q) (B / Q) (C / Q) (D / Q)) = 1 at hm
  rw [mul_assoc, stoch_to_det.H_eq_negMulLog hfin, hm, Real.log_one,
    one_mul, zero_add]
  simp [tableOfEntries, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hdist : Q * (Real.negMulLog (A / Q) + Real.negMulLog (B / Q) +
      (Real.negMulLog (C / Q) + Real.negMulLog (D / Q))) =
      Q * Real.negMulLog (A / Q) + Q * Real.negMulLog (B / Q) +
      (Q * Real.negMulLog (C / Q) + Q * Real.negMulLog (D / Q)) := by ring
  rw [hdist, norm_mul_negMulLog_div Q A hQ hA,
    norm_mul_negMulLog_div Q B hQ hB,
    norm_mul_negMulLog_div Q C hQ hC,
    norm_mul_negMulLog_div Q D hQ hD, ← hsum]
  unfold xLogX
  ring

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ}

private lemma latent_push_observable_joint (L : Latent p) :
    stoch_to_det.push (fun w : L.ι × (α × β) => w.2) L.joint = p := by
  funext z
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simpa [Latent.joint, stoch_to_det.Latent.joint] using L.mixture z

omit [DecidableEq α] [DecidableEq β] in
private lemma latent_push_prior_joint (L : Latent p) :
    stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint = L.prior := by
  funext v
  have hcomp : ∀ u, ∑ z, L.comp u z = 1 := fun u => by
    simpa [mass, stoch_to_det.mass] using (L.comp_isPMF u).total
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Latent.joint, stoch_to_det.Latent.joint]
  calc
    (∑ x, ∑ y, if x = v then L.prior x * L.comp x y else 0) =
        ∑ x, if x = v then L.prior x * (∑ y, L.comp x y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = v
      · simp [hx, Finset.mul_sum]
      · simp [hx]
    _ = L.prior v := by simp [hcomp]

private lemma entropyOf_observable_lift
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (L : Latent p) (f : α × β → γ) :
    stoch_to_det.Hvar (fun w : L.ι × (α × β) => f w.2) L.joint =
      stoch_to_det.Hvar f p := by
  unfold stoch_to_det.Hvar
  congr 1
  calc
    stoch_to_det.push (fun w : L.ι × (α × β) => f w.2) L.joint =
        stoch_to_det.push f
          (stoch_to_det.push (fun w : L.ι × (α × β) => w.2) L.joint) := by
      symm
      simpa [Function.comp_def] using
        (stoch_to_det.push_push (fun w : L.ι × (α × β) => w.2) f L.joint)
    _ = stoch_to_det.push f p := by rw [latent_push_observable_joint L]

omit [DecidableEq α] [DecidableEq β] in
private lemma entropyOf_prior_joint (L : Latent p) :
    stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.1) L.joint =
      stoch_to_det.H L.prior := by
  unfold stoch_to_det.Hvar
  rw [latent_push_prior_joint L]

omit [DecidableEq α] [DecidableEq β] in
private lemma entropyOf_lift_pair_prior
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (L : Latent p) (f : α × β → γ) :
    stoch_to_det.Hvar (fun w : L.ι × (α × β) => (f w.2, w.1)) L.joint =
      stoch_to_det.H L.prior +
        ∑ v, L.prior v * stoch_to_det.Hvar f (L.comp v) := by
  have hdecomp := stoch_to_det.Hvar_pair_eq_sum_fibers L.joint_isPMF
    (fun w : L.ι × (α × β) => f w.2) (fun w => w.1)
  rw [entropyOf_prior_joint L] at hdecomp
  rw [hdecomp]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have hfiber :
      stoch_to_det.push (fun w : L.ι × (α × β) => f w.2)
          (fun w => if w.1 = v then L.joint w else 0) =
        fun c => L.prior v * stoch_to_det.push f (L.comp v) c := by
    funext c
    unfold stoch_to_det.push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Latent.joint, stoch_to_det.Latent.joint]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : f z = c
    · simp only [hz, if_true]
      simp
    · simp [hz]
  rw [hfiber]
  by_cases hv : L.prior v = 0
  · simp [hv, stoch_to_det.Hvar, stoch_to_det.H, stoch_to_det.mass]
  · have hvpos : 0 < L.prior v :=
      lt_of_le_of_ne (L.prior_isPMF.nonneg v) (Ne.symm hv)
    simpa [stoch_to_det.Hvar] using
      (stoch_to_det.H_smul
        (stoch_to_det.isFinMeas_push (L.comp_isPMF v).isFinMeas) hvpos.le)

private lemma mutualInfo_prior_lift
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (L : Latent p) (f : α × β → γ) :
    stoch_to_det.MI (fun w : L.ι × (α × β) => w.1)
        (fun w => f w.2) L.joint =
      stoch_to_det.Hvar f p -
        ∑ v, L.prior v * stoch_to_det.Hvar f (L.comp v) := by
  have hpair :
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, f w.2)) L.joint =
        stoch_to_det.H L.prior +
          ∑ v, L.prior v * stoch_to_det.Hvar f (L.comp v) := by
    calc
      _ = stoch_to_det.Hvar
          (fun w : L.ι × (α × β) => (f w.2, w.1)) L.joint := by
        simpa using stoch_to_det.Hvar_equiv L.joint_isPMF
          (fun w : L.ι × (α × β) => (f w.2, w.1))
          (Equiv.prodComm γ L.ι)
      _ = _ := entropyOf_lift_pair_prior L f
  unfold stoch_to_det.MI
  rw [entropyOf_prior_joint L, entropyOf_observable_lift L f, hpair]
  ring

private theorem observableInfo_eq_entropy_sub_components (D : TransposeChart) :
    observableInfo D.latent = entropy D.law -
      ((1 - D.pi) * entropy D.firstComponent +
        D.pi * entropy D.secondComponent) := by
  rw [show observableInfo D.latent =
      entropyOf (fun z : Cell => z) D.law -
        ∑ v, D.latent.prior v * entropyOf (fun z : Cell => z) (D.latent.comp v) by
    exact mutualInfo_prior_lift D.latent (fun z : Cell => z)]
  have hid (m : RealTable) (hm : IsPMF m) :
      entropyOf (fun z : Cell => z) m = entropy m := by
    unfold entropyOf stoch_to_det.Hvar
    exact stoch_to_det.H_push_equiv (Equiv.refl Cell) m hm
  rw [hid D.law D.law_isPMF]
  have hsum :
      (∑ v, D.latent.prior v * entropyOf (fun z : Cell => z) (D.latent.comp v)) =
        (1 - D.pi) * entropy D.firstComponent +
          D.pi * entropy D.secondComponent := by
    change (∑ v : Bit, D.prior v * entropyOf (fun z : Cell => z)
      (if v = 0 then D.firstComponent else D.secondComponent)) = _
    rw [Fin.sum_univ_two]
    simp only [TransposeChart.prior, twoPointPrior, ↓reduceIte, one_ne_zero]
    rw [hid D.firstComponent D.firstComponent_isPMF,
      hid D.secondComponent D.secondComponent_isPMF]
  rw [hsum]

private theorem contact_entropy_ledgers
    (C : ContactChart) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hratio : C.ratio = x ^ 4) (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    S.norm * Real.log 2 * entropy C.toTransposeChart.law =
      xLogX S.norm - xLogX S.lowMass - xLogX S.ell - xLogX S.e -
        xLogX S.highMass ∧
    S.norm * Real.log 2 * entropy C.toTransposeChart.firstComponent =
      xLogX S.norm - xLogX S.lowMass - xLogX 1 - xLogX S.r -
        xLogX S.highMass ∧
    S.norm * Real.log 2 * entropy C.toTransposeChart.secondComponent =
      xLogX S.norm - xLogX S.lowMass - xLogX S.r - xLogX 1 -
        xLogX S.highMass := by
  let S := C.toScalarChart x hx0 hx1 hmass heq
  have hspec := C.toScalarChart_coordinates x hx0 hx1 hratio hmass heq
  have hlaw := C.toScalarChart_law x hx0 hx1 hratio hmass heq
  rcases hspec with ⟨hr, hs, hnorm, ha, hb, hc, hd⟩
  have hlow : 0 < S.lowMass := C.lowMass_pos
  have hhigh : 0 < S.highMass := C.highMass_pos
  have hsumLaw : S.lowMass + S.ell + S.e + S.highMass = S.norm := by
    calc
      S.lowMass + S.ell + S.e + S.highMass =
          S.e + S.ell + (S.lowMass + S.highMass) := by ring
      _ = S.norm := S.e_add_ell_add_s
  have hsumComponent : S.lowMass + 1 + S.r + S.highMass = S.norm := by
    unfold ScalarContactChart.norm ScalarContactChart.s
    ring
  rcases hlaw with ⟨hl00, hl01, hl10, hl11⟩
  have hlawFun : C.toTransposeChart.law =
      tableOfEntries (S.lowMass / S.norm) (S.ell / S.norm)
        (S.e / S.norm) (S.highMass / S.norm) := by
    funext z
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · exact hl00
    · exact hl01
    · exact hl10
    · exact hl11
  have hfirstFun : C.toTransposeChart.firstComponent =
      tableOfEntries (S.lowMass / S.norm) (1 / S.norm)
        (S.r / S.norm) (S.highMass / S.norm) := by
    funext z
    rcases z with ⟨i, j⟩
    unfold TransposeChart.firstComponent
    rw [ha, hb, hc, hd]
  have hsecondFun : C.toTransposeChart.secondComponent =
      tableOfEntries (S.lowMass / S.norm) (S.r / S.norm)
        (1 / S.norm) (S.highMass / S.norm) := by
    funext z
    rcases z with ⟨i, j⟩
    unfold TransposeChart.secondComponent transposeTableOfEntries
    rw [ha, hb, hc, hd]
  rw [hlawFun, hfirstFun, hsecondFun]
  exact ⟨scale_entropy_table S.norm S.lowMass S.ell S.e S.highMass
      S.norm_pos hlow S.ell_pos S.e_pos hhigh hsumLaw,
    scale_entropy_table S.norm S.lowMass 1 S.r S.highMass
      S.norm_pos hlow (by norm_num) S.r_pos hhigh hsumComponent,
    scale_entropy_table S.norm S.lowMass S.r 1 S.highMass
      S.norm_pos hlow S.r_pos (by norm_num) hhigh (by linarith [hsumComponent])⟩

namespace ScalarContactChart

/-- Exact bit-to-natural-log observable-information ledger for a bundled
contact chart. -/
theorem norm_mul_log_two_mul_observableInfo_eq
    (C : ContactChart) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hratio : C.ratio = x ^ 4) (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    S.norm * Real.log 2 * Binary.observableInfo C.toTransposeChart.latent =
      S.observableInfo := by
  let S := C.toScalarChart x hx0 hx1 hmass heq
  obtain ⟨hlaw0, hfirst0, hsecond0⟩ :=
    contact_entropy_ledgers C x hx0 hx1 hratio hmass heq
  have hlaw : S.norm * Real.log 2 * entropy C.toTransposeChart.law =
      xLogX S.norm - xLogX S.lowMass - xLogX S.ell - xLogX S.e -
        xLogX S.highMass := by
    simpa only [S] using hlaw0
  have hfirst : S.norm * Real.log 2 * entropy C.toTransposeChart.firstComponent =
      xLogX S.norm - xLogX S.lowMass - xLogX 1 - xLogX S.r -
        xLogX S.highMass := by
    simpa only [S] using hfirst0
  have hsecond : S.norm * Real.log 2 * entropy C.toTransposeChart.secondComponent =
      xLogX S.norm - xLogX S.lowMass - xLogX S.r - xLogX 1 -
        xLogX S.highMass := by
    simpa only [S] using hsecond0
  change S.norm * Real.log 2 * Binary.observableInfo C.toTransposeChart.latent =
    S.observableInfo
  rw [observableInfo_eq_entropy_sub_components]
  rw [mul_sub]
  have hdist : S.norm * Real.log 2 *
      ((1 - C.toTransposeChart.pi) * entropy C.toTransposeChart.firstComponent +
        C.toTransposeChart.pi * entropy C.toTransposeChart.secondComponent) =
      (1 - S.pi) *
          (S.norm * Real.log 2 * entropy C.toTransposeChart.firstComponent) +
        S.pi *
          (S.norm * Real.log 2 * entropy C.toTransposeChart.secondComponent) := by
    dsimp [S, ContactChart.toScalarChart]
    ring
  rw [hlaw, hdist, hfirst, hsecond]
  unfold observableInfo pairEntropy
  rw [S.e_add_ell, xLogX_one]
  ring_nf

end ScalarContactChart

private theorem firstMarginal_table (A B C D : ℝ) :
    stoch_to_det.mX (tableOfEntries A B C D) =
      twoPointMass (A + B) (C + D) := by
  funext i
  unfold stoch_to_det.mX stoch_to_det.push
  fin_cases i <;> rw [Finset.sum_filter, Fintype.sum_prod_type] <;>
    norm_num [tableOfEntries, twoPointMass, Fin.sum_univ_two]

private theorem secondMarginal_table (A B C D : ℝ) :
    stoch_to_det.mY (tableOfEntries A B C D) =
      twoPointMass (A + C) (B + D) := by
  funext i
  unfold stoch_to_det.mY stoch_to_det.push
  fin_cases i <;> rw [Finset.sum_filter, Fintype.sum_prod_type] <;>
    norm_num [tableOfEntries, twoPointMass, Fin.sum_univ_two]

namespace ScalarContactChart

/-- Exact bit-to-natural-log score ledger for a bundled contact chart. -/
theorem norm_mul_log_two_mul_score_eq_contactEntropyGap_add_mixingSum
    (C : ContactChart) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hratio : C.ratio = x ^ 4) (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    S.norm * Real.log 2 * C.toTransposeChart.latent.score =
      S.contactEntropyGap + S.mixingSum := by
  let S := C.toScalarChart x hx0 hx1 hmass heq
  have hspec := C.toScalarChart_coordinates x hx0 hx1 hratio hmass heq
  have hlawCells := C.toScalarChart_law x hx0 hx1 hratio hmass heq
  rcases hspec with ⟨hr, hs, hnorm, ha, hb, hc, hd⟩
  rcases hlawCells with ⟨hl00, hl01, hl10, hl11⟩
  have hlawFun : C.toTransposeChart.law =
      tableOfEntries (S.lowMass / S.norm) (S.ell / S.norm)
        (S.e / S.norm) (S.highMass / S.norm) := by
    funext z
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · exact hl00
    · exact hl01
    · exact hl10
    · exact hl11
  have hfirstFun : C.toTransposeChart.firstComponent =
      tableOfEntries (S.lowMass / S.norm) (1 / S.norm)
        (S.r / S.norm) (S.highMass / S.norm) := by
    unfold TransposeChart.firstComponent
    rw [ha, hb, hc, hd]
  have hsecondFun : C.toTransposeChart.secondComponent =
      tableOfEntries (S.lowMass / S.norm) (S.r / S.norm)
        (1 / S.norm) (S.highMass / S.norm) := by
    unfold TransposeChart.secondComponent transposeTableOfEntries
    rw [ha, hb, hc, hd]
  have hsumLaw : S.lowMass + S.ell + S.e + S.highMass = S.norm := by
    calc
      _ = S.e + S.ell + (S.lowMass + S.highMass) := by ring
      _ = S.norm := S.e_add_ell_add_s
  have hsumComponent : S.lowMass + 1 + S.r + S.highMass = S.norm := by
    unfold norm s
    ring
  have hlaw : S.norm * Real.log 2 * entropy C.toTransposeChart.law =
      xLogX S.norm - xLogX S.lowMass - xLogX S.ell - xLogX S.e -
        xLogX S.highMass := by
    rw [hlawFun]
    exact scale_entropy_table S.norm S.lowMass S.ell S.e S.highMass S.norm_pos
      C.lowMass_pos S.ell_pos S.e_pos C.highMass_pos hsumLaw
  have hfirst : S.norm * Real.log 2 * entropy C.toTransposeChart.firstComponent =
      xLogX S.norm - xLogX S.lowMass - xLogX 1 - xLogX S.r -
        xLogX S.highMass := by
    rw [hfirstFun]
    exact scale_entropy_table S.norm S.lowMass 1 S.r S.highMass S.norm_pos
      C.lowMass_pos (by norm_num) S.r_pos C.highMass_pos hsumComponent
  have hrowLaw : stoch_to_det.mX C.toTransposeChart.law =
      twoPointMass ((S.lowMass + S.ell) / S.norm)
        ((S.e + S.highMass) / S.norm) := by
    rw [hlawFun, firstMarginal_table]
    congr 1 <;> ring
  have hcolumnLaw : stoch_to_det.mY C.toTransposeChart.law =
      twoPointMass ((S.lowMass + S.e) / S.norm)
        ((S.ell + S.highMass) / S.norm) := by
    rw [hlawFun, secondMarginal_table]
    congr 1 <;> ring
  have hrowFirst : stoch_to_det.mX C.toTransposeChart.firstComponent =
      twoPointMass ((S.lowMass + 1) / S.norm)
        ((S.r + S.highMass) / S.norm) := by
    rw [hfirstFun, firstMarginal_table]
    congr 1 <;> ring
  have hcolumnFirst : stoch_to_det.mY C.toTransposeChart.firstComponent =
      twoPointMass ((S.lowMass + S.r) / S.norm)
        ((1 + S.highMass) / S.norm) := by
    rw [hfirstFun, secondMarginal_table]
    congr 1 <;> ring
  have hsumLawRow :
      (S.lowMass + S.ell) + (S.e + S.highMass) = S.norm := by
    linarith [hsumLaw]
  have hsumLawColumn :
      (S.lowMass + S.e) + (S.ell + S.highMass) = S.norm := by
    linarith [hsumLaw]
  have hsumComponentRow :
      (S.lowMass + 1) + (S.r + S.highMass) = S.norm := by
    linarith [hsumComponent]
  have hsumComponentColumn :
      (S.lowMass + S.r) + (1 + S.highMass) = S.norm := by
    linarith [hsumComponent]
  have hrowLawScale :
      S.norm * Real.log 2 * entropy (stoch_to_det.mX C.toTransposeChart.law) =
        xLogX S.norm - xLogX (S.lowMass + S.ell) -
          xLogX (S.e + S.highMass) := by
    rw [hrowLaw]
    exact scale_entropy_twoPointMass _ _ _ S.norm_pos
      (add_pos C.lowMass_pos S.ell_pos) (add_pos S.e_pos C.highMass_pos)
      hsumLawRow
  have hcolumnLawScale :
      S.norm * Real.log 2 * entropy (stoch_to_det.mY C.toTransposeChart.law) =
        xLogX S.norm - xLogX (S.lowMass + S.e) -
          xLogX (S.ell + S.highMass) := by
    rw [hcolumnLaw]
    exact scale_entropy_twoPointMass _ _ _ S.norm_pos
      (add_pos C.lowMass_pos S.e_pos) (add_pos S.ell_pos C.highMass_pos)
      hsumLawColumn
  have hrowFirstScale :
      S.norm * Real.log 2 *
          entropy (stoch_to_det.mX C.toTransposeChart.firstComponent) =
        xLogX S.norm - xLogX (S.lowMass + 1) -
          xLogX (S.r + S.highMass) := by
    rw [hrowFirst]
    exact scale_entropy_twoPointMass _ _ _ S.norm_pos
      (add_pos_of_pos_of_nonneg C.lowMass_pos zero_le_one)
      (add_pos S.r_pos C.highMass_pos) hsumComponentRow
  have hcolumnFirstScale :
      S.norm * Real.log 2 *
          entropy (stoch_to_det.mY C.toTransposeChart.firstComponent) =
        xLogX S.norm - xLogX (S.lowMass + S.r) -
          xLogX (1 + S.highMass) := by
    rw [hcolumnFirst]
    exact scale_entropy_twoPointMass _ _ _ S.norm_pos
      (add_pos C.lowMass_pos S.r_pos)
      (add_pos_of_pos_of_nonneg zero_lt_one C.highMass_pos.le)
      hsumComponentColumn
  have hphi : Phi C.toTransposeChart.secondComponent =
      Phi C.toTransposeChart.firstComponent := by
    rw [hsecondFun, hfirstFun]
    unfold Phi stoch_to_det.Phi
    rw [firstMarginal_table, secondMarginal_table,
      firstMarginal_table, secondMarginal_table]
    unfold stoch_to_det.H stoch_to_det.mass
    simp [tableOfEntries, twoPointMass, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring_nf
  change S.norm * Real.log 2 * C.toTransposeChart.latent.score =
    S.contactEntropyGap + S.mixingSum
  rw [latent_score_eq C.toTransposeChart.law_isPMF]
  have hcomponents :
      (∑ v : C.toTransposeChart.latent.ι,
          C.toTransposeChart.latent.prior v * Phi (C.toTransposeChart.latent.comp v)) =
        (1 - C.toTransposeChart.pi) * Phi C.toTransposeChart.firstComponent +
          C.toTransposeChart.pi * Phi C.toTransposeChart.secondComponent := by
    change (∑ v : Bit, C.toTransposeChart.prior v *
      Phi (if v = 0 then C.toTransposeChart.firstComponent
        else C.toTransposeChart.secondComponent)) = _
    rw [Fin.sum_univ_two]
    simp [TransposeChart.prior, twoPointPrior]
  rw [hcomponents, hphi]
  have hprior :
      (1 - C.toTransposeChart.pi) * Phi C.toTransposeChart.firstComponent +
          C.toTransposeChart.pi * Phi C.toTransposeChart.firstComponent =
        Phi C.toTransposeChart.firstComponent := by ring
  rw [hprior]
  have hdistPsi : S.norm * Real.log 2 * Psi C.toTransposeChart.law =
      2 * (S.norm * Real.log 2 * entropy C.toTransposeChart.law) -
      (S.norm * Real.log 2 * entropy (stoch_to_det.mX C.toTransposeChart.law)) -
      (S.norm * Real.log 2 * entropy (stoch_to_det.mY C.toTransposeChart.law)) := by
    unfold Psi stoch_to_det.Psi
    ring
  have hdistPhi :
      S.norm * Real.log 2 * Phi C.toTransposeChart.firstComponent =
        3 * (S.norm * Real.log 2 * entropy C.toTransposeChart.firstComponent) -
        2 * (S.norm * Real.log 2 *
          entropy (stoch_to_det.mX C.toTransposeChart.firstComponent)) -
        2 * (S.norm * Real.log 2 *
          entropy (stoch_to_det.mY C.toTransposeChart.firstComponent)) := by
    unfold Phi stoch_to_det.Phi
    ring
  rw [mul_sub, hdistPsi, hdistPhi]
  rw [hlaw, hrowLawScale, hcolumnLawScale, hfirst,
    hrowFirstScale, hcolumnFirstScale]
  rw [contactEntropyGap_expand, mixingSum_expand, xLogX_one]
  ring_nf

end ScalarContactChart

/-! ## Scaled selector ledger -/

theorem norm_mul_scalarSingletonReward_eq_splitEntropy
    (S : ScalarContactChart) :
    S.norm * scalarSingletonReward S.pi (S.r / S.norm) (1 / S.norm) =
      splitEntropy S.norm S.e -
        4 * ((1 - S.pi) * splitEntropy S.norm S.r +
          S.pi * splitEntropy S.norm 1) := by
  rw [scalarSingletonReward]
  have he :
      (1 - S.pi) * (S.r / S.norm) + S.pi * (1 / S.norm) =
        S.e / S.norm := by
    unfold ScalarContactChart.e
    field_simp [S.norm_pos.ne']
    ring
  rw [he, mul_sub]
  rw [norm_mul_binEntropy_div S.norm S.e S.norm_pos S.e_pos S.e_lt_norm]
  congr 1
  calc
    S.norm * (4 * ((1 - S.pi) * Real.binEntropy (S.r / S.norm) +
        S.pi * Real.binEntropy (1 / S.norm))) =
        4 * ((1 - S.pi) *
            (S.norm * Real.binEntropy (S.r / S.norm)) +
          S.pi * (S.norm * Real.binEntropy (1 / S.norm))) := by ring
    _ = _ := by
      rw [norm_mul_binEntropy_div S.norm S.r S.norm_pos S.r_pos S.r_lt_norm,
        norm_mul_binEntropy_div S.norm 1 S.norm_pos (by norm_num) S.one_lt_norm]

/-- The scaled high-singleton reward is exactly the scalar phase reward. -/
theorem norm_mul_log_two_mul_codeReward_singleton_eq_phaseReward
    (C : ContactChart) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hratio : C.ratio = x ^ 4) (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    S.norm * Real.log 2 *
        codeReward C.toTransposeChart.latent (singletonCode cell10) =
      S.phaseReward := by
  let S := C.toScalarChart x hx0 hx1 hmass heq
  have hspec := C.toScalarChart_coordinates x hx0 hx1 hratio hmass heq
  rcases hspec with ⟨hr, hs, hnorm, ha, hb, hc, hd⟩
  change S.norm * Real.log 2 *
      codeReward C.toTransposeChart.latent (singletonCode cell10) = _
  rw [mul_assoc, log_two_mul_codeReward_singleton]
  have hpi : C.toTransposeChart.pi = S.pi := rfl
  have hfirst : C.toTransposeChart.firstComponent cell10 = S.r / S.norm := by
    simpa [TransposeChart.firstComponent, tableOfEntries, cell10] using hc
  have hsecond : C.toTransposeChart.secondComponent cell10 = 1 / S.norm := by
    simpa [TransposeChart.secondComponent, transposeTableOfEntries,
      tableOfEntries, cell10] using hb
  rw [hpi, hfirst, hsecond,
    norm_mul_scalarSingletonReward_eq_splitEntropy, S.phaseReward_eq_splitEntropy]

/-- Scaling a positive-part maximum by the positive chart normalization and
`Real.log 2` commutes with the maximum. -/
theorem norm_mul_log_two_mul_max_eq_max_mul
    (S : ScalarContactChart) (z : ℝ) :
    S.norm * Real.log 2 * max 0 z =
      max 0 (S.norm * Real.log 2 * z) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hscale : 0 ≤ S.norm * Real.log 2 := mul_nonneg S.norm_pos.le hlog
  by_cases hz : 0 ≤ z
  · rw [max_eq_right hz, max_eq_right (mul_nonneg hscale hz)]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    rw [max_eq_left hz', max_eq_left (mul_nonpos_of_nonneg_of_nonpos hscale hz')]
    ring

/-- The scaled phase-selected cost ledger, conditional on the exact observable
information ledger. -/
theorem norm_mul_log_two_mul_w3Cost_phaseSelector_eq_of_observableInfo
    (C : ContactChart) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hratio : C.ratio = x ^ 4) (hmass : C.lowMass ≤ C.highMass)
    (heq : C.ContactEquation x)
    (hInfo : let S := C.toScalarChart x hx0 hx1 hmass heq
      S.norm * Real.log 2 * Binary.observableInfo C.toTransposeChart.latent =
        S.observableInfo) :
    let S := C.toScalarChart x hx0 hx1 hmass heq
    S.norm * Real.log 2 *
        w3Cost C.toTransposeChart.latent (phaseSelector C.toTransposeChart) =
      S.observableInfo - max 0 S.phaseReward := by
  let S := C.toScalarChart x hx0 hx1 hmass heq
  dsimp only
  rw [w3Cost_phaseSelector_eq_observableInfo_sub_max, mul_sub]
  rw [hInfo, norm_mul_log_two_mul_max_eq_max_mul]
  rw [norm_mul_log_two_mul_codeReward_singleton_eq_phaseReward
    C x hx0 hx1 hratio hmass heq]

end

end StochasticToDeterministicLatents.Binary
