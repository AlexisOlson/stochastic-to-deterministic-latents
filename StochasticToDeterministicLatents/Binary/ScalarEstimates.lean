import StochasticToDeterministicLatents.Binary.ContactChart
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Scalar estimates for binary contact charts

This module collects the shared real-analysis layer for the binary phase
arguments.  Every logarithm and scalar entropy expression in this module is in
natural-log units; conversion to bits belongs to later applications.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents.Binary

noncomputable section

open MeasureTheory Set

/-! ## Odd-log certificates -/

/-- The first `N` terms of the odd-power expansion of
`log ((1 + t) / (1 - t))`. -/
def oddLogPartialSum (N : Nat) (t : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range N, t ^ (2 * k + 1) / ((2 * k + 1 : Nat) : ℝ)

/-- A geometric upper bound for the terms after the first `N` odd powers. -/
def oddLogRemainder (N : Nat) (t : ℝ) : ℝ :=
  2 * t ^ (2 * N + 1) / ((2 * N + 1 : Nat) * (1 - t ^ 2))

/-- Every finite odd-log partial sum is a lower bound on the log ratio on
`[0, 1)`. -/
theorem oddLogPartialSum_le_logRatio (N : Nat) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    oddLogPartialSum N t ≤ Real.log ((1 + t) / (1 - t)) := by
  have h := Real.sum_range_le_log_div ht0 ht1 N
  unfold oddLogPartialSum
  push_cast
  linarith

/-- The explicit geometric remainder bounds the error after the first `N`
odd-log terms on `[0, 1)`. -/
theorem logRatio_le_oddLogPartialSum_add_remainder (N : Nat) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log ((1 + t) / (1 - t)) ≤
      oddLogPartialSum N t + oddLogRemainder N t := by
  let f : Nat → ℝ := fun k ↦
    2 * (1 / ((2 * k + 1 : Nat) : ℝ)) * t ^ (2 * k + 1)
  let g : Nat → ℝ := fun j ↦
    (2 * t ^ (2 * N + 1) / ((2 * N + 1 : Nat) : ℝ)) * (t ^ 2) ^ j
  have habs : |t| < 1 := by simpa [abs_of_nonneg ht0] using ht1
  have hf : Summable f := by
    simpa [f] using (Real.hasSum_log_sub_log_of_abs_lt_one habs).summable
  have ht2 : t ^ 2 < 1 := by nlinarith [sq_nonneg t]
  have hg : Summable g := by
    exact (hasSum_geometric_of_lt_one (sq_nonneg t) ht2).summable.mul_left _
  have hfg : ∀ j, f (j + N) ≤ g j := by
    intro j
    have hden : ((2 * N + 1 : Nat) : ℝ) ≤
        ((2 * (j + N) + 1 : Nat) : ℝ) := by
      exact_mod_cast (by omega : 2 * N + 1 ≤ 2 * (j + N) + 1)
    have hrecip : 1 / ((2 * (j + N) + 1 : Nat) : ℝ) ≤
        1 / ((2 * N + 1 : Nat) : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) hden
    dsimp [f, g]
    rw [show t ^ (2 * (j + N) + 1) = t ^ (2 * N + 1) * (t ^ 2) ^ j by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega]
    calc
      2 * (1 / ↑(2 * (j + N) + 1)) *
          (t ^ (2 * N + 1) * (t ^ 2) ^ j) ≤
          2 * (1 / ↑(2 * N + 1)) *
            (t ^ (2 * N + 1) * (t ^ 2) ^ j) := by
        gcongr
      _ = 2 * t ^ (2 * N + 1) / ↑(2 * N + 1) * (t ^ 2) ^ j := by ring
  have hshift : Summable (fun j ↦ f (j + N)) :=
    hf.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have htail : ∑' j, f (j + N) ≤ ∑' j, g j :=
    hshift.tsum_le_tsum hfg hg
  have hsplit := hf.sum_add_tsum_nat_add N
  have htotal : ∑' k, f k = Real.log ((1 + t) / (1 - t)) := by
    rw [show (∑' k, f k) = Real.log (1 + t) - Real.log (1 - t) by
      simpa [f] using (Real.hasSum_log_sub_log_of_abs_lt_one habs).tsum_eq]
    rw [Real.log_div]
    · positivity
    · positivity
  have hgeom : ∑' j, g j =
      2 * t ^ (2 * N + 1) / (((2 * N + 1 : Nat) : ℝ) * (1 - t ^ 2)) := by
    dsimp [g]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · field_simp
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
      exact ht2
  rw [← htotal, ← hsplit]
  calc
    (∑ i ∈ Finset.range N, f i) + ∑' i, f (i + N) ≤
        (∑ i ∈ Finset.range N, f i) + ∑' i, g i :=
      by simpa [add_comm] using
        add_le_add_left htail (∑ i ∈ Finset.range N, f i)
    _ = oddLogPartialSum N t + oddLogRemainder N t := by
      rw [hgeom]
      unfold oddLogPartialSum oddLogRemainder
      push_cast
      simp only [f, Finset.mul_sum]
      congr 2
      funext i
      push_cast
      ring

/-! ## Contact midpoint and the remaining-range derivative -/

/-- The contact-coordinate denominator. -/
def contactDenominator (x : ℝ) : ℝ := 1 + x + x ^ 2

/-- The contact-coordinate midpoint. -/
def contactMidpoint (x : ℝ) : ℝ := x ^ 3 / contactDenominator x

/-- The logarithmic factor on the remaining range. -/
def remainingLogFactor (x : ℝ) : ℝ :=
  Real.log ((1 + x ^ 3) ^ 2 / (4 * x ^ 3))

/-- The rational correction in the derivative of `remainingRangeProduct`. -/
def remainingRationalCorrection (x : ℝ) : ℝ :=
  3 * (1 + x + x ^ 2) * (1 - x ^ 3) /
    ((1 + x ^ 3) * (3 + 2 * x + x ^ 2))

/-- The one-variable product controlled on the remaining range. -/
def remainingRangeProduct (x : ℝ) : ℝ :=
  contactMidpoint x * remainingLogFactor x

/-- The derivative of the contact midpoint, in factored form. -/
def contactMidpointDerivative (x : ℝ) : ℝ :=
  x ^ 2 * (3 + 2 * x + x ^ 2) / (1 + x + x ^ 2) ^ 2

/-- Numerator in the derivative of the logarithmic correction difference. -/
def remainingDerivativeNumerator (x : ℝ) : ℝ :=
  (1 - x ^ 6) * (3 + 2 * x + x ^ 2) ^ 2
    - 6 * x ^ 3 * (1 + x + x ^ 2) * (3 + 2 * x + x ^ 2)
    + x * (1 - x ^ 6) * (1 + 4 * x + x ^ 2)

/-- Positive denominator in the derivative of the logarithmic correction
difference. -/
def remainingDerivativeDenominator (x : ℝ) : ℝ :=
  (1 + x ^ 3) ^ 2 * (3 + 2 * x + x ^ 2) ^ 2

/-- Derivative of the contact-coordinate denominator. -/
theorem hasDerivAt_contactDenominator {x : ℝ} :
    HasDerivAt contactDenominator (1 + 2 * x) x := by
  have hy : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h := (hy.add hsq).const_add (1 : ℝ)
  apply h.congr_of_eventuallyEq
  filter_upwards with y
  simp only [contactDenominator, Pi.add_apply]
  ring

/-- Derivative of the contact-coordinate midpoint. -/
theorem hasDerivAt_contactMidpoint {x : ℝ} (hx : 0 < x) :
    HasDerivAt contactMidpoint (contactMidpointDerivative x) x := by
  have hnum : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have hden : HasDerivAt (fun y : ℝ => contactDenominator y) (1 + 2 * x) x :=
    hasDerivAt_contactDenominator
  have hdpos : 0 < contactDenominator x := by
    unfold contactDenominator
    nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have hq := hnum.div hden (ne_of_gt hdpos)
  change HasDerivAt (fun y : ℝ => y ^ 3 / contactDenominator y)
    (contactMidpointDerivative x) x
  apply hq.congr_deriv
  simp only [contactMidpointDerivative, contactDenominator]
  field_simp
  ring

/-- Derivative of the logarithmic factor on the positive axis. -/
theorem hasDerivAt_remainingLogFactor {x : ℝ} (hx : 0 < x) :
    HasDerivAt remainingLogFactor
      (-3 * (1 - x ^ 3) / (x * (1 + x ^ 3))) x := by
  have hcube : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have honecube : HasDerivAt (fun y : ℝ => 1 + y ^ 3) (3 * x ^ 2) x :=
    hcube.const_add 1
  have hnum := honecube.pow 2
  have hden := hcube.const_mul 4
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hx)
  have hq := hnum.div hden (mul_ne_zero (by norm_num) hx3)
  have hqpos : 0 < (1 + x ^ 3) ^ 2 / (4 * x ^ 3) := by positivity
  have hlog := (Real.hasDerivAt_log (ne_of_gt hqpos)).comp x hq
  change HasDerivAt
    (fun y : ℝ => Real.log ((1 + y ^ 3) ^ 2 / (4 * y ^ 3)))
    (-3 * (1 - x ^ 3) / (x * (1 + x ^ 3))) x
  apply hlog.congr_deriv
  simp only [Pi.pow_apply, Function.comp_apply]
  field_simp
  ring

/-- Exact derivative ledger for the remaining-range product and correction. -/
theorem remainingRangeDerivativeLedger {x : ℝ} (hx0 : 0 < x) :
    HasDerivAt remainingRangeProduct
        (contactMidpointDerivative x *
          (remainingLogFactor x - remainingRationalCorrection x)) x ∧
    HasDerivAt (fun y => remainingLogFactor y - remainingRationalCorrection y)
      (-3 * remainingDerivativeNumerator x /
        (x * remainingDerivativeDenominator x)) x := by
  have hL := hasDerivAt_remainingLogFactor hx0
  have hy : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hcube : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have hd := hasDerivAt_contactDenominator (x := x)
  have honeSubCube : HasDerivAt (fun y : ℝ => 1 - y ^ 3) (-3 * x ^ 2) x := by
    simpa using hcube.const_sub 1
  have hpRaw := ((hy.const_mul 2).add hsq).const_add 3
  have hp : HasDerivAt (fun y : ℝ => 3 + 2 * y + y ^ 2) (2 + 2 * x) x := by
    apply (hpRaw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.add_apply]
    ring
  have honeAddCube : HasDerivAt (fun y : ℝ => 1 + y ^ 3) (3 * x ^ 2) x :=
    hcube.const_add 1
  have hnumT := ((hd.mul honeSubCube).const_mul 3)
  have hdenT := honeAddCube.mul hp
  have honecubePos : 0 < 1 + x ^ 3 := by positivity
  have hpPos : 0 < 3 + 2 * x + x ^ 2 := by positivity
  have hTraw := hnumT.div hdenT
    (mul_ne_zero (ne_of_gt honecubePos) (ne_of_gt hpPos))
  have hTpoint := hTraw.congr_of_eventuallyEq
    (f₁ := fun y : ℝ =>
      3 * (contactDenominator y * (1 - y ^ 3)) /
        ((1 + y ^ 3) * (3 + 2 * y + y ^ 2))) (by
      filter_upwards with y
      simp only [Pi.div_apply, Pi.mul_apply])
  have hT := hTpoint.congr_of_eventuallyEq (f₁ := remainingRationalCorrection) (by
    filter_upwards with y
    simp only [remainingRationalCorrection, contactDenominator]
    ring)
  constructor
  · have hhRaw := (hasDerivAt_contactMidpoint hx0).mul hL
    change HasDerivAt
      (fun y : ℝ => contactMidpoint y * remainingLogFactor y)
      (contactMidpointDerivative x *
        (remainingLogFactor x - remainingRationalCorrection x)) x
    apply hhRaw.congr_deriv
    simp only [contactMidpoint, contactMidpointDerivative,
      remainingRationalCorrection, contactDenominator]
    field_simp
    ring
  · have hdifference := hL.sub hT
    apply hdifference.congr_deriv
    simp only [remainingDerivativeNumerator, remainingDerivativeDenominator,
      contactDenominator, Pi.mul_apply, Pi.div_apply]
    field_simp
    ring

/-- The contact-midpoint derivative is positive on the positive axis. -/
theorem contactMidpointDerivative_pos {x : ℝ} (hx : 0 < x) :
    0 < contactMidpointDerivative x := by
  unfold contactMidpointDerivative
  positivity

/-- The numerator controlling the second derivative is positive on the
remaining range. -/
theorem remainingDerivativeNumerator_pos {x : ℝ}
    (hlo : 3 / 10 ≤ x) (hhi : x ≤ 1 / 2) :
    0 < remainingDerivativeNumerator x := by
  unfold remainingDerivativeNumerator
  norm_num at hlo hhi ⊢
  have hx0 : 0 ≤ x := by linarith
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg x]
  have hx3 : x ^ 3 ≤ 1 / 8 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx2),
      mul_nonneg (sub_nonneg.mpr hhi) (sq_nonneg x)]
  have hx6 : x ^ 6 ≤ 1 / 64 := by
    nlinarith [mul_nonneg (show 0 ≤ x ^ 3 by positivity) (sub_nonneg.mpr hx3)]
  have hp0 : 0 ≤ 3 + 2 * x + x ^ 2 := by nlinarith [sq_nonneg x]
  have hp3 : 3 ≤ 3 + 2 * x + x ^ 2 := by nlinarith [sq_nonneg x]
  have hp17 : 3 + 2 * x + x ^ 2 ≤ 17 / 4 := by linarith
  have hd0 : 0 ≤ 1 + x + x ^ 2 := by positivity
  have hd7 : 1 + x + x ^ 2 ≤ 7 / 4 := by linarith
  have hpSq9 : 9 ≤ (3 + 2 * x + x ^ 2) ^ 2 := by nlinarith
  have hfirst : 567 / 64 ≤ (1 - x ^ 6) * (3 + 2 * x + x ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx6) (sub_nonneg.mpr hpSq9)]
  have hab : x ^ 3 * (1 + x + x ^ 2) ≤ 7 / 32 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx3) hd0,
      mul_nonneg (sub_nonneg.mpr hd7) (show 0 ≤ x ^ 3 by positivity)]
  have hmiddle : 6 * x ^ 3 * (1 + x + x ^ 2) *
      (3 + 2 * x + x ^ 2) ≤ 357 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hp0,
      mul_nonneg (sub_nonneg.mpr hp17)
        (mul_nonneg (show 0 ≤ x ^ 3 by positivity) hd0)]
  have hlast : 0 ≤ x * (1 - x ^ 6) * (1 + 4 * x + x ^ 2) := by
    exact mul_nonneg (mul_nonneg hx0 (by linarith))
      (by nlinarith [sq_nonneg x])
  nlinarith

/-- The denominator controlling the second derivative is positive on the
remaining range. -/
theorem remainingDerivativeDenominator_pos {x : ℝ}
    (hlo : 3 / 10 ≤ x) :
    0 < remainingDerivativeDenominator x := by
  unfold remainingDerivativeDenominator
  positivity

/-- The logarithmic correction difference strictly decreases on the remaining
range. -/
theorem remainingLogDifference_strictAntiOn :
    StrictAntiOn
      (fun x : ℝ => remainingLogFactor x - remainingRationalCorrection x)
      (Set.Icc (3 / 10) (1 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (3 / 10 : ℝ) (1 / 2))
  · intro x hx
    exact (remainingRangeDerivativeLedger
      (by norm_num at hx ⊢; linarith)).2.continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc (3 / 10) (1 / 2) := interior_subset hx
    rw [(remainingRangeDerivativeLedger
      (by norm_num at hx' ⊢; linarith)).2.deriv]
    have hn := remainingDerivativeNumerator_pos hx'.1 hx'.2
    have hd := remainingDerivativeDenominator_pos hx'.1
    have hx0 : 0 < x := by norm_num at hx' ⊢; linarith
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hn)
      (mul_pos hx0 hd)

/-- On the remaining range, the controlled product cannot dip below both
endpoint values. -/
theorem remainingRangeProduct_ge_min_endpoints {x : ℝ}
    (hlo : 3 / 10 ≤ x) (hhi : x ≤ 1 / 2) :
    min (remainingRangeProduct (3 / 10)) (remainingRangeProduct (1 / 2)) ≤
      remainingRangeProduct x := by
  have hx0 : 0 < x := by norm_num at hlo ⊢; linarith
  by_cases hs : 0 ≤ remainingLogFactor x - remainingRationalCorrection x
  · apply le_trans (min_le_left _ _) ?_
    have hmono : MonotoneOn remainingRangeProduct (Set.Icc (3 / 10) x) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc (3 / 10 : ℝ) x)
      · intro y hy
        exact (remainingRangeDerivativeLedger
          (by norm_num at hy ⊢; linarith)).1.continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Set.Icc (3 / 10) x := interior_subset hy
        exact (remainingRangeDerivativeLedger
          (by norm_num at hy' ⊢; linarith)).1.differentiableAt.differentiableWithinAt
      · intro y hy
        have hy' : y ∈ Set.Icc (3 / 10) x := interior_subset hy
        rw [(remainingRangeDerivativeLedger
          (by norm_num at hy' ⊢; linarith)).1.deriv]
        exact mul_nonneg
          (le_of_lt (contactMidpointDerivative_pos
            (by norm_num at hy' ⊢; linarith)))
          (le_trans hs (remainingLogDifference_strictAntiOn.antitoneOn
            ⟨hy'.1, hy'.2.trans hhi⟩ ⟨hlo, hhi⟩ hy'.2))
    exact hmono ⟨by norm_num, hlo⟩ ⟨hlo, le_rfl⟩ hlo
  · apply le_trans (min_le_right _ _) ?_
    have hs' : remainingLogFactor x - remainingRationalCorrection x < 0 :=
      lt_of_not_ge hs
    have hanti : AntitoneOn remainingRangeProduct (Set.Icc x (1 / 2)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc x (1 / 2 : ℝ))
      · intro y hy
        exact (remainingRangeDerivativeLedger
          (hx0.trans_le hy.1)).1.continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Set.Icc x (1 / 2) := interior_subset hy
        exact (remainingRangeDerivativeLedger
          (hx0.trans_le hy'.1)).1.differentiableAt.differentiableWithinAt
      · intro y hy
        have hy' : y ∈ Set.Icc x (1 / 2) := interior_subset hy
        rw [(remainingRangeDerivativeLedger
          (hx0.trans_le hy'.1)).1.deriv]
        apply mul_nonpos_of_nonneg_of_nonpos
          (le_of_lt (contactMidpointDerivative_pos (hx0.trans_le hy'.1)))
        exact le_trans (remainingLogDifference_strictAntiOn.antitoneOn
          ⟨hlo, hhi⟩ ⟨hlo.trans hy'.1, hy'.2⟩ hy'.1) (le_of_lt hs')
    exact hanti ⟨le_rfl, hhi⟩ ⟨hhi, le_rfl⟩ hhi

/-! ## Inverse hyperbolic tangent -/

/-- The half-log presentation of the inverse hyperbolic tangent. -/
def atanhLog (q : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 + q) / (1 - q))

/-- The half-log surrogate `atanhLog` is positive on `(0, 1)`. -/
theorem atanhLog_pos_on_unitInterval {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < atanhLog q := by
  rw [atanhLog, ← Real.artanh_eq_half_log]
  · exact Real.artanh_pos hq
  · exact ⟨by linarith [hq.1], hq.2.le⟩

/-- The endpoint-zero auxiliary for a contracted `atanhLog` ratio. -/
def atanhEndpointGap (q k : ℝ) : ℝ :=
  (1 - k ^ 2 * q ^ 2) * atanhLog (k * q) -
    k * (1 - q ^ 2) * atanhLog q

/-- Derivative of `atanhLog` on `(-1, 1)`. -/
theorem hasDerivAt_atanhLog {x : ℝ} (hlo : -1 < x) (hhi : x < 1) :
    HasDerivAt atanhLog (1 / (1 - x ^ 2)) x := by
  have hn : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa [add_comm] using (hasDerivAt_id x).const_add 1
  have hd : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hd0 : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have hquot := hn.div hd hd0
  have hquot0 : (1 + x) / (1 - x) ≠ 0 :=
    div_ne_zero (ne_of_gt (by linarith)) hd0
  have hlog := (Real.hasDerivAt_log hquot0).comp x hquot
  change HasDerivAt
    (fun y : ℝ => (1 / 2) * Real.log ((1 + y) / (1 - y)))
    (1 / (1 - x ^ 2)) x
  apply hlog.const_mul (1 / 2 : ℝ) |>.congr_deriv
  have hp0 : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hs0 : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp [hp0, hd0, hs0]
  ring

/-- First derivative of the endpoint-zero auxiliary. -/
theorem hasDerivAt_atanhEndpointGap {q k : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hk0 : 0 < k) (hk1 : k < 1) :
    HasDerivAt (atanhEndpointGap q)
      (q - (1 - q ^ 2) * atanhLog q -
        2 * k * q ^ 2 * atanhLog (k * q)) k := by
  have hkq0 : -1 < k * q := by nlinarith [mul_pos hk0 hq0]
  have hkq1 : k * q < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hk1) hq0,
      mul_pos hk0 (sub_pos.mpr hq1)]
  have hA := (hasDerivAt_atanhLog hkq0 hkq1).comp k
    ((hasDerivAt_id k).mul_const q)
  have hpoly := (((hasDerivAt_pow 2 k).mul_const (q ^ 2)).const_sub 1)
  have hlin := (hasDerivAt_id k).mul_const ((1 - q ^ 2) * atanhLog q)
  have h := (hpoly.mul hA).sub hlin
  have hden : 1 - (k * q) ^ 2 ≠ 0 := by
    nlinarith [mul_pos hk0 hq0]
  have hderiv :
      q - (1 - q ^ 2) * atanhLog q - 2 * k * q ^ 2 * atanhLog (k * q) =
        -(2 * k ^ (2 - 1) * q ^ 2) * atanhLog (k * q) +
          (1 - k ^ 2 * q ^ 2) * (1 / (1 - (k * q) ^ 2) * (1 * q)) -
          1 * ((1 - q ^ 2) * atanhLog q) := by
    have hden' : 1 - q ^ 2 * k ^ 2 ≠ 0 := by nlinarith
    field_simp [hden, hden']
    ring
  apply h.congr_deriv hderiv.symm |>.congr_of_eventuallyEq
  filter_upwards with z
  simp only [atanhEndpointGap, Function.comp_apply, id_eq, Pi.mul_apply,
    Pi.sub_apply]
  ring

/-- The endpoint-zero auxiliary is concave on `[0, 1]`. -/
theorem atanhEndpointGap_concaveOn {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ConcaveOn ℝ (Icc 0 1) (atanhEndpointGap q) := by
  have hcont : ContinuousOn (atanhEndpointGap q) (Icc 0 1) := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hzq_lo : -1 < z * q := by nlinarith [mul_nonneg hz.1 hq0.le]
    have hzq_hi : z * q < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hz.2 hq0.le)
        (by simpa using hq1)
    have hA := (hasDerivAt_atanhLog hzq_lo hzq_hi).continuousAt
    change ContinuousAt
      (fun z : ℝ => (1 - z ^ 2 * q ^ 2) * atanhLog (z * q) -
        z * (1 - q ^ 2) * atanhLog q) z
    fun_prop
  have hdiff : DifferentiableOn ℝ (atanhEndpointGap q)
      (interior (Icc (0 : ℝ) 1)) := by
    intro z hz
    rw [interior_Icc] at hz
    exact (hasDerivAt_atanhEndpointGap hq0 hq1 hz.1 hz.2).differentiableAt
      |>.differentiableWithinAt
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1) hcont hdiff
  intro a ha b hb hab
  rw [interior_Icc] at ha hb
  rw [(hasDerivAt_atanhEndpointGap hq0 hq1 ha.1 ha.2).deriv]
  rw [(hasDerivAt_atanhEndpointGap hq0 hq1 hb.1 hb.2).deriv]
  have haq0 : 0 < a * q := mul_pos ha.1 hq0
  have hbq0 : 0 < b * q := mul_pos hb.1 hq0
  have haq1 : a * q < 1 := by
    nlinarith [mul_pos (sub_pos.mpr ha.2) hq0,
      mul_pos ha.1 (sub_pos.mpr hq1)]
  have hbq1 : b * q < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hb.2) hq0,
      mul_pos hb.1 (sub_pos.mpr hq1)]
  have hAmono : atanhLog (a * q) ≤ atanhLog (b * q) := by
    rw [atanhLog, ← Real.artanh_eq_half_log,
      atanhLog, ← Real.artanh_eq_half_log]
    · exact (Real.artanh_le_artanh_iff ⟨by linarith, haq1⟩
        ⟨by linarith, hbq1⟩).2 (mul_le_mul_of_nonneg_right hab hq0.le)
    · exact ⟨by linarith, hbq1.le⟩
    · exact ⟨by linarith, haq1.le⟩
  have hAa : 0 ≤ atanhLog (a * q) :=
    (atanhLog_pos_on_unitInterval ⟨haq0, haq1⟩).le
  have hAb : 0 ≤ atanhLog (b * q) :=
    (atanhLog_pos_on_unitInterval ⟨hbq0, hbq1⟩).le
  have hprod : a * atanhLog (a * q) ≤ b * atanhLog (b * q) :=
    mul_le_mul hab hAmono hAa hb.1.le
  nlinarith [sq_pos_of_pos hq0]

/-- The endpoint-zero auxiliary is nonnegative on `[0, 1]`. -/
theorem atanhEndpointGap_nonneg {q k : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    0 ≤ atanhEndpointGap q k := by
  have hmin := (atanhEndpointGap_concaveOn hq0 hq1).min_le_of_mem_Icc
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hk0, hk1⟩
  have hzero : atanhEndpointGap q 0 = 0 := by
    simp [atanhEndpointGap, atanhLog]
  have hone : atanhEndpointGap q 1 = 0 := by
    ring_nf
    simp [atanhEndpointGap]
  rw [hzero, hone, min_self] at hmin
  exact hmin

/-- Contraction by `k ∈ (0, 1)` makes the inverse-hyperbolic-tangent ratio
antitone. -/
theorem atanhLog_ratio_antitoneOn {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    AntitoneOn (fun q => atanhLog (k * q) / atanhLog q) (Set.Ioo 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · apply continuousOn_of_forall_continuousAt
    intro q hq
    have hg : atanhLog q ≠ 0 := ne_of_gt (atanhLog_pos_on_unitInterval hq)
    have hkq0 : -1 < k * q := by nlinarith [mul_pos hk0 hq.1]
    have hkq1 : k * q < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hk1) hq.1,
        mul_pos hk0 (sub_pos.mpr hq.2)]
    exact ((hasDerivAt_atanhLog hkq0 hkq1).comp q
      ((hasDerivAt_id q).const_mul k)).continuousAt.div
        (hasDerivAt_atanhLog (by linarith [hq.1]) hq.2).continuousAt hg
  · intro q hq
    rw [interior_Ioo] at hq
    have hg : atanhLog q ≠ 0 := ne_of_gt (atanhLog_pos_on_unitInterval hq)
    have hkq0 : -1 < k * q := by nlinarith [mul_pos hk0 hq.1]
    have hkq1 : k * q < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hk1) hq.1,
        mul_pos hk0 (sub_pos.mpr hq.2)]
    exact (((hasDerivAt_atanhLog hkq0 hkq1).comp q
      ((hasDerivAt_id q).const_mul k)).div
        (hasDerivAt_atanhLog (by linarith [hq.1]) hq.2) hg).differentiableAt
          |>.differentiableWithinAt
  · intro q hq
    rw [interior_Ioo] at hq
    have hgpos := atanhLog_pos_on_unitInterval hq
    have hg : atanhLog q ≠ 0 := ne_of_gt hgpos
    have hkq0 : -1 < k * q := by nlinarith [mul_pos hk0 hq.1]
    have hkq1 : k * q < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hk1) hq.1,
        mul_pos hk0 (sub_pos.mpr hq.2)]
    have hf := (hasDerivAt_atanhLog hkq0 hkq1).comp q
      ((hasDerivAt_id q).const_mul k)
    have hg' := hasDerivAt_atanhLog (by linarith [hq.1]) hq.2
    change deriv ((atanhLog ∘ fun q : ℝ => k * q) / atanhLog) q ≤ 0
    rw [(hf.div hg' hg).deriv]
    have hphi := atanhEndpointGap_nonneg hq.1 hq.2 hk0.le hk1.le
    have hk2 : k ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hk1) (by linarith [hk0] : 0 < 1 + k)]
    have hq2 : q ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hq.2) (by linarith [hq.1] : 0 < 1 + q)]
    have hden1 : 0 < 1 - k ^ 2 * q ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hk2) (sq_pos_of_pos hq.1),
        mul_pos (sq_pos_of_pos hk0) (sub_pos.mpr hq2)]
    have hden2 : 0 < 1 - q ^ 2 := by linarith
    dsimp [atanhEndpointGap] at hphi
    apply div_nonpos_of_nonpos_of_nonneg
    · simp only [Function.comp_apply, mul_one]
      rw [show (k * q) ^ 2 = k ^ 2 * q ^ 2 by ring]
      have hleft : 1 / (1 - k ^ 2 * q ^ 2) * k * atanhLog q =
          (k * atanhLog q) / (1 - k ^ 2 * q ^ 2) := by
        rw [div_eq_mul_inv]
        ring
      have hright : atanhLog (k * q) * (1 / (1 - q ^ 2)) =
          atanhLog (k * q) / (1 - q ^ 2) := by
        simp [div_eq_mul_inv]
      rw [hleft, hright, sub_nonpos, div_le_div_iff₀ hden1 hden2]
      nlinarith
    · exact sq_nonneg (atanhLog q)

/-! ## Bregman shape -/

/-- The derivative of a chart's mixing term on the positive half-line. -/
def mixingSlope (C : ScalarContactChart) (z : ℝ) : ℝ :=
  Real.log ((z + C.e) / z) + Real.log ((z + C.ell) / z) -
    Real.log ((z + C.r) / z) - Real.log ((z + 1) / z)

/-- The product gap between the two off-diagonal mixture masses. -/
def mixingGap (C : ScalarContactChart) : ℝ := C.e * C.ell - C.r

/-- Exact nonnegative factorization of the product gap. -/
theorem mixingGap_eq_prior_factorization (C : ScalarContactChart) :
    mixingGap C = C.pi * (1 - C.pi) * (1 - C.r) ^ 2 := by
  unfold mixingGap ScalarContactChart.e ScalarContactChart.ell
  ring

/-- The product gap is nonnegative on every closed scalar chart. -/
theorem mixingGap_nonnegative (C : ScalarContactChart) : 0 ≤ mixingGap C := by
  rw [mixingGap_eq_prior_factorization]
  have hp1 : 0 ≤ 1 - C.pi := by linarith [C.pi_le_half]
  exact mul_nonneg (mul_nonneg C.pi_nonneg hp1) (sq_nonneg _)

/-- The mixing term vanishes at the origin. -/
@[simp] theorem mixingTerm_zero (C : ScalarContactChart) : C.mixingTerm 0 = 0 := by
  simp [ScalarContactChart.mixingTerm]

/-- Derivative formula for the mixing term away from the origin. -/
theorem hasDerivAt_mixingTerm (C : ScalarContactChart) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (C.mixingTerm) (mixingSlope C z) z := by
  unfold ScalarContactChart.mixingTerm mixingSlope
  convert (((hasDerivAt_pairEntropy_left hz C.e_pos).add
      (hasDerivAt_pairEntropy_left hz C.ell_pos)).sub
      (hasDerivAt_pairEntropy_left hz C.r_pos)).sub
      (hasDerivAt_pairEntropy_left hz (by norm_num : (0 : ℝ) < 1)) using 1 <;> rfl

/-- Algebraic product identity underlying the Bregman shape. -/
theorem shifted_product_sub_eq_mixingGap (C : ScalarContactChart) (z : ℝ) :
    (z + C.e) * (z + C.ell) - (z + C.r) * (z + 1) = mixingGap C := by
  unfold mixingGap
  calc
    (z + C.e) * (z + C.ell) - (z + C.r) * (z + 1) =
        z * (C.e + C.ell - (1 + C.r)) + C.e * C.ell - C.r := by ring
    _ = C.e * C.ell - C.r := by rw [C.e_add_ell]; ring

/-- The mixing slope is nonnegative on the positive half-line. -/
theorem mixingSlope_nonnegative (C : ScalarContactChart) {z : ℝ} (hz : 0 < z) :
    0 ≤ mixingSlope C z := by
  have hze : 0 < z + C.e := add_pos hz C.e_pos
  have hzl : 0 < z + C.ell := add_pos hz C.ell_pos
  have hzr : 0 < z + C.r := add_pos hz C.r_pos
  have hz1 : 0 < z + 1 := by linarith
  have hprod : (z + C.r) * (z + 1) ≤ (z + C.e) * (z + C.ell) := by
    linarith [shifted_product_sub_eq_mixingGap C z, mixingGap_nonnegative C]
  have hlog : Real.log ((z + C.r) * (z + 1)) ≤
      Real.log ((z + C.e) * (z + C.ell)) :=
    Real.strictMonoOn_log.monotoneOn
      (by exact mul_pos hzr hz1 : (z + C.r) * (z + 1) ∈ Ioi 0)
      (by exact mul_pos hze hzl : (z + C.e) * (z + C.ell) ∈ Ioi 0) hprod
  rw [Real.log_mul hze.ne' hzl.ne', Real.log_mul hzr.ne' hz1.ne'] at hlog
  unfold mixingSlope
  rw [Real.log_div hze.ne' hz.ne', Real.log_div hzl.ne' hz.ne',
    Real.log_div hzr.ne' hz.ne', Real.log_div hz1.ne' hz.ne']
  linarith

/-- Global continuity of a chart's mixing term. -/
theorem continuous_mixingTerm (C : ScalarContactChart) : Continuous C.mixingTerm := by
  unfold ScalarContactChart.mixingTerm
  have h (v : ℝ) : Continuous (fun z : ℝ => pairEntropy z v) :=
    continuous_pairEntropy.comp (continuous_id.prodMk continuous_const)
  exact ((h C.e).add (h C.ell)).sub (h C.r) |>.sub (h 1)

/-- Logarithmic product-ratio form of the mixing slope. -/
theorem mixingSlope_eq_log_product_ratio (C : ScalarContactChart)
    {z : ℝ} (hz : 0 < z) :
    mixingSlope C z = Real.log (((z + C.e) * (z + C.ell)) /
      ((z + C.r) * (z + 1))) := by
  have hze : z + C.e ≠ 0 := (add_pos hz C.e_pos).ne'
  have hzl : z + C.ell ≠ 0 := (add_pos hz C.ell_pos).ne'
  have hzr : z + C.r ≠ 0 := (add_pos hz C.r_pos).ne'
  have hz1 : z + 1 ≠ 0 := (by linarith : 0 < z + 1).ne'
  unfold mixingSlope
  rw [Real.log_div hze hz.ne', Real.log_div hzl hz.ne',
    Real.log_div hzr hz.ne', Real.log_div hz1 hz.ne',
    Real.log_div (mul_ne_zero hze hzl) (mul_ne_zero hzr hz1),
    Real.log_mul hze hzl, Real.log_mul hzr hz1]
  ring

/-- Rational form of the product ratio, exposing its fixed nonnegative gap. -/
theorem mixing_product_ratio_eq_one_add (C : ScalarContactChart)
    {z : ℝ} (hz : 0 < z) :
    ((z + C.e) * (z + C.ell)) / ((z + C.r) * (z + 1)) =
      1 + mixingGap C / ((z + C.r) * (z + 1)) := by
  have hden : (z + C.r) * (z + 1) ≠ 0 :=
    (mul_pos (add_pos hz C.r_pos) (by linarith)).ne'
  rw [one_add_div hden]
  congr 1
  linarith [shifted_product_sub_eq_mixingGap C z]

/-- The mixing slope is antitone on the positive half-line. -/
theorem mixingSlope_antitone (C : ScalarContactChart) :
    AntitoneOn (mixingSlope C) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  have har : 0 < a + C.r := add_pos ha C.r_pos
  have hbr : 0 < b + C.r := add_pos hb C.r_pos
  have ha1 : 0 < a + 1 := by linarith
  have hb1 : 0 < b + 1 := by linarith
  have hUa : 0 < (a + C.r) * (a + 1) := mul_pos har ha1
  have hUb : 0 < (b + C.r) * (b + 1) := mul_pos hbr hb1
  have hU : (a + C.r) * (a + 1) ≤ (b + C.r) * (b + 1) :=
    mul_le_mul (by linarith) (by linarith) ha1.le hbr.le
  have hfrac : mixingGap C / ((b + C.r) * (b + 1)) ≤
      mixingGap C / ((a + C.r) * (a + 1)) := by
    exact div_le_div_of_nonneg_left (mixingGap_nonnegative C) hUa hU
  rw [mixingSlope_eq_log_product_ratio C ha,
    mixingSlope_eq_log_product_ratio C hb,
    mixing_product_ratio_eq_one_add C ha,
    mixing_product_ratio_eq_one_add C hb]
  exact Real.strictMonoOn_log.monotoneOn
    (by
      simp only [mem_Ioi]
      linarith [mixingGap_nonnegative C,
        div_nonneg (mixingGap_nonnegative C) hUb.le])
    (by
      simp only [mem_Ioi]
      linarith [mixingGap_nonnegative C,
        div_nonneg (mixingGap_nonnegative C) hUa.le])
    (by linarith)

/-- Concavity of the mixing term on the closed nonnegative half-line. -/
theorem mixingTerm_concave (C : ScalarContactChart) :
    ConcaveOn ℝ (Ici 0) C.mixingTerm := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
      (continuous_mixingTerm C).continuousOn ?_ ?_
  · intro z hz
    rw [interior_Ici, mem_Ioi] at hz
    exact (hasDerivAt_mixingTerm C hz).differentiableAt.differentiableWithinAt
  · intro a ha b hb hab
    rw [interior_Ici, mem_Ioi] at ha hb
    rw [(hasDerivAt_mixingTerm C ha).deriv, (hasDerivAt_mixingTerm C hb).deriv]
    exact mixingSlope_antitone C ha hb hab

/-- Concavity pays the total-mass mixing contribution from the two diagonal
masses. -/
theorem offDiagonalLoss_le_mixingSum (C : ScalarContactChart) :
    C.offDiagonalLoss ≤ C.mixingSum := by
  by_cases hs : C.s = 0
  · have hs' : C.lowMass + C.highMass = 0 := by simpa [ScalarContactChart.s] using hs
    have hlow : C.lowMass = 0 := by
      linarith [C.lowMass_nonneg, C.highMass_nonneg]
    have hhigh : C.highMass = 0 := by
      linarith [C.lowMass_nonneg, C.highMass_nonneg]
    simp [ScalarContactChart.offDiagonalLoss, ScalarContactChart.mixingSum,
      hs, hlow, hhigh]
  · have hspos : 0 < C.s := lt_of_le_of_ne C.s_nonneg (Ne.symm hs)
    let a : ℝ := C.lowMass / C.s
    let d : ℝ := C.highMass / C.s
    have ha : 0 ≤ a := div_nonneg C.lowMass_nonneg C.s_nonneg
    have hd : 0 ≤ d := div_nonneg C.highMass_nonneg C.s_nonneg
    have had : a + d = 1 := by
      dsimp [a, d]
      rw [← add_div]
      exact div_self hs
    have hconvLow := (mixingTerm_concave C).2
      (show C.s ∈ Ici 0 from C.s_nonneg) (by simp : (0 : ℝ) ∈ Ici 0)
      ha hd had
    have hconvHigh := (mixingTerm_concave C).2
      (by simp : (0 : ℝ) ∈ Ici 0) (show C.s ∈ Ici 0 from C.s_nonneg)
      ha hd had
    have hLowScale : a * C.s = C.lowMass := by
      dsimp [a]
      field_simp [hs]
    have hHighScale : d * C.s = C.highMass := by
      dsimp [d]
      field_simp [hs]
    change a * C.mixingTerm C.s + d * C.mixingTerm 0 ≤
      C.mixingTerm (a * C.s + d * 0) at hconvLow
    change a * C.mixingTerm 0 + d * C.mixingTerm C.s ≤
      C.mixingTerm (a * 0 + d * C.s) at hconvHigh
    simp only [mixingTerm_zero, mul_zero, add_zero, hLowScale] at hconvLow
    simp only [mixingTerm_zero, mul_zero, zero_add, hHighScale] at hconvHigh
    have hscale : (a + d) * C.mixingTerm C.s ≤
        C.mixingTerm C.lowMass + C.mixingTerm C.highMass := by
      nlinarith [hconvLow, hconvHigh]
    rw [had, one_mul] at hscale
    exact hscale

/-! ## Integral representations -/

/-- The rational kernel integrated over the finite interval `(0, z]`. -/
def mixingKernelBelow (C : ScalarContactChart) (c z : ℝ) : ℝ :=
  ∫ t in Ioc 0 z, 1 / (((t + C.r) * (t + 1)) + c)

/-- The rational kernel integrated over the positive half-line. -/
def mixingKernelTotal (C : ScalarContactChart) (c : ℝ) : ℝ :=
  ∫ t in Ioi 0, 1 / (((t + C.r) * (t + 1)) + c)

/-- The finite kernel vanishes when its upper endpoint is zero. -/
@[simp] theorem mixingKernelBelow_zero (C : ScalarContactChart) (c : ℝ) :
    mixingKernelBelow C c 0 = 0 := by
  simp [mixingKernelBelow]

/-- The improper kernel is nonnegative for a nonnegative gap parameter. -/
theorem mixingKernelTotal_nonnegative (C : ScalarContactChart) {c : ℝ}
    (hc : 0 ≤ c) : 0 ≤ mixingKernelTotal C c := by
  unfold mixingKernelTotal
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hden : 0 < (t + C.r) * (t + 1) + c := by
    have htr : 0 < t + C.r := add_pos ht0 C.r_pos
    have ht1 : 0 < t + 1 := by linarith
    positivity
  positivity

private theorem integral_one_div_add (A g : ℝ) (hA : 0 < A) (hg : 0 ≤ g) :
    ∫ c in Ioc 0 g, 1 / (A + c) = Real.log (A + g) - Real.log A := by
  rw [← intervalIntegral.integral_of_le hg]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := g) (f := Real.log ∘ fun c => A + c)
    (f' := fun c => 1 / (A + c))
    (fun c hc => by
      have hc0 : 0 ≤ c := (uIcc_of_le hg ▸ hc).1
      simpa only [zero_add, mul_one, one_div] using
        (Real.hasDerivAt_log (ne_of_gt (add_pos_of_pos_of_nonneg hA hc0))).comp c
          ((hasDerivAt_const c A).add (hasDerivAt_id c)))
    (by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add continuousOn_id)
      intro c hc hzero
      have hc0 : 0 ≤ c := (uIcc_of_le hg ▸ hc).1
      exact (ne_of_gt (add_pos_of_pos_of_nonneg hA hc0)) hzero)
  simpa [Function.comp_def] using h

private theorem integral_mixingGap_eq_mixingSlope
    (C : ScalarContactChart) {t : ℝ} (ht : 0 < t) :
    ∫ c in Ioc 0 (mixingGap C),
        1 / (((t + C.r) * (t + 1)) + c) = mixingSlope C t := by
  let A := (t + C.r) * (t + 1)
  have hA : 0 < A := mul_pos (add_pos ht C.r_pos) (by linarith)
  rw [integral_one_div_add A (mixingGap C) hA (mixingGap_nonnegative C)]
  have hshift : A + mixingGap C = (t + C.e) * (t + C.ell) := by
    dsimp [A]
    linarith [shifted_product_sub_eq_mixingGap C t]
  rw [hshift, ← Real.log_div
    (mul_pos (add_pos ht C.e_pos) (add_pos ht C.ell_pos)).ne' hA.ne']
  exact (mixingSlope_eq_log_product_ratio C ht).symm

private theorem mixingKernel_rectangle_integrable
    (C : ScalarContactChart) {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (Function.uncurry (fun c t : ℝ =>
      1 / (((t + C.r) * (t + 1)) + c)))
      (uIoc 0 (mixingGap C) ×ˢ uIoc 0 z) := by
  have hcont : ContinuousOn (Function.uncurry (fun c t : ℝ =>
      1 / (((t + C.r) * (t + 1)) + c)))
      (Icc 0 (mixingGap C) ×ˢ Icc 0 z) := by
    apply ContinuousOn.div
      (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (1 : ℝ)) _)
      (((continuousOn_snd.add continuousOn_const).mul
        (continuousOn_snd.add continuousOn_const)).add continuousOn_fst)
    rintro ⟨c, t⟩ ⟨hc, ht⟩ hzero
    change 0 ≤ c ∧ c ≤ mixingGap C at hc
    change 0 ≤ t ∧ t ≤ z at ht
    have hden : 0 < (t + C.r) * (t + 1) + c := by
      have htr : 0 < t + C.r := add_pos_of_nonneg_of_pos ht.1 C.r_pos
      have ht1 : 0 < t + 1 := by linarith
      exact add_pos_of_pos_of_nonneg (mul_pos htr ht1) hc.1
    exact hden.ne' hzero
  apply (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  rintro ⟨c, t⟩ ⟨hc, ht⟩
  rw [uIoc_of_le (mixingGap_nonnegative C)] at hc
  rw [uIoc_of_le hz] at ht
  exact ⟨⟨hc.1.le, hc.2⟩, ⟨ht.1.le, ht.2⟩⟩

/-- Finite double-integral representation of the mixing term. -/
theorem mixingTerm_eq_integral_kernel (C : ScalarContactChart)
    {z : ℝ} (hz : 0 ≤ z) :
    C.mixingTerm z =
      ∫ c in Ioc 0 (mixingGap C), mixingKernelBelow C c z := by
  rcases eq_or_lt_of_le hz with rfl | hz
  · simp
  have hrect := mixingKernel_rectangle_integrable C hz.le
  have hinner : IntervalIntegrable (mixingSlope C) volume 0 z := by
    rw [intervalIntegrable_iff, uIoc_of_le hz.le]
    have hr : Integrable (Function.uncurry (fun c t : ℝ =>
        1 / (((t + C.r) * (t + 1)) + c)))
        ((volume.restrict (Ioc 0 (mixingGap C))).prod
          (volume.restrict (Ioc 0 z))) := by
      change Integrable _ ((volume.prod volume).restrict
        (uIoc 0 (mixingGap C) ×ˢ uIoc 0 z)) at hrect
      rw [Measure.prod_restrict]
      simpa [uIoc_of_le (mixingGap_nonnegative C), uIoc_of_le hz.le] using hrect
    have hi := hr.integral_prod_right
    change IntegrableOn (fun t => ∫ c in Ioc 0 (mixingGap C),
      1 / (((t + C.r) * (t + 1)) + c)) (Ioc 0 z) at hi
    exact hi.congr_fun
      (fun t ht => integral_mixingGap_eq_mixingSlope C ht.1) measurableSet_Ioc
  have hb : C.mixingTerm z = ∫ t in Ioc 0 z, mixingSlope C t := by
    rw [← intervalIntegral.integral_of_le hz.le]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz.le
      (continuous_mixingTerm C).continuousOn
      (fun t ht => hasDerivAt_mixingTerm C ht.1) hinner
    simpa using h.symm
  rw [hb, ← intervalIntegral.integral_of_le hz.le,
    ← intervalIntegral.integral_of_le (mixingGap_nonnegative C)]
  simp only [mixingKernelBelow]
  simp_rw [← intervalIntegral.integral_of_le hz.le]
  rw [MeasureTheory.intervalIntegral_intervalIntegral_swap hrect]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t
  intro ht
  rw [uIoc_of_le hz.le] at ht
  rw [intervalIntegral.integral_of_le (mixingGap_nonnegative C)]
  exact (integral_mixingGap_eq_mixingSlope C ht.1).symm

/-- The two off-diagonal mixture masses sum to `1 + r`. -/
theorem mixtureMass_sum_eq_one_add_r (C : ScalarContactChart) :
    C.e + C.ell = 1 + C.r := by
  have h0 := shifted_product_sub_eq_mixingGap C 0
  have h1 := shifted_product_sub_eq_mixingGap C 1
  linarith

private theorem tendsto_add_mul_log_one_add_div (c : ℝ) :
    Filter.Tendsto (fun z : ℝ => (z + c) * Real.log (1 + c / z))
      Filter.atTop (nhds c) := by
  have hmain := Real.tendsto_mul_log_one_add_div_atTop c
  have hdiv : Filter.Tendsto (fun z : ℝ => c / z) Filter.atTop (nhds 0) := by
    exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => c)
      Filter.atTop (nhds c)).div_atTop
        (Filter.tendsto_atTop.2 (fun b => Filter.eventually_ge_atTop b))
  have hlog : Filter.Tendsto (fun z : ℝ => Real.log (1 + c / z))
      Filter.atTop (nhds 0) := by
    simpa using (((tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      Filter.atTop (nhds 1)).add hdiv).log (by norm_num))
  convert hmain.add (hlog.const_mul c) using 1
  · funext z
    ring
  · ring_nf

/-- The mixing term converges to its homogeneous entropy endpoint value. -/
theorem tendsto_mixingTerm_atTop (C : ScalarContactChart) :
    Filter.Tendsto C.mixingTerm Filter.atTop
      (nhds (C.r * Real.log C.r - C.e * Real.log C.e -
        C.ell * Real.log C.ell)) := by
  have hchart : C.e + C.ell = 1 + C.r := mixtureMass_sum_eq_one_add_r C
  have hrewrite : ∀ᶠ z : ℝ in Filter.atTop,
      C.mixingTerm z =
        (z + C.e) * Real.log (1 + C.e / z) +
        (z + C.ell) * Real.log (1 + C.ell / z) -
        (z + C.r) * Real.log (1 + C.r / z) -
        (z + 1) * Real.log (1 + 1 / z) +
        C.r * Real.log C.r - C.e * Real.log C.e -
        C.ell * Real.log C.ell := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    rw [C.mixingTerm_expand]
    have hzpos : 0 < z := zero_lt_one.trans_le hz
    have hz0 : z ≠ 0 := hzpos.ne'
    have hfac (c : ℝ) : z + c = z * (1 + c / z) := by field_simp
    have hlog (c : ℝ) (hc : 0 < c) :
        Real.log (z + c) = Real.log z + Real.log (1 + c / z) := by
      rw [hfac, Real.log_mul hz0]
      have : 1 + c / z ≠ 0 := by positivity
      exact this
    simp only [xLogX]
    rw [hlog C.e C.e_pos, hlog C.ell C.ell_pos, hlog C.r C.r_pos,
      hlog 1 (by norm_num)]
    linear_combination (Real.log z) * hchart
  have hlim := (((tendsto_add_mul_log_one_add_div C.e).add
      (tendsto_add_mul_log_one_add_div C.ell)).sub
      (tendsto_add_mul_log_one_add_div C.r)).sub
      (tendsto_add_mul_log_one_add_div 1) |>.add
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ =>
        C.r * Real.log C.r - C.e * Real.log C.e - C.ell * Real.log C.ell)
        Filter.atTop _)
  have hlim' : Filter.Tendsto (fun z : ℝ =>
        (z + C.e) * Real.log (1 + C.e / z) +
        (z + C.ell) * Real.log (1 + C.ell / z) -
        (z + C.r) * Real.log (1 + C.r / z) -
        (z + 1) * Real.log (1 + 1 / z) +
        C.r * Real.log C.r - C.e * Real.log C.e - C.ell * Real.log C.ell)
      Filter.atTop (nhds (C.r * Real.log C.r - C.e * Real.log C.e -
        C.ell * Real.log C.ell)) := by
    convert hlim using 1
    · funext z
      ring
    · congr 1
      linarith
  apply hlim'.congr'
  filter_upwards [hrewrite] with z hz
  exact hz.symm

/-- Closed logarithmic form of the chart's observable information. -/
theorem observableInfo_eq_r_log_r_sub (C : ScalarContactChart) :
    C.observableInfo =
      C.r * Real.log C.r - C.e * Real.log C.e - C.ell * Real.log C.ell := by
  rw [C.observableInfo_expand]
  rfl

/-- The mixing slope is integrable on the positive half-line. -/
theorem integrableOn_mixingSlope_Ioi (C : ScalarContactChart) :
    MeasureTheory.IntegrableOn (mixingSlope C) (Set.Ioi 0)
      MeasureTheory.volume := by
  have hlow : IntegrableOn (mixingSlope C) (Ioc 0 1) := by
    let f : ℝ → ℝ := fun z => Real.log (((z + C.e) * (z + C.ell)) /
      ((z + C.r) * (z + 1)))
    have hf : ContinuousOn f (Icc 0 1) := by
      apply ContinuousOn.log
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro z hz hzero
          have hzr : 0 < z + C.r := add_pos_of_nonneg_of_pos hz.1 C.r_pos
          have hz1 : 0 < z + 1 := by linarith [hz.1]
          exact (mul_pos hzr hz1).ne' hzero
      · intro z hz
        have hze : 0 < z + C.e := add_pos_of_nonneg_of_pos hz.1 C.e_pos
        have hzl : 0 < z + C.ell := add_pos_of_nonneg_of_pos hz.1 C.ell_pos
        have hzr : 0 < z + C.r := add_pos_of_nonneg_of_pos hz.1 C.r_pos
        have hz1 : 0 < z + 1 := by linarith [hz.1]
        exact (div_pos (mul_pos hze hzl) (mul_pos hzr hz1)).ne'
    have hfint : IntegrableOn f (Ioc 0 1) :=
      (hf.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    exact hfint.congr_fun
      (fun z hz => (mixingSlope_eq_log_product_ratio C hz.1).symm)
      measurableSet_Ioc
  have hhigh : IntegrableOn (mixingSlope C) (Ioi 1) := by
    exact integrableOn_Ioi_deriv_of_nonneg'
      (g := C.mixingTerm) (g' := mixingSlope C) (l := C.observableInfo)
      (fun z hz => hasDerivAt_mixingTerm C (zero_lt_one.trans_le hz))
      (fun z hz => mixingSlope_nonnegative C (zero_lt_one.trans_le hz.le))
      (by simpa [observableInfo_eq_r_log_r_sub] using tendsto_mixingTerm_atTop C)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hlow.union hhigh

/-- Improper double-integral representation of the chart's observable
information. -/
theorem observableInfo_eq_integral_kernel (C : ScalarContactChart) :
    C.observableInfo =
      ∫ c in Ioc 0 (mixingGap C), mixingKernelTotal C c := by
  let f : ℝ × ℝ → ℝ := fun p =>
    1 / (((p.2 + C.r) * (p.2 + 1)) + p.1)
  let μ : Measure ℝ := volume.restrict (Ioc 0 (mixingGap C))
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  have hfmeas : AEStronglyMeasurable f (μ.prod ν) := by
    apply Measurable.aestronglyMeasurable
    dsimp [f]
    fun_prop
  have hf : Integrable f (μ.prod ν) := by
    rw [integrable_prod_iff' hfmeas]
    constructor
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with t ht
      have hcont : ContinuousOn (fun c : ℝ =>
          1 / (((t + C.r) * (t + 1)) + c)) (Icc 0 (mixingGap C)) := by
        apply ContinuousOn.div continuousOn_const
          (continuousOn_const.add continuousOn_id)
        intro c hc hzero
        have ht1 : 0 < t + 1 := add_pos ht (by norm_num)
        have hbase : 0 < (t + C.r) * (t + 1) :=
          mul_pos (add_pos ht C.r_pos) ht1
        exact (add_pos_of_pos_of_nonneg hbase hc.1).ne' hzero
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self
    · have hnorm : ∀ᵐ t : ℝ ∂ν,
          (∫ c, ‖f (c, t)‖ ∂μ) = mixingSlope C t := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        filter_upwards with t ht
        change (∫ c in Ioc 0 (mixingGap C),
          ‖1 / (((t + C.r) * (t + 1)) + c)‖) = mixingSlope C t
        rw [← integral_mixingGap_eq_mixingSlope C ht]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with c hc
        rw [Real.norm_eq_abs, abs_of_pos]
        have hbase : 0 < (t + C.r) * (t + 1) :=
          mul_pos (add_pos ht C.r_pos) (add_pos ht (by norm_num))
        exact one_div_pos.mpr (add_pos_of_pos_of_nonneg hbase hc.1.le)
      have hbint : Integrable (mixingSlope C) ν := by
        change IntegrableOn (mixingSlope C) (Ioi 0) volume
        exact integrableOn_mixingSlope_Ioi C
      exact hbint.congr (Filter.EventuallyEq.symm hnorm)
  have hswap := integral_prod f hf
  have hswap' := integral_prod_symm f hf
  have hbeta : (∫ t in Ioi 0, mixingSlope C t) = C.observableInfo := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := C.mixingTerm) (f' := mixingSlope C) (m := C.observableInfo)
      (a := (0 : ℝ)) (continuous_mixingTerm C).continuousAt.continuousWithinAt
      (fun z hz => hasDerivAt_mixingTerm C hz)
      (integrableOn_mixingSlope_Ioi C)
      (by simpa [observableInfo_eq_r_log_r_sub] using tendsto_mixingTerm_atTop C)
    simpa using h
  rw [← hbeta]
  change (∫ t, mixingSlope C t ∂ν) = ∫ c, mixingKernelTotal C c ∂μ
  calc
    (∫ t, mixingSlope C t ∂ν) = ∫ t, ∫ c, f (c, t) ∂μ ∂ν := by
      apply integral_congr_ae
      change mixingSlope C =ᵐ[volume.restrict (Ioi 0)] _
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change mixingSlope C t = ∫ c in Ioc 0 (mixingGap C),
        1 / (((t + C.r) * (t + 1)) + c)
      exact (integral_mixingGap_eq_mixingSlope C ht).symm
    _ = ∫ z, f z ∂μ.prod ν := hswap'.symm
    _ = ∫ c, ∫ t, f (c, t) ∂ν ∂μ := hswap
    _ = ∫ c, mixingKernelTotal C c ∂μ := by
      apply integral_congr_ae
      filter_upwards with c
      rfl

/-! ## Two-point entropy envelopes -/

/-- Homogeneous pair entropy as the sum of its two perspective terms. -/
theorem pairEntropy_eq_sum_logs {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    pairEntropy u v =
      u * Real.log ((u + v) / u) + v * Real.log ((u + v) / v) := by
  rw [pairEntropy, xLogX, Real.log_div (add_pos hu hv).ne' hu.ne',
    Real.log_div (add_pos hu hv).ne' hv.ne']
  unfold xLogX
  ring

/-- A one-sided upper estimate retaining the logarithmic cost of the left
mass. -/
theorem pairEntropy_le_left_log {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    pairEntropy u v ≤ u * (1 + Real.log ((u + v) / u)) := by
  rcases hv.eq_or_lt with rfl | hv
  · simpa using hu.le
  rw [pairEntropy_eq_sum_logs hu hv]
  have hratio : 0 < (u + v) / v := div_pos (add_pos hu hv) hv
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hvlog : v * Real.log ((u + v) / v) ≤ u := by
    calc
      v * Real.log ((u + v) / v) ≤ v * ((u + v) / v - 1) :=
        mul_le_mul_of_nonneg_left hlog hv.le
      _ = u := by field_simp; ring
  linarith

/-- A lower bound for unit-mass pair entropy valid at both endpoints. -/
theorem pairEntropy_unit_lower {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z * Real.log (1 / z) + z * (1 - z) ≤ pairEntropy z (1 - z) := by
  rcases hz0.eq_or_lt with rfl | hz
  · simp
  rcases hz1.eq_or_lt with h | hz1
  · subst z
    simp
  have h1z : 0 < 1 - z := sub_pos.mpr hz1
  rw [pairEntropy_eq_sum_logs hz h1z]
  have hsum : z + (1 - z) = 1 := by ring
  rw [hsum]
  have hlog : z ≤ Real.log (1 / (1 - z)) := by
    simpa using Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr h1z)
  nlinarith

private lemma log_le_sub_inv_average {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - 1 / x) / 2 := by
  let f : ℝ → ℝ := fun z ↦ (z - 1 / z) / 2 - Real.log z
  have hcont : ContinuousOn f (Set.Icc 1 x) := by
    intro z hz
    have hz0 : z ≠ 0 := by nlinarith [hz.1]
    exact (((continuousAt_id.sub
      (continuousAt_const.div continuousAt_id hz0)).div_const 2).sub
        (Real.continuousAt_log hz0)).continuousWithinAt
  have hderiv : ∀ z ∈ Set.Ioo (1 : ℝ) x,
      HasDerivAt f ((z - 1) ^ 2 / (2 * z ^ 2)) z := by
    intro z hz
    have hz0 : z ≠ 0 := by nlinarith [hz.1]
    have hdiv := (hasDerivAt_const z (1 : ℝ)).div (hasDerivAt_id z) hz0
    have h := (((hasDerivAt_id z).sub hdiv).div_const 2).sub
      (Real.hasDerivAt_log hz0)
    change HasDerivAt (fun z ↦ (z - 1 / z) / 2 - Real.log z)
      ((z - 1) ^ 2 / (2 * z ^ 2)) z
    exact h.congr_deriv (by simp only [id_eq]; field_simp [hz0]; ring)
  have hmono : MonotoneOn f (Set.Icc 1 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (1 : ℝ) x) hcont
    · rw [interior_Icc]
      exact fun z hz ↦ (hderiv z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      rw [(hderiv z hz).deriv]
      positivity
  have h := hmono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  simpa [f] using h

private lemma negLogOneSub_quadratic_lower {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t ^ 2 / 2 ≤ Real.log (1 / (1 - t)) := by
  let f : ℝ → ℝ := fun z ↦ -Real.log (1 - z) - z - z ^ 2 / 2
  have hcont : ContinuousOn f (Set.Icc 0 t) := by
    intro z hz
    have hz1 : 1 - z ≠ 0 := by nlinarith [hz.2]
    exact ((((Real.continuousAt_log hz1).comp
      (continuousAt_const.sub continuousAt_id)).neg.sub continuousAt_id).sub
        ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
  have hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt f (z ^ 2 / (1 - z)) z := by
    intro z hz
    have hz1 : 1 - z ≠ 0 := by nlinarith [hz.2]
    have hlog := (Real.hasDerivAt_log hz1).comp z
      ((hasDerivAt_const z 1).sub (hasDerivAt_id z))
    have h := ((hlog.neg.sub (hasDerivAt_id z)).sub
      (((hasDerivAt_id z).pow 2).div_const 2))
    change HasDerivAt (fun z ↦ -Real.log (1 - z) - z - z ^ 2 / 2)
      (z ^ 2 / (1 - z)) z
    exact h.congr_deriv (by simp only [id_eq]; field_simp [hz1]; ring)
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) t) hcont
    · rw [interior_Icc]
      exact fun z hz ↦ (hderiv z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      rw [(hderiv z hz).deriv]
      exact div_nonneg (sq_nonneg z) (by nlinarith [hz.2])
  have h := hmono (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
  rw [show Real.log (1 / (1 - t)) = -Real.log (1 - t) by
    rw [Real.log_div (by norm_num) (by positivity)]
    simp]
  dsimp [f] at h
  norm_num at h
  linarith

private lemma oneSub_mul_negLog_envelope {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t - t ^ 2 / 2 - t ^ 3 / 2 ≤
        (1 - t) * Real.log (1 / (1 - t)) ∧
      (1 - t) * Real.log (1 / (1 - t)) ≤ t - t ^ 2 / 2 := by
  have hu : 0 < 1 - t := sub_pos.mpr ht1
  constructor
  · have h := mul_le_mul_of_nonneg_left
      (negLogOneSub_quadratic_lower ht0 ht1) hu.le
    nlinarith
  · have hx : 1 ≤ 1 / (1 - t) := by
      apply (le_div_iff₀ hu).mpr
      linarith
    have h := mul_le_mul_of_nonneg_left (log_le_sub_inv_average hx) hu.le
    have hne : 1 - t ≠ 0 := hu.ne'
    simp only [div_eq_mul_inv, one_mul, inv_inv] at h
    field_simp [hne] at h
    nlinarith

/-- The cubic two-sided envelope for homogeneous pair entropy. -/
theorem pairEntropy_cubic_upper {y Q : ℝ} (hy : 0 < y) (hyQ : y < Q) :
    y * Real.log (Q / y) + y - y ^ 2 / (2 * Q) - y ^ 3 / (2 * Q ^ 2) ≤
        pairEntropy y (Q - y) ∧
      pairEntropy y (Q - y) ≤
        y * Real.log (Q / y) + y - y ^ 2 / (2 * Q) := by
  have hQ : 0 < Q := lt_trans hy hyQ
  have ht0 : 0 ≤ y / Q := (div_pos hy hQ).le
  have ht1 : y / Q < 1 := (div_lt_one hQ).mpr hyQ
  have henv := oneSub_mul_negLog_envelope ht0 ht1
  rw [pairEntropy_eq_sum_logs hy (sub_pos.mpr hyQ)]
  have hsum : y + (Q - y) = Q := by ring
  rw [hsum]
  have hscale : Q - y = Q * (1 - y / Q) := by field_simp
  rw [hscale]
  have hratio : Q / (Q * (1 - y / Q)) = 1 / (1 - y / Q) := by
    field_simp
  rw [hratio]
  constructor
  · have h := mul_le_mul_of_nonneg_left henv.1 hQ.le
    have hpoly :
        Q * (y / Q - (y / Q) ^ 2 / 2 - (y / Q) ^ 3 / 2) =
          y - y ^ 2 / (2 * Q) - y ^ 3 / (2 * Q ^ 2) := by
      field_simp
    rw [hpoly] at h
    linarith
  · have h := mul_le_mul_of_nonneg_left henv.2 hQ.le
    have hpoly : Q * (y / Q - (y / Q) ^ 2 / 2) =
        y - y ^ 2 / (2 * Q) := by
      field_simp
    rw [hpoly] at h
    linarith

/-! ## Convex logarithmic kernel and scalar gap fill -/

/-- The chart-native slope kernel as a difference of four logarithms. -/
theorem mixingSlopeKernel_eq_log_sum (C : ScalarContactChart)
    {z : ℝ} (hz : 0 ≤ z) :
    Real.log (1 + mixingGap C / ((z + C.r) * (z + 1))) =
      Real.log (z + C.e) + Real.log (z + C.ell) -
        Real.log (z + C.r) - Real.log (z + 1) := by
  have hze : 0 < z + C.e := add_pos_of_nonneg_of_pos hz C.e_pos
  have hzl : 0 < z + C.ell := add_pos_of_nonneg_of_pos hz C.ell_pos
  have hzr : 0 < z + C.r := add_pos_of_nonneg_of_pos hz C.r_pos
  have hz1 : 0 < z + 1 := by linarith
  have hden : (z + C.r) * (z + 1) ≠ 0 := (mul_pos hzr hz1).ne'
  have hratio :
      1 + mixingGap C / ((z + C.r) * (z + 1)) =
        ((z + C.e) * (z + C.ell)) / ((z + C.r) * (z + 1)) := by
    field_simp [hden]
    linarith [shifted_product_sub_eq_mixingGap C z]
  rw [hratio, Real.log_div (mul_pos hze hzl).ne' hden,
    Real.log_mul hze.ne' hzl.ne', Real.log_mul hzr.ne' hz1.ne']
  ring

private def mixingLogKernel (C : ScalarContactChart) (z : ℝ) : ℝ :=
  Real.log (C.e + z) + Real.log (C.ell + z) -
    Real.log (C.r + z) - Real.log (1 + z)

private def mixingLogKernelDerivative (C : ScalarContactChart) (z : ℝ) : ℝ :=
  1 / (C.e + z) + 1 / (C.ell + z) -
    1 / (C.r + z) - 1 / (1 + z)

private def mixingLogKernelSecondDerivative
    (C : ScalarContactChart) (z : ℝ) : ℝ :=
  -(1 / (C.e + z) ^ 2) + -(1 / (C.ell + z) ^ 2) -
    -(1 / (C.r + z) ^ 2) - -(1 / (1 + z) ^ 2)

private theorem hasDerivAt_mixingLogKernel (C : ScalarContactChart)
    {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (mixingLogKernel C) (mixingLogKernelDerivative C z) z := by
  have he : z + C.e ≠ 0 := (add_pos_of_nonneg_of_pos hz C.e_pos).ne'
  have hl : z + C.ell ≠ 0 := (add_pos_of_nonneg_of_pos hz C.ell_pos).ne'
  have hr : z + C.r ≠ 0 := (add_pos_of_nonneg_of_pos hz C.r_pos).ne'
  have h1 : z + 1 ≠ 0 := by linarith
  have hde : HasDerivAt (fun x : ℝ => Real.log (C.e + x))
      (1 / (C.e + z)) z := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (by simpa [add_comm] using he)).comp z
        ((hasDerivAt_const z C.e).add (hasDerivAt_id z))
  have hdl : HasDerivAt (fun x : ℝ => Real.log (C.ell + x))
      (1 / (C.ell + z)) z := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (by simpa [add_comm] using hl)).comp z
        ((hasDerivAt_const z C.ell).add (hasDerivAt_id z))
  have hdr : HasDerivAt (fun x : ℝ => Real.log (C.r + x))
      (1 / (C.r + z)) z := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (by simpa [add_comm] using hr)).comp z
        ((hasDerivAt_const z C.r).add (hasDerivAt_id z))
  have hd1 : HasDerivAt (fun x : ℝ => Real.log (1 + x))
      (1 / (1 + z)) z := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (by simpa [add_comm] using h1)).comp z
        ((hasDerivAt_const z 1).add (hasDerivAt_id z))
  unfold mixingLogKernel mixingLogKernelDerivative
  exact ((hde.add hdl).sub hdr).sub hd1

private theorem hasDerivAt_mixingLogKernelDerivative
    (C : ScalarContactChart) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (mixingLogKernelDerivative C)
      (mixingLogKernelSecondDerivative C z) z := by
  have he : z + C.e ≠ 0 := (add_pos_of_nonneg_of_pos hz C.e_pos).ne'
  have hl : z + C.ell ≠ 0 := (add_pos_of_nonneg_of_pos hz C.ell_pos).ne'
  have hr : z + C.r ≠ 0 := (add_pos_of_nonneg_of_pos hz C.r_pos).ne'
  have h1 : z + 1 ≠ 0 := by linarith
  have h (a : ℝ) (ha : z + a ≠ 0) :
      HasDerivAt (fun x : ℝ => 1 / (a + x))
        (-(1 / (a + z) ^ 2)) z := by
    simpa [Function.comp_def] using
      (hasDerivAt_inv (by simpa [add_comm] using ha)).comp z
        ((hasDerivAt_const z a).add (hasDerivAt_id z))
  unfold mixingLogKernelDerivative mixingLogKernelSecondDerivative
  exact (((h C.e he).add (h C.ell hl)).sub (h C.r hr)).sub (h 1 h1)

private theorem mixingLogKernelSecondDerivative_nonnegative
    (C : ScalarContactChart) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ mixingLogKernelSecondDerivative C z := by
  let u := z + C.r
  let v := z + 1
  let p := z + C.e
  let q := z + C.ell
  have hu : 0 < u := add_pos_of_nonneg_of_pos hz C.r_pos
  have hv : 0 < v := by dsimp [v]; linarith
  have hp : 0 < p := add_pos_of_nonneg_of_pos hz C.e_pos
  have hq : 0 < q := add_pos_of_nonneg_of_pos hz C.ell_pos
  have hsum : p + q = u + v := by
    dsimp [p, q, u, v]
    linarith [C.e_add_ell]
  have hprod : u * v ≤ p * q := by
    dsimp [p, q, u, v]
    linarith [shifted_product_sub_eq_mixingGap C z, mixingGap_nonnegative C]
  have hamgm : 4 * (u * v) ≤ (u + v) ^ 2 := by
    nlinarith [sq_nonneg (u - v)]
  have hamgm' : 4 * (p * q) ≤ (u + v) ^ 2 := by
    rw [← hsum]
    nlinarith [sq_nonneg (p - q)]
  have hfactor : 0 ≤
      (u + v) ^ 2 * (p * q + u * v) - 2 * (p * q) * (u * v) := by
    have hm := mul_le_mul_of_nonneg_right hamgm'
      (by positivity : 0 ≤ p * q + u * v)
    have hpq : 0 ≤ p * q := (mul_pos hp hq).le
    have huv : 0 ≤ u * v := (mul_pos hu hv).le
    nlinarith [mul_nonneg hpq hpq, mul_nonneg hpq huv]
  have hnum : 0 ≤ (p * q - u * v) *
      ((u + v) ^ 2 * (p * q + u * v) - 2 * (p * q) * (u * v)) :=
    mul_nonneg (sub_nonneg.mpr hprod) hfactor
  have hrecip : 1 / p ^ 2 + 1 / q ^ 2 ≤ 1 / u ^ 2 + 1 / v ^ 2 := by
    field_simp [hp.ne', hq.ne', hu.ne', hv.ne']
    have hid :
        p ^ 2 * q ^ 2 * (v ^ 2 + u ^ 2) -
            (q ^ 2 + p ^ 2) * u ^ 2 * v ^ 2 =
          (p * q - u * v) *
            ((u + v) ^ 2 * (p * q + u * v) - 2 * (p * q) * (u * v)) := by
      calc
        _ = (p * q) ^ 2 * ((u + v) ^ 2 - 2 * (u * v)) -
              (u * v) ^ 2 * ((p + q) ^ 2 - 2 * (p * q)) := by ring
        _ = _ := by rw [hsum]; ring
    nlinarith [hnum, hid]
  unfold mixingLogKernelSecondDerivative
  dsimp [p, q, u, v] at hrecip
  rw [show C.e + z = z + C.e by ring, show C.ell + z = z + C.ell by ring,
    show C.r + z = z + C.r by ring, show 1 + z = z + 1 by ring]
  linarith

/-- The slope kernel is convex on nonnegative shifts. -/
theorem mixingSlopeKernel_convex (C : ScalarContactChart) :
    ConvexOn ℝ (Set.Ici 0)
      (fun z => Real.log
        (1 + mixingGap C / ((z + C.r) * (z + 1)))) := by
  have hmono : MonotoneOn (mixingLogKernelDerivative C) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun z hz =>
        (hasDerivAt_mixingLogKernelDerivative C hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hasDerivAt_mixingLogKernelDerivative C (interior_subset hz))
        |>.differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hasDerivAt_mixingLogKernelDerivative C (interior_subset hz)).deriv]
      exact mixingLogKernelSecondDerivative_nonnegative C (interior_subset hz)
  have hderivmono : MonotoneOn (deriv (mixingLogKernel C))
      (interior (Ici 0)) := by
    intro a ha b hb hab
    rw [(hasDerivAt_mixingLogKernel C (interior_subset ha)).deriv,
      (hasDerivAt_mixingLogKernel C (interior_subset hb)).deriv]
    exact hmono (interior_subset ha) (interior_subset hb) hab
  have hconvLog : ConvexOn ℝ (Ici 0) (mixingLogKernel C) := by
    refine hderivmono.convexOn_of_deriv (convex_Ici 0) ?_ ?_
    · exact fun z hz =>
        (hasDerivAt_mixingLogKernel C hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hasDerivAt_mixingLogKernel C (interior_subset hz))
        |>.differentiableAt.differentiableWithinAt
  exact hconvLog.congr (fun z hz => by
    simpa only [mixingLogKernel, add_comm] using
      (mixingSlopeKernel_eq_log_sum C hz).symm)

/-- Homogeneous pair entropy is total mass times binary entropy of the first
share. -/
theorem pairEntropy_eq_mass_mul_binEntropy {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 < u + v) :
    pairEntropy u v = (u + v) * Real.binEntropy (u / (u + v)) := by
  by_cases hu0 : u = 0
  · subst u
    simp [Real.binEntropy_zero]
  by_cases hv0 : v = 0
  · subst v
    simp [Real.binEntropy_one, hu0]
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold Real.negMulLog pairEntropy xLogX
  have hone : 1 - u / (u + v) = v / (u + v) := by
    field_simp [hs.ne']
    ring
  rw [hone, Real.log_div hup.ne' hs.ne', Real.log_div hvp.ne' hs.ne']
  field_simp [hs.ne']
  ring

/-- The log-sum grouping inequality for homogeneous pair entropy. -/
theorem pairEntropy_superadditive {u1 v1 u2 v2 : ℝ}
    (hu1 : 0 ≤ u1) (hv1 : 0 ≤ v1) (hu2 : 0 ≤ u2) (hv2 : 0 ≤ v2) :
    pairEntropy u1 v1 + pairEntropy u2 v2 ≤
      pairEntropy (u1 + u2) (v1 + v2) := by
  let s1 := u1 + v1
  let s2 := u2 + v2
  let s := s1 + s2
  have hs1n : 0 ≤ s1 := add_nonneg hu1 hv1
  have hs2n : 0 ≤ s2 := add_nonneg hu2 hv2
  by_cases hs10 : s1 = 0
  · have hu10 : u1 = 0 := by dsimp [s1] at hs10; linarith
    have hv10 : v1 = 0 := by dsimp [s1] at hs10; linarith
    subst u1
    subst v1
    simp
  by_cases hs20 : s2 = 0
  · have hu20 : u2 = 0 := by dsimp [s2] at hs20; linarith
    have hv20 : v2 = 0 := by dsimp [s2] at hs20; linarith
    subst u2
    subst v2
    simp
  have hs1 : 0 < s1 := lt_of_le_of_ne hs1n (Ne.symm hs10)
  have hs2 : 0 < s2 := lt_of_le_of_ne hs2n (Ne.symm hs20)
  have hs : 0 < s := add_pos hs1 hs2
  let p1 := u1 / s1
  let p2 := u2 / s2
  have hp1 : p1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hu1 hs1.le
    · exact (div_le_one hs1).2 (by dsimp [s1]; linarith)
  have hp2 : p2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hu2 hs2.le
    · exact (div_le_one hs2).2 (by dsimp [s2]; linarith)
  have hw1 : 0 ≤ s1 / s := div_nonneg hs1.le hs.le
  have hw2 : 0 ≤ s2 / s := div_nonneg hs2.le hs.le
  have hwsum : s1 / s + s2 / s = 1 := by
    dsimp [s]
    field_simp [show s1 + s2 ≠ 0 by positivity]
  have hconc := Real.strictConcave_binEntropy.concaveOn.2
    hp1 hp2 hw1 hw2 hwsum
  have hpcomb : (s1 / s) * p1 + (s2 / s) * p2 = (u1 + u2) / s := by
    dsimp [p1, p2]
    field_simp [hs.ne', hs1.ne', hs2.ne']
  have hscaled := mul_le_mul_of_nonneg_left hconc hs.le
  dsimp only [smul_eq_mul] at hscaled
  rw [hpcomb] at hscaled
  have hleft :
      s * (s1 / s * Real.binEntropy p1 + s2 / s * Real.binEntropy p2) =
        s1 * Real.binEntropy p1 + s2 * Real.binEntropy p2 := by
    field_simp [hs.ne']
  rw [hleft] at hscaled
  rw [pairEntropy_eq_mass_mul_binEntropy hu1 hv1 hs1,
    pairEntropy_eq_mass_mul_binEntropy hu2 hv2 hs2,
    pairEntropy_eq_mass_mul_binEntropy (add_nonneg hu1 hu2)
      (add_nonneg hv1 hv2) (by
        dsimp [s, s1, s2] at hs ⊢
        linarith)]
  have htotal : u1 + u2 + (v1 + v2) = s := by
    dsimp [s, s1, s2]
    ring
  rw [htotal]
  simpa only [s1, s2, p1, p2] using hscaled

/-- The chart's homogeneous contact entropy gap is nonnegative. -/
theorem contactEntropyGap_nonneg (C : ScalarContactChart) :
    0 ≤ C.contactEntropyGap := by
  have h := pairEntropy_superadditive C.lowMass_nonneg
    (by norm_num : (0 : ℝ) ≤ 1) C.r_pos.le C.highMass_nonneg
  unfold ScalarContactChart.contactEntropyGap
  linarith

/-! ## Small-argument ledgers -/

/-- The edge reward after writing the small row ratio as `q`. -/
def edgeReward (q pi : ℝ) : ℝ :=
  let rq := q ^ 2
  let e := rq + pi * (1 - rq)
  let ell := 1 - pi + pi * rq
  pairEntropy e (ell + q) -
    4 * ((1 - pi) * pairEntropy rq (1 + q) +
      pi * pairEntropy 1 (rq + q))

/-- Rational part of the exact small-prior lower expression. -/
def smallPriorRationalPart (q : ℝ) : ℝ :=
  (1000 * q ^ 10 - 3400 * q ^ 8 - 100 * q ^ 7 + 3730 * q ^ 6 +
      180 * q ^ 5 - 1314 * q ^ 4 - 249 * q ^ 3 - 215 * q ^ 2 -
      52 * q + 14) / (2 * (1 + q + q ^ 2) ^ 2)

/-- Exact lower expression produced by the cubic entropy envelopes at prior
`10q²`. -/
def smallPriorEnvelopeExpression (q : ℝ) : ℝ :=
  let a := 11 - 10 * q ^ 2
  smallPriorRationalPart q +
    (7 - 40 * q - 10 * q ^ 2) * Real.log (1 + q + q ^ 2) +
    40 * q * (1 + q) * Real.log (1 + q) -
    2 * (7 - 20 * q + 10 * q ^ 2) * Real.log q - a * Real.log a

/-- The unnormalized expression obtained by inserting the three cubic
envelopes. -/
def smallPriorRawEnvelope (q : ℝ) : ℝ :=
  let Q := 1 + q + q ^ 2
  let r := q ^ 2
  let a := 11 - 10 * q ^ 2
  let e := a * q ^ 2
  let y := q + q ^ 2
  (e * Real.log (Q / e) + e - e ^ 2 / (2 * Q) - e ^ 3 / (2 * Q ^ 2)) -
    4 * (1 - 10 * r) * (r * Real.log (Q / r) + r - r ^ 2 / (2 * Q)) -
    40 * r * (y * Real.log (Q / y) + y - y ^ 2 / (2 * Q))

/-- Logarithmic normalization of the raw cubic-envelope expression. -/
theorem smallPriorRawEnvelope_eq_scaled {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    smallPriorRawEnvelope q = q ^ 2 * smallPriorEnvelopeExpression q := by
  have hq : q ≠ 0 := hq0.ne'
  have ha : 11 - 10 * q ^ 2 ≠ 0 := by
    have : 0 < 11 - 10 * q ^ 2 := by
      nlinarith [sq_nonneg (q - 9 / 100)]
    exact this.ne'
  have h1q : 1 + q ≠ 0 := by positivity
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  have hQ : 1 + q + q ^ 2 ≠ 0 := by positivity
  have he : q ^ 2 * 11 - q ^ 4 * 10 ≠ 0 := by
    rw [show q ^ 2 * 11 - q ^ 4 * 10 = q ^ 2 * (11 - 10 * q ^ 2) by ring]
    exact mul_ne_zero hq2 ha
  rw [smallPriorRawEnvelope, smallPriorEnvelopeExpression]
  rw [Real.log_div, Real.log_mul ha hq2, Real.log_pow,
    Real.log_div, Real.log_pow, Real.log_div]
  rw [show q + q ^ 2 = q * (1 + q) by ring, Real.log_mul hq h1q]
  unfold smallPriorRationalPart
  field_simp [hq, hQ, hq2, ha, he]
  all_goals solve
    | ring
    | positivity

/-- The three cubic entropy envelopes give the exact small-prior reward
bound. -/
theorem smallPriorCubicEnvelope {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    q ^ 2 * smallPriorEnvelopeExpression q ≤ edgeReward q (10 * q ^ 2) := by
  let Q : ℝ := 1 + q + q ^ 2
  let r : ℝ := q ^ 2
  let a : ℝ := 11 - 10 * q ^ 2
  let e : ℝ := a * q ^ 2
  let y : ℝ := q + q ^ 2
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hrQ : r < Q := by dsimp [r, Q]; nlinarith
  have hy0 : 0 < y := by dsimp [y]; nlinarith [sq_nonneg q]
  have hyQ : y < Q := by dsimp [y, Q]; norm_num
  have ha0 : 0 < a := by
    dsimp [a]
    nlinarith [sq_nonneg (q - 9 / 100)]
  have he0 : 0 < e := by dsimp [e]; positivity
  have heQ : e < Q := by
    dsimp [e, a, Q]
    nlinarith [sq_nonneg q, sq_nonneg (q - 9 / 100),
      mul_nonneg (sq_nonneg q)
        (show 0 ≤ 1 - 10 * q ^ 2 by
          nlinarith [sq_nonneg (q - 9 / 100)])]
  have he := (pairEntropy_cubic_upper he0 heQ).1
  have hr := (pairEntropy_cubic_upper hr0 hrQ).2
  have hy := (pairEntropy_cubic_upper hy0 hyQ).2
  have hrm := mul_le_mul_of_nonpos_left hr
    (show -4 * (1 - 10 * r) ≤ 0 by
      dsimp [r]
      nlinarith [sq_nonneg (q - 9 / 100)])
  have hym := mul_le_mul_of_nonpos_left hy (show -40 * r ≤ 0 by
    dsimp [r]
    nlinarith [sq_nonneg q])
  have hraw : smallPriorRawEnvelope q ≤
      pairEntropy e (Q - e) -
        4 * (1 - 10 * r) * pairEntropy r (Q - r) -
        40 * r * pairEntropy y (Q - y) := by
    unfold smallPriorRawEnvelope
    dsimp [Q, r, a, e, y] at he hr hy hrm hym ⊢
    linarith
  rw [← smallPriorRawEnvelope_eq_scaled hq0 hq1]
  calc
    smallPriorRawEnvelope q ≤
        pairEntropy e (Q - e) -
          4 * (1 - 10 * r) * pairEntropy r (Q - r) -
          40 * r * pairEntropy y (Q - y) := hraw
    _ = edgeReward q (10 * q ^ 2) := by
      unfold edgeReward pairEntropy xLogX
      dsimp [Q, r, a, e, y]
      ring

/-- Exact rational lower bound for the quotient in the small-prior
expression. -/
theorem smallPriorRationalPart_lower {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    (365537402057293 : ℝ) / 120582361000000 ≤ smallPriorRationalPart q := by
  have hq : 0 ≤ q := hq0.le
  have hq2 : q ^ 2 ≤ (9 / 100 : ℝ) ^ 2 := by gcongr
  have hq3 : q ^ 3 ≤ (9 / 100 : ℝ) ^ 3 := by gcongr
  have hq4 : q ^ 4 ≤ (9 / 100 : ℝ) ^ 4 := by gcongr
  have hq7 : q ^ 7 ≤ (9 / 100 : ℝ) ^ 7 := by gcongr
  have hq8 : q ^ 8 ≤ (9 / 100 : ℝ) ^ 8 := by gcongr
  have hnum : (365537402057293 : ℝ) / 50000000000000 ≤
      1000 * q ^ 10 - 3400 * q ^ 8 - 100 * q ^ 7 + 3730 * q ^ 6 +
        180 * q ^ 5 - 1314 * q ^ 4 - 249 * q ^ 3 - 215 * q ^ 2 -
        52 * q + 14 := by
    have h10 : 0 ≤ q ^ 10 := by positivity
    have h6 : 0 ≤ q ^ 6 := by positivity
    have h5 : 0 ≤ q ^ 5 := by positivity
    norm_num at hq1 hq2 hq3 hq4 hq7 hq8 ⊢
    nlinarith
  have hQ : 1 + q + q ^ 2 ≤ (10981 : ℝ) / 10000 := by
    norm_num at hq1 hq2 ⊢
    linarith
  have hQ0 : 0 ≤ 1 + q + q ^ 2 := by positivity
  have hQsq := mul_self_le_mul_self hQ0 hQ
  have hden : 2 * (1 + q + q ^ 2) ^ 2 ≤ (120582361 : ℝ) / 50000000 := by
    norm_num [pow_two] at hQsq ⊢
    linarith
  have hden0 : 0 < 2 * (1 + q + q ^ 2) ^ 2 := by positivity
  unfold smallPriorRationalPart
  apply (le_div_iff₀ hden0).2
  calc
    (365537402057293 / 120582361000000 : ℝ) *
        (2 * (1 + q + q ^ 2) ^ 2) ≤
          (365537402057293 / 120582361000000 : ℝ) *
            (120582361 / 50000000) := by gcongr
    _ = (365537402057293 : ℝ) / 50000000000000 := by norm_num
    _ ≤ _ := hnum

/-- A rational odd-log certificate for `log 11`. -/
theorem log_eleven_upper : Real.log 11 < (12 : ℝ) / 5 := by
  have h := logRatio_le_oddLogPartialSum_add_remainder 9
    (t := (5 : ℝ) / 6) (by norm_num) (by norm_num)
  norm_num [oddLogPartialSum, oddLogRemainder] at h ⊢
  linarith

/-- The exact small-prior expression stays above its final rational
coefficient. -/
theorem smallPriorEnvelopeExpression_lower {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    (74007309 : ℝ) / 200000000 < smallPriorEnvelopeExpression q := by
  have hP := smallPriorRationalPart_lower hq0 hq1
  have hq11 : q < (1 : ℝ) / 11 := by norm_num at hq1 ⊢; linarith
  have hlogq := Real.strictMonoOn_log
    (show q ∈ Set.Ioi (0 : ℝ) by exact hq0)
    (show (1 : ℝ) / 11 ∈ Set.Ioi (0 : ℝ) by norm_num) hq11
  have hloginv : Real.log ((1 : ℝ) / 11) = -Real.log 11 := by
    rw [← Real.log_inv]
    norm_num
  rw [hloginv] at hlogq
  have hnq : Real.log 11 < -Real.log q := by linarith
  have hlog11nonneg : 0 ≤ Real.log 11 := Real.log_nonneg (by norm_num)
  have hc : (5281 : ℝ) / 1000 ≤ 7 - 20 * q + 10 * q ^ 2 := by
    have hleft : 0 ≤ (9 : ℝ) / 100 - q := by linarith
    have hright : 0 ≤ 20 - 10 * (q + 9 / 100) := by nlinarith
    have hfac : 0 ≤ (9 / 100 - q) * (20 - 10 * (q + 9 / 100)) :=
      mul_nonneg hleft hright
    norm_num at hfac ⊢
    nlinarith
  have hc0 : 0 < 7 - 20 * q + 10 * q ^ 2 :=
    lt_of_lt_of_le (by norm_num) hc
  have hmain : (2 * ((5281 : ℝ) / 1000)) * Real.log 11 <
      -2 * (7 - 20 * q + 10 * q ^ 2) * Real.log q := by
    have hleft := mul_le_mul_of_nonneg_right hc hlog11nonneg
    have hright := mul_lt_mul_of_pos_left hnq hc0
    nlinarith
  let a : ℝ := 11 - 10 * q ^ 2
  have ha1 : 1 ≤ a := by
    dsimp [a]
    nlinarith [sq_nonneg (q - 9 / 100)]
  have ha11 : a ≤ 11 := by dsimp [a]; nlinarith [sq_nonneg q]
  have hloga0 : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hloga : Real.log a ≤ Real.log 11 :=
    Real.strictMonoOn_log.monotoneOn
      (show a ∈ Set.Ioi (0 : ℝ) by exact lt_of_lt_of_le zero_lt_one ha1)
      (show (11 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) ha11
  have haLog : a * Real.log a ≤ 11 * Real.log 11 :=
    mul_le_mul ha11 hloga hloga0 (by norm_num)
  have hcore : -(657 : ℝ) / 625 <
      -2 * (7 - 20 * q + 10 * q ^ 2) * Real.log q - a * Real.log a := by
    have h11 := log_eleven_upper
    nlinarith
  have hcoef : 0 ≤ 7 - 40 * q - 10 * q ^ 2 := by
    nlinarith [sq_nonneg (q - 9 / 100)]
  have hlogQ : 0 ≤ Real.log (1 + q + q ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg q])
  have htermQ : 0 ≤
      (7 - 40 * q - 10 * q ^ 2) * Real.log (1 + q + q ^ 2) :=
    mul_nonneg hcoef hlogQ
  have hlog1q : 0 ≤ Real.log (1 + q) := Real.log_nonneg (by linarith)
  have hterm1q : 0 ≤ 40 * q * (1 + q) * Real.log (1 + q) := by positivity
  unfold smallPriorEnvelopeExpression
  dsimp
  dsimp [a] at hcore
  have hrough : (365537402057293 : ℝ) / 120582361000000 - 657 / 625 <
      smallPriorRationalPart q +
        (7 - 40 * q - 10 * q ^ 2) * Real.log (1 + q + q ^ 2) +
        40 * q * (1 + q) * Real.log (1 + q) -
        2 * (7 - 20 * q + 10 * q ^ 2) * Real.log q -
        (11 - 10 * q ^ 2) * Real.log (11 - 10 * q ^ 2) := by
    linarith
  norm_num at hrough ⊢
  linarith

/-- Exact small-prior envelope, rational floor, and strict reward ledger. -/
theorem smallPriorExactLedger {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    q ^ 2 * smallPriorEnvelopeExpression q ≤ edgeReward q (10 * q ^ 2) ∧
    (365537402057293 : ℝ) / 120582361000000 ≤ smallPriorRationalPart q ∧
    ((74007309 : ℝ) / 200000000) * q ^ 2 < edgeReward q (10 * q ^ 2) := by
  have henvelope := smallPriorCubicEnvelope hq0 hq1
  have hrational := smallPriorRationalPart_lower hq0 hq1
  have hexpr := smallPriorEnvelopeExpression_lower hq0 hq1
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq0
  have hscaled := mul_lt_mul_of_pos_right hexpr hq2
  refine ⟨henvelope, hrational, ?_⟩
  calc
    ((74007309 : ℝ) / 200000000) * q ^ 2 <
        q ^ 2 * smallPriorEnvelopeExpression q := by nlinarith
    _ ≤ edgeReward q (10 * q ^ 2) := henvelope

private lemma quarticKernel_nonnegative {a : ℝ} (ha : 1 ≤ a) :
    0 ≤ 15 * a ^ 4 - 108 * a + 99 := by
  nlinarith [sq_nonneg (a - 11 / 9), sq_nonneg (a ^ 2 - 121 / 81),
    sq_nonneg (a - 1), sq_nonneg (a * a - a), ha]

/-- Nine copies of the eleventh power fit under the first fifteen powers on
`[1, ∞)`. -/
theorem nine_mul_pow_eleven_le_sum_range_fifteen {a : ℝ} (ha : 1 ≤ a) :
    9 * a ^ 11 ≤ ∑ k ∈ Finset.range 15, a ^ k := by
  rcases ha.eq_or_lt with rfl | ha
  · norm_num
  let f : ℝ → ℝ := fun x => x ^ 15 - 9 * x ^ 12 + 9 * x ^ 11 - 1
  let f' : ℝ → ℝ := fun x => x ^ 10 * (15 * x ^ 4 - 108 * x + 99)
  have hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    dsimp [f, f']
    convert (((hasDerivAt_pow 15 x).sub
      ((hasDerivAt_const x 9).mul (hasDerivAt_pow 12 x))).add
      ((hasDerivAt_const x 9).mul (hasDerivAt_pow 11 x))).sub_const 1 using 1
    all_goals first | rfl | (norm_num; ring)
  have hmono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    · fun_prop
    · intro x hx
      exact (hderiv x).hasDerivWithinAt
    · intro x hx
      have hx1 : 1 ≤ x := le_of_lt (by simpa using hx)
      dsimp [f']
      exact mul_nonneg (by positivity) (quarticKernel_nonnegative hx1)
  have hf : 0 ≤ f a := by
    have h := hmono (by simp) ha.le ha.le
    norm_num [f] at h ⊢
    exact h
  have hgeom := geom_sum_mul_of_one_le ha.le 15
  have hmul : 9 * a ^ 11 * (a - 1) ≤
      (∑ k ∈ Finset.range 15, a ^ k) * (a - 1) := by
    rw [hgeom]
    dsimp [f] at hf
    nlinarith
  nlinarith [hmul]

/-- The exact integer margin in the fourth-power kernel-capture reduction. -/
theorem fourthPowerCapture_integer_margin :
    (1331 : Nat) * 2401 < 6561 * 625 := by
  norm_num

/-! ## Balanced-edge certificates -/

/-- Reward on the balanced edge. -/
def balancedEdgeScalarReward (q : ℝ) : ℝ :=
  (1 + q + q ^ 2) * Real.log 2 -
    3 * (1 + q + q ^ 2) * Real.log (1 + q + q ^ 2) -
    ((1 + q ^ 2) / 2) * Real.log (1 + q ^ 2) +
    (1 + q) ^ 2 * Real.log (1 + q) +
    (2 * q + 6 * q ^ 2) * Real.log q

/-- Closed form for the derivative of the balanced-edge reward. -/
def balancedEdgeDerivative (q : ℝ) : ℝ :=
  (2 * q + 1) * Real.log 2 +
    (12 * q + 2) * Real.log q +
    (2 * q + 2) * Real.log (1 + q) -
    (6 * q + 3) * Real.log (1 + q + q ^ 2) -
    q * Real.log (1 + q ^ 2)

/-- Exact lower certificate for `log 2`. -/
theorem log_two_gt_693147_div_million :
    (693147 : ℝ) / 1000000 < Real.log 2 := by
  have h := oddLogPartialSum_le_logRatio 6
    (t := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have hpartial : oddLogPartialSum 6 ((1 : ℝ) / 3) =
      15757912 / 22733865 := by
    norm_num [oddLogPartialSum]
  rw [hpartial] at h
  norm_num at h ⊢
  linarith

/-- Exact lower certificate for `log (109/100)`. -/
theorem log_109_div_100_gt_86177_div_million :
    (86177 : ℝ) / 1000000 < Real.log ((109 : ℝ) / 100) := by
  have h := oddLogPartialSum_le_logRatio 2
    (t := (9 : ℝ) / 209) (by norm_num) (by norm_num)
  have hpartial : oddLogPartialSum 2 ((9 : ℝ) / 209) =
      786744 / 9129329 := by
    norm_num [oddLogPartialSum]
  rw [hpartial] at h
  norm_num at h ⊢
  linarith

/-- Exact lower certificate for `log (9/100)`. -/
theorem log_9_div_100_gt_neg_2407950_div_million :
    -(2407950 : ℝ) / 1000000 < Real.log ((9 : ℝ) / 100) := by
  have h2 := logRatio_le_oddLogPartialSum_add_remainder 4
    (t := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have h53 := logRatio_le_oddLogPartialSum_add_remainder 3
    (t := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  have h2exact : oddLogPartialSum 4 ((1 : ℝ) / 3) +
      oddLogRemainder 4 ((1 : ℝ) / 3) = 1910051 / 2755620 := by
    norm_num [oddLogPartialSum, oddLogRemainder]
  have h53exact : oddLogPartialSum 3 ((1 : ℝ) / 4) +
      oddLogRemainder 3 ((1 : ℝ) / 4) = 4577 / 8960 := by
    norm_num [oddLogPartialSum, oddLogRemainder]
  rw [h2exact] at h2
  rw [h53exact] at h53
  have hinv : Real.log ((9 : ℝ) / 100) = -Real.log ((100 : ℝ) / 9) := by
    rw [← Real.log_inv]
    norm_num
  rw [hinv]
  rw [show (100 : ℝ) / 9 = 2 * 2 * ((5 : ℝ) / 3) * (5 / 3) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  norm_num at h2 h53 ⊢
  linarith

/-- Exact upper certificate for `log (10981/10000)`. -/
theorem log_10981_div_10000_lt_93582_div_million :
    Real.log ((10981 : ℝ) / 10000) < (93582 : ℝ) / 1000000 := by
  have h := logRatio_le_oddLogPartialSum_add_remainder 1
    (t := (981 : ℝ) / 20981) (by norm_num) (by norm_num)
  have hexact : oddLogPartialSum 1 ((981 : ℝ) / 20981) +
      oddLogRemainder 1 ((981 : ℝ) / 20981) =
        431209132047 / 4607847220000 := by
    norm_num [oddLogPartialSum, oddLogRemainder]
  rw [hexact] at h
  norm_num at h ⊢
  linarith

/-- Exact upper certificate for `log (10081/10000)`. -/
theorem log_10081_div_10000_lt_8068_div_million :
    Real.log ((10081 : ℝ) / 10000) < (8068 : ℝ) / 1000000 := by
  have h := logRatio_le_oddLogPartialSum_add_remainder 1
    (t := (81 : ℝ) / 20081) (by norm_num) (by norm_num)
  have hexact : oddLogPartialSum 1 ((81 : ℝ) / 20081) +
      oddLogRemainder 1 ((81 : ℝ) / 20081) =
        32662617147 / 4048731220000 := by
    norm_num [oddLogPartialSum, oddLogRemainder]
  rw [hexact] at h
  norm_num at h ⊢
  linarith

/-- Structural differentiation certificate for the balanced-edge reward. -/
theorem hasDerivAt_balancedEdgeScalarReward {q : ℝ} (hq0 : 0 < q) :
    HasDerivAt balancedEdgeScalarReward (balancedEdgeDerivative q) q := by
  have hQ : HasDerivAt (fun x : ℝ => 1 + x + x ^ 2) (1 + 2 * q) q := by
    convert (((hasDerivAt_const q 1).add (hasDerivAt_id q)).add
      (hasDerivAt_pow 2 q)) using 1
    · rfl
    · rfl
    · funext x
      rfl
    · norm_num
  have hR : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * q) q := by
    convert ((hasDerivAt_const q 1).add (hasDerivAt_pow 2 q)) using 1
    · rfl
    · rfl
    · funext x
      rfl
    · norm_num
  have hOne : HasDerivAt (fun x : ℝ => 1 + x) 1 q := by
    convert ((hasDerivAt_const q 1).add (hasDerivAt_id q)) using 1
    all_goals first | rfl | norm_num
  have hCoeff : HasDerivAt (fun x : ℝ => 2 * x + 6 * x ^ 2)
      (2 + 12 * q) q := by
    convert (((hasDerivAt_id q).const_mul 2).add
      ((hasDerivAt_pow 2 q).const_mul 6)) using 1
    all_goals first | rfl | (norm_num; ring)
  have hQ0 : 1 + q + q ^ 2 ≠ 0 := by positivity
  have hR0 : 1 + q ^ 2 ≠ 0 := by positivity
  have hOne0 : 1 + q ≠ 0 := by positivity
  have ht1 := hQ.mul_const (Real.log 2)
  have ht2 := (hQ.const_mul 3).mul ((Real.hasDerivAt_log hQ0).comp q hQ)
  have ht3 := (hR.div_const 2).mul ((Real.hasDerivAt_log hR0).comp q hR)
  have ht4 := (hOne.pow 2).mul ((Real.hasDerivAt_log hOne0).comp q hOne)
  have ht5 := hCoeff.mul (Real.hasDerivAt_log hq0.ne')
  have h := (((ht1.sub ht2).sub ht3).add ht4).add ht5
  rw [show balancedEdgeScalarReward =
    ((((fun y : ℝ => (1 + y + y ^ 2) * Real.log 2) -
      (fun y : ℝ => 3 * (1 + y + y ^ 2)) * Real.log ∘
        (fun x : ℝ => 1 + x + x ^ 2)) -
      (fun x : ℝ => (1 + x ^ 2) / 2) * Real.log ∘
        (fun x : ℝ => 1 + x ^ 2)) +
      (fun x : ℝ => 1 + x) ^ 2 * Real.log ∘ (fun x : ℝ => 1 + x)) +
      (fun x : ℝ => 2 * x + 6 * x ^ 2) * Real.log by rfl]
  convert h using 1 <;> try rfl
  unfold balancedEdgeDerivative
  dsimp only [Function.comp_apply, id_eq]
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The balanced-edge derivative is strictly negative on the small endpoint
interval. -/
theorem balancedEdgeDerivative_neg {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    balancedEdgeDerivative q < 0 := by
  have h2 := logRatio_le_oddLogPartialSum_add_remainder 1
    (t := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have hlog2 : Real.log 2 < (7 : ℝ) / 10 := by
    norm_num [oddLogPartialSum, oddLogRemainder] at h2 ⊢
    linarith
  have h2lo := oddLogPartialSum_le_logRatio 1
    (t := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have h53lo := oddLogPartialSum_le_logRatio 1
    (t := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num [oddLogPartialSum] at h2lo h53lo
  have h1009 : (9 : ℝ) / 4 < Real.log (100 / 9) := by
    rw [show (100 : ℝ) / 9 = 2 * 2 * ((5 : ℝ) / 3) * (5 / 3) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hlog_endpoint : Real.log ((9 : ℝ) / 100) < -(9 : ℝ) / 4 := by
    rw [show Real.log ((9 : ℝ) / 100) = -Real.log (100 / 9) by
      rw [← Real.log_inv]
      norm_num]
    linarith
  have hlogq_le : Real.log q ≤ Real.log ((9 : ℝ) / 100) :=
    Real.strictMonoOn_log.monotoneOn hq0 (by norm_num) hq1
  have hlogq : Real.log q < -(9 : ℝ) / 4 :=
    lt_of_le_of_lt hlogq_le hlog_endpoint
  have hlog1q : Real.log (1 + q) ≤ q := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + q by positivity)
    linarith
  have hlogQ : 0 ≤ Real.log (1 + q + q ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg q])
  have hlogR : 0 ≤ Real.log (1 + q ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg q])
  have ht1 : (2 * q + 1) * Real.log 2 < (59 / 50 : ℝ) * (7 / 10) := by
    have hc : 0 < 2 * q + 1 := by positivity
    have hc' : 2 * q + 1 ≤ (59 : ℝ) / 50 := by linarith
    nlinarith
  have ht2 : (12 * q + 2) * Real.log q < -(2 : ℝ) * (9 / 4) := by
    have hc : 2 ≤ 12 * q + 2 := by linarith
    nlinarith
  have ht3 : (2 * q + 2) * Real.log (1 + q) ≤
      (109 / 50 : ℝ) * (9 / 100) := by
    have hc0 : 0 ≤ 2 * q + 2 := by positivity
    have hc1 : 2 * q + 2 ≤ (109 : ℝ) / 50 := by linarith
    nlinarith
  unfold balancedEdgeDerivative
  have hdropQ : -(6 * q + 3) * Real.log (1 + q + q ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hlogQ
  have hdropR : -q * Real.log (1 + q ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hlogR
  linarith

/-- Fixed-endpoint reward certificate from the five logarithmic bounds. -/
theorem balancedEdgeScalarReward_at_endpoint :
    (20241 : ℝ) / 100000000 < balancedEdgeScalarReward (9 / 100) := by
  have h1 := log_two_gt_693147_div_million
  have h2 := log_109_div_100_gt_86177_div_million
  have h3 := log_9_div_100_gt_neg_2407950_div_million
  have h4 := log_10981_div_10000_lt_93582_div_million
  have h5 := log_10081_div_10000_lt_8068_div_million
  unfold balancedEdgeScalarReward
  norm_num
  linarith

/-- Derivative, sign, and endpoint certificates for the balanced edge. -/
theorem balancedEdgeExactLedger {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    HasDerivAt balancedEdgeScalarReward (balancedEdgeDerivative q) q ∧
    balancedEdgeDerivative q < 0 ∧
    20241 / 100000000 < balancedEdgeScalarReward (9 / 100) := by
  exact ⟨hasDerivAt_balancedEdgeScalarReward hq0,
    balancedEdgeDerivative_neg hq0 hq1, balancedEdgeScalarReward_at_endpoint⟩

/-! ## Strict proxy in free coordinates -/

/-- Lower off-diagonal mixture mass at free chart coordinates. -/
def freeLowerMixtureMass (x pi : ℝ) : ℝ :=
  pi + (1 - pi) * x ^ 4

/-- Upper off-diagonal mixture mass at free chart coordinates. -/
def freeUpperMixtureMass (x pi : ℝ) : ℝ :=
  1 - pi + pi * x ^ 4

/-- The mixing contribution with all chart parameters free. -/
def freeMixingTerm (x pi s : ℝ) : ℝ :=
  pairEntropy s (freeLowerMixtureMass x pi) +
    pairEntropy s (freeUpperMixtureMass x pi) -
    pairEntropy s (x ^ 4) - pairEntropy s 1

/-- Conditional-entropy part of the high singleton at free coordinates. -/
def highArmEntropy (x pi s : ℝ) : ℝ :=
  (1 - pi) * pairEntropy (x ^ 4) (1 + s) +
    pi * pairEntropy 1 (x ^ 4 + s)

/-- The strict high-arm proxy at free chart coordinates. -/
def strictProxy (x pi s : ℝ) : ℝ :=
  (5 / 2 : ℝ) * freeMixingTerm x pi s - highArmEntropy x pi s

/-- The free lower mixture mass specializes to the bundled chart value. -/
theorem freeLowerMixtureMass_eq_e (C : ScalarContactChart) :
    freeLowerMixtureMass C.x C.pi = C.e := by
  unfold freeLowerMixtureMass ScalarContactChart.e ScalarContactChart.r
  ring

/-- The free upper mixture mass specializes to the bundled chart value. -/
theorem freeUpperMixtureMass_eq_ell (C : ScalarContactChart) :
    freeUpperMixtureMass C.x C.pi = C.ell := by
  unfold freeUpperMixtureMass ScalarContactChart.ell ScalarContactChart.r
  ring

/-- The free mixing term specializes to the bundled chart term. -/
theorem freeMixingTerm_eq_mixingTerm (C : ScalarContactChart) (s : ℝ) :
    freeMixingTerm C.x C.pi s = C.mixingTerm s := by
  rw [freeMixingTerm, ScalarContactChart.mixingTerm,
    freeLowerMixtureMass_eq_e, freeUpperMixtureMass_eq_ell]
  rfl

/-- At the chart contact mass, the free mixing term is the off-diagonal loss. -/
theorem freeMixingTerm_eq_offDiagonalLoss (C : ScalarContactChart) :
    freeMixingTerm C.x C.pi C.s = C.offDiagonalLoss := by
  rw [freeMixingTerm_eq_mixingTerm]
  rfl

/-- The free high-arm entropy specializes to the bundled chart value. -/
theorem highArmEntropy_eq_highConditionalEntropy (C : ScalarContactChart) :
    highArmEntropy C.x C.pi C.s = C.highConditionalEntropy := by
  unfold highArmEntropy ScalarContactChart.highConditionalEntropy
    ScalarContactChart.r
  rfl

/-- Monotonicity of the strict proxy in the free contact-mass coordinate. -/
def StrictProxyMonotoneInContactMass : Prop :=
  ∀ {x pi : ℝ}, 0 < x → x < 2 / 5 → 3 * x ^ 4 ≤ pi → pi ≤ 1 / 2 →
    MonotoneOn (strictProxy x pi) (Set.Icc (2 * contactMidpoint x) (x ^ 2))

/-- Concavity of the strict proxy in the free prior coordinate. -/
def StrictProxyConcaveInPrior : Prop :=
  ∀ {x s : ℝ}, 0 < x → x < 1 → 2 * contactMidpoint x ≤ s → s ≤ x ^ 2 →
    ConcaveOn ℝ (Set.Icc 0 (1 / 2)) (fun pi => strictProxy x pi s)

/-- Reduction of the bundled strict proxy to its two seam endpoints. -/
def StrictProxyGeMinAtSeamEndpoints : Prop :=
  ∀ (C : ScalarContactChart), C.x < 2 / 5 → 3 * C.x ^ 4 ≤ C.pi →
    min (strictProxy C.x (3 * C.x ^ 4) (2 * contactMidpoint C.x))
        (strictProxy C.x (1 / 2) (2 * contactMidpoint C.x)) ≤
      strictProxy C.x C.pi C.s

/-! ## Seam positivity statements -/

/-- Positivity of the strict proxy at the balanced-prior seam. -/
def StrictProxyPositiveAtBalancedSeam : Prop :=
  ∀ {x : ℝ}, 0 < x → x ≤ 2 / 5 →
    0 < strictProxy x (1 / 2) (2 * contactMidpoint x)

/-- Positivity of the strict proxy at the low-prior seam. -/
def StrictProxyPositiveAtLowPriorSeam : Prop :=
  ∀ {x : ℝ}, 0 < x → x ≤ 2 / 5 →
    0 < strictProxy x (3 * x ^ 4) (2 * contactMidpoint x)

/-! ## Closed positive-phase ledgers -/

/-- The scalar at the balanced-prior seam. -/
def balancedSeamScalar (x : ℝ) : ℝ :=
  let alpha := x + x ^ 2 + x ^ 3
  let ellx := Real.log ((1 + x ^ 3) ^ 2 / (4 * x ^ 3))
  let hx := 4 * (1 + x) * (1 + x ^ 2) / (1 + x ^ 3)
  (3 - alpha) * ellx - (1 + alpha) * (1 + Real.log hx) +
    (1 / 2) * (alpha * Real.log alpha +
      (alpha + 2) * Real.log (alpha + 2))

/-- The exact polynomial occurring on the low-prior seam. -/
def lowPriorSeamPolynomial (x : ℝ) : ℝ :=
  5 + 3 * x + x ^ 2 - 51 * x ^ 3 - 34 * x ^ 4 - 17 * x ^ 5

/-- Exact rational and transcendental ledger at the positive `x = 2/5`
gate. -/
theorem positivePhaseTwoFifthsGateLedger :
    0 < (624 : ℝ) / 26999 ∧
    (624 : ℝ) / 26999 < (24375 : ℝ) / 26999 ∧
    9 / 10 < (107996 : ℝ) / 118755 ∧
    (107996 : ℝ) / 118755 < 1 ∧
    Real.exp (9 / 10) > 12 / 5 ∧
    Real.log (17 / 12) < 3 / 8 ∧
    ((107996 : ℝ) / 118755) * (624 / 26999) < 1 / 40 := by
  have hexp : (12 : ℝ) / 5 < Real.exp (9 / 10) := by
    have hsum := Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ 9 / 10 by norm_num) 4
    norm_num [Finset.sum_range_succ] at hsum ⊢
    linarith
  have hlog : Real.log ((17 : ℝ) / 12) < 3 / 8 := by
    have h := logRatio_le_oddLogPartialSum_add_remainder 3
      (t := (5 : ℝ) / 29) (by norm_num) (by norm_num)
    norm_num [oddLogPartialSum, oddLogRemainder] at h ⊢
    linarith
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    hexp, hlog, by norm_num⟩

/-- Exact logarithmic ledger at the balanced seam endpoint. -/
theorem balancedSeamEndpointLogLedger :
    Real.log (17689 / 4000) > (37 : ℝ) / 25 ∧
    Real.log (812 / 133) < (909 : ℝ) / 500 ∧
    Real.log (78 / 125) > -(59 : ℝ) / 125 ∧
    Real.log (328 / 125) > (241 : ℝ) / 250 ∧
    (3597 : ℝ) / 62500 < balancedSeamScalar (2 / 5) := by
  have h1 := oddLogPartialSum_le_logRatio 4
    (t := (13689 : ℝ) / 21689) (by norm_num) (by norm_num)
  have h2 := logRatio_le_oddLogPartialSum_add_remainder 4
    (t := (679 : ℝ) / 945) (by norm_num) (by norm_num)
  have h3' := logRatio_le_oddLogPartialSum_add_remainder 1
    (t := (47 : ℝ) / 203) (by norm_num) (by norm_num)
  have h4 := oddLogPartialSum_le_logRatio 4
    (t := (203 : ℝ) / 453) (by norm_num) (by norm_num)
  norm_num [oddLogPartialSum, oddLogRemainder] at h1 h2 h3' h4 ⊢
  have hl1 : (37 : ℝ) / 25 < Real.log (17689 / 4000) := by linarith
  have hl2 : Real.log (812 / 133) < (909 : ℝ) / 500 := by linarith
  have hl3 : -(59 : ℝ) / 125 < Real.log (78 / 125) := by
    rw [show Real.log ((78 : ℝ) / 125) = -Real.log (125 / 78) by
      rw [← Real.log_inv]
      norm_num]
    linarith
  have hl4 : (241 : ℝ) / 250 < Real.log (328 / 125) := by linarith
  constructor
  · exact hl1
  constructor
  · norm_num at hl2 ⊢
    exact hl2
  constructor
  · norm_num at hl3 ⊢
    exact hl3
  constructor
  · exact hl4
  unfold balancedSeamScalar
  norm_num
  linarith

/-- Exact endpoint ledger at the low-prior seam. -/
theorem lowPriorSeamEndpointLedger :
    0 < (103747643 : ℝ) / 3173828125 ∧
    (1157525834384227 : ℝ) / 69564432491875 > 16 ∧
    Real.log 2 ≥ (56 : ℝ) / 81 ∧ Real.log 2 < (7 : ℝ) / 10 ∧
    Real.log 11 < (12 : ℝ) / 5 ∧ Real.log 44 < (19 : ℝ) / 5 ∧
    (17500 : ℝ) / 3159 - 224632 / 40625 = 101924 / 9871875 ∧
    0 < (101924 : ℝ) / 9871875 := by
  have h2lo := oddLogPartialSum_le_logRatio 3
    (t := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have h2hi := logRatio_le_oddLogPartialSum_add_remainder 1
    (t := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have h11 := logRatio_le_oddLogPartialSum_add_remainder 9
    (t := (5 : ℝ) / 6) (by norm_num) (by norm_num)
  norm_num [oddLogPartialSum, oddLogRemainder] at h2lo h2hi h11 ⊢
  have hlog44 : Real.log (44 : ℝ) < 19 / 5 := by
    rw [show (44 : ℝ) = 2 * 2 * 11 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  constructor
  · exact le_trans (by norm_num) h2lo
  constructor
  · exact lt_of_le_of_lt h2hi (by norm_num)
  constructor
  · exact lt_of_le_of_lt h11 (by norm_num)
  · exact hlog44

end

end StochasticToDeterministicLatents.Binary
