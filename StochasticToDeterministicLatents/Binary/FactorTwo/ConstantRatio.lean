import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import StochasticToDeterministicLatents.Binary.FactorTwo.Shape
import StochasticToDeterministicLatents.Binary.FactorTwo.LogValues

/-!
# The constant margin's ratio term at the fixed cut

Nothing here is about a probability law.  In the estimate a later module
supplies, the constant margin at the fixed cut is bounded below by two copies
of one real function of one real variable,

`V x = 3 (3 + x) log (3 + x) - (6 + 4 x) log (1 + x) + x log x`,

evaluated at the two off-diagonal cells over the contact cell, less explicit
constants.  This module supplies that function and the only fact about it the
estimate needs: `19 / 2 < V x` for every positive `x`.

The bound is proved either side of `x = 1`.  Below it `V` is convex, since its
second derivative `(-3 x^2 + 4 x + 3) / (x (x + 1)^2 (x + 3))` is nonnegative
there, so `V` lies above its tangent at `1 / 2`; the tangent's intercept
already exceeds `19 / 2` and its slope is nonnegative, both by the decimal
enclosures of `Real.log 3` and `Real.log 7`.  Above it the substitution
`t = 1 / (x + 1)` turns `V'` into `3 log (1 + 2 t) + log (1 - t) - 2 t`, which
is concave on `[0, 1 / 2]` and so lies above its chord there; `V'` is
therefore positive, `V` is monotone, and `V 1 = 14 log 2` exceeds `19 / 2`.

Like `Shape` and `LogSeries`, this module mentions no probability law, no code
and no information quantity; from this library it imports only `Shape`, for
the shape lemmas, and `LogValues`, for the two constants.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-- The constant margin's contribution from one off-diagonal cell over the
contact cell, at the fixed cut. -/
noncomputable def constantRatioTerm (x : ℝ) : ℝ :=
  3 * (3 + x) * Real.log (3 + x) - (6 + 4 * x) * Real.log (1 + x) + x * Real.log x

/-- The derivative of `constantRatioTerm`. -/
private noncomputable def ratioDeriv (x : ℝ) : ℝ :=
  3 * Real.log ((x + 3) / (x + 1)) + Real.log (x / (x + 1)) - 2 / (x + 1)

/-- The second derivative of `constantRatioTerm`. -/
private noncomputable def ratioDeriv2 (x : ℝ) : ℝ :=
  (-3 * x ^ 2 + 4 * x + 3) / (x * (x + 1) ^ 2 * (x + 3))

/-- The slope of the tangent to `constantRatioTerm` at `1 / 2`. -/
private noncomputable def tangentSlope : ℝ := 3 * Real.log (7 / 3) - Real.log 3 - 4 / 3

/-- The intercept of the tangent to `constantRatioTerm` at `1 / 2`. -/
private noncomputable def tangentIntercept : ℝ :=
  9 * Real.log (7 / 2) - 6 * Real.log (3 / 2) + 2 / 3

private theorem constantRatioTerm_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt constantRatioTerm (ratioDeriv x) x := by
  unfold constantRatioTerm ratioDeriv
  have hx1 : x + 1 ≠ 0 := by positivity
  have hlin3 := (hasDerivAt_id' (x := x)).const_add 3
  have hlog3 := hlin3.log (by positivity : 3 + x ≠ 0)
  have hlin1 := (hasDerivAt_id' (x := x)).const_add 1
  have hlog1 := hlin1.log (by positivity : 1 + x ≠ 0)
  have hA := (hlin3.const_mul 3).mul hlog3
  have hB := ((hasDerivAt_id' (x := x)).const_mul 4 |>.const_add 6).mul hlog1
  have hC := Real.hasDerivAt_mul_log hx.ne'
  apply ((hA.sub hB).add hC).congr_deriv
  simp only [mul_one]
  rw [Real.log_div (by positivity : x + 3 ≠ 0) hx1, Real.log_div hx.ne' hx1]
  field_simp
  ring_nf

private theorem ratioDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt ratioDeriv (ratioDeriv2 x) x := by
  unfold ratioDeriv ratioDeriv2
  have hx1 : x + 1 ≠ 0 := by positivity
  have hx3 : x + 3 ≠ 0 := by positivity
  have hq1 := ((hasDerivAt_id x).add_const 3).div ((hasDerivAt_id x).add_const 1) hx1
  have hq2 := (hasDerivAt_id x).div ((hasDerivAt_id x).add_const 1) hx1
  have hq1ne : (x + 3) / (x + 1) ≠ 0 := div_ne_zero hx3 hx1
  have hq2ne : x / (x + 1) ≠ 0 := div_ne_zero hx.ne' hx1
  have hraw := ((((Real.hasDerivAt_log hq1ne).comp x hq1).const_mul 3).add
      ((Real.hasDerivAt_log hq2ne).comp x hq2)).sub
      ((hasDerivAt_const x 2).div ((hasDerivAt_id x).add_const 1) hx1)
  apply hraw.congr_deriv
  simp only [id_eq]
  field_simp [hx.ne', hx1, hx3]
  ring

private theorem ratioDeriv2_nonneg {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 0 ≤ ratioDeriv2 x := by
  unfold ratioDeriv2
  apply div_nonneg
  · nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  · positivity

private theorem constantRatioTerm_convexOn :
    ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) constantRatioTerm := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc (0 : ℝ) 1)
  · intro x hx
    exact (constantRatioTerm_hasDerivAt hx.1).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (constantRatioTerm_hasDerivAt hx.1).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (ratioDeriv_hasDerivAt hx.1).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact ratioDeriv2_nonneg hx.1 hx.2.le

private theorem constantRatioTerm_tangent {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    tangentIntercept + tangentSlope * x ≤ constantRatioTerm x := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hslope : ratioDeriv (1 / 2) = tangentSlope := by
    unfold ratioDeriv tangentSlope
    norm_num
    rw [show Real.log (1 / 3 : ℝ) = -Real.log 3 by
      rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]]
    ring
  have hintercept :
      constantRatioTerm (1 / 2) - tangentSlope * (1 / 2) = tangentIntercept := by
    unfold constantRatioTerm tangentSlope tangentIntercept
    norm_num
    rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
      rw [show (1 / 2 : ℝ) = 1 / 2 by norm_num, Real.log_div] <;> norm_num]
    rw [show Real.log 3 = Real.log (3 / 2) + Real.log 2 by
      rw [← Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num]
    rw [show Real.log (7 / 3) = Real.log (7 / 2) - Real.log (3 / 2) by
      rw [← Real.log_div (by norm_num : (7 / 2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      congr 1; norm_num]
    ring
  by_cases h : x = 1 / 2
  · subst x; linarith
  · have hxmem : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨hx, hx1⟩
    have hhmem : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hs := constantRatioTerm_convexOn.slope_le_of_hasDerivWithinAt hxmem hhmem hlt
        (constantRatioTerm_hasDerivAt hhalf).hasDerivWithinAt
      simp only [slope, smul_eq_mul, vsub_eq_sub] at hs
      rw [hslope] at hs
      have hpos : 0 < (1 / 2 : ℝ) - x := sub_pos.mpr hlt
      have hs' : (constantRatioTerm (1 / 2) - constantRatioTerm x) / ((1 / 2) - x)
          ≤ tangentSlope := by simpa [div_eq_inv_mul] using hs
      have hm := (div_le_iff₀ hpos).mp hs'
      linarith
    · have hs := constantRatioTerm_convexOn.le_slope_of_hasDerivAt hhmem hxmem hgt
        (constantRatioTerm_hasDerivAt hhalf)
      simp only [slope, smul_eq_mul, vsub_eq_sub] at hs
      rw [hslope] at hs
      have hpos : 0 < x - (1 / 2 : ℝ) := sub_pos.mpr hgt
      have hs' : tangentSlope
          ≤ (constantRatioTerm x - constantRatioTerm (1 / 2)) / (x - (1 / 2)) := by
        simpa [div_eq_inv_mul] using hs
      have hm := (le_div_iff₀ hpos).mp hs'
      linarith

/-- The derivative of `constantRatioTerm` read in the reciprocal variable
`t = 1 / (x + 1)`, on which it is concave. -/
private noncomputable def derivativeInRatio (t : ℝ) : ℝ :=
  3 * Real.log (1 + 2 * t) + Real.log (1 - t) - 2 * t

private theorem ratioDeriv_eq {x : ℝ} (hx : 0 < x) :
    ratioDeriv x = derivativeInRatio (1 / (x + 1)) := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have h1 : (x + 3) / (x + 1) = 1 + 2 * (1 / (x + 1)) := by field_simp; ring
  have h2 : x / (x + 1) = 1 - 1 / (x + 1) := by field_simp; ring
  unfold ratioDeriv derivativeInRatio
  rw [h1, h2]
  ring

private theorem constantRatioTerm_one : constantRatioTerm 1 = 14 * Real.log 2 := by
  unfold constantRatioTerm
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num]
  ring

private noncomputable def derivativeInRatioDeriv (t : ℝ) : ℝ := 6 / (1 + 2 * t) - 1 / (1 - t) - 2

private noncomputable def derivativeInRatioDeriv2 (t : ℝ) : ℝ :=
  -12 / (1 + 2 * t) ^ 2 - 1 / (1 - t) ^ 2

private theorem derivativeInRatio_hasDerivAt {t : ℝ} (ht : t < 1) (ht' : -1 / 2 < t) :
    HasDerivAt derivativeInRatio (derivativeInRatioDeriv t) t := by
  have hp : 1 + 2 * t ≠ 0 := by linarith
  have hm : 1 - t ≠ 0 := by linarith
  have hplus := (Real.hasDerivAt_log hp).comp t
    ((hasDerivAt_const t 1).add ((hasDerivAt_const t 2).mul (hasDerivAt_id t)))
  have hminus := (Real.hasDerivAt_log hm).comp t
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have h := (hplus.const_mul 3).add hminus |>.sub ((hasDerivAt_id t).const_mul 2)
  norm_num [Function.comp_apply] at h
  convert h using 1
  case e'_4 => rfl
  case e'_5 => rfl
  case e'_8 =>
    funext y
    unfold derivativeInRatio
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  case e'_9 =>
    unfold derivativeInRatioDeriv
    field_simp [hp, hm]
    ring

private theorem derivativeInRatioDeriv_hasDerivAt {t : ℝ} (ht : t < 1) (ht' : -1 / 2 < t) :
    HasDerivAt derivativeInRatioDeriv (derivativeInRatioDeriv2 t) t := by
  have hp : 1 + 2 * t ≠ 0 := by linarith
  have hm : 1 - t ≠ 0 := by linarith
  have hplus := (hasDerivAt_const t 6).div
    ((hasDerivAt_const t 1).add ((hasDerivAt_const t 2).mul (hasDerivAt_id t))) hp
  have hminus := (hasDerivAt_const t 1).div
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) hm
  have h := hplus.sub hminus |>.sub (hasDerivAt_const t 2)
  norm_num [Function.comp_apply] at h
  change HasDerivAt derivativeInRatioDeriv _ t at h
  convert h using 1
  unfold derivativeInRatioDeriv2
  field_simp [hp, hm]

private theorem derivativeInRatio_concaveOn :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) (1 / 2)) derivativeInRatio := by
  apply concaveOn_Icc_of_hasDerivAt2_nonpos 0 (1 / 2) derivativeInRatio
    derivativeInRatioDeriv derivativeInRatioDeriv2
  · intro t ht
    exact (derivativeInRatio_hasDerivAt (by linarith [ht.2])
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    exact derivativeInRatio_hasDerivAt (by linarith [ht.2]) (by linarith [ht.1])
  · intro t ht
    exact derivativeInRatioDeriv_hasDerivAt (by linarith [ht.2]) (by linarith [ht.1])
  · intro t ht
    unfold derivativeInRatioDeriv2
    have ha : -12 / (1 + 2 * t) ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)
    have hb : -(1 / (1 - t) ^ 2) ≤ 0 := neg_nonpos.mpr (by positivity)
    exact add_nonpos ha hb

private theorem derivativeInRatio_ge {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    2 * t / 3 ≤ derivativeInRatio t := by
  have h := derivativeInRatio_concaveOn.2 (Set.left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (Set.right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (show 0 ≤ 1 - 2 * t by linarith) (show 0 ≤ 2 * t by positivity) (by ring)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  norm_num [derivativeInRatio] at h
  rw [hloghalf] at h
  ring_nf at h
  unfold derivativeInRatio
  have hc : (2 : ℝ) / 3 ≤ 4 * Real.log 2 - 2 := by
    have hlog := Real.log_two_gt_d9
    norm_num at hlog
    linarith
  have htarget : 2 * t / 3 ≤ t * (4 * Real.log 2 - 2) := by
    calc
      2 * t / 3 = t * (2 / 3) := by ring
      _ ≤ t * (4 * Real.log 2 - 2) := mul_le_mul_of_nonneg_left hc ht0
  refine htarget.trans ?_
  rw [show 1 + t * 2 = 1 + 2 * t by ring] at h
  ring_nf at h ⊢
  exact h

private theorem ratioDeriv_pos {x : ℝ} (hx : 1 ≤ x) : 0 < ratioDeriv x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [ratioDeriv_eq hxpos]
  have ht0 : 0 ≤ 1 / (x + 1) := by positivity
  have ht : 1 / (x + 1) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < x + 1) (by norm_num : (0 : ℝ) < 2)).2
    linarith
  exact lt_of_lt_of_le (by positivity : 0 < 2 * (1 / (x + 1)) / 3) (derivativeInRatio_ge ht0 ht)

private theorem constantRatioTerm_monotoneOn :
    MonotoneOn constantRatioTerm (Set.Ici (1 : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
  · intro x hx
    exact (constantRatioTerm_hasDerivAt
      (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (constantRatioTerm_hasDerivAt (lt_trans zero_lt_one hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (ratioDeriv_pos hx.le).le

private theorem tangentSlope_nonneg : 0 ≤ tangentSlope := by
  unfold tangentSlope
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  linarith [log_three_bounds.2, log_seven_bounds.1]

private theorem tangentIntercept_gt : (19 : ℝ) / 2 < tangentIntercept := by
  unfold tangentIntercept
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  have hlog := Real.log_two_lt_d9
  norm_num at hlog
  linarith [log_three_bounds.2, log_seven_bounds.1]

/-- The constant margin's ratio term exceeds `19 / 2` at every positive ratio.
Below `1` this is the tangent at `1 / 2`; above it, monotonicity from
`constantRatioTerm 1 = 14 log 2`. -/
theorem constantRatioTerm_gt {x : ℝ} (hx : 0 < x) : (19 : ℝ) / 2 < constantRatioTerm x := by
  rcases le_total x 1 with h | h
  · calc
      (19 : ℝ) / 2 < tangentIntercept := tangentIntercept_gt
      _ ≤ tangentIntercept + tangentSlope * x :=
        le_add_of_nonneg_right (mul_nonneg tangentSlope_nonneg hx.le)
      _ ≤ constantRatioTerm x := constantRatioTerm_tangent hx h
  · have hmono : constantRatioTerm 1 ≤ constantRatioTerm x :=
      constantRatioTerm_monotoneOn (by simp) (by simpa using h) h
    rw [constantRatioTerm_one] at hmono
    have hlog := Real.log_two_gt_d9
    norm_num at hlog
    linarith

end StochasticToDeterministicLatents.Binary
