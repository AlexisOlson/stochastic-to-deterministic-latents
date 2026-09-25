import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Binary entropy against Bernoulli variance

For `0 < ε` and `ε ≤ x ≤ 1 - ε`, binary entropy is at most `h(ε)/(ε(1-ε))` times the Bernoulli
variance `x(1-x)` (`binEntropy_le_mul_of_mem`). The ratio `h(x)/(x(1-x))` is symmetric about `1/2`
(`binEntropy_div_symm`) and antitone on `(0, 1/2]` (`binEntropy_div_antitoneOn`): its derivative
has the sign of `(1-x)² log(1-x) − x² log x`, a function convex on `[0, 1/2]` that vanishes at both
ends.

Everything here is in nats, through Mathlib's `Real.binEntropy`; statements about the library's
bit-valued entropies carry `Real.log 2` on the information side. This module imports only Mathlib.

## Attribution

Original to this repository.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

/-- The ratio `h(x)/(x(1-x))` of binary entropy to Bernoulli variance is unchanged by
`x ↦ 1 - x`. -/
theorem binEntropy_div_symm (x : ℝ) :
    Real.binEntropy (1 - x) / ((1 - x) * (1 - (1 - x))) = Real.binEntropy x / (x * (1 - x)) := by
  rw [Real.binEntropy_one_sub]
  congr 1
  ring

/-- Binary entropy written out with natural logarithms. -/
private theorem binEntropy_eq (p : ℝ) :
    Real.binEntropy p = -(p * Real.log p) - (1 - p) * Real.log (1 - p) := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  ring

/-- The auxiliary function `(1 - y)² log (1 - y) - y² log y`, the sign of the derivative of
`h(y) / (y (1 - y))`. -/
private def ratioN (y : ℝ) : ℝ := (1 - y) ^ 2 * Real.log (1 - y) - y ^ 2 * Real.log y

private theorem ratioN_eq : ratioN = fun y : ℝ =>
    (1 - y) * ((1 - y) * Real.log (1 - y)) - y * (y * Real.log y) := by
  funext y
  simp only [ratioN]
  ring

private theorem ratioN_continuous : Continuous ratioN := by
  rw [ratioN_eq]
  have h1 : Continuous fun y : ℝ => 1 - y := continuous_const.sub continuous_id
  exact (h1.mul (Real.continuous_mul_log.comp h1)).sub
    (continuous_id.mul Real.continuous_mul_log)

private theorem ratioN_hasDerivAt {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt ratioN (2 * Real.binEntropy y - 1) y := by
  have hne0 : y ≠ 0 := hy0.ne'
  have hne1 : (1 - y) ≠ 0 := by linarith
  have hs : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := (hasDerivAt_id' y).const_sub 1
  have h := ((hs.fun_pow 2).fun_mul (hs.log hne1)).fun_sub (((hasDerivAt_id' y).fun_pow 2).fun_mul
    ((hasDerivAt_id' y).log hne0))
  have hfun : ratioN = fun t : ℝ => (1 - t) ^ 2 * Real.log (1 - t) - t ^ 2 * Real.log t := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [binEntropy_eq]
  field_simp
  ring

private theorem ratioN_nonpos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : ratioN x ≤ 0 := by
  have hmono : MonotoneOn (deriv ratioN) (interior (Set.Icc (0 : ℝ) (1 / 2))) := by
    rw [interior_Icc]
    intro a ha b hb hab
    rw [(ratioN_hasDerivAt ha.1 (by linarith [ha.2])).deriv,
      (ratioN_hasDerivAt hb.1 (by linarith [hb.2])).deriv]
    have hmem : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2), t ∈ Set.Icc (0 : ℝ) 2⁻¹ := by
      intro t ht
      refine ⟨ht.1.le, ?_⟩
      have := ht.2
      norm_num at this ⊢
      linarith
    have := Real.binEntropy_strictMonoOn.monotoneOn (hmem a ha) (hmem b hb) hab
    linarith
  have hdiff : DifferentiableOn ℝ ratioN (interior (Set.Icc (0 : ℝ) (1 / 2))) := by
    rw [interior_Icc]
    intro t ht
    exact (ratioN_hasDerivAt ht.1 (by linarith [ht.2])).differentiableAt.differentiableWithinAt
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) (1 / 2)) ratioN :=
    MonotoneOn.convexOn_of_deriv (convex_Icc _ _) ratioN_continuous.continuousOn hdiff hmono
  have h0 : ratioN 0 = 0 := by simp [ratioN]
  have hhalf : ratioN (1 / 2) = 0 := by
    simp only [ratioN]
    norm_num
  have key := hconv.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨le_refl _, by norm_num⟩)
    (show (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by norm_num, le_refl _⟩)
    (show (0 : ℝ) ≤ 1 - 2 * x by linarith) (show (0 : ℝ) ≤ 2 * x by linarith)
    (show 1 - 2 * x + 2 * x = (1 : ℝ) by ring)
  simp only [smul_eq_mul, h0, hhalf, mul_zero, add_zero, zero_add] at key
  have hx : 2 * x * (1 / 2) = x := by ring
  rw [hx] at key
  exact key

private theorem div_hasDerivAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y : ℝ => Real.binEntropy y / (y * (1 - y)))
      (ratioN x / (x * (1 - x)) ^ 2) x := by
  have hne0 : x ≠ 0 := hx0.ne'
  have hne1 : x ≠ 1 := hx1.ne
  have hv : x * (1 - x) ≠ 0 := (mul_pos hx0 (by linarith)).ne'
  have h := (Real.hasDerivAt_binEntropy hne0 hne1).fun_div
    ((hasDerivAt_id' x).fun_mul ((hasDerivAt_id' x).const_sub 1)) hv
  refine h.congr_deriv ?_
  simp only [ratioN, binEntropy_eq]
  ring

/-- The ratio `h(x)/(x(1-x))` is antitone on `(0, 1/2]`. -/
theorem binEntropy_div_antitoneOn :
    AntitoneOn (fun x : ℝ => Real.binEntropy x / (x * (1 - x))) (Set.Ioc 0 (1 / 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
  · refine ContinuousOn.div Real.binEntropy_continuous.continuousOn (by fun_prop) ?_
    intro y hy
    exact (mul_pos hy.1 (by linarith [hy.2])).ne'
  · rw [interior_Ioc]
    intro t ht
    exact (div_hasDerivAt ht.1 (by linarith [ht.2])).differentiableAt.differentiableWithinAt
  · rw [interior_Ioc]
    intro t ht
    rw [(div_hasDerivAt ht.1 (by linarith [ht.2])).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (ratioN_nonpos ht.1.le ht.2.le) (sq_nonneg _)

/-- For `0 < ε ≤ 1/2` and `ε ≤ x ≤ 1 - ε`, `h(x) ≤ h(ε)/(ε(1-ε)) · x(1-x)`, in nats. -/
theorem binEntropy_le_mul_of_mem {ε x : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hx0 : ε ≤ x)
    (hx1 : x ≤ 1 - ε) :
    Real.binEntropy x ≤ Real.binEntropy ε / (ε * (1 - ε)) * (x * (1 - x)) := by
  have hv : 0 < x * (1 - x) := mul_pos (by linarith) (by linarith)
  have hg : Real.binEntropy x / (x * (1 - x)) ≤ Real.binEntropy ε / (ε * (1 - ε)) := by
    have hεmem : ε ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨hε0, hε⟩
    rcases le_total x (1 - x) with hle | hle
    · have hxmem : x ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by linarith, by linarith⟩
      exact binEntropy_div_antitoneOn hεmem hxmem hx0
    · have hxmem : 1 - x ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by linarith, by linarith⟩
      have := binEntropy_div_antitoneOn hεmem hxmem (by linarith)
      simp only at this
      rw [binEntropy_div_symm] at this
      exact this
  calc Real.binEntropy x = Real.binEntropy x / (x * (1 - x)) * (x * (1 - x)) :=
        (div_mul_cancel₀ _ hv.ne').symm
    _ ≤ Real.binEntropy ε / (ε * (1 - ε)) * (x * (1 - x)) :=
        mul_le_mul_of_nonneg_right hg hv.le

end

end BinaryRow

end StochasticToDeterministicLatents
