import Mathlib.Analysis.Convex.Deriv

/-!
# The sign of a concave function with two zeros

A concave function on a convex subset of `ℝ` that vanishes at `r < z` is nonpositive on the set
before `r`, nonnegative on `[r, z]`, and nonpositive after `z` (`concaveOn_sign_of_roots`). This
module imports only Mathlib.

## Attribution

Original to this repository.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

/-- The concavity inequality at an intermediate point, with explicit weights. -/
private theorem concave_mid {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {a b c : ℝ}
    (ha : a ∈ s) (hc : c ∈ s) (hac : a < c) (hab : a ≤ b) (hbc : b ≤ c) :
    (c - b) / (c - a) * f a + (b - a) / (c - a) * f c ≤ f b := by
  have hca : 0 < c - a := by linarith
  have key := hf.2 ha hc (show 0 ≤ (c - b) / (c - a) from div_nonneg (by linarith) hca.le)
    (show 0 ≤ (b - a) / (c - a) from div_nonneg (by linarith) hca.le)
    (show (c - b) / (c - a) + (b - a) / (c - a) = 1 by field_simp; ring)
  simp only [smul_eq_mul] at key
  have hb : (c - b) / (c - a) * a + (b - a) / (c - a) * c = b := by
    field_simp
    ring
  rw [hb] at key
  exact key

/-- The sign pattern of a concave function with two zeros: on a convex set `s`, if `f` is
concave with `f r = 0` and `f z = 0` for `r < z` in `s`, then `f ≤ 0` on `s` before `r`,
`0 ≤ f` on `[r, z]`, and `f ≤ 0` on `s` after `z`. -/
theorem concaveOn_sign_of_roots {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {r z x : ℝ}
    (hr : r ∈ s) (hz : z ∈ s) (hrz : r < z) (hfr : f r = 0) (hfz : f z = 0) (hx : x ∈ s) :
    (x ≤ r → f x ≤ 0) ∧ (r ≤ x → x ≤ z → 0 ≤ f x) ∧ (z ≤ x → f x ≤ 0) := by
  refine ⟨fun hxr => ?_, fun hrx hxz => ?_, fun hzx => ?_⟩
  · rcases hxr.lt_or_eq with hlt | heq
    · have key := concave_mid hf hx hz (by linarith) hlt.le hrz.le
      rw [hfr, hfz, mul_zero, add_zero] at key
      have hc : 0 < (z - r) / (z - x) := div_pos (by linarith) (by linarith)
      by_contra hcon
      rw [not_le] at hcon
      have := mul_pos hc hcon
      linarith
    · rw [heq, hfr]
  · have key := concave_mid hf hr hz hrz hrx hxz
    rw [hfr, hfz, mul_zero, mul_zero, add_zero] at key
    exact key
  · rcases hzx.lt_or_eq with hlt | heq
    · have key := concave_mid hf hr hx (by linarith) hrz.le hlt.le
      rw [hfr, hfz, mul_zero, zero_add] at key
      have hc : 0 < (z - r) / (x - r) := div_pos (by linarith) (by linarith)
      by_contra hcon
      rw [not_le] at hcon
      have := mul_pos hc hcon
      linarith
    · rw [← heq, hfz]

end

end BinaryRow

end StochasticToDeterministicLatents
