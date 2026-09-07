import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Rational enclosures of a logarithm

The quantitative estimates of the factor-two argument compare logarithms at
fixed rational points with fixed rational bounds.  This module supplies the
one tool they all use: the odd part of the logarithm's power series, with the
two closed forms those estimates measure it against.  It mentions no
probability law, no code, and no information quantity, and it imports nothing
from this library.

`logRatioSeries n t` is the sum of the first `n` odd terms of the series for
`log ((1 + t) / (1 - t))`, and `logRatioRemainder n t`, from Mathlib's
remainder for `log (1 - x)`, is proved here to bracket what that sum omits.
`logRatioTail n t` is a second closed form, the geometric majorant of the
omitted terms with the coefficient frozen at its first value; no theorem here
relates it to the series, and it enters only as a comparison target.

The enclosure holds at every truncation length, so a consumer names its own
length and discharges the arithmetic by `norm_num` at its own point.
`logRatio_mem_of_side` is the shape those consumers want: a short series
brackets the logarithm as soon as a longer one is seen to fall inside the
short one's tail.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-- The first `n` odd terms of the series for `log ((1 + t) / (1 - t))`. -/
noncomputable def logRatioSeries (n : ℕ) (t : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1)

/-- The error left by `logRatioSeries n`, from Mathlib's logarithm
remainder. -/
noncomputable def logRatioRemainder (n : ℕ) (t : ℝ) : ℝ :=
  2 * t ^ (2 * n + 1) / (1 - t)

/-- The geometric majorant of the terms `logRatioSeries n` omits, with the
coefficient frozen at its first value.  Nothing here proves it majorises them:
it is a comparison target, supplied by the consumer of
`logRatio_mem_of_side`. -/
noncomputable def logRatioTail (n : ℕ) (t : ℝ) : ℝ :=
  2 * t ^ (2 * n + 1) / ((2 * n + 1) * (1 - t ^ 2))

/-- The even terms of the two logarithm series cancel and the odd ones
double. -/
private theorem sum_sub_sum_neg (n : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range (2 * n), t ^ (i + 1) / (i + 1))
        - ∑ i ∈ Finset.range (2 * n), (-t) ^ (i + 1) / (i + 1)
      = logRatioSeries n t := by
  induction n with
  | zero => simp [logRatioSeries]
  | succ m ih =>
    have hidx : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    have hodd : (-t) ^ (2 * m + 1) = -t ^ (2 * m + 1) :=
      Odd.neg_pow ⟨m, by ring⟩ t
    have heven : (-t) ^ (2 * m + 1 + 1) = t ^ (2 * m + 1 + 1) :=
      Even.neg_pow ⟨m + 1, by ring⟩ t
    simp only [logRatioSeries] at ih ⊢
    rw [hidx]
    simp only [Finset.sum_range_succ]
    rw [hodd, heven]
    push_cast at ih ⊢
    linear_combination ih

private theorem abs_sum_add_log_le {t : ℝ} (n : ℕ) (h0 : 0 ≤ t) (h1 : t < 1) :
    |(∑ i ∈ Finset.range (2 * n), t ^ (i + 1) / (i + 1)) + Real.log (1 - t)|
      ≤ t ^ (2 * n + 1) / (1 - t) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := t) (by rw [abs_of_nonneg h0]; exact h1) (2 * n)
  rw [abs_of_nonneg h0] at h
  exact h

private theorem abs_sum_neg_add_log_le {t : ℝ} (n : ℕ) (h0 : 0 ≤ t) (h1 : t < 1) :
    |(∑ i ∈ Finset.range (2 * n), (-t) ^ (i + 1) / (i + 1)) + Real.log (1 + t)|
      ≤ t ^ (2 * n + 1) / (1 - t) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -t) (by simpa [abs_of_nonneg h0] using h1) (2 * n)
  simpa [abs_of_nonneg h0] using h

/-- The truncated series brackets the logarithm to within the remainder. -/
theorem logRatioSeries_enclosure (n : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    logRatioSeries n t - logRatioRemainder n t ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤ logRatioSeries n t + logRatioRemainder n t := by
  rw [Real.log_div (by linarith) (by linarith)]
  have hs := sum_sub_sum_neg n t
  obtain ⟨a1, a2⟩ := abs_le.mp (abs_sum_add_log_le n h0 h1)
  obtain ⟨b1, b2⟩ := abs_le.mp (abs_sum_neg_add_log_le n h0 h1)
  unfold logRatioRemainder
  rw [div_eq_mul_inv] at a1 a2 b1 b2 ⊢
  constructor <;> linarith

/-- A short truncation brackets the logarithm as soon as a longer one, with
its remainder, is seen to lie inside the short one's tail.  In use both
hypotheses are inequalities between explicit rationals at a rational point,
discharged where they stand. -/
theorem logRatio_mem_of_side (m n : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1)
    (hlo : logRatioSeries n t ≤ logRatioSeries m t - logRatioRemainder m t)
    (hhi : logRatioSeries m t + logRatioRemainder m t
      ≤ logRatioSeries n t + logRatioTail n t) :
    logRatioSeries n t ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤ logRatioSeries n t + logRatioTail n t := by
  obtain ⟨h₁, h₂⟩ := logRatioSeries_enclosure m h0 h1
  exact ⟨hlo.trans h₁, h₂.trans hhi⟩

end StochasticToDeterministicLatents.Binary
