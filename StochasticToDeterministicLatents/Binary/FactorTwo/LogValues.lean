import Mathlib.Analysis.Complex.ExponentialBounds
import StochasticToDeterministicLatents.Binary.FactorTwo.LogSeries

/-!
# Decimal enclosures of five logarithms

The quantitative estimates of the factor-two argument reduce to linear
inequalities in `Real.log 2`, `Real.log 3`, `Real.log 5`, `Real.log 7`,
`Real.log 11` and `Real.log 13`.  Mathlib supplies the first to nine places;
this module supplies the other five to eight, each from `LogSeries` at one
rational point.

Every proof has the same four steps: write the number as a power of two times
`(1 + t) / (1 - t)` for a small rational `t`, bracket that ratio by six series
terms and their tail, evaluate the two brackets by `norm_num`, and combine
with Mathlib's enclosure of `Real.log 2`.  The bracketing hypotheses are
inequalities between explicit rationals, so `norm_num` discharges them where
they stand.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-- `Real.log 3` to eight places. -/
theorem log_three_bounds :
    (109861228 : ℝ) / 10 ^ 8 ≤ Real.log 3 ∧
      Real.log 3 ≤ (109861229 : ℝ) / 10 ^ 8 := by
  have harg : (3 : ℝ) = 2 * ((1 + (1 / 5 : ℝ)) / (1 - 1 / 5)) := by norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num)]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 5` to eight places. -/
theorem log_five_bounds :
    (160943791 : ℝ) / 10 ^ 8 ≤ Real.log 5 ∧
      Real.log 5 ≤ (160943792 : ℝ) / 10 ^ 8 := by
  have harg : (5 : ℝ) = 2 ^ 2 * ((1 + (1 / 9 : ℝ)) / (1 - 1 / 9)) := by norm_num
  have hp : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (1 / 9 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 7` to eight places. -/
theorem log_seven_bounds :
    (194591014 : ℝ) / 10 ^ 8 ≤ Real.log 7 ∧
      Real.log 7 ≤ (194591015 : ℝ) / 10 ^ 8 := by
  have harg : (7 : ℝ) = 2 ^ 2 * ((1 + (3 / 11 : ℝ)) / (1 - 3 / 11)) := by norm_num
  have hp : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (3 / 11 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 11` to eight places. -/
theorem log_eleven_bounds :
    (239789526 : ℝ) / 10 ^ 8 ≤ Real.log 11 ∧
      Real.log 11 ≤ (239789528 : ℝ) / 10 ^ 8 := by
  have harg : (11 : ℝ) = 2 ^ 3 * ((1 + (3 / 19 : ℝ)) / (1 - 3 / 19)) := by norm_num
  have hp : Real.log ((2 : ℝ) ^ 3) = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (3 / 19 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 13` to eight places. -/
theorem log_thirteen_bounds :
    (256494935 : ℝ) / 10 ^ 8 ≤ Real.log 13 ∧
      Real.log 13 ≤ (256494936 : ℝ) / 10 ^ 8 := by
  have harg : (13 : ℝ) = 2 ^ 3 * ((1 + (5 / 21 : ℝ)) / (1 - 5 / 21)) := by norm_num
  have hp : Real.log ((2 : ℝ) ^ 3) = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (5 / 21 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

end StochasticToDeterministicLatents.Binary
