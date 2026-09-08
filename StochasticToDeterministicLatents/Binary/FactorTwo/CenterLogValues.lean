import Mathlib.Analysis.Complex.ExponentialBounds
import StochasticToDeterministicLatents.Binary.FactorTwo.LogSeries

/-!
# Decimal enclosures of eight more logarithms

`LogValues` supplies `Real.log` at 3, 5, 7, 11 and 13, which
is what the fixed cut needs.  The centre needs eight more primes: 17, 19, 23,
47, 173, 179, 313 and 3581.  Every logarithm the centre compares against a
rational is a logarithm of a ratio of products of those eight and the earlier
six, so an integer combination of the thirteen enclosures and Mathlib's
`Real.log 2` replaces a separate estimate at each ratio.

Each proof is the four steps of the sibling module: write the prime as a power
of two times `(1 + t) / (1 - t)` for the rational `t = (p - 2^n) / (p + 2^n)`,
bracket that ratio by six series terms and their tail, evaluate the two
brackets by `norm_num`, and combine with Mathlib's enclosure of `Real.log 2`.

The points here are coarser than the sibling's -- 3581 needs `t` near `0.27`,
where 11 needed `3/19` -- so the six-term tail is the wider of the two error
sources for the last of them and the enclosure is three units in the eighth
place rather than one.  Six terms still suffice at every point: the widest
tail is `7.6e-9`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-- `Real.log 17` to eight places. -/
theorem log_seventeen_bounds :
    (283321334 : ℝ) / 10 ^ 8 ≤ Real.log 17 ∧
      Real.log 17 ≤ (283321335 : ℝ) / 10 ^ 8 := by
  have harg : (17 : ℝ) = 2 ^ 4 * ((1 + (1 / 33 : ℝ)) / (1 - 1 / 33)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (1 / 33 : ℝ)) (by norm_num)
    (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 19` to eight places. -/
theorem log_nineteen_bounds :
    (294443897 : ℝ) / 10 ^ 8 ≤ Real.log 19 ∧
      Real.log 19 ≤ (294443899 : ℝ) / 10 ^ 8 := by
  have harg : (19 : ℝ) = 2 ^ 4 * ((1 + (3 / 35 : ℝ)) / (1 - 3 / 35)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (3 / 35 : ℝ)) (by norm_num)
    (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 23` to eight places. -/
theorem log_twentythree_bounds :
    (313549421 : ℝ) / 10 ^ 8 ≤ Real.log 23 ∧
      Real.log 23 ≤ (313549422 : ℝ) / 10 ^ 8 := by
  have harg : (23 : ℝ) = 2 ^ 4 * ((1 + (7 / 39 : ℝ)) / (1 - 7 / 39)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (7 / 39 : ℝ)) (by norm_num)
    (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 47` to eight places. -/
theorem log_fortyseven_bounds :
    (385014760 : ℝ) / 10 ^ 8 ≤ Real.log 47 ∧
      Real.log 47 ≤ (385014761 : ℝ) / 10 ^ 8 := by
  have harg : (47 : ℝ) = 2 ^ 5 * ((1 + (15 / 79 : ℝ)) / (1 - 15 / 79)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 5) = 5 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (15 / 79 : ℝ)) (by norm_num)
    (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 173` to eight places. -/
theorem log_onehundredseventythree_bounds :
    (515329159 : ℝ) / 10 ^ 8 ≤ Real.log 173 ∧
      Real.log 173 ≤ (515329160 : ℝ) / 10 ^ 8 := by
  have harg : (173 : ℝ) = 2 ^ 7 * ((1 + (45 / 301 : ℝ)) / (1 - 45 / 301)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 7) = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (45 / 301 : ℝ)) (by norm_num)
    (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 179` to eight places. -/
theorem log_onehundredseventynine_bounds :
    (518738580 : ℝ) / 10 ^ 8 ≤ Real.log 179 ∧
      Real.log 179 ≤ (518738581 : ℝ) / 10 ^ 8 := by
  have harg : (179 : ℝ) = 2 ^ 7 * ((1 + (51 / 307 : ℝ)) / (1 - 51 / 307)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 7) = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (51 / 307 : ℝ)) (by norm_num)
    (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 313` to eight places. -/
theorem log_threehundredthirteen_bounds :
    (574620318 : ℝ) / 10 ^ 8 ≤ Real.log 313 ∧
      Real.log 313 ≤ (574620320 : ℝ) / 10 ^ 8 := by
  have harg : (313 : ℝ) = 2 ^ 8 * ((1 + (57 / 569 : ℝ)) / (1 - 57 / 569)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 8) = 8 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (57 / 569 : ℝ)) (by norm_num)
    (by norm_num)
    (by simp only [logRatioSeries, logRatioRemainder,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
    (by simp only [logRatioSeries, logRatioRemainder, logRatioTail,
          Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  rw [harg, Real.log_mul (by norm_num) (by norm_num), hp]
  simp only [logRatioSeries, logRatioTail,
    Finset.sum_range_succ, Finset.sum_range_zero] at hs1 hs2
  norm_num at hs1 hs2
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `Real.log 3581` to within three units in the eighth place. -/
theorem log_thirtyfivehundredeightyone_bounds :
    (818339735 : ℝ) / 10 ^ 8 ≤ Real.log 3581 ∧
      Real.log 3581 ≤ (818339738 : ℝ) / 10 ^ 8 := by
  have harg : (3581 : ℝ) = 2 ^ 11 * ((1 + (1533 / 5629 : ℝ)) / (1 - 1533 / 5629)) := by
    norm_num
  have hp : Real.log ((2 : ℝ) ^ 11) = 11 * Real.log 2 := by rw [Real.log_pow]; norm_num
  obtain ⟨hs1, hs2⟩ := logRatio_mem_of_side 12 6 (t := (1533 / 5629 : ℝ)) (by norm_num)
    (by norm_num)
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
