import StochasticToDeterministicLatents.Binary.FactorTwo.LogValues
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterLogValues
import StochasticToDeterministicLatents.Binary.FactorTwo.PlaneBound

/-!
# The plane bound at the endpoints of the four reference intervals

`centerPlaneBound_concaveOn` makes each reference plane's bound concave on
`[0, 1]`, so on any subinterval of `[0, 1]` it is least at an endpoint.  This
module evaluates the bound at the two endpoints of the interval its plane
governs, for each of the four planes, and shows it exceeds `1/100` there.

The four intervals are `[0, 1/3]`, `[1/3, 2/3]`, `[2/3, 19/20]` and
`[19/20, 1]`.  They cover `[0, 1]`, so with concavity these eight numbers are
what a lower bound on the whole range of the imbalance would rest on.  This
module does not take that step: nothing here mentions a law, a code or a
margin, and no bound on any margin is stated.  These are eight facts about
real numbers.

## How the numbers are proved

Unfolding the definitions at a rational `z` leaves a rational combination of
logarithms of rationals: the two diagonal cells contribute `Real.log (7/16)`,
the off-diagonal cells `Real.log ((1 + z)/16)` and `Real.log ((1 - z)/16)`, the
two marginals `Real.log ((8 + z)/16)` and `Real.log ((8 - z)/16)`, and the
plane its three values `K`, `L_b`, `L_c`.

Every one of those rationals factors over the fourteen primes enclosed by
`LogValues` and `CenterLogValues` -- all fourteen are used, and none other
occurs.  The private table below rewrites each logarithm into that basis
**exactly**, and `linarith` then applies the enclosures once, at the end.  This
is why the table holds equations rather than enclosures: bounding each of eight
terms separately would compound the enclosure error eight times over, where
expanding first and bounding last does not.  The margin is wide either way --
the smallest slack over `1/100` is about `2.6e-3`, against an accumulated
enclosure error near `3e-7`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and module
boundaries; it is unpublished and supplies no verification evidence.  Two
adapted modules are merged here, their sharp rational intermediates are
dropped, and each logarithm of a rational is expanded over the prime basis
rather than carrying a series estimate of its own.
-/

namespace StochasticToDeterministicLatents.Binary

/-! ## The logarithms the endpoints produce

Twenty-eight rationals occur across the eight endpoint values.  Each equation
is exact, so nothing is lost before the enclosures are applied. -/

/-- `Real.log (152 / 114738821)` over the prime basis. -/
private theorem log_152_114738821 :
    Real.log (152 / 114738821 : ℝ) = 3 * Real.log 2 + Real.log 19
      - 2 * Real.log 179 - Real.log 3581 := by
  rw [show (152 / 114738821 : ℝ) = (2 ^ 3 * 19 ^ 1) / (179 ^ 2 * 3581 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (154 / 249985)` over the prime basis. -/
private theorem log_154_249985 :
    Real.log (154 / 249985 : ℝ) = Real.log 2 - Real.log 5 + Real.log 7
      + Real.log 11 - 2 * Real.log 17 - Real.log 173 := by
  rw [show (154 / 249985 : ℝ) = (2 ^ 1 * 7 ^ 1 * 11 ^ 1) / (5 ^ 1 * 17 ^ 2 * 173 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (1 / 320)` over the prime basis. -/
private theorem log_1_320 :
    Real.log (1 / 320 : ℝ) = -6 * Real.log 2 - Real.log 5 := by
  rw [show (1 / 320 : ℝ) = 1 / (2 ^ 6 * 5 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_one]
  push_cast
  ring

/-- `Real.log (5831 / 903944)` over the prime basis. -/
private theorem log_5831_903944 :
    Real.log (5831 / 903944 : ℝ) = -3 * Real.log 2 + 3 * Real.log 7
      + Real.log 17 - 2 * Real.log 19 - Real.log 313 := by
  rw [show (5831 / 903944 : ℝ) = (7 ^ 3 * 17 ^ 1) / (2 ^ 3 * 19 ^ 2 * 313 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (1 / 48)` over the prime basis. -/
private theorem log_1_48 :
    Real.log (1 / 48 : ℝ) = -4 * Real.log 2 - Real.log 3 := by
  rw [show (1 / 48 : ℝ) = 1 / (2 ^ 4 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_one]
  push_cast
  ring

/-- `Real.log (8 / 375)` over the prime basis. -/
private theorem log_8_375 :
    Real.log (8 / 375 : ℝ) = 3 * Real.log 2 - Real.log 3
      - 3 * Real.log 5 := by
  rw [show (8 / 375 : ℝ) = 2 ^ 3 / (3 ^ 1 * 5 ^ 3) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (1 / 24)` over the prime basis. -/
private theorem log_1_24 :
    Real.log (1 / 24 : ℝ) = -3 * Real.log 2 - Real.log 3 := by
  rw [show (1 / 24 : ℝ) = 1 / (2 ^ 3 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_one]
  push_cast
  ring

/-- `Real.log (5831 / 120192)` over the prime basis. -/
private theorem log_5831_120192 :
    Real.log (5831 / 120192 : ℝ) = -7 * Real.log 2 - Real.log 3
      + 3 * Real.log 7 + Real.log 17 - Real.log 313 := by
  rw [show (5831 / 120192 : ℝ) = (7 ^ 3 * 17 ^ 1) / (2 ^ 7 * 3 ^ 1 * 313 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (1 / 16)` over the prime basis. -/
private theorem log_1_16 :
    Real.log (1 / 16 : ℝ) = -4 * Real.log 2 := by
  rw [show (1 / 16 : ℝ) = 1 / 2 ^ 4 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_one]
  push_cast
  ring

/-- `Real.log (1078 / 14013)` over the prime basis. -/
private theorem log_1078_14013 :
    Real.log (1078 / 14013 : ℝ) = Real.log 2 - 4 * Real.log 3 + 2 * Real.log 7
      + Real.log 11 - Real.log 173 := by
  rw [show (1078 / 14013 : ℝ) = (2 ^ 1 * 7 ^ 2 * 11 ^ 1) / (3 ^ 4 * 173 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (1 / 12)` over the prime basis. -/
private theorem log_1_12 :
    Real.log (1 / 12 : ℝ) = -2 * Real.log 2 - Real.log 3 := by
  rw [show (1 / 12 : ℝ) = 1 / (2 ^ 2 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_one]
  push_cast
  ring

/-- `Real.log (2888 / 32229)` over the prime basis. -/
private theorem log_2888_32229 :
    Real.log (2888 / 32229 : ℝ) = 3 * Real.log 2 - 2 * Real.log 3
      + 2 * Real.log 19 - Real.log 3581 := by
  rw [show (2888 / 32229 : ℝ) = (2 ^ 3 * 19 ^ 2) / (3 ^ 2 * 3581 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (5 / 48)` over the prime basis. -/
private theorem log_5_48 :
    Real.log (5 / 48 : ℝ) = -4 * Real.log 2 - Real.log 3 + Real.log 5 := by
  rw [show (5 / 48 : ℝ) = 5 ^ 1 / (2 ^ 4 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (39 / 320)` over the prime basis. -/
private theorem log_39_320 :
    Real.log (39 / 320 : ℝ) = -6 * Real.log 2 + Real.log 3 - Real.log 5
      + Real.log 13 := by
  rw [show (39 / 320 : ℝ) = (3 ^ 1 * 13 ^ 1) / (2 ^ 6 * 5 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (1 / 8)` over the prime basis. -/
private theorem log_1_8 :
    Real.log (1 / 8 : ℝ) = -3 * Real.log 2 := by
  rw [show (1 / 8 : ℝ) = 1 / 2 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_one]
  push_cast
  ring

/-- `Real.log (7 / 16)` over the prime basis. -/
private theorem log_7_16 :
    Real.log (7 / 16 : ℝ) = -4 * Real.log 2 + Real.log 7 := by
  rw [show (7 / 16 : ℝ) = 7 ^ 1 / 2 ^ 4 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (141 / 320)` over the prime basis. -/
private theorem log_141_320 :
    Real.log (141 / 320 : ℝ) = -6 * Real.log 2 + Real.log 3 - Real.log 5
      + Real.log 47 := by
  rw [show (141 / 320 : ℝ) = (3 ^ 1 * 47 ^ 1) / (2 ^ 6 * 5 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (11 / 24)` over the prime basis. -/
private theorem log_11_24 :
    Real.log (11 / 24 : ℝ) = -3 * Real.log 2 - Real.log 3 + Real.log 11 := by
  rw [show (11 / 24 : ℝ) = 11 ^ 1 / (2 ^ 3 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (23 / 48)` over the prime basis. -/
private theorem log_23_48 :
    Real.log (23 / 48 : ℝ) = -4 * Real.log 2 - Real.log 3 + Real.log 23 := by
  rw [show (23 / 48 : ℝ) = 23 ^ 1 / (2 ^ 4 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (1 / 2)` over the prime basis. -/
private theorem log_1_2 :
    Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [show (1 / 2 : ℝ) = 1 / 2 ^ 1 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_one]
  push_cast
  ring

/-- `Real.log (25 / 48)` over the prime basis. -/
private theorem log_25_48 :
    Real.log (25 / 48 : ℝ) = -4 * Real.log 2 - Real.log 3
      + 2 * Real.log 5 := by
  rw [show (25 / 48 : ℝ) = 5 ^ 2 / (2 ^ 4 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (13 / 24)` over the prime basis. -/
private theorem log_13_24 :
    Real.log (13 / 24 : ℝ) = -3 * Real.log 2 - Real.log 3 + Real.log 13 := by
  rw [show (13 / 24 : ℝ) = 13 ^ 1 / (2 ^ 3 * 3 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (179 / 320)` over the prime basis. -/
private theorem log_179_320 :
    Real.log (179 / 320 : ℝ) = -6 * Real.log 2 - Real.log 5
      + Real.log 179 := by
  rw [show (179 / 320 : ℝ) = 179 ^ 1 / (2 ^ 6 * 5 ^ 1) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (9 / 16)` over the prime basis. -/
private theorem log_9_16 :
    Real.log (9 / 16 : ℝ) = -4 * Real.log 2 + 2 * Real.log 3 := by
  rw [show (9 / 16 : ℝ) = 3 ^ 2 / 2 ^ 4 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (375 / 343)` over the prime basis. -/
private theorem log_375_343 :
    Real.log (375 / 343 : ℝ) = Real.log 3 + 3 * Real.log 5
      - 3 * Real.log 7 := by
  rw [show (375 / 343 : ℝ) = (3 ^ 1 * 5 ^ 3) / 7 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `Real.log (190304 / 172125)` over the prime basis. -/
private theorem log_190304_172125 :
    Real.log (190304 / 172125 : ℝ) = 5 * Real.log 2 - 4 * Real.log 3
      - 3 * Real.log 5 - Real.log 17 + Real.log 19 + Real.log 313 := by
  rw [show (190304 / 172125 : ℝ) = (2 ^ 5 * 19 ^ 1 * 313 ^ 1) / (3 ^ 4 * 5 ^ 3 * 17 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (640999 / 576000)` over the prime basis. -/
private theorem log_640999_576000 :
    Real.log (640999 / 576000 : ℝ) = -9 * Real.log 2 - 2 * Real.log 3
      - 3 * Real.log 5 + Real.log 179 + Real.log 3581 := by
  rw [show (640999 / 576000 : ℝ) = (179 ^ 1 * 3581 ^ 1) / (2 ^ 9 * 3 ^ 2 * 5 ^ 3) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `Real.log (2941 / 2640)` over the prime basis. -/
private theorem log_2941_2640 :
    Real.log (2941 / 2640 : ℝ) = -4 * Real.log 2 - Real.log 3 - Real.log 5
      - Real.log 11 + Real.log 17 + Real.log 173 := by
  rw [show (2941 / 2640 : ℝ) = (17 ^ 1 * 173 ^ 1) / (2 ^ 4 * 3 ^ 1 * 5 ^ 1 * 11 ^ 1) by
        norm_num,
    Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-! ## The eight endpoint values

Each theorem covers one plane at the two ends of its interval.  The plane's
three values are supplied definitionally, `norm_num` evaluates the cells at the
rational `z`, and `linarith` combines the table above with the enclosures. -/

/-- **Plane 1 exceeds `1/100` at both ends of `[0, 1 / 3]`.** -/
theorem centerPlaneBound_endpoints_one :
    (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 0) 0 ∧
      (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 0) (1 / 3) := by
  have hK : (referencePlanes 0).diagValue = (375 / 343 : ℝ) := by rfl
  have hB : (referencePlanes 0).offValueB = (8 / 375 : ℝ) := by rfl
  have hC : (referencePlanes 0).offValueC = (8 / 375 : ℝ) := by rfl
  constructor
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_8_375, log_1_16, log_7_16, log_1_2, log_375_343,
      log_three_bounds.1, log_three_bounds.2, log_five_bounds.1,
      log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2,
      Real.log_two_gt_d9, Real.log_two_lt_d9]
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_8_375, log_1_24, log_1_12, log_7_16, log_23_48, log_25_48,
      log_375_343, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1,
      log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2,
      log_twentythree_bounds.1, log_twentythree_bounds.2, Real.log_two_gt_d9,
      Real.log_two_lt_d9]

/-- **Plane 2 exceeds `1/100` at both ends of `[1 / 3, 2 / 3]`.** -/
theorem centerPlaneBound_endpoints_two :
    (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 1) (1 / 3) ∧
      (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 1) (2 / 3) := by
  have hK : (referencePlanes 1).diagValue = (190304 / 172125 : ℝ) := by rfl
  have hB : (referencePlanes 1).offValueB = (5831 / 120192 : ℝ) := by rfl
  have hC : (referencePlanes 1).offValueC = (5831 / 903944 : ℝ) := by rfl
  constructor
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_5831_903944, log_1_24, log_5831_120192, log_1_12, log_7_16,
      log_23_48, log_25_48, log_190304_172125, log_three_bounds.1,
      log_three_bounds.2, log_five_bounds.1, log_five_bounds.2,
      log_seven_bounds.1, log_seven_bounds.2, log_seventeen_bounds.1,
      log_seventeen_bounds.2, log_nineteen_bounds.1, log_nineteen_bounds.2,
      log_twentythree_bounds.1, log_twentythree_bounds.2,
      log_threehundredthirteen_bounds.1, log_threehundredthirteen_bounds.2,
      Real.log_two_gt_d9, Real.log_two_lt_d9]
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_5831_903944, log_1_48, log_5831_120192, log_5_48, log_7_16,
      log_11_24, log_13_24, log_190304_172125, log_three_bounds.1,
      log_three_bounds.2, log_five_bounds.1, log_five_bounds.2,
      log_seven_bounds.1, log_seven_bounds.2, log_eleven_bounds.1,
      log_eleven_bounds.2, log_thirteen_bounds.1, log_thirteen_bounds.2,
      log_seventeen_bounds.1, log_seventeen_bounds.2, log_nineteen_bounds.1,
      log_nineteen_bounds.2, log_threehundredthirteen_bounds.1,
      log_threehundredthirteen_bounds.2, Real.log_two_gt_d9,
      Real.log_two_lt_d9]

/-- **Plane 3 exceeds `1/100` at both ends of `[2 / 3, 19 / 20]`.** -/
theorem centerPlaneBound_endpoints_three :
    (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 2) (2 / 3) ∧
      (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 2) (19 / 20) := by
  have hK : (referencePlanes 2).diagValue = (2941 / 2640 : ℝ) := by rfl
  have hB : (referencePlanes 2).offValueB = (1078 / 14013 : ℝ) := by rfl
  have hC : (referencePlanes 2).offValueC = (154 / 249985 : ℝ) := by rfl
  constructor
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_154_249985, log_1_48, log_1078_14013, log_5_48, log_7_16,
      log_11_24, log_13_24, log_2941_2640, log_three_bounds.1,
      log_three_bounds.2, log_five_bounds.1, log_five_bounds.2,
      log_seven_bounds.1, log_seven_bounds.2, log_eleven_bounds.1,
      log_eleven_bounds.2, log_thirteen_bounds.1, log_thirteen_bounds.2,
      log_seventeen_bounds.1, log_seventeen_bounds.2,
      log_onehundredseventythree_bounds.1, log_onehundredseventythree_bounds.2,
      Real.log_two_gt_d9, Real.log_two_lt_d9]
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_154_249985, log_1_320, log_1078_14013, log_39_320, log_7_16,
      log_141_320, log_179_320, log_2941_2640, log_three_bounds.1,
      log_three_bounds.2, log_five_bounds.1, log_five_bounds.2,
      log_seven_bounds.1, log_seven_bounds.2, log_eleven_bounds.1,
      log_eleven_bounds.2, log_thirteen_bounds.1, log_thirteen_bounds.2,
      log_seventeen_bounds.1, log_seventeen_bounds.2, log_fortyseven_bounds.1,
      log_fortyseven_bounds.2, log_onehundredseventythree_bounds.1,
      log_onehundredseventythree_bounds.2, log_onehundredseventynine_bounds.1,
      log_onehundredseventynine_bounds.2, Real.log_two_gt_d9,
      Real.log_two_lt_d9]

/-- **Plane 4 exceeds `1/100` at both ends of `[19 / 20, 1]`.** -/
theorem centerPlaneBound_endpoints_four :
    (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 3) (19 / 20) ∧
      (1 : ℝ) / 100 < centerPlaneBound (referencePlanes 3) 1 := by
  have hK : (referencePlanes 3).diagValue = (640999 / 576000 : ℝ) := by rfl
  have hB : (referencePlanes 3).offValueB = (2888 / 32229 : ℝ) := by rfl
  have hC : (referencePlanes 3).offValueC = (152 / 114738821 : ℝ) := by rfl
  constructor
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_152_114738821, log_1_320, log_2888_32229, log_39_320,
      log_7_16, log_141_320, log_179_320, log_640999_576000,
      log_three_bounds.1, log_three_bounds.2, log_five_bounds.1,
      log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2,
      log_thirteen_bounds.1, log_thirteen_bounds.2, log_nineteen_bounds.1,
      log_nineteen_bounds.2, log_fortyseven_bounds.1, log_fortyseven_bounds.2,
      log_onehundredseventynine_bounds.1, log_onehundredseventynine_bounds.2,
      log_thirtyfivehundredeightyone_bounds.1,
      log_thirtyfivehundredeightyone_bounds.2, Real.log_two_gt_d9,
      Real.log_two_lt_d9]
  · norm_num [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy, xLogX, hK, hB, hC]
    linarith [log_2888_32229, log_1_8, log_7_16, log_9_16, log_640999_576000,
      log_three_bounds.1, log_three_bounds.2, log_five_bounds.1,
      log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2,
      log_nineteen_bounds.1, log_nineteen_bounds.2,
      log_onehundredseventynine_bounds.1, log_onehundredseventynine_bounds.2,
      log_thirtyfivehundredeightyone_bounds.1,
      log_thirtyfivehundredeightyone_bounds.2, Real.log_two_gt_d9,
      Real.log_two_lt_d9]

end StochasticToDeterministicLatents.Binary
