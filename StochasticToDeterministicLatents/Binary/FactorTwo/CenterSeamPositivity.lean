/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  The quartic cofactor and its
three lemmas come from a separate private module, all four of whose remaining
declarations land here as private helpers.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterSeamChart

/-!
# Signs on the seam

Everything the seam's derivative calculation needs to know about signs.  The
two rescaled off-diagonal cells are positive and strictly ordered wherever the
imbalance does not vanish, and the two quantities that appear as denominators
in the seam's logarithms are positive as well.

The last result is the one the derivative's sign turns on: a ratio built from
the smaller cell over the larger, each weighted by the fourth power of its
denominator, exceeds one, so its logarithm is positive.  The proof factors the
difference of the two products through a quartic in the cells' sum and product,
and that quartic is positive on the seam because a substitution turns it into a
ratio of polynomials with positive coefficients.

**This route is not the page's.**  Its Proposition 4.6 bounds the isolating
code's seam derivative in the difference of the two off-diagonal cells, through
an integral remainder inequality; nothing here corresponds to a display.

Nothing in this module bounds a margin and nothing in it differentiates
anything.
-/

namespace StochasticToDeterministicLatents.Binary

variable {r : ℝ}

/-! ## The quartic cofactor -/

/-- The cofactor left when the difference of the two weighted cells is divided
by the difference of the cells themselves.  Its arguments are the cells' sum
and their product. -/
private noncomputable def seamCofactor (r q : ℝ) : ℝ :=
  -(1 - 2 * q) ^ 4 + 4 * (1 - 2 * q) ^ 3 * r
    - 6 * (1 - 2 * q) ^ 2 * (r ^ 2 - q)
    + 4 * (1 - 2 * q) * (r ^ 3 - 2 * r * q)
    - (r ^ 4 - 3 * r ^ 2 * q + q ^ 2)

private theorem seamCofactor_factor (x y : ℝ) :
    y * (1 - y - 2 * x * y) ^ 4 - x * (1 - x - 2 * x * y) ^ 4
      = (x - y) * seamCofactor (x + y) (x * y) := by
  unfold seamCofactor
  ring

private theorem seamCofactor_eq (t : ℝ) (ht : 0 < t) :
    seamCofactor ((1 + t) / (2 + t)) (1 / (8 * t + 9))
      = (512 * t ^ 7 + 6272 * t ^ 6 + 32456 * t ^ 5 + 89464 * t ^ 4
            + 142378 * t ^ 3 + 130783 * t ^ 2 + 64044 * t + 12875)
          / ((t + 2) ^ 4 * (8 * t + 9) ^ 4) := by
  have ht2 : 2 + t ≠ 0 := by positivity
  have ht9 : 8 * t + 9 ≠ 0 := by positivity
  unfold seamCofactor
  field_simp [ht2, ht9]
  ring

private theorem seamCofactor_pos (t : ℝ) (ht : 0 < t) :
    0 < seamCofactor ((1 + t) / (2 + t)) (1 / (8 * t + 9)) := by
  rw [seamCofactor_eq t ht]
  positivity

/-- The cofactor is positive at every radius the seam runs through.  The
substitution `t = (2 r - 1) / (1 - r)` carries the interval to the positive
half line, where the cofactor is a ratio of polynomials with positive
coefficients. -/
private theorem seamCofactor_pos_of_radius (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    0 < seamCofactor r (seamProduct r) := by
  have hrlo : (1 : ℝ) / 2 < r := hr.1
  have hrhi : r < 1 := hr.2
  have hden : 1 - r ≠ 0 := by linarith
  have ht : 0 < (2 * r - 1) / (1 - r) :=
    div_pos (by nlinarith [hrlo]) (by linarith)
  have hr' : r = (1 + (2 * r - 1) / (1 - r)) / (2 + (2 * r - 1) / (1 - r)) := by
    field_simp [hden]
    ring_nf
  have hpi : seamProduct r = 1 / (8 * ((2 * r - 1) / (1 - r)) + 9) := by
    have hdenpi : 1 + 7 * r ≠ 0 := by nlinarith [hrlo]
    have hdenpi' : 1 + r * 7 ≠ 0 := by nlinarith [hrlo]
    unfold seamProduct
    field_simp [hden, hdenpi, hdenpi']
    rw [show 8 * (r * 2 - 1) + (1 - r) * 9 = 1 + r * 7 by ring]
    rw [div_self hdenpi']
  rw [hpi]
  nth_rewrite 1 [hr']
  exact seamCofactor_pos _ ht

/-! ## The two cells, and the two denominators -/

/-- **The seam's cells are positive, ordered and below one, and both seam
denominators are positive**, at any radius the seam runs through whose
imbalance does not vanish. -/
theorem seamCells_pos (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    0 < seamCellC r ∧ seamCellC r < seamCellB r ∧ seamCellB r < 1
      ∧ 0 < 1 - seamCellB r - 2 * seamProduct r
      ∧ 0 < 1 - seamCellC r - 2 * seamProduct r := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr.1
  have hpi : 0 < seamProduct r := by
    unfold seamProduct
    exact div_pos (by linarith [hr.2]) (by nlinarith [hr0])
  have hh_lt : seamImbalanceSq r < 1 := by
    unfold seamImbalanceSq
    have : 0 < 4 * seamProduct r / r ^ 2 := by positivity
    linarith
  have hsqrt0 : 0 < Real.sqrt (seamImbalanceSq r) := Real.sqrt_pos.2 hh
  have hsqrt1 : Real.sqrt (seamImbalanceSq r) < 1 := by
    have hsqrt_sq : (Real.sqrt (seamImbalanceSq r)) ^ 2 = seamImbalanceSq r :=
      Real.sq_sqrt (le_of_lt hh)
    have hsqrt_nonneg := Real.sqrt_nonneg (seamImbalanceSq r)
    nlinarith
  have hsy0 : 0 < seamCellC r := by
    unfold seamCellC
    positivity
  have hxy : seamCellC r < seamCellB r := by
    unfold seamCellC seamCellB
    nlinarith
  have hsx_lt_r : seamCellB r < r := by
    unfold seamCellB
    nlinarith
  have hbase : 0 < 1 - r - 2 * seamProduct r := by
    unfold seamProduct
    have hden : 0 < 1 + 7 * r := by positivity
    have hnum : 0 < 7 * r - 1 := by nlinarith [hr.1]
    calc
      0 < (1 - r) * (7 * r - 1) / (1 + 7 * r) :=
        div_pos (mul_pos (by linarith [hr.2]) hnum) hden
      _ = 1 - r - 2 * ((1 - r) / (1 + 7 * r)) := by field_simp; ring
  refine ⟨hsy0, hxy, lt_trans hsx_lt_r hr.2, ?_, ?_⟩
  · linarith
  · linarith

/-! ## The logarithms -/

/-- A logarithm identity in two positive reals.  It mentions no law and no
seam quantity: it says that the combination the seam's derivative produces
collapses to a single logarithm of a ratio. -/
theorem seam_log_identity (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hr : x + y < 1) (hA : 0 < 1 - x - 2 * x * y)
    (hB : 0 < 1 - y - 2 * x * y) :
    let A := 1 - x - 2 * x * y
    let B := 1 - y - 2 * x * y
    2 * ((3 / 2) * Real.log (x / y)
        + 2 * Real.log (((1 - x) * B) / ((1 - y) * A))
        - 2 * Real.log ((x * (1 - x)) / (y * (1 - y))))
      = Real.log ((y * B ^ 4) / (x * A ^ 4)) := by
  dsimp only
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  rw [Real.log_div hx.ne' hy.ne']
  rw [Real.log_div (mul_ne_zero hx1.ne' hB.ne')
    (mul_ne_zero hy1.ne' hA.ne')]
  rw [Real.log_mul hx1.ne' hB.ne', Real.log_mul hy1.ne' hA.ne']
  rw [Real.log_div (mul_ne_zero hx.ne' hx1.ne')
    (mul_ne_zero hy.ne' hy1.ne')]
  rw [Real.log_mul hx.ne' hx1.ne', Real.log_mul hy.ne' hy1.ne']
  rw [Real.log_div (mul_ne_zero hy.ne' (pow_ne_zero 4 hB.ne'))
    (mul_ne_zero hx.ne' (pow_ne_zero 4 hA.ne'))]
  rw [Real.log_mul hy.ne' (pow_ne_zero 4 hB.ne'),
    Real.log_mul hx.ne' (pow_ne_zero 4 hA.ne'), Real.log_pow, Real.log_pow]
  ring

/-- **The seam's logarithm is positive.**  The smaller cell weighted by the
fourth power of its denominator exceeds the larger cell weighted by the fourth
power of its own, so the logarithm of their ratio is positive.  This is the
sign the seam's derivative turns on. -/
theorem seam_logRatio_pos (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    0 < Real.log ((seamCellC r * (1 - seamCellC r - 2 * seamProduct r) ^ 4)
      / (seamCellB r * (1 - seamCellB r - 2 * seamProduct r) ^ 4)) := by
  obtain ⟨hsy, hyx, hsx1, hA, hB⟩ := seamCells_pos hr hh
  have hr0 : 0 < r := lt_trans (by norm_num) hr.1
  have hsqrt_sq : (Real.sqrt (seamImbalanceSq r)) ^ 2 = seamImbalanceSq r :=
    Real.sq_sqrt (le_of_lt hh)
  have hsum : seamCellB r + seamCellC r = r := by
    unfold seamCellB seamCellC
    ring
  have hprod : seamCellB r * seamCellC r = seamProduct r := by
    have halg : seamCellB r * seamCellC r
        = r ^ 2 * (1 - (Real.sqrt (seamImbalanceSq r)) ^ 2) / 4 := by
      unfold seamCellB seamCellC
      ring
    rw [halg, hsqrt_sq]
    unfold seamImbalanceSq
    field_simp [hr0.ne']
    ring
  have hdiff : 0 < seamCellC r * (1 - seamCellC r - 2 * seamProduct r) ^ 4
      - seamCellB r * (1 - seamCellB r - 2 * seamProduct r) ^ 4 := by
    rw [show 2 * seamProduct r = 2 * seamCellB r * seamCellC r by
      nlinarith [hprod]]
    rw [seamCofactor_factor]
    rw [hsum, hprod]
    exact mul_pos (sub_pos.mpr hyx) (seamCofactor_pos_of_radius hr)
  have hden : 0 < seamCellB r * (1 - seamCellB r - 2 * seamProduct r) ^ 4 := by
    have hsx : 0 < seamCellB r := lt_trans hsy hyx
    positivity
  apply Real.log_pos
  apply (one_lt_div hden).2
  linarith

end StochasticToDeterministicLatents.Binary
