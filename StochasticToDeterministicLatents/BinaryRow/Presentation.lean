import StochasticToDeterministicLatents.BinaryRow.Optimizer
import StochasticToDeterministicLatents.BinaryRow.Moments

/-!
# The oriented two-contact presentation on `Bit × Y`

A full-support law on `Bit × Y` whose stochastic optimum is below `I(X;Y)` is a mixture of two
contacts of one feasible kernel, labelled by `Bit` so that their row parameters satisfy
`0 < s < t` (`rowTwoContact_presentation`). This module collects what the two-contact case gives:

* the column law of a contact, `colMass q y = c_y³ / (1 + x³)²` (`rowContact_colMass`), which is
  positive;
* the Lagrange identities for the two kernel-moment determinants (`rowMoment_det_low`,
  `rowMoment_det_high`), both strictly positive for two distinct contacts
  (`rowTwoContact_det_pos`), which in the row parameters reads `(st)² < s + t` and
  `1 < st(s + t)` (`rowTwoContact_param_ineq`);
* the resulting strict bounds on `ℓ = s³`, `a = s³/(1 + s³)` and `b = 1/(1 + t³)` in terms of
  `k = t/s` and `N = k² + k + 1` (`twoContact_ell_mem`, `twoContact_a_mem`, `twoContact_b_mem`);
* the variance over `Y` of a contact's row-one posterior, `κ r (1 - r)` with
  `κ = st/(s + t)²` (`rowTwoContact_variance`).

The kernel is written `w`; the mixture weight of the second component is `V.prior (e.symm 1)`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose `Feasible`,
`IsContact` and `Latent` these statements use.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Polynomial Binary

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-! ## The column law of a contact -/

omit [DecidableEq Y] in
/-- The column coefficients are positive for a feasible kernel and a positive parameter. -/
private theorem colCoeff_pos_aux {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    {x : ℝ} (hx : 0 < x) (y : Y) : 0 < colCoeff w x y := by
  have h0 := hw.1 (0, y) (mem_univ _)
  have h1 := hw.1 (1, y) (mem_univ _)
  unfold colCoeff
  positivity

/-- A contact's column masses are the normalized cubes of the column coefficients:
`colMass q y = a_y(x)³/(1 + x³)²`. -/
theorem rowContact_colMass {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {x : ℝ} (hx : RowCubeParam q x) (y : Y) :
    colMass q y = colCoeff w x y ^ 3 / (1 + x ^ 3) ^ 2 := by
  rw [(rowContact_root hw hq hx).2 y, rowContact_cubeSum hw hq hx]

/-- Every column mass of a contact is positive. -/
theorem rowContact_colMass_pos {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    (y : Y) : 0 < colMass q y := by
  obtain ⟨x, hx⟩ := rowContact_hasCubeParam hw hq
  rw [rowContact_colMass hw hq hx y]
  have hc := colCoeff_pos_aux hw hx.1 y
  have hxp : 0 < x := hx.1
  positivity

/-! ## Moment determinants (Lagrange identities) -/

omit [DecidableEq Y] in
/-- Expanding a double sum of products of one-variable factors. -/
private theorem aux_double_sum (f g h k u v : Y → ℝ) :
    ∑ y, ∑ y', (f y * g y' + h y * k y' - 2 * (u y * v y')) =
      (∑ y, f y) * (∑ y, g y) + (∑ y, h y) * (∑ y, k y) - 2 * ((∑ y, u y) * (∑ y, v y)) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-- The per-term expansion of the low Lagrange identity. -/
private theorem aux_low_term (a b a' b' : ℝ) :
    a * a' * (b * a' - b' * a) ^ 2 =
      (a * b ^ 2) * a' ^ 3 + a ^ 3 * (a' * b' ^ 2) - 2 * ((a ^ 2 * b) * (a' ^ 2 * b')) := by
  ring

/-- The per-term expansion of the high Lagrange identity. -/
private theorem aux_high_term (a b a' b' : ℝ) :
    b * b' * (b * a' - b' * a) ^ 2 =
      b ^ 3 * (a' ^ 2 * b') + (a ^ 2 * b) * b' ^ 3 - 2 * ((a * b ^ 2) * (a' * b' ^ 2)) := by
  ring

omit [DecidableEq Y] in
/-- The low double sum is twice the low moment determinant. -/
private theorem aux_low_sum (w : Bit × Y → ℝ) :
    ∑ y, ∑ y', w (0, y) * w (0, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2 =
      2 * (rowMoment w 0 * rowMoment w 2 - rowMoment w 1 ^ 2) := by
  have h := aux_double_sum (fun y => w (0, y) * w (1, y) ^ 2) (fun y => w (0, y) ^ 3)
    (fun y => w (0, y) ^ 3) (fun y => w (0, y) * w (1, y) ^ 2)
    (fun y => w (0, y) ^ 2 * w (1, y)) (fun y => w (0, y) ^ 2 * w (1, y))
  rw [rowMoment_zero, rowMoment_one, rowMoment_two]
  calc
    _ = ∑ y, ∑ y', (w (0, y) * w (1, y) ^ 2 * w (0, y') ^ 3 +
          w (0, y) ^ 3 * (w (0, y') * w (1, y') ^ 2) -
          2 * (w (0, y) ^ 2 * w (1, y) * (w (0, y') ^ 2 * w (1, y')))) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => aux_low_term _ _ _ _
    _ = _ := by rw [h]; ring

omit [DecidableEq Y] in
/-- The high double sum is twice the high moment determinant. -/
private theorem aux_high_sum (w : Bit × Y → ℝ) :
    ∑ y, ∑ y', w (1, y) * w (1, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2 =
      2 * (rowMoment w 1 * rowMoment w 3 - rowMoment w 2 ^ 2) := by
  have h := aux_double_sum (fun y => w (1, y) ^ 3) (fun y => w (0, y) ^ 2 * w (1, y))
    (fun y => w (0, y) ^ 2 * w (1, y)) (fun y => w (1, y) ^ 3)
    (fun y => w (0, y) * w (1, y) ^ 2) (fun y => w (0, y) * w (1, y) ^ 2)
  rw [rowMoment_one, rowMoment_two, rowMoment_three]
  calc
    _ = ∑ y, ∑ y', (w (1, y) ^ 3 * (w (0, y') ^ 2 * w (1, y')) +
          w (0, y) ^ 2 * w (1, y) * w (1, y') ^ 3 -
          2 * (w (0, y) * w (1, y) ^ 2 * (w (0, y') * w (1, y') ^ 2))) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => aux_high_term _ _ _ _
    _ = _ := by rw [h]; ring

omit [DecidableEq Y] in
/-- The lower moment determinant `m₀ m₂ - m₁²` as a weighted sum of squares. -/
theorem rowMoment_det_low (w : Bit × Y → ℝ) :
    rowMoment w 0 * rowMoment w 2 - rowMoment w 1 ^ 2 =
      (∑ y, ∑ y', w (0, y) * w (0, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2)
        / 2 := by
  rw [aux_low_sum]
  ring

omit [DecidableEq Y] in
/-- The upper moment determinant `m₁ m₃ - m₂²` as a weighted sum of squares. -/
theorem rowMoment_det_high (w : Bit × Y → ℝ) :
    rowMoment w 1 * rowMoment w 3 - rowMoment w 2 ^ 2 =
      (∑ y, ∑ y', w (1, y) * w (1, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2)
        / 2 := by
  rw [aux_high_sum]
  ring

omit [DecidableEq Y] in
/-- A double sum of positively weighted squares is nonnegative. -/
private theorem aux_weighted_nonneg {c : Y → ℝ} (hc : ∀ y, 0 < c y) (d : Y → Y → ℝ) :
    0 ≤ ∑ y, ∑ y', c y * c y' * d y y' ^ 2 :=
  Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun y' _ =>
    mul_nonneg (mul_pos (hc y) (hc y')).le (sq_nonneg _)

omit [DecidableEq Y] in
/-- A vanishing double sum of positively weighted squares has every square zero. -/
private theorem aux_weighted_eq_zero {c : Y → ℝ} (hc : ∀ y, 0 < c y) (d : Y → Y → ℝ)
    (h : ∑ y, ∑ y', c y * c y' * d y y' ^ 2 = 0) (y y' : Y) : d y y' = 0 := by
  have hin : ∀ y ∈ (univ : Finset Y), 0 ≤ ∑ y', c y * c y' * d y y' ^ 2 :=
    fun y _ => Finset.sum_nonneg fun y' _ => mul_nonneg (mul_pos (hc y) (hc y')).le (sq_nonneg _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hin).mp h y (mem_univ y)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y' _ => mul_nonneg (mul_pos (hc y) (hc y')).le (sq_nonneg (d y y')))).mp h1 y'
      (mem_univ y')
  have hne : c y * c y' ≠ 0 := (mul_pos (hc y) (hc y')).ne'
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hne
  · simpa using h3

omit [DecidableEq Y] in
/-- If every difference vanishes, so does every weighted double sum of their squares. -/
private theorem aux_weighted_zero_of {c : Y → ℝ} (d : Y → Y → ℝ) (hd : ∀ y y', d y y' = 0) :
    ∑ y, ∑ y', c y * c y' * d y y' ^ 2 = 0 :=
  Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun y' _ => by rw [hd y y']; ring

omit [DecidableEq Y] in
/-- For a feasible kernel the lower moment determinant `m₀ m₂ - m₁²` is nonnegative. -/
theorem rowMoment_det_low_nonneg {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w) :
    0 ≤ rowMoment w 0 * rowMoment w 2 - rowMoment w 1 ^ 2 := by
  rw [rowMoment_det_low]
  exact div_nonneg (aux_weighted_nonneg (c := fun y => w (0, y)) (fun y => hw.1 _ (mem_univ _))
    (fun y y' => w (1, y) * w (0, y') - w (1, y') * w (0, y))) (by norm_num)

omit [DecidableEq Y] in
/-- For a feasible kernel the upper moment determinant `m₁ m₃ - m₂²` is nonnegative. -/
theorem rowMoment_det_high_nonneg {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w) :
    0 ≤ rowMoment w 1 * rowMoment w 3 - rowMoment w 2 ^ 2 := by
  rw [rowMoment_det_high]
  exact div_nonneg (aux_weighted_nonneg (c := fun y => w (1, y)) (fun y => hw.1 _ (mem_univ _))
    (fun y y' => w (1, y) * w (0, y') - w (1, y') * w (0, y))) (by norm_num)

omit [DecidableEq Y] in
/-- A vanishing low determinant makes the two kernel rows proportional. -/
private theorem aux_cross_zero_of_low {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h : rowMoment w 0 * rowMoment w 2 - rowMoment w 1 ^ 2 = 0) (y y' : Y) :
    w (1, y) * w (0, y') - w (1, y') * w (0, y) = 0 := by
  rw [rowMoment_det_low] at h
  have h' : ∑ y, ∑ y', w (0, y) * w (0, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2
      = 0 := by linarith
  exact aux_weighted_eq_zero (c := fun y => w (0, y)) (fun y => hw.1 _ (mem_univ _))
    (fun y y' => w (1, y) * w (0, y') - w (1, y') * w (0, y)) h' y y'

omit [DecidableEq Y] in
/-- A vanishing high determinant makes the two kernel rows proportional. -/
private theorem aux_cross_zero_of_high {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h : rowMoment w 1 * rowMoment w 3 - rowMoment w 2 ^ 2 = 0) (y y' : Y) :
    w (1, y) * w (0, y') - w (1, y') * w (0, y) = 0 := by
  rw [rowMoment_det_high] at h
  have h' : ∑ y, ∑ y', w (1, y) * w (1, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2
      = 0 := by linarith
  exact aux_weighted_eq_zero (c := fun y => w (1, y)) (fun y => hw.1 _ (mem_univ _))
    (fun y y' => w (1, y) * w (0, y') - w (1, y') * w (0, y)) h' y y'

omit [DecidableEq Y] in
/-- Proportional rows make the low determinant vanish. -/
private theorem aux_low_zero_of_cross {w : Bit × Y → ℝ}
    (hd : ∀ y y', w (1, y) * w (0, y') - w (1, y') * w (0, y) = 0) :
    rowMoment w 0 * rowMoment w 2 - rowMoment w 1 ^ 2 = 0 := by
  have h0 : ∑ y, ∑ y', w (0, y) * w (0, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2
      = 0 := aux_weighted_zero_of (c := fun y => w (0, y))
        (fun y y' => w (1, y) * w (0, y') - w (1, y') * w (0, y)) hd
  rw [rowMoment_det_low, h0]
  norm_num

omit [DecidableEq Y] in
/-- Proportional rows make the high determinant vanish. -/
private theorem aux_high_zero_of_cross {w : Bit × Y → ℝ}
    (hd : ∀ y y', w (1, y) * w (0, y') - w (1, y') * w (0, y) = 0) :
    rowMoment w 1 * rowMoment w 3 - rowMoment w 2 ^ 2 = 0 := by
  have h0 : ∑ y, ∑ y', w (1, y) * w (1, y') * (w (1, y) * w (0, y') - w (1, y') * w (0, y)) ^ 2
      = 0 := aux_weighted_zero_of (c := fun y => w (1, y))
        (fun y y' => w (1, y) * w (0, y') - w (1, y') * w (0, y)) hd
  rw [rowMoment_det_high, h0]
  norm_num

/-- The low determinant in the two row parameters. -/
private theorem aux_det_low_formula {s t A B E : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hA : A = 1 - (s * t) ^ 3 / (s + t) ^ 3)
    (hB : B = s * t * (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3)
    (hE : E = (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3) :
    A * E - B ^ 2 = (s ^ 2 + s * t + t ^ 2) * (s + t - (s * t) ^ 2) / (s + t) ^ 4 := by
  have hR : s + t ≠ 0 := (add_pos hs ht).ne'
  subst hA hB hE
  field_simp
  ring

/-- The high determinant in the two row parameters. -/
private theorem aux_det_high_formula {s t B E D : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hB : B = s * t * (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3)
    (hE : E = (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3)
    (hD : D = 1 - 1 / (s + t) ^ 3) :
    B * D - E ^ 2 = (s ^ 2 + s * t + t ^ 2) * (s * t * (s + t) - 1) / (s + t) ^ 4 := by
  have hR : s + t ≠ 0 := (add_pos hs ht).ne'
  subst hB hE hD
  field_simp
  ring

/-- A quotient with positive outer factors vanishes only with its middle factor. -/
private theorem aux_zero_of_quot_zero {Q X H : ℝ} (hQ : 0 < Q) (hH : 0 < H) (h : Q * X / H = 0) :
    X = 0 := by
  rcases div_eq_zero_iff.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hQ.ne'
    · exact h2
  · exact absurd h1 hH.ne'

/-- A quotient with positive outer factors is positive only with its middle factor. -/
private theorem aux_pos_of_quot_pos {Q X H : ℝ} (hQ : 0 < Q) (hH : 0 < H) (h : 0 < Q * X / H) :
    0 < X := by
  have h1 : 0 < Q * X := by
    have := mul_pos h hH
    rwa [div_mul_cancel₀ _ hH.ne'] at this
  by_contra hX
  have hX' : X ≤ 0 := not_lt.mp hX
  nlinarith

/-- The two determinant factors cannot vanish together at positive parameters. -/
private theorem aux_param_not_both {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h1 : s + t - (s * t) ^ 2 = 0) (h2 : s * t * (s + t) - 1 = 0) : False := by
  have hv : 0 < s * t := mul_pos hs ht
  have hv3 : (s * t) ^ 3 = 1 := by linear_combination h2 - (s * t) * h1
  have he : s + t = (s * t) ^ 2 := by linarith
  have hsq : (s + t) ^ 2 = s * t := by
    rw [he]
    linear_combination (s * t) * hv3
  nlinarith [sq_nonneg (s - t)]

/-- Two distinct contacts make both moment determinants strictly positive. -/
theorem rowTwoContact_det_pos {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    (hqr : q ≠ r) {s t : ℝ} (hs : RowCubeParam q s) (ht : RowCubeParam r t) :
    0 < rowMoment w 0 * rowMoment w 2 - rowMoment w 1 ^ 2 ∧
      0 < rowMoment w 1 * rowMoment w 3 - rowMoment w 2 ^ 2 := by
  obtain ⟨hA, hB, hE, hD⟩ := rowTwoContact_moments hw hq hr hqr hs ht
  have hs0 : 0 < s := hs.1
  have ht0 : 0 < t := ht.1
  have hQ : 0 < s ^ 2 + s * t + t ^ 2 := by positivity
  have hH : 0 < (s + t) ^ 4 := by positivity
  have hnot : ¬ (rowMoment w 0 * rowMoment w 2 - rowMoment w 1 ^ 2 = 0 ∧
      rowMoment w 1 * rowMoment w 3 - rowMoment w 2 ^ 2 = 0) := by
    rintro ⟨h1, h2⟩
    rw [aux_det_low_formula hs0 ht0 hA hB hE] at h1
    rw [aux_det_high_formula hs0 ht0 hB hE hD] at h2
    exact aux_param_not_both hs0 ht0 (aux_zero_of_quot_zero hQ hH h1)
      (aux_zero_of_quot_zero hQ hH h2)
  refine ⟨lt_of_le_of_ne (rowMoment_det_low_nonneg hw) fun h => hnot ⟨h.symm, ?_⟩,
    lt_of_le_of_ne (rowMoment_det_high_nonneg hw) fun h => hnot ⟨?_, h.symm⟩⟩
  · exact aux_high_zero_of_cross (aux_cross_zero_of_low hw h.symm)
  · exact aux_low_zero_of_cross (aux_cross_zero_of_high hw h.symm)

/-- The determinant inequalities in the two row parameters. -/
theorem rowTwoContact_param_ineq {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    (hqr : q ≠ r) {s t : ℝ} (hs : RowCubeParam q s) (ht : RowCubeParam r t) :
    (s * t) ^ 2 < s + t ∧ 1 < s * t * (s + t) := by
  obtain ⟨hA, hB, hE, hD⟩ := rowTwoContact_moments hw hq hr hqr hs ht
  obtain ⟨hlow, hhigh⟩ := rowTwoContact_det_pos hw hq hr hqr hs ht
  have hs0 : 0 < s := hs.1
  have ht0 : 0 < t := ht.1
  have hQ : 0 < s ^ 2 + s * t + t ^ 2 := by positivity
  have hH : 0 < (s + t) ^ 4 := by positivity
  rw [aux_det_low_formula hs0 ht0 hA hB hE] at hlow
  rw [aux_det_high_formula hs0 ht0 hB hE hD] at hhigh
  have h1 := aux_pos_of_quot_pos hQ hH hlow
  have h2 := aux_pos_of_quot_pos hQ hH hhigh
  constructor <;> linarith

/-! ## Scalar bounds -/

/-- The lower endpoint for `ℓ`, cleared of `t/s`. -/
private theorem aux_ell_lower_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    1 / (t / s * (t / s + 1)) = s ^ 2 / (t * (s + t)) := by
  have hs' : s ≠ 0 := hs.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hst : s + t ≠ 0 := (add_pos hs ht).ne'
  field_simp
  ring

/-- The upper endpoint for `ℓ`, cleared of `t/s`. -/
private theorem aux_ell_upper_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (t / s + 1) / (t / s) ^ 2 = s * (s + t) / t ^ 2 := by
  have hs' : s ≠ 0 := hs.ne'
  have ht' : t ≠ 0 := ht.ne'
  field_simp
  ring

/-- The lower endpoint `1/N`, cleared of `t/s`. -/
private theorem aux_N_lower_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    1 / ((t / s) ^ 2 + t / s + 1) = s ^ 2 / (s ^ 2 + s * t + t ^ 2) := by
  have hs' : s ≠ 0 := hs.ne'
  have hQ : s ^ 2 + s * t + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The upper endpoint `(k+1)/N`, cleared of `t/s`. -/
private theorem aux_N_upper_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (t / s + 1) / ((t / s) ^ 2 + t / s + 1) = s * (s + t) / (s ^ 2 + s * t + t ^ 2) := by
  have hs' : s ≠ 0 := hs.ne'
  have hQ : s ^ 2 + s * t + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- For two-contact parameters, `1/(k (k + 1)) < s³ < (k + 1)/k²` with `k = t/s`. -/
theorem twoContact_ell_mem {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h1 : (s * t) ^ 2 < s + t) (h2 : 1 < s * t * (s + t)) :
    1 / (t / s * (t / s + 1)) < s ^ 3 ∧ s ^ 3 < (t / s + 1) / (t / s) ^ 2 := by
  rw [aux_ell_lower_eq hs ht, aux_ell_upper_eq hs ht]
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left h2 (pow_pos hs 2)]
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left h1 hs]

/-- For two-contact parameters, `a = s³/(1 + s³)` lies strictly between `1/N` and `(k + 1)/N`,
with `k = t/s` and `N = k² + k + 1`. -/
theorem twoContact_a_mem {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h1 : (s * t) ^ 2 < s + t) (h2 : 1 < s * t * (s + t)) :
    1 / ((t / s) ^ 2 + t / s + 1) < s ^ 3 / (1 + s ^ 3) ∧
      s ^ 3 / (1 + s ^ 3) < (t / s + 1) / ((t / s) ^ 2 + t / s + 1) := by
  rw [aux_N_lower_eq hs ht, aux_N_upper_eq hs ht]
  have hQ : 0 < s ^ 2 + s * t + t ^ 2 := by positivity
  have hU : 0 < 1 + s ^ 3 := by positivity
  constructor
  · rw [div_lt_div_iff₀ hQ hU]
    nlinarith [mul_lt_mul_of_pos_left h2 (pow_pos hs 2)]
  · rw [div_lt_div_iff₀ hU hQ]
    nlinarith [mul_lt_mul_of_pos_left h1 hs]

/-- For two-contact parameters, `b = 1/(1 + t³)` lies strictly between `1/N` and `(k + 1)/N`,
with `k = t/s` and `N = k² + k + 1`. -/
theorem twoContact_b_mem {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h1 : (s * t) ^ 2 < s + t) (h2 : 1 < s * t * (s + t)) :
    1 / ((t / s) ^ 2 + t / s + 1) < 1 / (1 + t ^ 3) ∧
      1 / (1 + t ^ 3) < (t / s + 1) / ((t / s) ^ 2 + t / s + 1) := by
  rw [aux_N_lower_eq hs ht, aux_N_upper_eq hs ht]
  have hQ : 0 < s ^ 2 + s * t + t ^ 2 := by positivity
  have hU : 0 < 1 + t ^ 3 := by positivity
  constructor
  · rw [div_lt_div_iff₀ hQ hU]
    nlinarith [mul_lt_mul_of_pos_left h1 ht]
  · rw [div_lt_div_iff₀ hU hQ]
    nlinarith [mul_lt_mul_of_pos_left h2 (pow_pos ht 2)]

/-! ## The variance identity -/

/-- One column's contribution, with the column coefficient kept as an atom. -/
private theorem aux_variance_term_coeff {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {s : ℝ} (hs : RowCubeParam q s) (y : Y) :
    colMass q y * (q (1, y) / colMass q y) ^ 2 =
      w (1, y) ^ 2 * s ^ 4 * colCoeff w s y / (1 + s ^ 3) ^ 2 := by
  have hc := colCoeff_pos_aux hw hs.1 y
  have hsp : 0 < s := hs.1
  have hU : 0 < 1 + s ^ 3 := by positivity
  have hc' : colCoeff w s y ≠ 0 := hc.ne'
  have hU' : 1 + s ^ 3 ≠ 0 := hU.ne'
  rw [(rowContact_entry hw hq hs y).2, rowContact_colMass hw hq hs y]
  field_simp

/-- One column's contribution, in the kernel entries. -/
private theorem aux_variance_term {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {s : ℝ} (hs : RowCubeParam q s) (y : Y) :
    colMass q y * (q (1, y) / colMass q y) ^ 2 =
      s ^ 4 * (w (0, y) * w (1, y) ^ 2 + s ^ 2 * w (1, y) ^ 3) / (1 + s ^ 3) ^ 2 := by
  rw [aux_variance_term_coeff hw hq hs y, colCoeff]
  ring

/-- The second moment of the row-one posterior, in the kernel moments. -/
theorem rowContact_posterior_sq_sum {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {s : ℝ} (hs : RowCubeParam q s) :
    ∑ y, colMass q y * (q (1, y) / colMass q y) ^ 2 =
      s ^ 4 * (rowMoment w 2 + s ^ 2 * rowMoment w 3) / (1 + s ^ 3) ^ 2 := by
  rw [rowMoment_two, rowMoment_three]
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [aux_variance_term hw hq hs y]

/-- The variance identity as pure algebra in the two row parameters. -/
private theorem aux_variance_identity {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    s ^ 4 * ((s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3 + s ^ 2 * (1 - 1 / (s + t) ^ 3)) /
        (1 + s ^ 3) ^ 2 - (s ^ 3 / (1 + s ^ 3)) ^ 2 =
      s * t / (s + t) ^ 2 * (s ^ 3 / (1 + s ^ 3)) * (1 - s ^ 3 / (1 + s ^ 3)) := by
  have hR : s + t ≠ 0 := (add_pos hs ht).ne'
  have hU : 1 + s ^ 3 ≠ 0 := by positivity
  field_simp
  ring

/-- Under a contact, the variance over `Y` of the row-one posterior `q(1,y)/colMass q y` is
`κ r (1 - r)`, with `r` the contact's row-one mass and `κ = st/(s+t)²`. -/
theorem rowTwoContact_variance {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    (hqr : q ≠ r) {s t : ℝ} (hs : RowCubeParam q s) (ht : RowCubeParam r t) :
    ∑ y, colMass q y * (q (1, y) / colMass q y) ^ 2 - rowMass q 1 ^ 2 =
      s * t / (s + t) ^ 2 * rowMass q 1 * (1 - rowMass q 1) := by
  obtain ⟨-, -, hE, hD⟩ := rowTwoContact_moments hw hq hr hqr hs ht
  rw [rowContact_posterior_sq_sum hw hq hs, hs.2.2, hE, hD]
  exact aux_variance_identity hs.1 ht.1

/-! ## The oriented presentation -/

/-- Swapping the two `Bit` labels exchanges the two preimages. -/
private theorem aux_swap_symm {ι : Type*} (e : ι ≃ Bit) :
    (e.trans (Equiv.swap (0 : Bit) 1)).symm 0 = e.symm 1 ∧
      (e.trans (Equiv.swap (0 : Bit) 1)).symm 1 = e.symm 0 := by
  constructor <;> simp [Equiv.symm_swap]

omit [DecidableEq Y] in
/-- The prior of a `Bit`-relabelled latent sums to one over the two labels. -/
theorem bitLatent_prior_sum {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit) :
    V.prior (e.symm 0) + V.prior (e.symm 1) = 1 := by
  have h : ∑ v, V.prior v = 1 := by
    simpa [stoch_to_det.mass] using V.prior_isPMF.total
  rw [← Equiv.sum_comp e.symm, Fin.sum_univ_two] at h
  exact h

omit [DecidableEq Y] in
/-- The cellwise mixture of a `Bit`-relabelled latent. -/
theorem bitLatent_mixture {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit) (z : Bit × Y) :
    p z = V.prior (e.symm 0) * V.comp (e.symm 0) z + V.prior (e.symm 1) * V.comp (e.symm 1) z := by
  rw [← V.mixture z, ← Equiv.sum_comp e.symm, Fin.sum_univ_two]

/-- The presentation, once the labels are ordered by row parameter. -/
private theorem aux_presentation_of_lt {p : Bit × Y → ℝ} {w : Bit × Y → ℝ} (V : Latent p)
    (e : V.ι ≃ Bit) {s t : ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hscore : V.score = tau p) (hprior : ∀ v, 0 < V.prior v)
    (hc : ∀ v, IsContact (univ : Finset (Bit × Y)) w (V.comp v)) (hs0 : 0 < s) (hst : s < t)
    (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t) :
    ∃ (w : Bit × Y → ℝ) (V : Latent p) (e : V.ι ≃ Bit) (s t : ℝ),
      Feasible (univ : Finset (Bit × Y)) w ∧ V.score = tau p ∧ (∀ v, 0 < V.prior v) ∧
      IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)) ∧
      IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)) ∧
      0 < s ∧ s < t ∧
      RowCubeParam (V.comp (e.symm 0)) s ∧ RowCubeParam (V.comp (e.symm 1)) t ∧
      V.prior (e.symm 0) + V.prior (e.symm 1) = 1 ∧
      ∀ z, p z = V.prior (e.symm 0) * V.comp (e.symm 0) z
        + V.prior (e.symm 1) * V.comp (e.symm 1) z :=
  ⟨w, V, e, s, t, hw, hscore, hprior, hc _, hc _, hs0, hst, hs, ht, bitLatent_prior_sum V e,
    bitLatent_mixture V e⟩

/-- A full-support law on `Bit × Y` whose stochastic optimum is below `I(X;Y)` is the mixture
of two contacts of one feasible kernel, labelled so that the row parameters satisfy
`0 < s < t`. -/
theorem rowTwoContact_presentation {p : Bit × Y → ℝ} (hp : IsPMF p) (hpos : ∀ z, 0 < p z)
    (hne : tau p ≠ mutualInfo (fun z : Bit × Y => z.1) (fun z : Bit × Y => z.2) p) :
    ∃ (w : Bit × Y → ℝ) (V : Latent p) (e : V.ι ≃ Bit) (s t : ℝ),
      Feasible (univ : Finset (Bit × Y)) w ∧ V.score = tau p ∧ (∀ v, 0 < V.prior v) ∧
      IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)) ∧
      IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)) ∧
      0 < s ∧ s < t ∧
      RowCubeParam (V.comp (e.symm 0)) s ∧ RowCubeParam (V.comp (e.symm 1)) t ∧
      V.prior (e.symm 0) + V.prior (e.symm 1) = 1 ∧
      ∀ z, p z = V.prior (e.symm 0) * V.comp (e.symm 0) z
        + V.prior (e.symm 1) * V.comp (e.symm 1) z := by
  rcases rowOptimizer_dichotomy hp hpos with h | ⟨w, V, e, hw, hscore, hprior, hc, hne01⟩
  · exact absurd h hne
  obtain ⟨x0, hx0⟩ := rowContact_hasCubeParam hw (hc (e.symm 0))
  obtain ⟨x1, hx1⟩ := rowContact_hasCubeParam hw (hc (e.symm 1))
  rcases lt_or_gt_of_ne (rowContact_param_ne hw (hc _) (hc _) hne01 hx0 hx1) with hlt | hgt
  · exact aux_presentation_of_lt V e hw hscore hprior hc hx0.1 hlt hx0 hx1
  · obtain ⟨h0, h1⟩ := aux_swap_symm e
    refine aux_presentation_of_lt V (e.trans (Equiv.swap (0 : Bit) 1)) hw hscore hprior hc
      hx1.1 hgt ?_ ?_
    · rw [h0]; exact hx1
    · rw [h1]; exact hx0

end

end BinaryRow

end StochasticToDeterministicLatents
