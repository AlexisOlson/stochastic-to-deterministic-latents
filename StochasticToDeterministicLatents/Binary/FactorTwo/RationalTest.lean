import StochasticToDeterministicLatents.Binary.FactorTwo.Touch

/-!
# The rational test at a contact and at a constant optimum

`PositivityGate` is a sign condition on four rational expressions in the cells.
This module verifies it in the two places the factor-two argument needs it: at
the upper contact of a law whose cubic has the root `u`, and at a law that is
already at a constant optimum.

Both verifications are rational.  Clearing the denominators turns the three gate
quantities into polynomials in the four cells; the gate inequality then becomes
a polynomial statement, and at a contact it collapses to an equality.  Every
step is either a `ring` identity in named indeterminates or a positivity
argument from the cells, so the whole test is elementary.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

/-! ## Polynomial identities

Each of these is a `ring` identity in indeterminates.  They are the algebraic
content of the test, isolated from the probabilistic reading of the cells.
-/

/-- The cubic at two points, cross-multiplied by the squares of the other.
This is what compares the top root with the geometric mean of the diagonal. -/
theorem cubic_cross_difference (p : RealTable) (t u : ℝ) :
    u ^ 2 * cubic p t - t ^ 2 * cubic p u
      = (t - u) * (u ^ 2 * t ^ 2 + offDiagonalProduct p * u * t
        + offDiagonalProduct p * diagonalMass p * (t + u)) := by
  simp only [cubic]
  ring

private theorem diagonalGap_factor (a d u : ℝ) :
    (a + d - 2 * u) * (a + d + 2 * u) = (a - d) ^ 2 + 4 * (a * d - u ^ 2) := by
  ring

private theorem balance_eq_cubic (a b c d u : ℝ) :
    a * d * (b + c) + b * c * (a + d) - u * (a * d - b * c)
      = -(u ^ 3 - (b + c) * u ^ 2 - b * c * u - b * c * (a + d))
        + (b + c - u) * (a * d - u ^ 2) := by
  ring

private theorem crossProduct_expand (a b c d u : ℝ) :
    (a + b) * (c + d) * (a + c) * (b + d) - 3 * (a * d - b * c) ^ 2
      = (a + d - 2 * u) * (a * d * (b + c) + b * c * (a + d))
        + (b + c) * (a * d * (b + c) + b * c * (a + d))
        + 2 * u * (a * d * (b + c) + b * c * (a + d) - u * (a * d - b * c))
        + 2 * (b * c) * (a * d - b * c)
        - 2 * (a * d - b * c) * (a * d - u ^ 2) := by
  ring

private theorem balanceSquare_split (a b c d u : ℝ) :
    (a * d * (b + c) + b * c * (a + d)) ^ 2 - a * d * (a * d - b * c) ^ 2
      = (a * d * (b + c) + b * c * (a + d) - u * (a * d - b * c))
          * (a * d * (b + c) + b * c * (a + d) + u * (a * d - b * c))
        - (a * d - u ^ 2) * (a * d - b * c) ^ 2 := by
  ring

private theorem balanceSquare_shift (a b c d : ℝ) :
    (a * d * (b + c) + b * c * (a + d)) ^ 2 - b * c * (a * d - b * c) ^ 2
      = ((a * d * (b + c) + b * c * (a + d)) ^ 2 - a * d * (a * d - b * c) ^ 2)
        + (a * d - b * c) ^ 3 := by
  ring

private theorem gateNumerator_sum (a b c d : ℝ) :
    ((a + c) ^ 2 * ((a + b) * (c + d)) ^ 2
        - (a + b + c + d) * (a ^ 3 * (c + d) ^ 2 + c ^ 3 * (a + b) ^ 2))
      + ((b + d) ^ 2 * ((a + b) * (c + d)) ^ 2
        - (a + b + c + d) * (b ^ 3 * (c + d) ^ 2 + d ^ 3 * (a + b) ^ 2))
      = ((a + b) * (c + d))
        * ((a + b) * (c + d) * (a + c) * (b + d) - 3 * (a * d - b * c) ^ 2) := by
  ring

private theorem gateNumerator_product (a b c d : ℝ) :
    ((a + c) ^ 2 * ((a + b) * (c + d)) ^ 2
        - (a + b + c + d) * (a ^ 3 * (c + d) ^ 2 + c ^ 3 * (a + b) ^ 2))
      * ((b + d) ^ 2 * ((a + b) * (c + d)) ^ 2
        - (a + b + c + d) * (b ^ 3 * (c + d) ^ 2 + d ^ 3 * (a + b) ^ 2))
      * ((a + c) * (b + d))
      = (a * d - b * c) ^ 6 * ((a + b) * (c + d))
        + (a + b + c + d) ^ 2
          * ((a * d * (b + c) + b * c * (a + d)) ^ 2 - a * d * (a * d - b * c) ^ 2)
          * ((a * d * (b + c) + b * c * (a + d)) ^ 2
            - b * c * (a * d - b * c) ^ 2) := by
  ring

/-! ## Sign lemmas -/

private theorem balance_pos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) : 0 < a * d * (b + c) + b * c * (a + d) := by positivity

private theorem two_mul_le_add {a d u : ℝ} (ha : 0 < a) (hd : 0 < d) (hu : 0 < u)
    (hsq : u ^ 2 = a * d) : 2 * u ≤ a + d := by
  nlinarith [sq_nonneg (a - d), diagonalGap_factor a d u]

/-- The cross product of the four marginal sums beats three times the squared
determinant, whenever the balance is nonnegative at a square root of the
diagonal product. -/
private theorem crossProduct_gt {a b c d u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hu : 0 < u) (hsq : u ^ 2 = a * d)
    (hdet : 0 ≤ a * d - b * c)
    (hbal : 0 ≤ a * d * (b + c) + b * c * (a + d) - u * (a * d - b * c)) :
    0 < (a + b) * (c + d) * (a + c) * (b + d) - 3 * (a * d - b * c) ^ 2 := by
  have hL := balance_pos ha hb hc hd
  have hs := two_mul_le_add ha hd hu hsq
  have hv : 0 < b + c := add_pos hb hc
  have hY : 0 < b * c := mul_pos hb hc
  have hi := crossProduct_expand a b c d u
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hL.le, mul_pos hv hL,
    mul_nonneg (by positivity : (0:ℝ) ≤ 2 * u) hbal,
    mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (b * c)) hdet]

private theorem nonneg_of_sum_prod {x y : ℝ} (hsum : 0 < x + y)
    (hprod : 0 ≤ x * y) : 0 ≤ x ∧ 0 ≤ y := by
  constructor <;> by_contra h <;> push Not at h <;> nlinarith

private theorem pos_of_sum_prod {x y : ℝ} (hsum : 0 < x + y) (hprod : 0 < x * y) :
    0 < x ∧ 0 < y := by
  constructor <;> by_contra h <;> push Not at h <;> nlinarith

/-! ## The gate quantities with denominators cleared -/

private theorem gateA_normalized {q : RealTable} (hq : IsPMF q)
    (hpos : FullSupport q) :
    ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 2 * gateA q
      = (q (0, 0) + q (1, 0)) ^ 2
          * ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 2
        - (q (0, 0) + q (0, 1) + q (1, 0) + q (1, 1))
          * (q (0, 0) ^ 3 * (q (1, 0) + q (1, 1)) ^ 2
            + q (1, 0) ^ 3 * (q (0, 0) + q (0, 1)) ^ 2) := by
  have hx0 : q (0, 0) + q (0, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have hx1 : q (1, 0) + q (1, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have ht := hq.total
  rw [stoch_to_det.mass, sum_cells] at ht
  rw [gateA, marginalX_zero, marginalX_one, marginalY_zero]
  field_simp
  rw [ht]
  ring

private theorem gateE_normalized {q : RealTable} (hq : IsPMF q)
    (hpos : FullSupport q) :
    ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 2 * gateE q
      = (q (0, 1) + q (1, 1)) ^ 2
          * ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 2
        - (q (0, 0) + q (0, 1) + q (1, 0) + q (1, 1))
          * (q (0, 1) ^ 3 * (q (1, 0) + q (1, 1)) ^ 2
            + q (1, 1) ^ 3 * (q (0, 0) + q (0, 1)) ^ 2) := by
  have hx0 : q (0, 0) + q (0, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have hx1 : q (1, 0) + q (1, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have ht := hq.total
  rw [stoch_to_det.mass, sum_cells] at ht
  rw [gateE, marginalX_zero, marginalX_one, marginalY_one]
  field_simp
  rw [ht]
  ring

private theorem gateV_normalized {q : RealTable} (hpos : FullSupport q) :
    ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) * gateV q
      = (q (0, 0) * q (1, 1) - q (0, 1) * q (1, 0)) ^ 2 := by
  have hR : (q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1)) ≠ 0 :=
    (mul_pos (add_pos (hpos _) (hpos _)) (add_pos (hpos _) (hpos _))).ne'
  rw [gateV, determinant_eq, entryA, entryB, entryC, entryD,
    marginalX_zero, marginalX_one, mul_comm]
  exact div_mul_cancel₀ _ hR

private theorem gateM_normalized (q : RealTable) :
    gateM q = (q (0, 0) + q (1, 0)) * (q (0, 1) + q (1, 1)) := by
  rw [gateM, marginalY_zero, marginalY_one]

/-! ## The gate gap as a product of two balance forms -/

private theorem gateGap_normalized {q : RealTable} (hq : IsPMF q)
    (hpos : FullSupport q) :
    ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 4
        * (gateA q * gateE q * gateM q - gateV q ^ 3)
      = ((q (0, 0) * q (1, 1) * (q (0, 1) + q (1, 0))
            + q (0, 1) * q (1, 0) * (q (0, 0) + q (1, 1))) ^ 2
          - q (0, 0) * q (1, 1) * (q (0, 0) * q (1, 1) - q (0, 1) * q (1, 0)) ^ 2)
        * ((q (0, 0) * q (1, 1) * (q (0, 1) + q (1, 0))
            + q (0, 1) * q (1, 0) * (q (0, 0) + q (1, 1))) ^ 2
          - q (0, 1) * q (1, 0)
            * (q (0, 0) * q (1, 1) - q (0, 1) * q (1, 0)) ^ 2) := by
  have hA := gateA_normalized hq hpos
  have hE := gateE_normalized hq hpos
  have hV := gateV_normalized (q := q) hpos
  have hM := gateM_normalized q
  have hz := hq.total
  rw [stoch_to_det.mass, sum_cells] at hz
  simp only [hz, one_mul] at hA hE
  have h8 := gateNumerator_product (q (0, 0)) (q (0, 1)) (q (1, 0)) (q (1, 1))
  simp only [hz, one_pow, one_mul] at h8
  calc ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 4
        * (gateA q * gateE q * gateM q - gateV q ^ 3)
      = ((((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 2 * gateA q)
          * (((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) ^ 2 * gateE q)
          * gateM q)
        - ((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1)))
          * ((((q (0, 0) + q (0, 1)) * (q (1, 0) + q (1, 1))) * gateV q) ^ 3) := by
        ring
    _ = _ := by rw [hA, hE, hV, hM]; linear_combination h8

/-! ## The contact relations -/

variable {p : RealTable} {u : ℝ}

private theorem contactCell_mul (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) :
    upperContactCell p u * lowerContactCell p u = u ^ 2 := by
  have hr := contactRadius_sq hpos hu hnc
  rw [upperContactCell, lowerContactCell]
  nlinarith

/-- At a root of the cubic the balance form vanishes at the contact. -/
private theorem contactBalance_zero (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    upperContactCell p u * lowerContactCell p u * (entryB p + entryC p)
        + entryB p * entryC p * (upperContactCell p u + lowerContactCell p u)
        - u * (upperContactCell p u * lowerContactCell p u
          - entryB p * entryC p) = 0 := by
  have had := contactCell_mul hpos hu hnc
  have hs : upperContactCell p u + lowerContactCell p u = diagonalMass p := by
    rw [upperContactCell, lowerContactCell]; ring
  rw [cubic, offDiagonalMass, offDiagonalProduct_eq] at hroot
  rw [had, hs]
  nlinarith

/-- At a root of the cubic the product of the two diagonal contact cells
exceeds the off-diagonal product. -/
theorem contactCell_mul_gt_offDiagonalProduct (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    0 < upperContactCell p u * lowerContactCell p u - entryB p * entryC p := by
  have hcell := cell_pos hpos
  have hA := upperContactCell_pos hpos hu hnc
  have hD := lowerContactCell_pos hpos hu hnc
  have hL := balance_pos hA hcell.2.1 hcell.2.2.1 hD
  have he := contactBalance_zero hpos hu hnc hroot
  nlinarith

private theorem contactCrossProduct_pos (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    0 < (upperContactCell p u + entryB p) * (entryC p + lowerContactCell p u)
        * (upperContactCell p u + entryC p) * (entryB p + lowerContactCell p u)
      - 3 * (upperContactCell p u * lowerContactCell p u
        - entryB p * entryC p) ^ 2 := by
  have hcell := cell_pos hpos
  have hA := upperContactCell_pos hpos hu hnc
  have hD := lowerContactCell_pos hpos hu hnc
  exact crossProduct_gt hA hcell.2.1 hcell.2.2.1 hD hu
    (contactCell_mul hpos hu hnc).symm
    (contactCell_mul_gt_offDiagonalProduct hpos hu hnc hroot).le
    (contactBalance_zero hpos hu hnc hroot).ge

/-- The first balance form vanishes at a contact.  This is what makes the gate
inequality an equality there. -/
private theorem contactBalanceSquare_zero (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    (upperContactCell p u * lowerContactCell p u * (entryB p + entryC p)
        + entryB p * entryC p
          * (upperContactCell p u + lowerContactCell p u)) ^ 2
      - upperContactCell p u * lowerContactCell p u
        * (upperContactCell p u * lowerContactCell p u
          - entryB p * entryC p) ^ 2 = 0 := by
  have hi := balanceSquare_split (upperContactCell p u) (entryB p) (entryC p)
    (lowerContactCell p u) u
  have he := contactBalance_zero hpos hu hnc hroot
  have had := contactCell_mul hpos hu hnc
  rw [he, zero_mul, had, sub_self, zero_mul, sub_zero] at hi
  simpa [had] using hi

/-! ## The gate at a contact -/

private theorem contactAt_zero_one (p : RealTable) (u : ℝ) :
    contactAt p u (0, 1) = entryB p := by simp [contactAt, entryB]

private theorem contactAt_one_zero (p : RealTable) (u : ℝ) :
    contactAt p u (1, 0) = entryC p := by simp [contactAt, entryC]

private theorem contactAt_total (hp : IsPMF p) (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) :
    upperContactCell p u + entryB p + entryC p + lowerContactCell p u = 1 := by
  have ht := (isPMF_contactAt hp hpos hu hnc).total
  rw [stoch_to_det.mass, sum_cells] at ht
  rw [contactAt_apply_zero, contactAt_zero_one, contactAt_one_zero,
    contactAt_apply_one] at ht
  exact ht

private theorem gate_contactAt_pos (hp : IsPMF p) (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    0 < gateA (contactAt p u) ∧ 0 < gateE (contactAt p u) := by
  have hq := isPMF_contactAt hp hpos hu hnc
  have hqp : FullSupport (contactAt p u) := contactAt_pos hpos hu hnc
  have hcell := cell_pos hpos
  have hApos := upperContactCell_pos hpos hu hnc
  have hDpos := lowerContactCell_pos hpos hu hnc
  have hz := contactAt_total hp hpos hu hnc
  set A := upperContactCell p u with hA
  set D := lowerContactCell p u with hD
  set b := entryB p with hb
  set c := entryC p with hc
  have hbpos : 0 < b := hcell.2.1
  have hcpos : 0 < c := hcell.2.2.1
  have hR : 0 < (A + b) * (c + D) := mul_pos (add_pos hApos hbpos) (add_pos hcpos hDpos)
  have hC : 0 < (A + c) * (b + D) := mul_pos (add_pos hApos hcpos) (add_pos hbpos hDpos)
  have hdelta : 0 < A * D - b * c :=
    contactCell_mul_gt_offDiagonalProduct hpos hu hnc hroot
  have hcross : 0 < (A + b) * (c + D) * (A + c) * (b + D) - 3 * (A * D - b * c) ^ 2 :=
    contactCrossProduct_pos hpos hu hnc hroot
  have hfx : (A * D * (b + c) + b * c * (A + D)) ^ 2
      - A * D * (A * D - b * c) ^ 2 = 0 :=
    contactBalanceSquare_zero hpos hu hnc hroot
  have hAeq := gateA_normalized hq hqp
  have hEeq := gateE_normalized hq hqp
  rw [contactAt_apply_zero, contactAt_zero_one, contactAt_one_zero,
    contactAt_apply_one, hz] at hAeq hEeq
  have hsum : 0 < ((A + c) ^ 2 * ((A + b) * (c + D)) ^ 2
        - 1 * (A ^ 3 * (c + D) ^ 2 + c ^ 3 * (A + b) ^ 2))
      + ((b + D) ^ 2 * ((A + b) * (c + D)) ^ 2
        - 1 * (b ^ 3 * (c + D) ^ 2 + D ^ 3 * (A + b) ^ 2)) := by
    have hi := gateNumerator_sum A b c D
    rw [hz] at hi
    rw [hi]
    exact mul_pos hR (by linarith [hcross])
  have hprod : 0 < ((A + c) ^ 2 * ((A + b) * (c + D)) ^ 2
        - 1 * (A ^ 3 * (c + D) ^ 2 + c ^ 3 * (A + b) ^ 2))
      * ((b + D) ^ 2 * ((A + b) * (c + D)) ^ 2
        - 1 * (b ^ 3 * (c + D) ^ 2 + D ^ 3 * (A + b) ^ 2)) := by
    have hi := gateNumerator_product A b c D
    rw [hz, hfx] at hi
    have hpos' : 0 < (A * D - b * c) ^ 6 * ((A + b) * (c + D)) :=
      mul_pos (pow_pos hdelta 6) hR
    have hmul : 0 < (((A + c) ^ 2 * ((A + b) * (c + D)) ^ 2
          - 1 * (A ^ 3 * (c + D) ^ 2 + c ^ 3 * (A + b) ^ 2))
        * ((b + D) ^ 2 * ((A + b) * (c + D)) ^ 2
          - 1 * (b ^ 3 * (c + D) ^ 2 + D ^ 3 * (A + b) ^ 2)))
        * ((A + c) * (b + D)) := by
      rw [hi]; linarith
    exact pos_of_mul_pos_right (by simpa [mul_comm] using hmul) hC.le
  have hsigns := pos_of_sum_prod hsum hprod
  constructor
  · exact pos_of_mul_pos_right
      (by simpa [mul_comm] using
        (show 0 < ((A + b) * (c + D)) ^ 2 * gateA (contactAt p u) by
          rw [hAeq]; exact hsigns.1))
      (sq_nonneg ((A + b) * (c + D)))
  · exact pos_of_mul_pos_right
      (by simpa [mul_comm] using
        (show 0 < ((A + b) * (c + D)) ^ 2 * gateE (contactAt p u) by
          rw [hEeq]; exact hsigns.2))
      (sq_nonneg ((A + b) * (c + D)))

private theorem gate_contactAt_eq (hp : IsPMF p) (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    gateV (contactAt p u) ^ 3
      = gateA (contactAt p u) * gateE (contactAt p u) * gateM (contactAt p u) := by
  have hq := isPMF_contactAt hp hpos hu hnc
  have hqp : FullSupport (contactAt p u) := contactAt_pos hpos hu hnc
  have hApos := upperContactCell_pos hpos hu hnc
  have hDpos := lowerContactCell_pos hpos hu hnc
  have hcell := cell_pos hpos
  have hgap := gateGap_normalized hq hqp
  rw [contactAt_apply_zero, contactAt_zero_one, contactAt_one_zero,
    contactAt_apply_one] at hgap
  have hfx := contactBalanceSquare_zero hpos hu hnc hroot
  rw [hfx, zero_mul] at hgap
  have hR : 0 < ((upperContactCell p u + entryB p)
      * (entryC p + lowerContactCell p u)) ^ 4 :=
    pow_pos (mul_pos (add_pos hApos hcell.2.1)
      (add_pos hcell.2.2.1 hDpos)) 4
  have hzero : gateA (contactAt p u) * gateE (contactAt p u) * gateM (contactAt p u)
      - gateV (contactAt p u) ^ 3 = 0 := (mul_eq_zero.mp hgap).resolve_left hR.ne'
  linarith

/-- The positivity gate holds at the upper contact of a law whose cubic has the
root `u`.  With `majorizes_tangentCert_of_normBound` and the reduction of the
gate this is the certificate side of the contact bound. -/
theorem positivityGate_contactAt (hp : IsPMF p) (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    PositivityGate (contactAt p u) :=
  ⟨(gate_contactAt_pos hp hpos hu hnc hroot).1.le,
    (gate_contactAt_pos hp hpos hu hnc hroot).2.le,
    le_of_eq (gate_contactAt_eq hp hpos hu hnc hroot)⟩

/-! ## The gate at a constant optimum

When the top root reaches the geometric mean of the diagonal the optimum is
constant, and the gate has to be checked at `p` itself.  The balance form is now
only nonnegative rather than zero, so the gate inequality is strict no longer,
but the same two polynomial identities carry it.
-/

private theorem sqrtDiagonalProduct_pos (hpos : FullSupport p) :
    0 < √(diagonalProduct p) := by
  rw [diagonalProduct_eq]
  exact Real.sqrt_pos.2 (mul_pos (hpos (0, 0)) (hpos (1, 1)))

private theorem sqrtDiagonalProduct_sq (hpos : FullSupport p) :
    √(diagonalProduct p) ^ 2 = entryA p * entryD p := by
  rw [diagonalProduct_eq]
  exact Real.sq_sqrt (mul_nonneg (hpos (0, 0)).le (hpos (1, 1)).le)

private theorem topRoot_pos (hpos : FullSupport p) (htop : IsTopRoot p u) :
    0 < u := by
  refine lt_of_le_of_ne htop.1 ?_
  intro hu
  subst hu
  have hzero := htop.2.1
  rw [cubic_zero] at hzero
  have hcell := cell_pos hpos
  have hw : 0 < offDiagonalProduct p * diagonalMass p := by
    rw [offDiagonalProduct_eq, diagonalMass]
    exact mul_pos (mul_pos hcell.2.1 hcell.2.2.1) (add_pos hcell.1 hcell.2.2.2)
  linarith

private theorem cubic_expand (p : RealTable) (t : ℝ) :
    cubic p t = t ^ 3 - (entryB p + entryC p) * t ^ 2 - entryB p * entryC p * t
      - entryB p * entryC p * (entryA p + entryD p) := by
  rw [cubic, offDiagonalMass, offDiagonalProduct_eq, diagonalMass]

/-- Below the top root the cubic is nonpositive, in particular at the geometric
mean of the diagonal when the optimum is constant. -/
private theorem cubic_sqrtDiagonalProduct_nonpos (hpos : FullSupport p)
    (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    cubic p (√(diagonalProduct p)) ≤ 0 := by
  have hcell := cell_pos hpos
  have hs := sqrtDiagonalProduct_pos hpos
  have hu := topRoot_pos hpos htop
  have hle : √(diagonalProduct p) ≤ u := not_lt.mp (by rwa [Nonconstant] at hnc)
  have h9 := cubic_cross_difference p u (√(diagonalProduct p))
  have hf0 : cubic p u = 0 := htop.2.1
  have hbr : 0 < √(diagonalProduct p) ^ 2 * u ^ 2
      + offDiagonalProduct p * √(diagonalProduct p) * u
      + offDiagonalProduct p * diagonalMass p * (u + √(diagonalProduct p)) := by
    have hw : 0 < offDiagonalProduct p := by
      rw [offDiagonalProduct_eq]; exact mul_pos hcell.2.1 hcell.2.2.1
    have hm : 0 < diagonalMass p := by
      rw [diagonalMass]; exact add_pos hcell.1 hcell.2.2.2
    have h1 : 0 < √(diagonalProduct p) ^ 2 * u ^ 2 :=
      mul_pos (pow_pos hs 2) (pow_pos hu 2)
    have h2 : 0 < offDiagonalProduct p * √(diagonalProduct p) * u :=
      mul_pos (mul_pos hw hs) hu
    have h3 : 0 < offDiagonalProduct p * diagonalMass p * (u + √(diagonalProduct p)) :=
      mul_pos (mul_pos hw hm) (add_pos hu hs)
    linarith
  have hmul : 0 ≤ (u - √(diagonalProduct p))
      * (√(diagonalProduct p) ^ 2 * u ^ 2
        + offDiagonalProduct p * √(diagonalProduct p) * u
        + offDiagonalProduct p * diagonalMass p * (u + √(diagonalProduct p))) :=
    mul_nonneg (sub_nonneg.2 hle) hbr.le
  rw [hf0, mul_zero, zero_sub] at h9
  nlinarith [h9, hmul, pow_pos hu 2]

private theorem balance_nonneg (hpos : FullSupport p) (htop : IsTopRoot p u)
    (hnc : ¬ Nonconstant p u) :
    0 ≤ entryA p * entryD p * (entryB p + entryC p)
      + entryB p * entryC p * (entryA p + entryD p)
      - √(diagonalProduct p) * (entryA p * entryD p - entryB p * entryC p) := by
  have hi := balance_eq_cubic (entryA p) (entryB p) (entryC p) (entryD p)
    (√(diagonalProduct p))
  have hs := sqrtDiagonalProduct_sq hpos
  have hf := cubic_sqrtDiagonalProduct_nonpos hpos htop hnc
  rw [cubic_expand] at hf
  rw [hs] at hi hf
  nlinarith [hi, hf]

private theorem crossProduct_pos_self (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    0 < (entryA p + entryB p) * (entryC p + entryD p)
        * (entryA p + entryC p) * (entryB p + entryD p)
      - 3 * (entryA p * entryD p - entryB p * entryC p) ^ 2 := by
  have hcell := cell_pos hpos
  have hdet' : 0 ≤ entryA p * entryD p - entryB p * entryC p := by
    rwa [determinant, diagonalProduct_eq, offDiagonalProduct_eq] at hdet
  exact crossProduct_gt hcell.1 hcell.2.1 hcell.2.2.1 hcell.2.2.2
    (sqrtDiagonalProduct_pos hpos) (sqrtDiagonalProduct_sq hpos) hdet'
    (balance_nonneg hpos htop hnc)

private theorem balanceSquare_nonneg (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    0 ≤ (entryA p * entryD p * (entryB p + entryC p)
        + entryB p * entryC p * (entryA p + entryD p)) ^ 2
      - entryA p * entryD p * (entryA p * entryD p - entryB p * entryC p) ^ 2 := by
  have hcell := cell_pos hpos
  have hi := balanceSquare_split (entryA p) (entryB p) (entryC p) (entryD p)
    (√(diagonalProduct p))
  have he := balance_nonneg hpos htop hnc
  have hs := sqrtDiagonalProduct_sq hpos
  have hL := balance_pos hcell.1 hcell.2.1 hcell.2.2.1 hcell.2.2.2
  have hdet' : 0 ≤ entryA p * entryD p - entryB p * entryC p := by
    rwa [determinant, diagonalProduct_eq, offDiagonalProduct_eq] at hdet
  have hsum : 0 ≤ entryA p * entryD p * (entryB p + entryC p)
      + entryB p * entryC p * (entryA p + entryD p)
      + √(diagonalProduct p) * (entryA p * entryD p - entryB p * entryC p) :=
    add_nonneg hL.le (mul_nonneg (sqrtDiagonalProduct_pos hpos).le hdet')
  rw [hs] at hi
  nlinarith [hi, hsum, he]

private theorem balanceSquare_shift_nonneg (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    0 ≤ (entryA p * entryD p * (entryB p + entryC p)
        + entryB p * entryC p * (entryA p + entryD p)) ^ 2
      - entryB p * entryC p * (entryA p * entryD p - entryB p * entryC p) ^ 2 := by
  have hi := balanceSquare_shift (entryA p) (entryB p) (entryC p) (entryD p)
  have hx := balanceSquare_nonneg hpos hdet htop hnc
  have hdet' : 0 ≤ entryA p * entryD p - entryB p * entryC p := by
    rwa [determinant, diagonalProduct_eq, offDiagonalProduct_eq] at hdet
  nlinarith [pow_nonneg hdet' 3]

private theorem gateSum_pos_self (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    0 < ((entryA p + entryC p) ^ 2
          * ((entryA p + entryB p) * (entryC p + entryD p)) ^ 2
        - (entryA p + entryB p + entryC p + entryD p)
          * (entryA p ^ 3 * (entryC p + entryD p) ^ 2
            + entryC p ^ 3 * (entryA p + entryB p) ^ 2))
      + ((entryB p + entryD p) ^ 2
          * ((entryA p + entryB p) * (entryC p + entryD p)) ^ 2
        - (entryA p + entryB p + entryC p + entryD p)
          * (entryB p ^ 3 * (entryC p + entryD p) ^ 2
            + entryD p ^ 3 * (entryA p + entryB p) ^ 2)) := by
  have hcell := cell_pos hpos
  have hi := gateNumerator_sum (entryA p) (entryB p) (entryC p) (entryD p)
  rw [hi]
  exact mul_pos (mul_pos (add_pos hcell.1 hcell.2.1)
      (add_pos hcell.2.2.1 hcell.2.2.2))
    (crossProduct_pos_self hpos hdet htop hnc)

private theorem gateProduct_nonneg_self (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    0 ≤ ((entryA p + entryC p) ^ 2
          * ((entryA p + entryB p) * (entryC p + entryD p)) ^ 2
        - (entryA p + entryB p + entryC p + entryD p)
          * (entryA p ^ 3 * (entryC p + entryD p) ^ 2
            + entryC p ^ 3 * (entryA p + entryB p) ^ 2))
      * ((entryB p + entryD p) ^ 2
          * ((entryA p + entryB p) * (entryC p + entryD p)) ^ 2
        - (entryA p + entryB p + entryC p + entryD p)
          * (entryB p ^ 3 * (entryC p + entryD p) ^ 2
            + entryD p ^ 3 * (entryA p + entryB p) ^ 2)) := by
  obtain ⟨ha, hb, hc, hd⟩ := cell_pos hpos
  have hi := gateNumerator_product (entryA p) (entryB p) (entryC p) (entryD p)
  have hC : 0 < (entryA p + entryC p) * (entryB p + entryD p) :=
    mul_pos (add_pos ha hc) (add_pos hb hd)
  have hrhs : 0 ≤ (entryA p * entryD p - entryB p * entryC p) ^ 6
      * ((entryA p + entryB p) * (entryC p + entryD p))
      + (entryA p + entryB p + entryC p + entryD p) ^ 2
        * ((entryA p * entryD p * (entryB p + entryC p)
            + entryB p * entryC p * (entryA p + entryD p)) ^ 2
          - entryA p * entryD p
            * (entryA p * entryD p - entryB p * entryC p) ^ 2)
        * ((entryA p * entryD p * (entryB p + entryC p)
            + entryB p * entryC p * (entryA p + entryD p)) ^ 2
          - entryB p * entryC p
            * (entryA p * entryD p - entryB p * entryC p) ^ 2) := by
    have h1 := balanceSquare_nonneg hpos hdet htop hnc
    have h2 := balanceSquare_shift_nonneg hpos hdet htop hnc
    positivity
  have hmul : 0 ≤ ((entryA p + entryC p) ^ 2
        * ((entryA p + entryB p) * (entryC p + entryD p)) ^ 2
      - (entryA p + entryB p + entryC p + entryD p)
        * (entryA p ^ 3 * (entryC p + entryD p) ^ 2
          + entryC p ^ 3 * (entryA p + entryB p) ^ 2))
    * ((entryB p + entryD p) ^ 2
        * ((entryA p + entryB p) * (entryC p + entryD p)) ^ 2
      - (entryA p + entryB p + entryC p + entryD p)
        * (entryB p ^ 3 * (entryC p + entryD p) ^ 2
          + entryD p ^ 3 * (entryA p + entryB p) ^ 2))
    * ((entryA p + entryC p) * (entryB p + entryD p)) := by
    rw [hi]; exact hrhs
  exact nonneg_of_mul_nonneg_left hmul hC

private theorem gate_nonneg_self (hp : IsPMF p) (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    0 ≤ gateA p ∧ 0 ≤ gateE p := by
  have hcell := cell_pos hpos
  have hA := gateA_normalized hp hpos
  have hE := gateE_normalized hp hpos
  rw [show p (0, 0) = entryA p from rfl, show p (0, 1) = entryB p from rfl,
    show p (1, 0) = entryC p from rfl, show p (1, 1) = entryD p from rfl] at hA hE
  have hsigns := nonneg_of_sum_prod (gateSum_pos_self hpos hdet htop hnc)
    (gateProduct_nonneg_self hpos hdet htop hnc)
  have hR : 0 < (entryA p + entryB p) * (entryC p + entryD p) :=
    mul_pos (add_pos hcell.1 hcell.2.1) (add_pos hcell.2.2.1 hcell.2.2.2)
  constructor
  · nlinarith [hA, hsigns.1, pow_pos hR 2]
  · nlinarith [hE, hsigns.2, pow_pos hR 2]

private theorem gap_nonneg_self (hp : IsPMF p) (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : ¬ Nonconstant p u) :
    gateV p ^ 3 ≤ gateA p * gateE p * gateM p := by
  have hg := gateGap_normalized hp hpos
  have hprod := mul_nonneg (balanceSquare_nonneg hpos hdet htop hnc)
    (balanceSquare_shift_nonneg hpos hdet htop hnc)
  have hR : 0 < ((p (0, 0) + p (0, 1)) * (p (1, 0) + p (1, 1))) ^ 4 :=
    pow_pos (mul_pos (add_pos (hpos _) (hpos _)) (add_pos (hpos _) (hpos _))) 4
  have hrhs : 0 ≤ ((p (0, 0) * p (1, 1) * (p (0, 1) + p (1, 0))
        + p (0, 1) * p (1, 0) * (p (0, 0) + p (1, 1))) ^ 2
      - p (0, 0) * p (1, 1) * (p (0, 0) * p (1, 1) - p (0, 1) * p (1, 0)) ^ 2)
    * ((p (0, 0) * p (1, 1) * (p (0, 1) + p (1, 0))
        + p (0, 1) * p (1, 0) * (p (0, 0) + p (1, 1))) ^ 2
      - p (0, 1) * p (1, 0)
        * (p (0, 0) * p (1, 1) - p (0, 1) * p (1, 0)) ^ 2) := hprod
  have hdiff : 0 ≤ gateA p * gateE p * gateM p - gateV p ^ 3 := by
    nlinarith [hg, hrhs, hR]
  linarith

/-- The positivity gate holds at a law whose top root has reached the geometric
mean of the diagonal, so that the stochastic optimum is constant. -/
theorem positivityGate_of_constant (hp : IsPMF p) (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u)
    (hnc : ¬ Nonconstant p u) : PositivityGate p :=
  ⟨(gate_nonneg_self hp hpos hdet htop hnc).1,
    (gate_nonneg_self hp hpos hdet htop hnc).2,
    gap_nonneg_self hp hpos hdet htop hnc⟩

end StochasticToDeterministicLatents.Binary
