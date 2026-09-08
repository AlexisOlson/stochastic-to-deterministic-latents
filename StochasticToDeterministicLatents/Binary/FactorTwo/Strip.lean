import StochasticToDeterministicLatents.Binary.FactorTwo.Chord
import StochasticToDeterministicLatents.Binary.ContactChart

/-!
# The fixed cut, the root sign test, and the corner information

Three pieces of the factor-two argument that the quantitative estimates need
and the chord modules do not.

* When the off-diagonal mass is small, the smaller contact cell is smaller
  still -- below half the off-diagonal mass -- and so the point
  `fixedCut p u`, which leaves three times that cell below it, lies strictly
  inside the segment.  The first of these is a named target of the contract
  page; the second is what makes a fixed cut available to test a competitor
  at.
* A point where the cubic is already positive lies beyond the top root.  This
  is the converse of the top root's defining property, and it is what turns a
  numerical sign check into a bound on the root.
* `cornerInfo` is the unnormalized mutual information of a law with one zero
  corner, and it is squeezed between two rational functions of the three
  remaining cells.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u t : ℝ}

/-! ## The off-diagonal product against the off-diagonal mass -/

/-- The product of the two off-diagonal cells is at most a quarter of the
square of their sum. -/
theorem offDiagonalProduct_le_sq_div_four (p : RealTable) :
    offDiagonalProduct p ≤ offDiagonalMass p ^ 2 / 4 := by
  rw [offDiagonalProduct_eq, offDiagonalMass]
  nlinarith [sq_nonneg (entryB p - entryC p)]

/-! ## The smaller contact cell under a small off-diagonal mass -/

private theorem cut_poly_neg {v : ℝ} (hv0 : 0 < v) (hv : v ≤ (1 : ℝ) / 8) :
    -2 + 20 * v - 44 * v ^ 2 + 28 * v ^ 3 < 0 := by
  have hmul := mul_nonneg hv0.le (sub_nonneg.mpr hv)
  have hcubic : 28 * v ^ 3 ≤ (7 / 2 : ℝ) * v ^ 2 := by nlinarith
  have hquad : -2 + 20 * v - (81 / 2 : ℝ) * v ^ 2 < 0 := by
    nlinarith [sq_nonneg (v - (1 : ℝ) / 8)]
  nlinarith

private theorem topRoot_sq_lt (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    u ^ 2 < offDiagonalMass p * (2 * diagonalMass p - offDiagonalMass p) / 4 := by
  have hv0 := offDiagonalMass_pos h.fullSupport
  have huv := offDiagonalMass_lt_topRoot h.isPMF h.fullSupport h.topRoot
  have hu0 := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hs0 := diagonalMass_pos h.fullSupport
  have hsum := diagonalMass_add_offDiagonalMass h.isPMF
  have hw := offDiagonalProduct_le_sq_div_four p
  have hcub := h.topRoot.2.1
  rw [cubic] at hcub
  by_contra hn
  rw [not_lt] at hn
  have huvs : 0 < u - offDiagonalMass p := by linarith
  have hus : 0 < u + diagonalMass p := by linarith
  have hcub' : u ^ 2 * (u - offDiagonalMass p)
      = offDiagonalProduct p * (u + diagonalMass p) := by nlinarith
  have hwprod : offDiagonalProduct p * (u + diagonalMass p) ≤
      offDiagonalMass p ^ 2 / 4 * (u + diagonalMass p) :=
    mul_le_mul_of_nonneg_right hw hus.le
  have hKprod :
      offDiagonalMass p * (2 * diagonalMass p - offDiagonalMass p) / 4
            * (u - offDiagonalMass p) ≤
        u ^ 2 * (u - offDiagonalMass p) :=
    mul_le_mul_of_nonneg_right hn huvs.le
  have hlin : (2 * diagonalMass p - offDiagonalMass p) * (u - offDiagonalMass p) ≤
      offDiagonalMass p * (u + diagonalMass p) := by
    nlinarith [mul_pos hv0 hv0]
  have hbound : 2 * (diagonalMass p - offDiagonalMass p) * u ≤
      offDiagonalMass p * (3 * diagonalMass p - offDiagonalMass p) := by nlinarith
  have hsv : 0 < diagonalMass p - offDiagonalMass p := by nlinarith
  have hlhs : 0 ≤ 2 * (diagonalMass p - offDiagonalMass p) * u := by positivity
  have hrhs : 0 ≤ offDiagonalMass p * (3 * diagonalMass p - offDiagonalMass p) := by
    have : 0 < 3 * diagonalMass p - offDiagonalMass p := by nlinarith
    positivity
  have hsq : (2 * (diagonalMass p - offDiagonalMass p) * u) ^ 2 ≤
      (offDiagonalMass p * (3 * diagonalMass p - offDiagonalMass p)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg hlhs hrhs)]
  have hpoly : (2 * diagonalMass p - offDiagonalMass p)
        * (diagonalMass p - offDiagonalMass p) ^ 2 ≤
      offDiagonalMass p * (3 * diagonalMass p - offDiagonalMass p) ^ 2 := by
    nlinarith [mul_pos hv0 hsv, mul_pos hsv hsv]
  nlinarith [cut_poly_neg hv0 hv]

/-- Below an eighth of off-diagonal mass, the smaller cell of the contact pair
is below half that mass. -/
theorem contactMass_lt_half_disagreement (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    chordBottom p u < offDiagonalMass p / 2 := by
  have hsq := topRoot_sq_lt h hv
  have hD0 := chordBottom_pos h
  have hDmid := chordBottom_lt_chordMidpoint h
  have hsum := chordTop_add_chordBottom (p := p) (u := u)
  have hprod := chordTop_mul_chordBottom h
  have hv0 := offDiagonalMass_pos h.fullSupport
  have hone := diagonalMass_add_offDiagonalMass h.isPMF
  have hvsmid : offDiagonalMass p / 2 < chordMidpoint p := by
    rw [chordMidpoint]; linarith
  have hvtop : offDiagonalMass p / 2 < chordTop p u :=
    lt_trans hvsmid (chordMidpoint_lt_chordTop h)
  have hid : (offDiagonalMass p / 2 - chordBottom p u)
        * (offDiagonalMass p / 2 - chordTop p u)
      = offDiagonalMass p ^ 2 / 4 - diagonalMass p * offDiagonalMass p / 2 + u ^ 2 := by
    nlinarith
  have hneg : (offDiagonalMass p / 2 - chordBottom p u)
      * (offDiagonalMass p / 2 - chordTop p u) < 0 := by
    rw [hid]; nlinarith
  by_contra hnD
  rw [not_lt] at hnD
  have hfD : offDiagonalMass p / 2 - chordBottom p u ≤ 0 := by linarith
  have hfA : offDiagonalMass p / 2 - chordTop p u ≤ 0 := (sub_neg.mpr hvtop).le
  linarith [mul_nonneg_of_nonpos_of_nonpos hfD hfA]

/-! ## The fixed cut -/

/-- The point of the diagonal that leaves three times the smaller contact cell
below it. -/
noncomputable def fixedCut (p : RealTable) (u : ℝ) : ℝ :=
  diagonalMass p - 3 * chordBottom p u

/-- Below an eighth of off-diagonal mass the fixed cut is an interior point of
the segment, so a competitor may be tested there. -/
theorem fixedCut_mem_chord (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    fixedCut p u ∈ Set.Ioo (chordMidpoint p) (chordTop p u) := by
  have hD0 := chordBottom_pos h
  have hDv := contactMass_lt_half_disagreement h hv
  have hone := diagonalMass_add_offDiagonalMass h.isPMF
  have htopD := chordTop_add_chordBottom (p := p) (u := u)
  constructor
  · rw [fixedCut, chordMidpoint]; linarith
  · rw [fixedCut]; linarith

/-! ## A positive value of the cubic lies beyond the top root -/

/-- The converse of the top root's defining property: wherever the cubic is
already positive, the top root is below. -/
theorem topRoot_lt_of_cubic_pos (h : ChordDomain p u) (ht : 0 < t)
    (hpos : 0 < cubic p t) : u < t := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hw := offDiagonalProduct_pos h.fullSupport
  have hs := diagonalMass_pos h.fullSupport
  have hid : u ^ 2 * cubic p t - t ^ 2 * cubic p u
      = (t - u) * (u ^ 2 * t ^ 2 + offDiagonalProduct p * u * t
          + offDiagonalProduct p * diagonalMass p * (t + u)) := by
    rw [cubic, cubic]; ring
  rw [h.topRoot.2.1, mul_zero, sub_zero] at hid
  have hfactor : 0 < u ^ 2 * t ^ 2 + offDiagonalProduct p * u * t
      + offDiagonalProduct p * diagonalMass p * (t + u) := by positivity
  have hleft : 0 < u ^ 2 * cubic p t := mul_pos (pow_pos hu 2) hpos
  by_contra hnot
  have htu : t - u ≤ 0 := by linarith
  linarith [mul_nonpos_of_nonpos_of_nonneg htu hfactor.le]

/-! ## The corner information -/

/-- The unnormalized mutual information of the law `(a, b; c, 0)`, in
natural-log units: with `s = a + b + c` it is
`a log(a s / ((a+b)(a+c))) + b log(s / (a+b)) + c log(s / (a+c))`. -/
noncomputable def cornerInfo (a b c : ℝ) : ℝ :=
  xLogX a + xLogX (a + b + c) - xLogX (a + b) - xLogX (a + c)

private theorem cornerInfo_eq {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    cornerInfo a b c = a * Real.log (a * (a + b + c) / ((a + b) * (a + c)))
      + b * Real.log ((a + b + c) / (a + b)) + c * Real.log ((a + b + c) / (a + c)) := by
  have hab : 0 < a + b := add_pos ha hb
  have hac : 0 < a + c := add_pos ha hc
  have habc : 0 < a + b + c := add_pos hab hc
  rw [cornerInfo, xLogX, xLogX, xLogX, xLogX,
    Real.log_div (mul_pos ha habc).ne' (mul_pos hab hac).ne',
    Real.log_mul ha.ne' habc.ne', Real.log_mul hab.ne' hac.ne',
    Real.log_div habc.ne' hab.ne', Real.log_div habc.ne' hac.ne']
  ring

private theorem cornerInfo_rat_upper {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * (a * (a + b + c) / ((a + b) * (a + c)) - 1) + b * ((a + b + c) / (a + b) - 1)
        + c * ((a + b + c) / (a + c) - 1) ≤ b * c / a := by
  rw [← sub_nonneg]
  have hid : b * c / a - (a * (a * (a + b + c) / ((a + b) * (a + c)) - 1)
        + b * ((a + b + c) / (a + b) - 1) + c * ((a + b + c) / (a + c) - 1))
      = b ^ 2 * c ^ 2 / (a * ((a + b) * (a + c))) := by
    field_simp [ha.ne', (add_pos ha hb).ne', (add_pos ha hc).ne']
    ring
  rw [hid]
  positivity

private theorem cornerInfo_rat_lower {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b * c / (a + b + c) ≤ a * (1 - (a + b) * (a + c) / (a * (a + b + c)))
      + b * (1 - (a + b) / (a + b + c)) + c * (1 - (a + c) / (a + b + c)) := by
  apply le_of_eq
  field_simp [ha.ne', (add_pos (add_pos ha hb) hc).ne']
  ring

private theorem log_le_sub_one_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log y ≤ x * (y - 1) :=
  mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hy) hx

private theorem one_sub_inv_le_log_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * (1 - y⁻¹) ≤ x * Real.log y :=
  mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hy) hx

/-- The corner information is squeezed between two rational functions of the
three cells. -/
theorem cornerInfo_bounds {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b * c / (a + b + c) ≤ cornerInfo a b c ∧ cornerInfo a b c ≤ b * c / a := by
  have hab : 0 < a + b := add_pos ha hb
  have hac : 0 < a + c := add_pos ha hc
  have habc : 0 < a + b + c := add_pos hab hc
  have hlba := one_sub_inv_le_log_mul ha.le
    (show (0 : ℝ) < a * (a + b + c) / ((a + b) * (a + c)) by positivity)
  have hlbb := one_sub_inv_le_log_mul hb.le
    (show (0 : ℝ) < (a + b + c) / (a + b) by positivity)
  have hlbc := one_sub_inv_le_log_mul hc.le
    (show (0 : ℝ) < (a + b + c) / (a + c) by positivity)
  rw [inv_div] at hlba hlbb hlbc
  have huba := log_le_sub_one_mul ha.le
    (show (0 : ℝ) < a * (a + b + c) / ((a + b) * (a + c)) by positivity)
  have hubb := log_le_sub_one_mul hb.le
    (show (0 : ℝ) < (a + b + c) / (a + b) by positivity)
  have hubc := log_le_sub_one_mul hc.le
    (show (0 : ℝ) < (a + b + c) / (a + c) by positivity)
  rw [cornerInfo_eq ha hb hc]
  exact ⟨by linarith [cornerInfo_rat_lower ha hb hc],
    by linarith [cornerInfo_rat_upper ha hb hc]⟩

/-! ## The two ends of the chord carry the same log combination -/

/-- At a contact pair the combination `2 log((x+b)(x+c)) - 3 log x` takes the
same value at both diagonal cells.  This is the cube-square identity of
`Touch.lean` read through the logarithm. -/
theorem contactEnds_log_eq (h : ChordDomain p u) :
    2 * Real.log ((chordBottom p u + entryB p) * (chordBottom p u + entryC p))
        - 3 * Real.log (chordBottom p u)
      = 2 * Real.log ((chordTop p u + entryB p) * (chordTop p u + entryC p))
        - 3 * Real.log (chordTop p u) := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hD := chordBottom_pos h
  have hA : 0 < chordTop p u := lt_trans (by linarith [chordBottom_lt_chordMidpoint h])
    (chordMidpoint_lt_chordTop h)
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hsquare := contactCell_cube_quadratic_sq h.fullSupport hu h.nonconstant h.topRoot.2.1
  have hAu : chordTop p u = upperContactCell p u := by
    rw [chordTop_eq, upperContactCell]
  have hDl : chordBottom p u = lowerContactCell p u := by
    rw [chordBottom_eq, lowerContactCell]
  have key : chordTop p u ^ 3
        * ((chordBottom p u + entryB p) * (chordBottom p u + entryC p)) ^ 2
      = chordBottom p u ^ 3
        * ((chordTop p u + entryB p) * (chordTop p u + entryC p)) ^ 2 := by
    rw [offDiagonalQuadratic_factor, offDiagonalQuadratic_factor, hAu, hDl]
    exact hsquare
  have hlog := congrArg Real.log key
  rw [Real.log_mul (pow_ne_zero 3 hA.ne')
      (pow_ne_zero 2 (mul_pos (add_pos hD hb) (add_pos hD hc)).ne'),
    Real.log_mul (pow_ne_zero 3 hD.ne')
      (pow_ne_zero 2 (mul_pos (add_pos hA hb) (add_pos hA hc)).ne')] at hlog
  simp_rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

end StochasticToDeterministicLatents.Binary
