import StochasticToDeterministicLatents.BinaryRow.Contact

/-!
# Cell formulas and the two-contact moments on `Bit × Y`

For a feasible kernel `w` on `Bit × Y`, a contact `q` with row parameter `x` has cells
`q(0,y) = w(0,y) c_y² / (1 + x³)²` and `q(1,y) = w(1,y) x² c_y² / (1 + x³)²`, where
`c_y = w(0,y) + w(1,y) x²` is the column coefficient (`rowContact_entry`), and the cubed column
coefficients sum to `(1 + x³)²` (`rowContact_cubeSum`). The row feasibility expression is a
sparse sextic in the four kernel moments `rowMoment w j = ∑_y w(0,y)^(3-j) w(1,y)^j`
(`rowFeasibilityExpression_eq_moments`). Two distinct contacts, with row parameters `s` and
`t`, factor it as `(x-s)²(x-t)²(x² + 2(s+t)x + st)/(s+t)³` (`rowTwoContact_factorization`),
which fixes all four moments (`rowTwoContact_moments`).

Writing `m_y = w(0,y)³` and `ρ_y = w(1,y)/w(0,y)`, the cells read
`q(0,y) = m_y (1 + ρ_y x²)² / (1 + x³)²` and `q(1,y) = ρ_y x² q(0,y)`, and the moments are
`∑ m_y ρ_y^j`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose `Feasible`
and `IsContact` these statements use. The factorization follows the `Bit × Bit` proof of
`Binary/TransposeNormalForm.lean` with sums over `Y`.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Polynomial Binary

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- The kernel moments `∑_y w(0,y)^(3-j) w(1,y)^j`, for `j = 0, 1, 2, 3`. -/
def rowMoment (w : Bit × Y → ℝ) (j : ℕ) : ℝ := ∑ y, w (0, y) ^ (3 - j) * w (1, y) ^ j

/-! ## The moment form of the feasibility expression -/

omit [DecidableEq Y] in
/-- `rowMoment w 0 = Σ_y w(0, y)³`. -/
theorem rowMoment_zero (w : Bit × Y → ℝ) : rowMoment w 0 = ∑ y, w (0, y) ^ 3 := by
  simp [rowMoment]

omit [DecidableEq Y] in
/-- `rowMoment w 1 = Σ_y w(0, y)² w(1, y)`. -/
theorem rowMoment_one (w : Bit × Y → ℝ) :
    rowMoment w 1 = ∑ y, w (0, y) ^ 2 * w (1, y) := by
  simp [rowMoment]

omit [DecidableEq Y] in
/-- `rowMoment w 2 = Σ_y w(0, y) w(1, y)²`. -/
theorem rowMoment_two (w : Bit × Y → ℝ) :
    rowMoment w 2 = ∑ y, w (0, y) * w (1, y) ^ 2 := by
  simp [rowMoment]

omit [DecidableEq Y] in
/-- `rowMoment w 3 = Σ_y w(1, y)³`. -/
theorem rowMoment_three (w : Bit × Y → ℝ) : rowMoment w 3 = ∑ y, w (1, y) ^ 3 := by
  simp [rowMoment]

omit [DecidableEq Y] in
/-- The cube sum of the column coefficients in the four moments. -/
theorem sum_colCoeff_cube_eq_moments (w : Bit × Y → ℝ) (x : ℝ) :
    ∑ y, colCoeff w x y ^ 3 =
      rowMoment w 0 + 3 * rowMoment w 1 * x ^ 2 + 3 * rowMoment w 2 * x ^ 4 +
        rowMoment w 3 * x ^ 6 := by
  rw [rowMoment_zero, rowMoment_one, rowMoment_two, rowMoment_three]
  simp only [colCoeff, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq Y] in
/-- The row feasibility expression is a sparse sextic in the four kernel moments. -/
theorem rowFeasibilityExpression_eq_moments (w : Bit × Y → ℝ) (x : ℝ) :
    rowFeasibilityExpression w x =
      (1 - rowMoment w 0) - 3 * rowMoment w 1 * x ^ 2 + 2 * x ^ 3
        - 3 * rowMoment w 2 * x ^ 4 + (1 - rowMoment w 3) * x ^ 6 := by
  unfold rowFeasibilityExpression
  rw [sum_colCoeff_cube_eq_moments]
  ring

/-- At a contact's row parameter the cubed column coefficients sum to `(1 + x³)²`. -/
theorem rowContact_cubeSum {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {x : ℝ} (hx : RowCubeParam q x) :
    ∑ y, colCoeff w x y ^ 3 = (1 + x ^ 3) ^ 2 := by
  have h := (rowContact_root hw hq hx).1
  unfold rowFeasibilityExpression at h
  linarith

/-! ## Cells of a contact -/

omit [DecidableEq Y] in
/-- The column coefficients are positive for a feasible kernel and a positive parameter. -/
private theorem colCoeff_pos' {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    {x : ℝ} (hx : 0 < x) (y : Y) : 0 < colCoeff w x y := by
  have h0 := hw.1 (0, y) (mem_univ _)
  have h1 := hw.1 (1, y) (mem_univ _)
  unfold colCoeff
  positivity

/-- A product of two-thirds powers is determined by its cube. -/
private theorem twoThirds_mul_eq {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : a ^ 2 * b ^ 2 = r ^ 3) :
    a ^ ((2 : ℝ) / 3) * b ^ ((2 : ℝ) / 3) = r := by
  have hp : 0 ≤ a ^ ((2 : ℝ) / 3) * b ^ ((2 : ℝ) / 3) :=
    mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)
  have hc : (a ^ ((2 : ℝ) / 3) * b ^ ((2 : ℝ) / 3)) ^ 3 = r ^ 3 := by
    rw [mul_pow, twoThirds_rpow_cube ha, twoThirds_rpow_cube hb, h]
  exact (pow_left_inj₀ hp hr (by norm_num)).mp hc

/-- The row-zero cell factor. -/
private theorem cell_zero {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    (1 / A) ^ ((2 : ℝ) / 3) * (c ^ 3 / A ^ 2) ^ ((2 : ℝ) / 3) = c ^ 2 / A ^ 2 := by
  have hA0 : A ≠ 0 := hA.ne'
  have h1 : (0 : ℝ) ≤ 1 / A := by positivity
  have h2 : (0 : ℝ) ≤ c ^ 3 / A ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ c ^ 2 / A ^ 2 := by positivity
  apply twoThirds_mul_eq h1 h2 h3
  field_simp

/-- The row-one cell factor. -/
private theorem cell_one {A c x : ℝ} (hA : 0 < A) (hc : 0 < c) (hx : 0 < x) :
    (x ^ 3 / A) ^ ((2 : ℝ) / 3) * (c ^ 3 / A ^ 2) ^ ((2 : ℝ) / 3) =
      x ^ 2 * c ^ 2 / A ^ 2 := by
  have hA0 : A ≠ 0 := hA.ne'
  have h1 : (0 : ℝ) ≤ x ^ 3 / A := by positivity
  have h2 : (0 : ℝ) ≤ c ^ 3 / A ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ x ^ 2 * c ^ 2 / A ^ 2 := by positivity
  apply twoThirds_mul_eq h1 h2 h3
  field_simp

/-- The cells of a contact, in terms of the kernel and the contact's row parameter. -/
theorem rowContact_entry {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {x : ℝ} (hx : RowCubeParam q x) (y : Y) :
    q (0, y) = w (0, y) * colCoeff w x y ^ 2 / (1 + x ^ 3) ^ 2 ∧
      q (1, y) = w (1, y) * x ^ 2 * colCoeff w x y ^ 2 / (1 + x ^ 3) ^ 2 := by
  have hroot := rowContact_root hw hq hx
  have hsum := rowContact_cubeSum hw hq hx
  have hxp : 0 < x := hx.1
  have hA : 0 < 1 + x ^ 3 := by positivity
  have hc : 0 < colCoeff w x y := colCoeff_pos' hw hxp y
  have hcol : colMass q y = colCoeff w x y ^ 3 / (1 + x ^ 3) ^ 2 := by
    rw [hroot.2 y, hsum]
  have hz0 : q (0, y) = w (0, y) * stoch_to_det.mX q 0 ^ ((2 : ℝ) / 3) *
      stoch_to_det.mY q y ^ ((2 : ℝ) / 3) := hq.2.2 (0, y) (mem_univ _)
  have hz1 : q (1, y) = w (1, y) * stoch_to_det.mX q 1 ^ ((2 : ℝ) / 3) *
      stoch_to_det.mY q y ^ ((2 : ℝ) / 3) := hq.2.2 (1, y) (mem_univ _)
  rw [mX_eq_rowMass, mY_eq_colMass, hx.2.1, hcol] at hz0
  rw [mX_eq_rowMass, mY_eq_colMass, hx.2.2, hcol] at hz1
  have hcell0 := cell_zero hA hc
  have hcell1 := cell_one hA hc hxp
  constructor
  · calc
      q (0, y) = w (0, y) * ((1 / (1 + x ^ 3)) ^ ((2 : ℝ) / 3) *
          (colCoeff w x y ^ 3 / (1 + x ^ 3) ^ 2) ^ ((2 : ℝ) / 3)) := by
        rw [hz0]; ring
      _ = w (0, y) * colCoeff w x y ^ 2 / (1 + x ^ 3) ^ 2 := by
        rw [hcell0]; ring
  · calc
      q (1, y) = w (1, y) * ((x ^ 3 / (1 + x ^ 3)) ^ ((2 : ℝ) / 3) *
          (colCoeff w x y ^ 3 / (1 + x ^ 3) ^ 2) ^ ((2 : ℝ) / 3)) := by
        rw [hz1]; ring
      _ = w (1, y) * x ^ 2 * colCoeff w x y ^ 2 / (1 + x ^ 3) ^ 2 := by
        rw [hcell1]; ring

/-! ## Sparse sextics -/

/-- Coefficients of a sextic written in monomial form. -/
private theorem sparse_coeff (a6 a5 a4 a3 a2 a1 a0 : ℝ) :
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 6 = a6 ∧
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 5 = a5 ∧
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 4 = a4 ∧
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 3 = a3 ∧
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 2 = a2 ∧
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 1 = a1 ∧
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 0 = a0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] <;> norm_num

/-- Two equal sextics in monomial form have equal coefficients. -/
private theorem sparse_inj {a6 a5 a4 a3 a2 a1 a0 b6 b5 b4 b3 b2 b1 b0 : ℝ}
    (h : (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ) =
      C b6 * X ^ 6 + C b5 * X ^ 5 + C b4 * X ^ 4 + C b3 * X ^ 3 +
        C b2 * X ^ 2 + C b1 * X + C b0) :
    a6 = b6 ∧ a5 = b5 ∧ a4 = b4 ∧ a3 = b3 ∧ a2 = b2 ∧ a1 = b1 ∧ a0 = b0 := by
  have ha := sparse_coeff a6 a5 a4 a3 a2 a1 a0
  have hb := sparse_coeff b6 b5 b4 b3 b2 b1 b0
  rw [h] at ha
  exact ⟨ha.1.symm.trans hb.1, ha.2.1.symm.trans hb.2.1, ha.2.2.1.symm.trans hb.2.2.1,
    ha.2.2.2.1.symm.trans hb.2.2.2.1, ha.2.2.2.2.1.symm.trans hb.2.2.2.2.1,
    ha.2.2.2.2.2.1.symm.trans hb.2.2.2.2.2.1, ha.2.2.2.2.2.2.symm.trans hb.2.2.2.2.2.2⟩

/-- Two sextics agreeing at every real point have equal coefficients. -/
private theorem sparse_inj_eval {a6 a5 a4 a3 a2 a1 a0 b6 b5 b4 b3 b2 b1 b0 : ℝ}
    (h : ∀ x : ℝ, a6 * x ^ 6 + a5 * x ^ 5 + a4 * x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 =
      b6 * x ^ 6 + b5 * x ^ 5 + b4 * x ^ 4 + b3 * x ^ 3 + b2 * x ^ 2 + b1 * x + b0) :
    a6 = b6 ∧ a5 = b5 ∧ a4 = b4 ∧ a3 = b3 ∧ a2 = b2 ∧ a1 = b1 ∧ a0 = b0 := by
  apply sparse_inj
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  exact h x

omit [DecidableEq Y] in
/-- The row feasibility polynomial in monomial form. -/
theorem rowFeasibilityPolynomial_eq_moments (w : Bit × Y → ℝ) :
    rowFeasibilityPolynomial w =
      C (1 - rowMoment w 3) * X ^ 6 + C 0 * X ^ 5 + C (-3 * rowMoment w 2) * X ^ 4 +
        C 2 * X ^ 3 + C (-3 * rowMoment w 1) * X ^ 2 + C 0 * X + C (1 - rowMoment w 0) := by
  apply Polynomial.funext
  intro u
  rw [rowFeasibilityPolynomial_eval, rowFeasibilityExpression_eq_moments]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-! ## The two-contact factorization -/

/-- Two distinct contacts have distinct row parameters. -/
private theorem param_ne {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    (hqr : q ≠ r) {s t : ℝ} (hs : RowCubeParam q s) (ht : RowCubeParam r t) : s ≠ t := by
  intro h
  subst h
  exact hqr (rowContact_injective hw hq hr hs ht)

/-- A contact's row parameter is a double root of the row feasibility polynomial. -/
private theorem param_square_dvd {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {x : ℝ} (hx : RowCubeParam q x) :
    (X - C x) ^ 2 ∣ rowFeasibilityPolynomial w := by
  have : Nonempty Y := ⟨(univ_nonempty_of_isPMF (colMass_isPMF hq.1)).choose⟩
  have hnn : ∀ y : ℝ, 0 < y → 0 ≤ (rowFeasibilityPolynomial w).eval y := by
    intro y hy
    rw [rowFeasibilityPolynomial_eval]
    exact rowFeasibility_nonneg hw hy
  have hroot : (rowFeasibilityPolynomial w).eval x = 0 := by
    rw [rowFeasibilityPolynomial_eval]
    exact (rowContact_root hw hq hx).1
  exact positiveRoot_square_dvd _ x hx.1 hnn hroot

/-- The cofactor of two double roots in a sextic has degree at most two. -/
private theorem quot_natDegree {P Q : Polynomial ℝ} {s t : ℝ} (hP : P.natDegree ≤ 6)
    (hPQ : P = (X - C s) ^ 2 * (X - C t) ^ 2 * Q) : Q.natDegree ≤ 2 := by
  have hFmonic : ((X - C s) ^ 2 * (X - C t) ^ 2 : Polynomial ℝ).Monic :=
    ((monic_X_sub_C s).pow 2).mul ((monic_X_sub_C t).pow 2)
  have hFdeg : ((X - C s) ^ 2 * (X - C t) ^ 2 : Polynomial ℝ).natDegree = 4 := by
    simp [natDegree_mul, X_sub_C_ne_zero]
  by_cases hQ : Q = 0
  · simp [hQ]
  have hm := natDegree_mul hFmonic.ne_zero hQ
  rw [hFdeg] at hm
  rw [hPQ, hm] at hP
  omega

/-- A polynomial of degree at most two in monomial form. -/
private theorem quadratic_form (Q : Polynomial ℝ) (h : Q.natDegree ≤ 2) :
    ∃ a b c : ℝ, Q = C a * X ^ 2 + C b * X + C c := by
  refine ⟨Q.coeff 2, Q.coeff 1, Q.coeff 0, ?_⟩
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases hn2 : n = 2
  · subst n
    simp
  have hn : 2 < n := by omega
  have hzero : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hn)
  rw [hzero]
  simp [coeff_X, coeff_C, hn0, Ne.symm hn1, hn2]

/-- The quartic of two double roots times a quadratic, in monomial form. -/
private theorem quartic_mul (s t a b c : ℝ) :
    (X - C s) ^ 2 * (X - C t) ^ 2 * (C a * X ^ 2 + C b * X + C c) =
      C a * X ^ 6 + C (b - 2 * (s + t) * a) * X ^ 5 +
        C (c - 2 * (s + t) * b + ((s + t) ^ 2 + 2 * (s * t)) * a) * X ^ 4 +
        C (-2 * (s + t) * c + ((s + t) ^ 2 + 2 * (s * t)) * b - 2 * (s + t) * (s * t) * a) *
          X ^ 3 +
        C (((s + t) ^ 2 + 2 * (s * t)) * c - 2 * (s + t) * (s * t) * b + (s * t) ^ 2 * a) *
          X ^ 2 +
        C ((s * t) ^ 2 * b - 2 * (s + t) * (s * t) * c) * X + C ((s * t) ^ 2 * c) := by
  apply Polynomial.funext
  intro u
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- Solving the three odd-coefficient equations for the quadratic cofactor. -/
private theorem sextic_solve {s t a b c : ℝ} (hs : 0 < s) (ht : 0 < t)
    (e5 : (0 : ℝ) = b - 2 * (s + t) * a)
    (e3 : (2 : ℝ) =
      -2 * (s + t) * c + ((s + t) ^ 2 + 2 * (s * t)) * b - 2 * (s + t) * (s * t) * a)
    (e1 : (0 : ℝ) = (s * t) ^ 2 * b - 2 * (s + t) * (s * t) * c) :
    b = 2 * (s + t) * a ∧ c = s * t * a ∧ a = 1 / (s + t) ^ 3 := by
  have hR : s + t ≠ 0 := (add_pos hs ht).ne'
  have eq1 : b = 2 * (s + t) * a := by linarith
  have eq0 : c = s * t * a := by
    have hne : 2 * (s + t) * (s * t) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    linear_combination e1 - (s * t) ^ 2 * e5
  have eq2 : a = 1 / (s + t) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero 3 hR)]
    linear_combination (-1 / 2 : ℝ) * (e3 - 2 * (s + t) * eq0 + ((s + t) ^ 2 + 2 * (s * t)) * eq1)
  exact ⟨eq1, eq0, eq2⟩

omit [DecidableEq Y] in
/-- Two distinct positive double roots of the row feasibility polynomial factor it. -/
private theorem factor_of_dvd (w : Bit × Y → ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t)
    (hsd : (X - C s) ^ 2 ∣ rowFeasibilityPolynomial w)
    (htd : (X - C t) ^ 2 ∣ rowFeasibilityPolynomial w) (x : ℝ) :
    rowFeasibilityExpression w x =
      (x - s) ^ 2 * (x - t) ^ 2 * (x ^ 2 + 2 * (s + t) * x + s * t) / (s + t) ^ 3 := by
  have hcop : IsCoprime ((X - C s) ^ 2) ((X - C t) ^ 2) := by
    apply (Polynomial.isCoprime_X_sub_C_of_isUnit_sub ?_).pow
    rw [isUnit_iff_ne_zero]
    exact sub_ne_zero.mpr hst
  obtain ⟨Q, hPQ⟩ := hcop.mul_dvd hsd htd
  have hQdeg : Q.natDegree ≤ 2 :=
    quot_natDegree (rowFeasibilityPolynomial_natDegree_le w) hPQ
  obtain ⟨a, b, c, rfl⟩ := quadratic_form Q hQdeg
  have hP2 := hPQ.trans (quartic_mul s t a b c)
  obtain ⟨-, e5, -, e3, -, e1, -⟩ :=
    sparse_inj ((rowFeasibilityPolynomial_eq_moments w).symm.trans hP2)
  obtain ⟨eq1, eq0, eq2⟩ := sextic_solve hs ht e5 e3 e1
  have hR : s + t ≠ 0 := (add_pos hs ht).ne'
  rw [← rowFeasibilityPolynomial_eval, hPQ]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  rw [eq1, eq0, eq2]
  field_simp

/-- Two distinct contacts of one feasible kernel factor its feasibility expression. -/
theorem rowTwoContact_factorization {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    (hqr : q ≠ r) {s t : ℝ} (hs : RowCubeParam q s) (ht : RowCubeParam r t) (x : ℝ) :
    rowFeasibilityExpression w x =
      (x - s) ^ 2 * (x - t) ^ 2 * (x ^ 2 + 2 * (s + t) * x + s * t) / (s + t) ^ 3 := by
  have hst : s ≠ t := param_ne hw hq hr hqr hs ht
  exact factor_of_dvd w hs.1 ht.1 hst (param_square_dvd hw hq hs) (param_square_dvd hw hr ht) x

/-! ## The moments -/

/-- The factorized sextic in monomial form. -/
private theorem factor_expand {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    (x - s) ^ 2 * (x - t) ^ 2 * (x ^ 2 + 2 * (s + t) * x + s * t) / (s + t) ^ 3 =
      1 / (s + t) ^ 3 * x ^ 6 + 0 * x ^ 5 +
        (-3 * ((s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3)) * x ^ 4 + 2 * x ^ 3 +
        (-3 * (s * t * (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3)) * x ^ 2 + 0 * x +
        (s * t) ^ 3 / (s + t) ^ 3 := by
  have hR : s + t ≠ 0 := (add_pos hs ht).ne'
  field_simp
  ring

/-- The four kernel moments of two distinct contacts with row parameters `s` and `t`. -/
theorem rowTwoContact_moments {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    (hqr : q ≠ r) {s t : ℝ} (hs : RowCubeParam q s) (ht : RowCubeParam r t) :
    rowMoment w 0 = 1 - (s * t) ^ 3 / (s + t) ^ 3 ∧
      rowMoment w 1 = s * t * (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3 ∧
      rowMoment w 2 = (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3 ∧
      rowMoment w 3 = 1 - 1 / (s + t) ^ 3 := by
  have h : ∀ x : ℝ,
      (1 - rowMoment w 3) * x ^ 6 + 0 * x ^ 5 + (-3 * rowMoment w 2) * x ^ 4 + 2 * x ^ 3 +
          (-3 * rowMoment w 1) * x ^ 2 + 0 * x + (1 - rowMoment w 0) =
        1 / (s + t) ^ 3 * x ^ 6 + 0 * x ^ 5 +
          (-3 * ((s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3)) * x ^ 4 + 2 * x ^ 3 +
          (-3 * (s * t * (s ^ 2 + s * t + t ^ 2) / (s + t) ^ 3)) * x ^ 2 + 0 * x +
          (s * t) ^ 3 / (s + t) ^ 3 := by
    intro x
    have e1 := rowFeasibilityExpression_eq_moments w x
    have e2 := rowTwoContact_factorization hw hq hr hqr hs ht x
    have e3 := factor_expand hs.1 ht.1 x
    linear_combination e2 - e1 + e3
  obtain ⟨h6, -, h4, -, h2, -, h0⟩ := sparse_inj_eval h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end

end BinaryRow

end StochasticToDeterministicLatents
