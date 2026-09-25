import StochasticToDeterministicLatents.Binary.TransposeNormalForm

/-!
# Contacts of a feasible kernel on `Bit × Y`

The two-column contact algebra of `Binary/TransposeNormalForm.lean`, with the second
coordinate an arbitrary finite type `Y`. For a feasible kernel `w` on `Bit × Y`, every contact
`q` has a positive row cube parameter `x` (`rowContact_hasCubeParam`): its row marginal is
`(1, x³)/(1 + x³)`. That parameter is a root of the row feasibility polynomial
`(1 + x³)² - ∑ y, (w(0,y) + w(1,y) x²)³`, which feasibility keeps nonnegative on the positive
ray; the column marginal is the normalized cube of the column coefficients
(`rowContact_root`); and the parameter determines the contact (`rowContact_injective`).
The column side rests on the finite-type maximum `sum_twoThirds_le_cubeRoot`:
`∑ A_y v_y^{2/3} ≤ (∑ A_y³)^{1/3}` over probability laws `v`, with equality only at
`v_y = A_y³ / ∑ A³`.

These are the `Bit × Y` forms of `contact_hasRowCubeParameter`,
`feasibilityExpression_nonneg`, `contactParameter_bestResponse` and
`contactParameter_injective`; the row side reuses that module's two-point lemmas unchanged.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose
`Feasible`, `IsContact` and `Lambda` these statements use. The proofs follow the
two-column proofs of `Binary/TransposeNormalForm.lean` with sums over `Y`.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Polynomial Binary

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-! ## Row and column marginals on `Bit × Y` -/

/-- Row marginal of a table on `Bit × Y`. -/
def rowMass (q : Bit × Y → ℝ) (i : Bit) : ℝ := ∑ y, q (i, y)

/-- Column marginal of a table on `Bit × Y`. -/
def colMass (q : Bit × Y → ℝ) (y : Y) : ℝ := q (0, y) + q (1, y)

/-- Positive cube-root parametrization of the row marginal. -/
def RowCubeParam (q : Bit × Y → ℝ) (x : ℝ) : Prop :=
  0 < x ∧ rowMass q 0 = 1 / (1 + x ^ 3) ∧ rowMass q 1 = x ^ 3 / (1 + x ^ 3)

/-- The column coefficient `a_y(x) = w(0,y) + w(1,y) x²`. -/
def colCoeff (w : Bit × Y → ℝ) (x : ℝ) (y : Y) : ℝ := w (0, y) + w (1, y) * x ^ 2

/-! ## Marginals as pushforwards -/

omit [DecidableEq Y] in
/-- Pushing forward along the first projection gives the row marginal. -/
theorem pushforward_fst_eq_rowMass (q : Bit × Y → ℝ) :
    pushforward Prod.fst q = rowMass q := by
  funext i
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  fin_cases i <;> simp [rowMass, Fin.sum_univ_two]

/-- Pushing forward along the second projection gives the column marginal. -/
theorem pushforward_snd_eq_colMass (q : Bit × Y → ℝ) :
    pushforward Prod.snd q = colMass q := by
  funext y
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [colMass, Fin.sum_univ_two]

omit [DecidableEq Y] in
/-- The upstream row marginal is `rowMass`. -/
theorem mX_eq_rowMass (q : Bit × Y → ℝ) : stoch_to_det.mX q = rowMass q :=
  pushforward_fst_eq_rowMass q

/-- The upstream column marginal is `colMass`. -/
theorem mY_eq_colMass (q : Bit × Y → ℝ) : stoch_to_det.mY q = colMass q :=
  pushforward_snd_eq_colMass q

omit [DecidableEq Y] in
/-- The row marginal of a PMF is a PMF. -/
theorem rowMass_isPMF {q : Bit × Y → ℝ} (hq : IsPMF q) : IsPMF (rowMass q) := by
  rw [← pushforward_fst_eq_rowMass]
  exact pushforward_isPMF hq

/-- The column marginal of a PMF is a PMF. -/
theorem colMass_isPMF {q : Bit × Y → ℝ} (hq : IsPMF q) : IsPMF (colMass q) := by
  rw [← pushforward_snd_eq_colMass]
  exact pushforward_isPMF hq

/-! ## The row feasibility polynomial -/

/-- The row feasibility expression `(1 + x³)² − Σ_y a_y(x)³`. -/
def rowFeasibilityExpression (w : Bit × Y → ℝ) (x : ℝ) : ℝ :=
  (1 + x ^ 3) ^ 2 - ∑ y, colCoeff w x y ^ 3

/-- The row feasibility polynomial. -/
def rowFeasibilityPolynomial (w : Bit × Y → ℝ) : Polynomial ℝ :=
  (1 + X ^ 3) ^ 2 - ∑ y, (C (w (0, y)) + C (w (1, y)) * X ^ 2) ^ 3

omit [DecidableEq Y] in
/-- Evaluating the row feasibility polynomial at `x` gives the row feasibility expression. -/
theorem rowFeasibilityPolynomial_eval (w : Bit × Y → ℝ) (x : ℝ) :
    (rowFeasibilityPolynomial w).eval x = rowFeasibilityExpression w x := by
  simp [rowFeasibilityPolynomial, rowFeasibilityExpression, colCoeff, Polynomial.eval_finsetSum]

/-- Each cubed column coefficient has degree at most six. -/
private theorem cube_natDegree_le (a b : ℝ) :
    ((C a + C b * X ^ 2) ^ 3 : Polynomial ℝ).natDegree ≤ 6 := by
  compute_degree

/-- The base term has degree at most six. -/
private theorem base_natDegree_le :
    (((1 : Polynomial ℝ) + X ^ 3) ^ 2).natDegree ≤ 6 := by
  compute_degree

omit [DecidableEq Y] in
/-- The row feasibility polynomial has degree at most six. -/
theorem rowFeasibilityPolynomial_natDegree_le (w : Bit × Y → ℝ) :
    (rowFeasibilityPolynomial w).natDegree ≤ 6 := by
  unfold rowFeasibilityPolynomial
  refine (natDegree_sub_le _ _).trans (max_le base_natDegree_le ?_)
  exact natDegree_sum_le_of_forall_le _ _ (fun y _ => cube_natDegree_le _ _)

/-- A cubed column coefficient has no degree-five term. -/
private theorem cube_coeff_five (a b : ℝ) :
    ((C a + C b * X ^ 2) ^ 3 : Polynomial ℝ).coeff 5 = 0 := by
  rw [show (C a + C b * X ^ 2) ^ 3 =
      C (a ^ 3) + C (3 * a ^ 2 * b) * X ^ 2 +
        C (3 * a * b ^ 2) * X ^ 4 + C (b ^ 3) * X ^ 6 by
    simp only [C_mul, C_pow, C_ofNat]
    ring]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
  norm_num

/-- The base term has no degree-five term. -/
private theorem base_coeff_five :
    (((1 : Polynomial ℝ) + X ^ 3) ^ 2).coeff 5 = 0 := by
  rw [show ((1 : Polynomial ℝ) + X ^ 3) ^ 2 = 1 + 2 * X ^ 3 + X ^ 6 by ring]
  simp [coeff_one, coeff_X_pow]

omit [DecidableEq Y] in
/-- The row feasibility polynomial has no degree-five term. -/
theorem rowFeasibilityPolynomial_coeff_five (w : Bit × Y → ℝ) :
    (rowFeasibilityPolynomial w).coeff 5 = 0 := by
  simp only [rowFeasibilityPolynomial, coeff_sub, finsetSum_coeff, base_coeff_five,
    cube_coeff_five, sum_const_zero, sub_zero]

/-! ## The column-side two-thirds-power maximum on a finite type -/

omit [DecidableEq Y] in
/-- The index type of a PMF is inhabited. -/
theorem univ_nonempty_of_isPMF {v : Y → ℝ} (hv : IsPMF v) :
    (univ : Finset Y).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have ht := hv.total
  unfold stoch_to_det.mass at ht
  rw [h, Finset.sum_empty] at ht
  exact zero_ne_one ht

omit [DecidableEq Y] in
/-- A PMF has a positive coordinate. -/
private theorem exists_pos_of_isPMF {v : Y → ℝ} (hv : IsPMF v) : ∃ y, 0 < v y := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hz : ∀ y, v y = 0 := fun y => le_antisymm (h y) (hv.nonneg y)
  have ht := hv.total
  unfold stoch_to_det.mass at ht
  simp [hz] at ht

omit [DecidableEq Y] in
/-- A PMF sums to one. -/
private theorem pmf_sum_eq_one {v : Y → ℝ} (hv : IsPMF v) : ∑ y, v y = 1 := hv.total

omit [DecidableEq Y] in
/-- The cube sum of positive coefficients is positive on a nonempty type. -/
private theorem cubeSum_pos {A : Y → ℝ} (hA : ∀ y, 0 < A y) (hne : (univ : Finset Y).Nonempty) :
    0 < ∑ y, A y ^ 3 :=
  Finset.sum_pos (fun y _ => pow_pos (hA y) 3) hne

/-- The one-third power of the scale times the normalized cube recovers the coefficient. -/
private theorem cubeRoot_mul {S a : ℝ} (hS : 0 < S) (ha : 0 < a) :
    S ^ ((1 : ℝ) / 3) * (a ^ 3 / S) ^ ((1 : ℝ) / 3) = a := by
  have hp : 0 ≤ a ^ 3 / S := div_nonneg (by positivity) hS.le
  rw [← Real.mul_rpow hS.le hp, mul_div_cancel₀ _ hS.ne']
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast (n := 3) ha.le (by norm_num : (3 : ℕ) ≠ 0))

/-- Rewrite a term through the normalized cube. -/
private theorem twoThirds_term_eq_scaled {S a s : ℝ} (hS : 0 < S) (ha : 0 < a) :
    a * s ^ ((2 : ℝ) / 3) =
      S ^ ((1 : ℝ) / 3) * ((a ^ 3 / S) ^ ((1 : ℝ) / 3) * s ^ ((2 : ℝ) / 3)) := by
  rw [← mul_assoc, cubeRoot_mul hS ha]

/-- The termwise weighted AM-GM bound. -/
private theorem twoThirds_term_le {S a s : ℝ} (hS : 0 < S) (ha : 0 < a) (hs : 0 ≤ s) :
    a * s ^ ((2 : ℝ) / 3) ≤
      S ^ ((1 : ℝ) / 3) * ((1 / 3) * (a ^ 3 / S) + (2 / 3) * s) := by
  have hp : 0 ≤ a ^ 3 / S := div_nonneg (by positivity) hS.le
  rw [twoThirds_term_eq_scaled hS ha]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hS.le _)
  exact Real.geom_mean_le_arith_mean2_weighted
    (w₁ := (1 : ℝ) / 3) (w₂ := (2 : ℝ) / 3) (p₁ := a ^ 3 / S) (p₂ := s)
    (by norm_num) (by norm_num) hp hs (by norm_num)

/-- The termwise equality case. -/
private theorem twoThirds_term_eq_iff {S a s : ℝ} (hS : 0 < S) (ha : 0 < a) (hs : 0 ≤ s) :
    a * s ^ ((2 : ℝ) / 3) =
        S ^ ((1 : ℝ) / 3) * ((1 / 3) * (a ^ 3 / S) + (2 / 3) * s) ↔
      a ^ 3 / S = s := by
  have hp : 0 ≤ a ^ 3 / S := div_nonneg (by positivity) hS.le
  have hc : S ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hS _).ne'
  rw [twoThirds_term_eq_scaled hS ha, mul_right_inj' hc]
  exact Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (w₁ := (1 : ℝ) / 3) (w₂ := (2 : ℝ) / 3) (p₁ := a ^ 3 / S) (p₂ := s)
    (by norm_num) (by norm_num) hp hs (by norm_num)

omit [DecidableEq Y] in
/-- Summing the termwise bounds gives exactly the cube root. -/
private theorem twoThirds_rhs_sum {A v : Y → ℝ} {S : ℝ} (hS : 0 < S) (hSdef : ∑ y, A y ^ 3 = S)
    (hv : ∑ y, v y = 1) :
    ∑ y, S ^ ((1 : ℝ) / 3) * ((1 / 3) * (A y ^ 3 / S) + (2 / 3) * v y) =
      S ^ ((1 : ℝ) / 3) := by
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_div, hSdef, div_self hS.ne', hv]
  norm_num

omit [DecidableEq Y] in
/-- For positive coefficients `A`, every probability law `v` on `Y` satisfies
`Σ_y A_y v_y^{2/3} ≤ (Σ_y A_y³)^{1/3}`, with equality exactly at `v_y = A_y³ / Σ A³`. -/
theorem sum_twoThirds_le_cubeRoot {A : Y → ℝ} (hA : ∀ y, 0 < A y)
    {v : Y → ℝ} (hv : IsPMF v) :
    ∑ y, A y * v y ^ ((2 : ℝ) / 3) ≤ (∑ y, A y ^ 3) ^ ((1 : ℝ) / 3) ∧
      (∑ y, A y * v y ^ ((2 : ℝ) / 3) = (∑ y, A y ^ 3) ^ ((1 : ℝ) / 3) →
        ∀ y, v y = A y ^ 3 / ∑ y', A y' ^ 3) := by
  obtain ⟨S, hSdef⟩ : ∃ S, ∑ y, A y ^ 3 = S := ⟨_, rfl⟩
  rw [hSdef]
  have hS : 0 < S := hSdef ▸ cubeSum_pos hA (univ_nonempty_of_isPMF hv)
  have hRHS := twoThirds_rhs_sum (v := v) hS hSdef (pmf_sum_eq_one hv)
  have hle : ∀ y ∈ (univ : Finset Y), A y * v y ^ ((2 : ℝ) / 3) ≤
      S ^ ((1 : ℝ) / 3) * ((1 / 3) * (A y ^ 3 / S) + (2 / 3) * v y) :=
    fun y _ => twoThirds_term_le hS (hA y) (hv.nonneg y)
  refine ⟨?_, ?_⟩
  · calc
      ∑ y, A y * v y ^ ((2 : ℝ) / 3) ≤
          ∑ y, S ^ ((1 : ℝ) / 3) * ((1 / 3) * (A y ^ 3 / S) + (2 / 3) * v y) :=
        Finset.sum_le_sum hle
      _ = S ^ ((1 : ℝ) / 3) := hRHS
  · intro heq y
    by_contra hne
    have hlt : A y * v y ^ ((2 : ℝ) / 3) <
        S ^ ((1 : ℝ) / 3) * ((1 / 3) * (A y ^ 3 / S) + (2 / 3) * v y) :=
      lt_of_le_of_ne (hle y (mem_univ y))
        (fun h => hne ((twoThirds_term_eq_iff hS (hA y) (hv.nonneg y)).mp h).symm)
    have hsum := Finset.sum_lt_sum hle ⟨y, mem_univ y, hlt⟩
    rw [hRHS, heq] at hsum
    exact lt_irrefl _ hsum

omit [DecidableEq Y] in
/-- The maximum is attained at `v_y = A_y³ / Σ A³`. -/
theorem sum_twoThirds_cubeLaw {A : Y → ℝ} (hA : ∀ y, 0 < A y) [Nonempty Y] :
    IsPMF (fun y => A y ^ 3 / ∑ y', A y' ^ 3) ∧
      ∑ y, A y * (A y ^ 3 / ∑ y', A y' ^ 3) ^ ((2 : ℝ) / 3) =
        (∑ y, A y ^ 3) ^ ((1 : ℝ) / 3) := by
  obtain ⟨S, hSdef⟩ : ∃ S, ∑ y, A y ^ 3 = S := ⟨_, rfl⟩
  rw [hSdef]
  have hS : 0 < S := hSdef ▸ cubeSum_pos hA univ_nonempty
  have hvsum : ∑ y, A y ^ 3 / S = 1 := by
    rw [← Finset.sum_div, hSdef, div_self hS.ne']
  refine ⟨⟨fun y => div_nonneg (pow_pos (hA y) 3).le hS.le, hvsum⟩, ?_⟩
  rw [← twoThirds_rhs_sum (v := fun y => A y ^ 3 / S) hS hSdef hvsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact (twoThirds_term_eq_iff hS (hA y) (div_nonneg (pow_pos (hA y) 3).le hS.le)).mpr rfl

omit [DecidableEq Y] in
/-- A uniform cap on the `Y`-indexed response bounds its cube sum by one. -/
theorem sum_cube_le_one_of_twoThirds_cap [Nonempty Y] {B : Y → ℝ} (hB : ∀ y, 0 < B y)
    (hcap : ∀ t : Y → ℝ, IsPMF t → ∑ y, B y * t y ^ ((2 : ℝ) / 3) ≤ 1) :
    (∑ y, B y ^ 3) ^ ((1 : ℝ) / 3) ≤ 1 ∧ ∑ y, B y ^ 3 ≤ 1 := by
  have hmax := sum_twoThirds_cubeLaw hB
  have hroot : (∑ y, B y ^ 3) ^ ((1 : ℝ) / 3) ≤ 1 := by
    rw [← hmax.2]
    exact hcap _ hmax.1
  refine ⟨hroot, ?_⟩
  have hD : 0 ≤ ∑ y, B y ^ 3 := Finset.sum_nonneg fun y _ => (pow_pos (hB y) 3).le
  have hc := pow_le_pow_left₀ (Real.rpow_nonneg hD _) hroot 3
  rw [oneThird_rpow_cube hD] at hc
  simpa using hc

omit [DecidableEq Y] in
/-- Equality at the cap determines the cube law and makes the cube sum one. -/
theorem sum_twoThirds_eq_one_bestResponse {B : Y → ℝ} (hB : ∀ y, 0 < B y)
    {v : Y → ℝ} (hv : IsPMF v)
    (hcap : ∀ t : Y → ℝ, IsPMF t → ∑ y, B y * t y ^ ((2 : ℝ) / 3) ≤ 1)
    (hattains : ∑ y, B y * v y ^ ((2 : ℝ) / 3) = 1) :
    ∑ y, B y ^ 3 = 1 ∧ ∀ y, v y = B y ^ 3 / ∑ y', B y' ^ 3 := by
  have hne : Nonempty Y := by
    obtain ⟨y, -⟩ := univ_nonempty_of_isPMF hv
    exact ⟨y⟩
  have hmax := sum_twoThirds_le_cubeRoot hB hv
  have hle := (sum_cube_le_one_of_twoThirds_cap hB hcap).1
  have hge : 1 ≤ (∑ y, B y ^ 3) ^ ((1 : ℝ) / 3) := by
    calc
      1 = ∑ y, B y * v y ^ ((2 : ℝ) / 3) := hattains.symm
      _ ≤ (∑ y, B y ^ 3) ^ ((1 : ℝ) / 3) := hmax.1
  have hr : (∑ y, B y ^ 3) ^ ((1 : ℝ) / 3) = 1 := le_antisymm hle hge
  have hD : 0 ≤ ∑ y, B y ^ 3 := Finset.sum_nonneg fun y _ => (pow_pos (hB y) 3).le
  have hsum : ∑ y, B y ^ 3 = 1 := by
    calc
      ∑ y, B y ^ 3 = ((∑ y, B y ^ 3) ^ ((1 : ℝ) / 3)) ^ 3 :=
        (oneThird_rpow_cube hD).symm
      _ = 1 := by rw [hr]; norm_num
  refine ⟨hsum, ?_⟩
  apply hmax.2
  rw [hattains, hr]

/-! ## Contacts -/

omit [DecidableEq Y] in
/-- Expand `Lambda` by rows on `Bit × Y`. -/
theorem rowLambda_eq_rows (w : Bit × Y → ℝ) (u : Bit → ℝ) (v : Y → ℝ) :
    Lambda (univ : Finset (Bit × Y)) w u v =
      (∑ y, w (0, y) * v y ^ ((2 : ℝ) / 3)) * u 0 ^ ((2 : ℝ) / 3) +
        (∑ y, w (1, y) * v y ^ ((2 : ℝ) / 3)) * u 1 ^ ((2 : ℝ) / 3) := by
  simp only [Lambda, stoch_to_det.Lambda, Fintype.sum_prod_type, Fin.sum_univ_two,
    Finset.sum_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq Y] in
/-- Expand `Lambda` by columns on `Bit × Y`. -/
theorem rowLambda_eq_cols (w : Bit × Y → ℝ) (u : Bit → ℝ) (v : Y → ℝ) :
    Lambda (univ : Finset (Bit × Y)) w u v =
      ∑ y, (w (0, y) * u 0 ^ ((2 : ℝ) / 3) + w (1, y) * u 1 ^ ((2 : ℝ) / 3)) *
        v y ^ ((2 : ℝ) / 3) := by
  simp only [Lambda, stoch_to_det.Lambda, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- A contact attains `Lambda = 1` at its row and column marginals. -/
theorem rowContact_lambda_eq_one {w q : Bit × Y → ℝ}
    (hq : IsContact (univ : Finset (Bit × Y)) w q) :
    Lambda (univ : Finset (Bit × Y)) w (rowMass q) (colMass q) = 1 := by
  rw [← pushforward_fst_eq_rowMass, ← pushforward_snd_eq_colMass]
  change stoch_to_det.Lambda (univ : Finset (Bit × Y)) w
      (stoch_to_det.mX q) (stoch_to_det.mY q) = 1
  rw [stoch_to_det.Lambda]
  have heq : ∀ z : Bit × Y,
      w z * stoch_to_det.mX q z.1 ^ ((2 : ℝ) / 3) *
          stoch_to_det.mY q z.2 ^ ((2 : ℝ) / 3) = q z := by
    intro z
    exact (hq.2.2 z (mem_univ z)).symm
  simp_rw [heq]
  simpa [stoch_to_det.mass] using hq.1.total

omit [DecidableEq Y] in
/-- A positive-coefficient response to a PMF is positive. -/
private theorem twoThirds_response_pos {c v : Y → ℝ} (hc : ∀ y, 0 < c y) (hv : IsPMF v) :
    0 < ∑ y, c y * v y ^ ((2 : ℝ) / 3) := by
  obtain ⟨y0, hy0⟩ := exists_pos_of_isPMF hv
  apply Finset.sum_pos'
  · intro y _
    exact mul_nonneg (hc y).le (Real.rpow_nonneg (hv.nonneg y) _)
  · exact ⟨y0, mem_univ y0, mul_pos (hc y0) (Real.rpow_pos_of_pos hy0 _)⟩

/-- Every contact of a feasible kernel on `Bit × Y` has a positive row cube parameter. -/
theorem rowContact_hasCubeParam {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q) :
    ∃ x, RowCubeParam q x := by
  have hu : IsPMF (rowMass q) := rowMass_isPMF hq.1
  have hv : IsPMF (colMass q) := colMass_isPMF hq.1
  have hA : 0 < ∑ y, w (0, y) * colMass q y ^ ((2 : ℝ) / 3) :=
    twoThirds_response_pos (fun y => hw.1 _ (mem_univ _)) hv
  have hB : 0 < ∑ y, w (1, y) * colMass q y ^ ((2 : ℝ) / 3) :=
    twoThirds_response_pos (fun y => hw.1 _ (mem_univ _)) hv
  have hcap : ∀ t : Bit → ℝ, IsPMF t →
      (∑ y, w (0, y) * colMass q y ^ ((2 : ℝ) / 3)) * t 0 ^ ((2 : ℝ) / 3) +
        (∑ y, w (1, y) * colMass q y ^ ((2 : ℝ) / 3)) * t 1 ^ ((2 : ℝ) / 3) ≤ 1 := by
    intro t ht
    rw [← rowLambda_eq_rows w t (colMass q)]
    exact hw.2 t (colMass q) ht hv
  have hattains :
      (∑ y, w (0, y) * colMass q y ^ ((2 : ℝ) / 3)) * rowMass q 0 ^ ((2 : ℝ) / 3) +
        (∑ y, w (1, y) * colMass q y ^ ((2 : ℝ) / 3)) * rowMass q 1 ^ ((2 : ℝ) / 3) = 1 := by
    rw [← rowLambda_eq_rows w (rowMass q) (colMass q)]
    exact rowContact_lambda_eq_one hq
  obtain ⟨-, hu0, hu1⟩ := twoThirds_eq_one_bestResponse hA hB hu hcap hattains
  have hu0p : 0 < rowMass q 0 := by rw [hu0]; positivity
  have hu1p : 0 < rowMass q 1 := by rw [hu1]; positivity
  obtain ⟨hx, -, -, hnorm⟩ :=
    positiveCubeRootIdentities (rowMass q 0) (rowMass q 1) hu0p hu1p
  have forms := hnorm (binaryPMF_sum hu)
  exact ⟨_, hx, forms.1, forms.2⟩

/-- Cubing a scaled coefficient. -/
private theorem scaled_cube {s a : ℝ} (hs : 0 ≤ s) :
    (s ^ ((2 : ℝ) / 3) * a) ^ 3 = s ^ 2 * a ^ 3 := by
  rw [mul_pow, twoThirds_rpow_cube hs]

omit [DecidableEq Y] in
/-- The cube sum of the scaled column coefficients. -/
private theorem scaled_cubeSum {s : ℝ} (hs : 0 ≤ s) (a : Y → ℝ) :
    ∑ y, (s ^ ((2 : ℝ) / 3) * a y) ^ 3 = s ^ 2 * ∑ y, a y ^ 3 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => scaled_cube hs

omit [DecidableEq Y] in
/-- The column coefficients are positive for a feasible kernel and a positive parameter. -/
private theorem colCoeff_pos {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    {x : ℝ} (hx : 0 < x) (y : Y) : 0 < colCoeff w x y := by
  have h0 := hw.1 (0, y) (mem_univ _)
  have h1 := hw.1 (1, y) (mem_univ _)
  unfold colCoeff
  positivity

omit [DecidableEq Y] in
/-- With a normalized row parameter, `Lambda` is the column response to scaled coefficients. -/
private theorem rowLambda_eq_colCoeff (w : Bit × Y → ℝ) {u : Bit → ℝ} {x : ℝ} (hx : 0 < x)
    (hu0 : u 0 = 1 / (1 + x ^ 3)) (hu1 : u 1 = x ^ 3 / (1 + x ^ 3)) (t : Y → ℝ) :
    Lambda (univ : Finset (Bit × Y)) w u t =
      ∑ y, (u 0 ^ ((2 : ℝ) / 3) * colCoeff w x y) * t y ^ ((2 : ℝ) / 3) := by
  have hscale := normalized_cubeParameter_rpow_scale hx hu0 hu1
  rw [rowLambda_eq_cols]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hscale, colCoeff]
  ring

/-- The row law `1/(1+x³)` squared times a sum, as a quotient. -/
private theorem rowScale_mul {x T : ℝ} :
    (1 / (1 + x ^ 3)) ^ 2 * T = T / (1 + x ^ 3) ^ 2 := by
  rw [div_pow, one_pow, one_div, inv_mul_eq_div]

omit [DecidableEq Y] in
/-- Feasibility makes the row feasibility expression nonnegative at every positive parameter. -/
theorem rowFeasibility_nonneg [Nonempty Y] {w : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) {x : ℝ} (hx : 0 < x) :
    0 ≤ rowFeasibilityExpression w x := by
  have hu : IsPMF (cubeLaw 1 x) := cubeLaw_isPMF one_pos hx
  have hd : 0 < 1 + x ^ 3 := by positivity
  have hu0 : cubeLaw 1 x 0 = 1 / (1 + x ^ 3) := by simp [cubeLaw]
  have hu1 : cubeLaw 1 x 1 = x ^ 3 / (1 + x ^ 3) := by simp [cubeLaw]
  have hu0p : 0 < cubeLaw 1 x 0 := by rw [hu0]; positivity
  have hspos : 0 < cubeLaw 1 x 0 ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hu0p _
  have hB : ∀ y, 0 < cubeLaw 1 x 0 ^ ((2 : ℝ) / 3) * colCoeff w x y :=
    fun y => mul_pos hspos (colCoeff_pos hw hx y)
  have hcap : ∀ t : Y → ℝ, IsPMF t →
      ∑ y, (cubeLaw 1 x 0 ^ ((2 : ℝ) / 3) * colCoeff w x y) * t y ^ ((2 : ℝ) / 3) ≤ 1 := by
    intro t ht
    rw [← rowLambda_eq_colCoeff w hx hu0 hu1 t]
    exact hw.2 _ t hu ht
  have hsum := (sum_cube_le_one_of_twoThirds_cap hB hcap).2
  rw [scaled_cubeSum (hu.nonneg 0), hu0, rowScale_mul] at hsum
  have hd2 : 0 < (1 + x ^ 3) ^ 2 := by positivity
  have hpoly : ∑ y, colCoeff w x y ^ 3 ≤ (1 + x ^ 3) ^ 2 := (div_le_one hd2).mp hsum
  unfold rowFeasibilityExpression
  linarith

/-- A contact's row parameter is a root, and it fixes the column marginal as the
normalized cubes of the column coefficients. -/
theorem rowContact_root {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {x : ℝ} (hx : RowCubeParam q x) :
    rowFeasibilityExpression w x = 0 ∧
      ∀ y, colMass q y = colCoeff w x y ^ 3 / ∑ y', colCoeff w x y' ^ 3 := by
  obtain ⟨hxp, hu0, hu1⟩ := hx
  have hu : IsPMF (rowMass q) := rowMass_isPMF hq.1
  have hv : IsPMF (colMass q) := colMass_isPMF hq.1
  have hd : 0 < 1 + x ^ 3 := by positivity
  have hu0p : 0 < rowMass q 0 := by rw [hu0]; positivity
  have hspos : 0 < rowMass q 0 ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hu0p _
  have hB : ∀ y, 0 < rowMass q 0 ^ ((2 : ℝ) / 3) * colCoeff w x y :=
    fun y => mul_pos hspos (colCoeff_pos hw hxp y)
  have hcap : ∀ t : Y → ℝ, IsPMF t →
      ∑ y, (rowMass q 0 ^ ((2 : ℝ) / 3) * colCoeff w x y) * t y ^ ((2 : ℝ) / 3) ≤ 1 := by
    intro t ht
    rw [← rowLambda_eq_colCoeff w hxp hu0 hu1 t]
    exact hw.2 _ t hu ht
  have hattains :
      ∑ y, (rowMass q 0 ^ ((2 : ℝ) / 3) * colCoeff w x y) * colMass q y ^ ((2 : ℝ) / 3) =
        1 := by
    rw [← rowLambda_eq_colCoeff w hxp hu0 hu1 (colMass q)]
    exact rowContact_lambda_eq_one hq
  obtain ⟨hsum, hcol⟩ := sum_twoThirds_eq_one_bestResponse hB hv hcap hattains
  have hs2 : rowMass q 0 ^ 2 ≠ 0 := (pow_pos hu0p 2).ne'
  refine ⟨?_, ?_⟩
  · have h1 := hsum
    rw [scaled_cubeSum (hu.nonneg 0), hu0, rowScale_mul] at h1
    have hd2 : (1 + x ^ 3) ^ 2 ≠ 0 := (pow_pos hd 2).ne'
    have hT : ∑ y, colCoeff w x y ^ 3 = (1 + x ^ 3) ^ 2 := (div_eq_one_iff_eq hd2).mp h1
    unfold rowFeasibilityExpression
    rw [hT]
    ring
  · intro y
    rw [hcol y, scaled_cubeSum (hu.nonneg 0), scaled_cube (hu.nonneg 0)]
    exact mul_div_mul_left _ _ hs2

/-- Two contacts of one feasible kernel with the same row parameter coincide. -/
theorem rowContact_injective {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    {x : ℝ} (hqx : RowCubeParam q x) (hrx : RowCubeParam r x) : q = r := by
  have hX : rowMass q = rowMass r := by
    funext i
    fin_cases i
    · exact hqx.2.1.trans hrx.2.1.symm
    · exact hqx.2.2.trans hrx.2.2.symm
  have hY : colMass q = colMass r := by
    funext y
    rw [(rowContact_root hw hq hqx).2 y, (rowContact_root hw hr hrx).2 y]
  funext z
  rw [hq.2.2 z (mem_univ z), hr.2.2 z (mem_univ z), mX_eq_rowMass, mX_eq_rowMass, mY_eq_colMass,
    mY_eq_colMass, hX, hY]

end

end BinaryRow

end StochasticToDeterministicLatents
