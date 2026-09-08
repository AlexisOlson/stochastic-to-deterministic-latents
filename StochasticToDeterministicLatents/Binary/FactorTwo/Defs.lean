import StochasticToDeterministicLatents.Binary.Selector
import Mathlib.Analysis.Real.Sqrt

/-!
# Objects of the binary factor-two argument

The stochastic optimum of a binary law is controlled by the largest
nonnegative root of a cubic in the off-diagonal data.  This module defines
that cubic, its top root, the two contact laws that swap the diagonal, and
the mixing weight between them, and proves the root exists, is unique, and
that the two contacts are probability laws mixing back to `p`.

Write `a = p (0,0)`, `b = p (0,1)`, `c = p (1,0)`, `d = p (1,1)`.  The cubic is

`f(u) = u^3 - (b + c) u^2 - b c u - b c (a + d)`,

and its top root `cubicRoot p` is the largest `u` with `f(u) = 0`, equivalently
the unique positive root when `b c > 0`.  The two contacts move mass along the
diagonal, keeping `b` and `c` fixed and keeping `a + d` fixed.

The determinant, and the diagonal and off-diagonal products, are the ones
already defined in `Binary.Selector`; this module does not redefine them.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Real

/-! ## Cells and marginal combinations -/

/-- The cell `a = p (0,0)`. -/
def entryA (p : RealTable) : ℝ := p (0, 0)
/-- The cell `b = p (0,1)`. -/
def entryB (p : RealTable) : ℝ := p (0, 1)
/-- The cell `c = p (1,0)`. -/
def entryC (p : RealTable) : ℝ := p (1, 0)
/-- The cell `d = p (1,1)`. -/
def entryD (p : RealTable) : ℝ := p (1, 1)

/-- The diagonal mass `s = a + d`. -/
def diagonalMass (p : RealTable) : ℝ := entryA p + entryD p

/-- The off-diagonal, or disagreement, mass `v = b + c`. -/
def offDiagonalMass (p : RealTable) : ℝ := entryB p + entryC p

/-- Full support, spelled as the library states it elsewhere. -/
abbrev FullSupport (p : RealTable) : Prop := ∀ z, 0 < p z

/-! The products and determinant of `Binary.Selector`, in entry notation. -/

theorem diagonalProduct_eq (p : RealTable) :
    diagonalProduct p = entryA p * entryD p := rfl

theorem offDiagonalProduct_eq (p : RealTable) :
    offDiagonalProduct p = entryB p * entryC p := rfl

theorem determinant_eq (p : RealTable) :
    determinant p = entryA p * entryD p - entryB p * entryC p := rfl

/-! ## The cubic and its top root -/

/-- The cubic `f(u) = u^3 - v u^2 - w u - w s` whose largest nonnegative root
governs the stochastic optimum. -/
noncomputable def cubic (p : RealTable) (u : ℝ) : ℝ :=
  u ^ 3 - offDiagonalMass p * u ^ 2 - offDiagonalProduct p * u
    - offDiagonalProduct p * diagonalMass p

/-- `u` is the top root: a nonnegative root beyond which the cubic is
positive. -/
def IsTopRoot (p : RealTable) (u : ℝ) : Prop :=
  0 ≤ u ∧ cubic p u = 0 ∧ ∀ x, u < x → 0 < cubic p x

/-! ## Contacts along the diagonal -/

/-- The half-width `r = sqrt (s ^ 2 - 4 u ^ 2)` of the diagonal contact pair. -/
noncomputable def contactRadius (p : RealTable) (u : ℝ) : ℝ :=
  √(diagonalMass p ^ 2 - 4 * u ^ 2)

/-- The upper contact `((s + r)/2, b, c, (s - r)/2)`. -/
noncomputable def contactAt (p : RealTable) (u : ℝ) : RealTable := fun z =>
  if z = (0, 0) then (diagonalMass p + contactRadius p u) / 2
  else if z = (1, 1) then (diagonalMass p - contactRadius p u) / 2
  else p z

/-- The lower contact `((s - r)/2, b, c, (s + r)/2)`, the diagonal swap of
`contactAt`. -/
noncomputable def oppositeContactAt (p : RealTable) (u : ℝ) : RealTable := fun z =>
  if z = (0, 0) then (diagonalMass p - contactRadius p u) / 2
  else if z = (1, 1) then (diagonalMass p + contactRadius p u) / 2
  else p z

/-- The weight `lambda = (a - (s - r)/2)/r` mixing the two contacts back to
`p`. -/
noncomputable def mixingWeight (p : RealTable) (u : ℝ) : ℝ :=
  (entryA p - (diagonalMass p - contactRadius p u) / 2) / contactRadius p u

/-- The diagonal swap `(a,b,c,d)` to `(d,b,c,a)`. -/
def swapDiagonal (q : RealTable) : RealTable := fun z =>
  if z = (0, 0) then q (1, 1) else if z = (1, 1) then q (0, 0) else q z

/-- The optimum is non-constant exactly when the top root falls below
`sqrt (a d)`. -/
def Nonconstant (p : RealTable) (u : ℝ) : Prop :=
  u < √(diagonalProduct p)

/-! ## Elementary rewriting -/

/-- The four cells of a binary table, summed in row-major order. -/
theorem sum_cells (f : Cell → ℝ) :
    ∑ z, f z = f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1) := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]
  ring

theorem cubic_zero (p : RealTable) :
    cubic p 0 = -(offDiagonalProduct p * diagonalMass p) := by
  simp [cubic]

private theorem cubic_eq_sq_mul (p : RealTable) (u : ℝ) (hu : u ≠ 0) :
    cubic p u = u ^ 2 * (u - offDiagonalMass p - offDiagonalProduct p / u
      - offDiagonalProduct p * diagonalMass p / u ^ 2) := by
  unfold cubic
  field_simp

private theorem cubic_pos_of_large {p : RealTable} (hv : 0 ≤ offDiagonalMass p)
    (hw : 0 ≤ offDiagonalProduct p) (hs : 0 ≤ diagonalMass p) :
    0 < cubic p (offDiagonalMass p + offDiagonalProduct p
      + offDiagonalProduct p * diagonalMass p + 1) := by
  let M := offDiagonalMass p + offDiagonalProduct p
    + offDiagonalProduct p * diagonalMass p + 1
  have hws : 0 ≤ offDiagonalProduct p * diagonalMass p := mul_nonneg hw hs
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hmw : offDiagonalProduct p * M ≤ M ^ 2 * offDiagonalProduct p := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hMM hw
  have hmws : offDiagonalProduct p * diagonalMass p
      ≤ M ^ 2 * (offDiagonalProduct p * diagonalMass p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hMM) hws]
  dsimp [M] at *
  unfold cubic
  nlinarith [sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hM)]

private theorem shape_strictMonoOn {p : RealTable} (hw : 0 ≤ offDiagonalProduct p)
    (hs : 0 ≤ diagonalMass p) :
    StrictMonoOn (fun u : ℝ => u - offDiagonalMass p - offDiagonalProduct p / u
      - offDiagonalProduct p * diagonalMass p / u ^ 2) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hdiv : offDiagonalProduct p / y ≤ offDiagonalProduct p / x :=
    div_le_div_of_nonneg_left hw hx0 hxy.le
  have hsquare : x ^ 2 < y ^ 2 := by nlinarith
  have hws : 0 ≤ offDiagonalProduct p * diagonalMass p := mul_nonneg hw hs
  have hdivsq : offDiagonalProduct p * diagonalMass p / y ^ 2
      ≤ offDiagonalProduct p * diagonalMass p / x ^ 2 :=
    div_le_div_of_nonneg_left hws (sq_pos_of_pos hx0) hsquare.le
  linarith

/-- Beyond a positive root the cubic stays positive. -/
private theorem cubic_pos_of_gt_root {p : RealTable} {u : ℝ}
    (hw : 0 ≤ offDiagonalProduct p) (hs : 0 ≤ diagonalMass p)
    (hu : 0 < u) (h0 : cubic p u = 0) :
    ∀ x, u < x → 0 < cubic p x := by
  intro x hux
  have hu0 : u ≠ 0 := hu.ne'
  have hx_pos : 0 < x := lt_trans hu hux
  have hshape0 : u - offDiagonalMass p - offDiagonalProduct p / u
      - offDiagonalProduct p * diagonalMass p / u ^ 2 = 0 := by
    have h := cubic_eq_sq_mul p u hu0
    rw [h0] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 hu0)
  have hshape := shape_strictMonoOn hw hs hu hx_pos hux
  rw [cubic_eq_sq_mul p x hx_pos.ne']
  exact mul_pos (sq_pos_of_pos hx_pos) (by simpa [hshape0] using hshape)

/-- Every positive root of the cubic is the top root. -/
theorem isTopRoot_of_pos_root {p : RealTable} {u : ℝ}
    (hw : 0 ≤ offDiagonalProduct p) (hs : 0 ≤ diagonalMass p)
    (hu : 0 < u) (h0 : cubic p u = 0) : IsTopRoot p u :=
  ⟨hu.le, h0, cubic_pos_of_gt_root hw hs hu h0⟩

private theorem exists_pos_root {p : RealTable} (hv : 0 ≤ offDiagonalMass p)
    (hw : 0 < offDiagonalProduct p) (hs : 0 < diagonalMass p) :
    ∃ u, 0 < u ∧ cubic p u = 0 := by
  let M := offDiagonalMass p + offDiagonalProduct p
    + offDiagonalProduct p * diagonalMass p + 1
  have hneg : cubic p 0 < 0 := by
    rw [cubic_zero]
    exact neg_lt_zero.mpr (mul_pos hw hs)
  have hpos : 0 < cubic p M := cubic_pos_of_large hv hw.le hs.le
  have hM : 0 ≤ M := by
    dsimp [M]
    nlinarith [mul_pos hw hs]
  have hcont : Continuous (cubic p) := by
    unfold cubic
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (cubic p 0) (cubic p M) := ⟨hneg, hpos⟩
  obtain ⟨u, huIoo, hroot⟩ := intermediate_value_Ioo hM hcont.continuousOn hmem
  exact ⟨u, huIoo.1, hroot⟩

/-- When `b c > 0` the cubic has exactly one positive root. -/
theorem exists_unique_pos_root {p : RealTable} (hv : 0 ≤ offDiagonalMass p)
    (hw : 0 < offDiagonalProduct p) (hs : 0 < diagonalMass p) :
    ∃! u, 0 < u ∧ cubic p u = 0 := by
  obtain ⟨u, hu, hroot⟩ := exists_pos_root hv hw hs
  refine ⟨u, ⟨hu, hroot⟩, ?_⟩
  rintro x ⟨hx, hxroot⟩
  rcases lt_trichotomy x u with hlt | heq | hgt
  · exact absurd hroot (cubic_pos_of_gt_root hw.le hs.le hx hxroot u hlt).ne'
  · exact heq
  · exact absurd hxroot (cubic_pos_of_gt_root hw.le hs.le hu hroot x hgt).ne'

/-- A top root is unique: two of them bound each other. -/
theorem isTopRoot_unique {p : RealTable} {u x : ℝ}
    (hu : IsTopRoot p u) (hx : IsTopRoot p x) : u = x := by
  rcases lt_trichotomy u x with h | h | h
  · exact absurd hx.2.1 (hu.2.2 x h).ne'
  · exact h
  · exact absurd hu.2.1 (hx.2.2 u h).ne'

open Classical in
/-- The top root of the cubic, `0` when none exists.  The contract permits a
choice-based definition; `isTopRoot_unique` makes it well determined wherever a
top root is available. -/
noncomputable def cubicRoot (p : RealTable) : ℝ :=
  if h : ∃ u, IsTopRoot p u then h.choose else 0

theorem isTopRoot_cubicRoot {p : RealTable} (h : ∃ u, IsTopRoot p u) :
    IsTopRoot p (cubicRoot p) := by
  classical
  rw [cubicRoot, dif_pos h]
  exact h.choose_spec

theorem cubicRoot_eq {p : RealTable} {u : ℝ} (hu : IsTopRoot p u) :
    cubicRoot p = u :=
  isTopRoot_unique (isTopRoot_cubicRoot ⟨u, hu⟩) hu

/-- The upper contact of `p`, at its own top root. -/
noncomputable def swapContact (p : RealTable) : RealTable :=
  contactAt p (cubicRoot p)

/-! ## The contact pair is a mixture of `p`

Below the top root, the two diagonal contacts are strictly positive laws and
`p` is a proper convex combination of them.  Each lemma carries exactly the
hypotheses it uses; the private material collected all four in a section, which
the unused-section-variable linter rightly objects to.
-/

theorem cell_pos {p : RealTable} (hpos : FullSupport p) :
    0 < entryA p ∧ 0 < entryB p ∧ 0 < entryC p ∧ 0 < entryD p :=
  ⟨hpos (0, 0), hpos (0, 1), hpos (1, 0), hpos (1, 1)⟩

/-- The diagonal of a fully supported law carries positive mass. -/
theorem diagonalMass_pos {p : RealTable} (hpos : FullSupport p) :
    0 < diagonalMass p :=
  add_pos (cell_pos hpos).1 (cell_pos hpos).2.2.2

/-- The off-diagonal of a fully supported law carries positive mass. -/
theorem offDiagonalMass_pos {p : RealTable} (hpos : FullSupport p) :
    0 < offDiagonalMass p :=
  add_pos (cell_pos hpos).2.1 (cell_pos hpos).2.2.1

/-- The off-diagonal product of a fully supported law is positive. -/
theorem offDiagonalProduct_pos {p : RealTable} (hpos : FullSupport p) :
    0 < offDiagonalProduct p := by
  rw [offDiagonalProduct_eq]
  exact mul_pos (cell_pos hpos).2.1 (cell_pos hpos).2.2.1

private theorem sq_lt_diagonalProduct {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : u ^ 2 < diagonalProduct p := by
  have had : 0 ≤ diagonalProduct p :=
    (mul_pos (cell_pos hpos).1 (cell_pos hpos).2.2.2).le
  rw [Nonconstant] at hnc
  nlinarith [Real.sq_sqrt had]

private theorem disc_pos {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) :
    (entryA p - entryD p) ^ 2 < diagonalMass p ^ 2 - 4 * u ^ 2 := by
  have hsq := sq_lt_diagonalProduct hpos hu hnc
  rw [diagonalProduct_eq] at hsq
  rw [diagonalMass]
  nlinarith [hsq]

theorem contactRadius_pos {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : 0 < contactRadius p u := by
  rw [contactRadius, Real.sqrt_pos]
  nlinarith [disc_pos hpos hu hnc, sq_nonneg (entryA p - entryD p)]

theorem contactRadius_sq {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) :
    contactRadius p u ^ 2 = diagonalMass p ^ 2 - 4 * u ^ 2 := by
  rw [contactRadius, Real.sq_sqrt]
  nlinarith [disc_pos hpos hu hnc, sq_nonneg (entryA p - entryD p)]

theorem abs_sub_lt_contactRadius {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) :
    |entryA p - entryD p| < contactRadius p u := by
  have hr := contactRadius_pos hpos hu hnc
  have hd := disc_pos hpos hu hnc
  have hrsq := contactRadius_sq hpos hu hnc
  nlinarith [sq_abs (entryA p - entryD p)]

private theorem contactRadius_lt_diagonalMass {p : RealTable} {u : ℝ}
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u) :
    contactRadius p u < diagonalMass p := by
  have hs := diagonalMass_pos hpos
  have hrsq := contactRadius_sq hpos hu hnc
  have hr := contactRadius_pos hpos hu hnc
  nlinarith [sq_pos_of_pos hu]

theorem diagonalMass_sub_contactRadius_pos {p : RealTable} {u : ℝ}
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u) :
    0 < (diagonalMass p - contactRadius p u) / 2 := by
  nlinarith [contactRadius_lt_diagonalMass hpos hu hnc]

private theorem mixingWeight_eq {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) :
    mixingWeight p u
      = (entryA p - entryD p + contactRadius p u) / (2 * contactRadius p u) := by
  rw [mixingWeight, diagonalMass]
  field_simp [ne_of_gt (contactRadius_pos hpos hu hnc)]
  ring

private theorem mixingWeight_pos {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : 0 < mixingWeight p u := by
  rw [mixingWeight_eq hpos hu hnc]
  have h := abs_sub_lt_contactRadius hpos hu hnc
  have hr := contactRadius_pos hpos hu hnc
  rw [abs_lt] at h
  exact div_pos (by linarith) (by positivity)

private theorem mixingWeight_lt_one {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : mixingWeight p u < 1 := by
  rw [mixingWeight_eq hpos hu hnc]
  have h := abs_sub_lt_contactRadius hpos hu hnc
  have hr := contactRadius_pos hpos hu hnc
  rw [abs_lt] at h
  refine (div_lt_one (by positivity : 0 < 2 * contactRadius p u)).mpr ?_
  linarith

theorem contactAt_pos {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : ∀ z, 0 < contactAt p u z := by
  rintro ⟨x, y⟩
  fin_cases x <;> fin_cases y
  · simp only [contactAt]
    norm_num
    have hs := diagonalMass_pos hpos
    have hr := contactRadius_pos hpos hu hnc
    nlinarith
  · simpa [contactAt, entryB] using (cell_pos hpos).2.1
  · simpa [contactAt, entryC] using (cell_pos hpos).2.2.1
  · simpa [contactAt] using diagonalMass_sub_contactRadius_pos hpos hu hnc

private theorem oppositeContactAt_pos {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : ∀ z, 0 < oppositeContactAt p u z := by
  rintro ⟨x, y⟩
  fin_cases x <;> fin_cases y
  · simpa [oppositeContactAt] using diagonalMass_sub_contactRadius_pos hpos hu hnc
  · simpa [oppositeContactAt, entryB] using (cell_pos hpos).2.1
  · simpa [oppositeContactAt, entryC] using (cell_pos hpos).2.2.1
  · simp only [oppositeContactAt]
    have hs := diagonalMass_pos hpos
    have hr := contactRadius_pos hpos hu hnc
    norm_num
    positivity

private theorem contactAt_total {p : RealTable} {u : ℝ} (hp : IsPMF p) :
    ∑ z, contactAt p u z = 1 := by
  rw [sum_cells]
  simp [contactAt, diagonalMass, entryA, entryD]
  have ht := hp.total
  rw [stoch_to_det.mass, sum_cells] at ht
  convert ht using 1
  ring

private theorem oppositeContactAt_total {p : RealTable} {u : ℝ} (hp : IsPMF p) :
    ∑ z, oppositeContactAt p u z = 1 := by
  rw [sum_cells]
  simp [oppositeContactAt, diagonalMass, entryA, entryD]
  have ht := hp.total
  rw [stoch_to_det.mass, sum_cells] at ht
  convert ht using 1
  ring

theorem isPMF_contactAt {p : RealTable} {u : ℝ} (hp : IsPMF p) (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : IsPMF (contactAt p u) :=
  ⟨fun z => (contactAt_pos hpos hu hnc z).le, contactAt_total hp⟩

private theorem isPMF_oppositeContactAt {p : RealTable} {u : ℝ} (hp : IsPMF p)
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u) :
    IsPMF (oppositeContactAt p u) :=
  ⟨fun z => (oppositeContactAt_pos hpos hu hnc z).le, oppositeContactAt_total hp⟩

private theorem mixture_cell {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : ∀ z,
    mixingWeight p u * contactAt p u z
      + (1 - mixingWeight p u) * oppositeContactAt p u z = p z := by
  rintro ⟨x, y⟩
  fin_cases x <;> fin_cases y
  all_goals simp [contactAt, oppositeContactAt]
  · rw [mixingWeight_eq hpos hu hnc, diagonalMass]
    unfold entryA entryD
    field_simp [ne_of_gt (contactRadius_pos hpos hu hnc)]
    ring
  · ring
  · ring
  · rw [mixingWeight_eq hpos hu hnc, diagonalMass]
    unfold entryA entryD
    field_simp [ne_of_gt (contactRadius_pos hpos hu hnc)]
    ring

/-- Below the top root, `p` is a proper convex combination of two strictly
positive laws that differ from `p` only along the diagonal. -/
theorem contact_mixture {p : RealTable} {u : ℝ} (hp : IsPMF p) (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) :
    IsPMF (contactAt p u) ∧ IsPMF (oppositeContactAt p u) ∧
      0 < mixingWeight p u ∧ mixingWeight p u < 1 ∧ ∀ z,
      mixingWeight p u * contactAt p u z
        + (1 - mixingWeight p u) * oppositeContactAt p u z = p z :=
  ⟨isPMF_contactAt hp hpos hu hnc, isPMF_oppositeContactAt hp hpos hu hnc,
    mixingWeight_pos hpos hu hnc, mixingWeight_lt_one hpos hu hnc,
    mixture_cell hpos hu hnc⟩

end StochasticToDeterministicLatents.Binary
