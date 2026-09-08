/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Modified: the plane index is
produced existentially rather than by a nested conditional, the pairing step is
stated for any chord domain rather than only on the seam, and the bound is
stated multiplied through by `Real.log 2`, as every other margin bound in this
tree is.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.PlaneEndpoints

/-!
# The constant margin on the seam

At a chord domain whose off-diagonal mass is exactly `1/8` -- the seam -- the
constant code's margin at the centre of the contact chord is bounded below:

```
1/100 < Real.log 2 * constantMargin p u (chordMidpoint p)
```

This is the first bound on a margin in the reference-plane route.  Everything
before it was about numbers.

## The three steps

`centerPlaneBound` is `centerConstantScalar` at off-diagonal mass `1/8` with the
plane's constant in place of the contact's `Phi`, and `centerConstantScalar`
*subtracts* twice that argument.  So the plane bound sits **below** the margin
exactly when the plane's constant sits **above** `Real.log 2 * Phi`, and that is
what the reference plane buys:

* the contact's `Phi` is at most its pairing against any reference plane's
  certificate, and the two diagonal cells of `chordAt p (chordMidpoint p)` sum
  to `diagonalMass p` whatever the chord parameter is, so the pairing collapses
  to three terms and needs no seam hypothesis;
* on the seam the three terms are exactly the plane's constant, because
  `diagonalMass p = 7/8` and the two off-diagonal cells are
  `(1 ± z)/16` for the imbalance `z`;
* the four intervals of `PlaneEndpoints` cover `[0, 1]`, and on each of them
  concavity puts the plane bound above `1/100`.

The certificate is in bits and the margin scalar in nats, so the pairing is
multiplied through by `Real.log 2` once, where the two meet.

## Against the page

The page proves this seam bound as Proposition 4.5, with the constant
`1/200` and by a different route: it separates the two off-diagonal cells'
entropy and bounds the remainder's derivative in `b c`, using no reference
plane at all.  The bound here is the same statement with `1/100`, which is
twice as strong, reached through four reference planes and concavity in the
imbalance.  Neither route is a formalisation of the other.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and module
boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u z : ℝ}

/-! ## The contact's potential, against a reference plane -/

/-- **The pairing bound, in nats.**  The contact's `Phi` is at most its pairing
against any reference plane's certificate.  The two diagonal cells of the chord
at any parameter sum to `diagonalMass p`, so only three terms survive and no
hypothesis on the off-diagonal mass is needed. -/
private theorem log_two_mul_phi_le_plane (h : ChordDomain p u) (i : Fin 4) :
    Real.log 2 * Phi (contactAt p u)
      ≤ diagonalMass p * Real.log (referencePlanes i).diagValue
        - entryB p * Real.log (referencePlanes i).offValueB
        - entryC p * Real.log (referencePlanes i).offValueC := by
  have hpair := phi_contact_le_chordMidpoint_pairing h (chordDomain_referencePlane i)
  obtain ⟨e00, e11, e01, e10⟩ := tangentCert_referencePlane i
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Fintype.sum_prod_type] at hpair
  simp only [Fin.sum_univ_two] at hpair
  rw [e00, e01, e10, e11] at hpair
  norm_num [chordAt, Real.logb] at hpair
  have h2 := mul_le_mul_of_nonneg_left hpair hlog.le
  field_simp at h2
  simp only [entryB, entryC]
  linarith

/-! ## The seam -/

/-- On the seam the two off-diagonal cells are `(1 ± z)/16` and the diagonal
mass is `7/8`. -/
private theorem seam_cells (h : ChordDomain p u)
    (hv : offDiagonalMass p = (1 : ℝ) / 8) :
    entryB p = (1 + (entryB p - entryC p) / ((1 : ℝ) / 8)) / 16
      ∧ entryC p = (1 - (entryB p - entryC p) / ((1 : ℝ) / 8)) / 16
      ∧ diagonalMass p = (7 : ℝ) / 8 := by
  have hs := diagonalMass_add_offDiagonalMass h.isPMF
  have hbc : entryB p + entryC p = (1 : ℝ) / 8 := by
    rw [← hv]; simp [offDiagonalMass]
  refine ⟨by field_simp; linarith, by field_simp; linarith, by linarith⟩

/-- **The plane bound lies below the constant margin on the seam.**  The
inequality reverses because `centerConstantScalar` subtracts twice its
argument. -/
private theorem centerPlaneBound_le_constantMargin (h : ChordDomain p u)
    (hv : offDiagonalMass p = (1 : ℝ) / 8) (i : Fin 4) :
    centerPlaneBound (referencePlanes i)
        ((entryB p - entryC p) / offDiagonalMass p)
      ≤ Real.log 2 * constantMargin p u (chordMidpoint p) := by
  obtain ⟨hb, hc, hd⟩ := seam_cells h hv
  have hphi := log_two_mul_phi_le_plane h i
  rw [hd] at hphi
  rw [log_two_mul_constantMargin_center h, hv]
  unfold centerPlaneBound centerConstantScalar
  rw [← hb, ← hc]
  linarith

/-! ## The imbalance lies in the unit interval -/

private theorem imbalance_mem_Icc (h : ChordDomain p u) :
    (entryB p - entryC p) / offDiagonalMass p ∈ Set.Icc (0 : ℝ) 1 := by
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hvpos : 0 < offDiagonalMass p := by
    have : offDiagonalMass p = entryB p + entryC p := by simp [offDiagonalMass]
    rw [this]; linarith
  constructor
  · exact div_nonneg (by linarith [h.offDiagonal_le]) hvpos.le
  · rw [div_le_one hvpos]
    have : offDiagonalMass p = entryB p + entryC p := by simp [offDiagonalMass]
    rw [this]; linarith

/-! ## One of the four planes covers every imbalance -/

/-- The four intervals cover `[0, 1]`, and on each of them the plane bound is
least at an endpoint, where `PlaneEndpoints` puts it above `1/100`. -/
private theorem exists_plane_gt (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin 4, (1 : ℝ) / 100 < centerPlaneBound (referencePlanes i) z := by
  obtain ⟨hz0, hz1⟩ := hz
  rcases le_or_gt z (1 / 3) with h13 | h13
  · refine ⟨0, ?_⟩
    have hm := (centerPlaneBound_concaveOn (referencePlanes 0)).min_le_of_mem_Icc
      (by norm_num) (by norm_num) ⟨hz0, h13⟩
    obtain ⟨ha, hb⟩ := centerPlaneBound_endpoints_one
    simp only [min_def] at hm
    split at hm <;> linarith
  rcases le_or_gt z (2 / 3) with h23 | h23
  · refine ⟨1, ?_⟩
    have hm := (centerPlaneBound_concaveOn (referencePlanes 1)).min_le_of_mem_Icc
      (by norm_num) (by norm_num) ⟨h13.le, h23⟩
    obtain ⟨ha, hb⟩ := centerPlaneBound_endpoints_two
    simp only [min_def] at hm
    split at hm <;> linarith
  rcases le_or_gt z (19 / 20) with h1920 | h1920
  · refine ⟨2, ?_⟩
    have hm := (centerPlaneBound_concaveOn (referencePlanes 2)).min_le_of_mem_Icc
      (by norm_num) (by norm_num) ⟨h23.le, h1920⟩
    obtain ⟨ha, hb⟩ := centerPlaneBound_endpoints_three
    simp only [min_def] at hm
    split at hm <;> linarith
  · refine ⟨3, ?_⟩
    have hm := (centerPlaneBound_concaveOn (referencePlanes 3)).min_le_of_mem_Icc
      (by norm_num) (by norm_num) ⟨h1920.le, hz1⟩
    obtain ⟨ha, hb⟩ := centerPlaneBound_endpoints_four
    simp only [min_def] at hm
    split at hm <;> linarith

/-! ## The seam bound -/

/-- **The constant margin at the centre exceeds one hundredth on the seam.**
For a chord domain whose off-diagonal mass is exactly `1/8`, the constant
code's margin at the centre of the contact chord satisfies
`1/100 < Real.log 2 * constantMargin p u (chordMidpoint p)`.

The page proves the same statement with `1/200` in place of `1/100`, by a route
that uses no reference plane. -/
theorem seam_constantMargin_center_gt (h : ChordDomain p u)
    (hv : offDiagonalMass p = (1 : ℝ) / 8) :
    (1 : ℝ) / 100 < Real.log 2 * constantMargin p u (chordMidpoint p) := by
  obtain ⟨i, hi⟩ := exists_plane_gt (imbalance_mem_Icc h)
  have hle := centerPlaneBound_le_constantMargin h hv i
  linarith

end StochasticToDeterministicLatents.Binary
