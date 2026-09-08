/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  One theorem of the private
working material is dropped as dead, and a second private module's content is
not carried over at all: `Binary/FactorTwo/Center.lean` already states it.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterLaws
import StochasticToDeterministicLatents.Binary.FactorTwo.Center

/-!
# The dictionary between a chord law and the ray

`Center` writes the two margins at the chord's midpoint as functions of the
off-diagonal mass and the imbalance; `CenterRay` runs a family of laws of fixed
imbalance out along a radius.  This module is the dictionary between them.

Its first result reads a chord law in the ray's coordinates: the law's
imbalance lies in `[0, 1)`, its off-diagonal mass over its top root lies
strictly between zero and the critical radius, and at that pair the ray's root,
its off-diagonal mass and its law are the chord law's own root, its own
off-diagonal mass, and the chord law recentred at its midpoint.

The other two put the two margins in the ray's coordinates alone.
`rayConstantScalar` and `raySingletonScalar` are functions of the imbalance and
the radius, with no law in them; read at a chord law's coordinates, they are
that law's two margins at the midpoint.

Nothing here differentiates anything, and nothing here bounds a margin.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-! ## The two margins as functions of the ray -/

/-- The constant code's margin at the midpoint of the ray law of imbalance `z`
and radius `r`, as a function of those two alone.  The contact's `Phi` in
natural-log units is minus the chart's height, by
`log_two_mul_phi_contact_chart`. -/
noncomputable def rayConstantScalar (z r : ℝ) : ℝ :=
  centerConstantScalar (rayMass z r) z
    (-chartHeight ((1 + z) * r / 2) ((1 - z) * r / 2))

/-- The isolating code's margin at the midpoint of that same law. -/
noncomputable def raySingletonScalar (z r : ℝ) : ℝ :=
  centerSingletonScalar (rayMass z r) z
    (-chartHeight ((1 + z) * r / 2) ((1 - z) * r / 2))

/-! ## A chord law, read in the ray's coordinates -/

/-- **Every chord law is a point of the ray family.**  Its imbalance and its
off-diagonal mass over its top root are a valid pair, and there the ray's root,
off-diagonal mass and law are the chord law's own root, its own off-diagonal
mass, and the chord law recentred at its midpoint. -/
theorem chordDomain_rayCoordinates (h : ChordDomain p u) :
    (entryB p - entryC p) / offDiagonalMass p ∈ Set.Ico (0 : ℝ) 1
      ∧ offDiagonalMass p / u ∈ Set.Ioo (0 : ℝ)
          (criticalRadius ((entryB p - entryC p) / offDiagonalMass p))
      ∧ rayRoot ((entryB p - entryC p) / offDiagonalMass p)
          (offDiagonalMass p / u) = u
      ∧ rayMass ((entryB p - entryC p) / offDiagonalMass p)
          (offDiagonalMass p / u) = offDiagonalMass p
      ∧ rayLaw ((entryB p - entryC p) / offDiagonalMass p)
          (offDiagonalMass p / u) = chordAt p (chordMidpoint p) := by
  obtain ⟨_, _, hD, hu_chart⟩ := chartDomain_of_chordDomain h
  have hu : 0 < u := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hv : 0 < offDiagonalMass p := offDiagonalMass_pos h.fullSupport
  have hb : 0 < entryB p := h.fullSupport (0, 1)
  have hc : 0 < entryC p := h.fullSupport (1, 0)
  have hvdef : offDiagonalMass p = entryB p + entryC p := rfl
  have hz0 : 0 ≤ (entryB p - entryC p) / offDiagonalMass p :=
    div_nonneg (sub_nonneg.mpr h.offDiagonal_le) hv.le
  have hz1 : (entryB p - entryC p) / offDiagonalMass p < 1 := by
    rw [div_lt_one hv, hvdef]
    linarith
  have hr0 : 0 < offDiagonalMass p / u := div_pos hv hu
  have hr1 : offDiagonalMass p / u < 1 := by
    rw [div_lt_one hu]
    exact offDiagonalMass_lt_topRoot h.isPMF h.fullSupport h.topRoot
  have hsum : entryB p / u + entryC p / u = offDiagonalMass p / u := by
    rw [hvdef]
    ring
  have hk : rayProductCoeff ((entryB p - entryC p) / offDiagonalMass p)
      * (offDiagonalMass p / u) ^ 2 = entryB p / u * (entryC p / u) := by
    unfold rayProductCoeff
    rw [hvdef]
    field_simp
    ring
  have hq : 0 < 1 - offDiagonalMass p / u
      - 3 * rayProductCoeff ((entryB p - entryC p) / offDiagonalMass p)
        * (offDiagonalMass p / u) ^ 2 := by
    calc
      0 < 1 - (entryB p / u + entryC p / u)
          - 3 * (entryB p / u * (entryC p / u)) := hD.interior
      _ = 1 - offDiagonalMass p / u
          - 3 * rayProductCoeff ((entryB p - entryC p) / offDiagonalMass p)
            * (offDiagonalMass p / u) ^ 2 := by
        rw [hsum, ← hk]
        ring
  have hrc : offDiagonalMass p / u
      < criticalRadius ((entryB p - entryC p) / offDiagonalMass p) :=
    (radius_lt_criticalRadius_iff ⟨hz0, hz1⟩ hr0 hr1).2 hq
  have hU : rayRoot ((entryB p - entryC p) / offDiagonalMass p)
      (offDiagonalMass p / u) = u := by
    unfold rayRoot
    rw [hk, ← hsum, ← hu_chart]
  have hV : rayMass ((entryB p - entryC p) / offDiagonalMass p)
      (offDiagonalMass p / u) = offDiagonalMass p := by
    unfold rayMass chartOffDiagonalMass
    rw [hk, ← hsum, ← hu_chart, hsum]
    exact div_mul_cancel₀ _ hu.ne'
  refine ⟨⟨hz0, hz1⟩, ⟨hr0, hrc⟩, hU, hV, ?_⟩
  have hs := diagonalMass_add_offDiagonalMass h.isPMF
  funext a
  rcases a with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rayLaw, tableOfEntries, hV, chordAt, chordMidpoint]
  · linarith
  · field_simp [hv.ne']
    unfold offDiagonalMass entryB entryC
    ring
  · field_simp [hv.ne']
    unfold offDiagonalMass entryB entryC
    ring
  · linarith

/-! ## The two margins, in the ray's coordinates -/

private theorem rayCell_left (h : ChordDomain p u) :
    (1 + (entryB p - entryC p) / offDiagonalMass p)
        * (offDiagonalMass p / u) / 2 = entryB p / u := by
  have hv : 0 < offDiagonalMass p := offDiagonalMass_pos h.fullSupport
  have hvdef : offDiagonalMass p = entryB p + entryC p := rfl
  rw [hvdef] at hv ⊢
  field_simp
  ring

private theorem rayCell_right (h : ChordDomain p u) :
    (1 - (entryB p - entryC p) / offDiagonalMass p)
        * (offDiagonalMass p / u) / 2 = entryC p / u := by
  have hv : 0 < offDiagonalMass p := offDiagonalMass_pos h.fullSupport
  have hvdef : offDiagonalMass p = entryB p + entryC p := rfl
  rw [hvdef] at hv ⊢
  field_simp
  ring

/-- **The constant code's margin at the midpoint, in the ray's coordinates.**
-/
theorem rayConstantScalar_eq (h : ChordDomain p u) :
    rayConstantScalar ((entryB p - entryC p) / offDiagonalMass p)
        (offDiagonalMass p / u)
      = Real.log 2 * constantMargin p u (chordMidpoint p) := by
  rw [log_two_mul_constantMargin_center h, log_two_mul_phi_contact_chart h]
  unfold rayConstantScalar
  rw [(chordDomain_rayCoordinates h).2.2.2.1, rayCell_left h, rayCell_right h]

/-- **The isolating code's margin at the midpoint, in the ray's coordinates.**
-/
theorem raySingletonScalar_eq (h : ChordDomain p u) :
    raySingletonScalar ((entryB p - entryC p) / offDiagonalMass p)
        (offDiagonalMass p / u)
      = Real.log 2 * singletonMargin p u (chordMidpoint p) := by
  rw [log_two_mul_singletonMargin_center h, log_two_mul_phi_contact_chart h]
  unfold raySingletonScalar
  rw [(chordDomain_rayCoordinates h).2.2.2.1, rayCell_left h, rayCell_right h]
