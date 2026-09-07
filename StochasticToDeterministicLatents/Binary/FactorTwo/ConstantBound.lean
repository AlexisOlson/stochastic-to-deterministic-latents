import StochasticToDeterministicLatents.Binary.FactorTwo.FixedCutConstant

/-!
# The constant margin's lower bound at the fixed cut

This module assembles `FixedCutConstant` into the estimate the gates consume:
at a law whose off-diagonal mass is at most an eighth, the constant code's
margin is strictly positive at the fixed cut, with a margin proportional to
the contact mass.

The chain is arithmetic once the identities are in place.  The potential's
decrease from the contact mass to the cut is bounded by three elementary
remainders, the mutual information at the cut is written in the same terms,
and the corner information is positive, so the margin exceeds an explicit
expression in the two cell ratios.  Dividing by the contact mass leaves two
copies of `constantRatioTerm`, each above `19/2`, against three logarithms
that are small when the off-diagonal mass is: the contact mass is below a
sixteenth, so the upper contact is above thirteen sixteenths and its two cell
ratios are together below `2/13`.  Nineteen against `15 log 3` and change
leaves `3 * chordBottom p u / 208 < Real.log 2 * constantMargin p u
(fixedCut p u)`, which is `fixedCut_constantMargin_gt`.  It is stated
multiplied through by `Real.log 2` so that no statement of the public tree
divides by it.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-- The contact identity of `Strip`, rearranged into the cell ratios at the
two ends of the chord.  This is what turns the estimate's `- 3 log D` into
quantities carried by the upper contact, where the off-diagonal bound bites. -/
private theorem contactRatio_log_eq (h : ChordDomain p u) :
    -Real.log (chordBottom p u)
      = 2 * Real.log (1 + entryB p / chordBottom p u)
        + 2 * Real.log (1 + entryC p / chordBottom p u)
        - Real.log (chordTop p u)
        - 2 * Real.log (1 + entryB p / chordTop p u)
        - 2 * Real.log (1 + entryC p / chordTop p u) := by
  have hD := chordBottom_pos h
  have hA : 0 < chordTop p u :=
    lt_trans (by linarith [chordBottom_lt_chordMidpoint h]) (chordMidpoint_lt_chordTop h)
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have lDb : Real.log (chordBottom p u + entryB p)
      = Real.log (chordBottom p u) + Real.log (1 + entryB p / chordBottom p u) := by
    rw [show chordBottom p u + entryB p
        = chordBottom p u * (1 + entryB p / chordBottom p u) by field_simp,
      Real.log_mul hD.ne' (by positivity : 1 + entryB p / chordBottom p u ≠ 0)]
  have lDc : Real.log (chordBottom p u + entryC p)
      = Real.log (chordBottom p u) + Real.log (1 + entryC p / chordBottom p u) := by
    rw [show chordBottom p u + entryC p
        = chordBottom p u * (1 + entryC p / chordBottom p u) by field_simp,
      Real.log_mul hD.ne' (by positivity : 1 + entryC p / chordBottom p u ≠ 0)]
  have lAb : Real.log (chordTop p u + entryB p)
      = Real.log (chordTop p u) + Real.log (1 + entryB p / chordTop p u) := by
    rw [show chordTop p u + entryB p
        = chordTop p u * (1 + entryB p / chordTop p u) by field_simp,
      Real.log_mul hA.ne' (by positivity : 1 + entryB p / chordTop p u ≠ 0)]
  have lAc : Real.log (chordTop p u + entryC p)
      = Real.log (chordTop p u) + Real.log (1 + entryC p / chordTop p u) := by
    rw [show chordTop p u + entryC p
        = chordTop p u * (1 + entryC p / chordTop p u) by field_simp,
      Real.log_mul hA.ne' (by positivity : 1 + entryC p / chordTop p u ≠ 0)]
  have ht := contactEnds_log_eq h
  rw [Real.log_mul (add_pos hD hb).ne' (add_pos hD hc).ne',
    Real.log_mul (add_pos hA hb).ne' (add_pos hA hc).ne', lDb, lDc, lAb, lAc] at ht
  linarith

/-- The margin at the cut, divided by the contact mass, exceeds two copies of
`constantRatioTerm` less an explicit remainder in the upper contact. -/
private theorem constantMargin_fixedCut_scalar (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    constantRatioTerm (entryB p / chordBottom p u)
        + constantRatioTerm (entryC p / chordBottom p u)
        - 15 * Real.log 3 - 1 - 9 * chordBottom p u - 3 * Real.log (chordTop p u)
        - 6 * Real.log (1 + entryB p / chordTop p u)
        - 6 * Real.log (1 + entryC p / chordTop p u)
      < Real.log 2 * constantMargin p u (fixedCut p u) / chordBottom p u := by
  have hD := chordBottom_pos h
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hcut := fixedCut_mem_chord h hv
  have hmem : diagonalMass p - 3 * chordBottom p u
      ∈ Set.Icc (chordMidpoint p) (chordTop p u) := by
    rw [← fixedCut]
    exact ⟨hcut.1.le, hcut.2.le⟩
  have hM := log_two_mul_constantMargin_potential h hmem
  rw [← fixedCut] at hM
  have hR := chordPotential_remainder h hv
  have hI := log_two_mul_mutualInfo_fixedCut h hv
  have hmid : 0 < chordMidpoint p := by linarith [chordBottom_lt_chordMidpoint h]
  have hJ := cornerInfo_pos (lt_trans hmid hcut.1) hb hc
  have hDv := contactMass_lt_half_disagreement h hv
  have h3D1 : 3 * chordBottom p u < 1 := by linarith
  have hhn := binaryEntropyNat_ge h3D1
  have hlog3D : Real.log (3 * chordBottom p u) = Real.log 3 + Real.log (chordBottom p u) :=
    Real.log_mul (by norm_num) hD.ne'
  have hraw :
      3 * chordBottom p u * (-Real.log (3 * chordBottom p u) + 1 - 3 * chordBottom p u)
          - pairInfo (3 * chordBottom p u) (entryB p)
          - pairInfo (3 * chordBottom p u) (entryC p)
          - 6 * remainderTerm (chordBottom p u) (3 * chordBottom p u) 0
          + 4 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryB p)
          + 4 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryC p)
        < Real.log 2 * constantMargin p u (fixedCut p u) := by
    linarith
  have hsplit :
      (3 * chordBottom p u * (-Real.log (3 * chordBottom p u) + 1 - 3 * chordBottom p u)
            - pairInfo (3 * chordBottom p u) (entryB p)
            - pairInfo (3 * chordBottom p u) (entryC p)
            - 6 * remainderTerm (chordBottom p u) (3 * chordBottom p u) 0
            + 4 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryB p)
            + 4 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryC p))
          / chordBottom p u
        = 3 * (-Real.log (3 * chordBottom p u) + 1 - 3 * chordBottom p u)
          + (-pairInfo (3 * chordBottom p u) (entryB p)
              - pairInfo (3 * chordBottom p u) (entryC p)
              - 6 * remainderTerm (chordBottom p u) (3 * chordBottom p u) 0
              + 4 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryB p)
              + 4 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryC p))
            / chordBottom p u := by
    field_simp
    ring
  have hdiv := (div_lt_div_iff_of_pos_right hD).2 hraw
  rw [hsplit, constantRatioTerm_affine hD hb hc, hlog3D] at hdiv
  linarith [contactRatio_log_eq h]

/-- Below an eighth of off-diagonal mass, the constant code's margin at the
fixed cut is bounded below by the contact mass over `208/3`, in natural-log
units.  This is the constant arm of the cut gates. -/
theorem fixedCut_constantMargin_gt (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    3 * chordBottom p u / 208 < Real.log 2 * constantMargin p u (fixedCut p u) := by
  have hD := chordBottom_pos h
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hv0 := offDiagonalMass_pos h.fullSupport
  have hone := diagonalMass_add_offDiagonalMass h.isPMF
  have hDv := contactMass_lt_half_disagreement h hv
  have hsum := chordTop_add_chordBottom (p := p) (u := u)
  have hD16 : chordBottom p u < (1 : ℝ) / 16 := by linarith
  have hA13 : (13 : ℝ) / 16 < chordTop p u := by linarith
  have hA : 0 < chordTop p u := lt_trans (by norm_num) hA13
  have hA1 : chordTop p u < 1 := by linarith
  have hlogA : Real.log (chordTop p u) < 0 := Real.log_neg hA hA1
  have hlb := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + entryB p / chordTop p u)
  have hlc := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + entryC p / chordTop p u)
  have hratio : entryB p / chordTop p u + entryC p / chordTop p u < (2 : ℝ) / 13 := by
    rw [show entryB p / chordTop p u + entryC p / chordTop p u
        = offDiagonalMass p / chordTop p u from by rw [offDiagonalMass]; ring,
      div_lt_iff₀ hA]
    linarith
  have hlogs : Real.log (1 + entryB p / chordTop p u)
      + Real.log (1 + entryC p / chordTop p u) < (2 : ℝ) / 13 := by
    rw [show (1 + entryB p / chordTop p u) - 1 = entryB p / chordTop p u by ring] at hlb
    rw [show (1 + entryC p / chordTop p u) - 1 = entryC p / chordTop p u by ring] at hlc
    linarith
  have hVb := constantRatioTerm_gt (div_pos hb hD)
  have hVc := constantRatioTerm_gt (div_pos hc hD)
  have hquot : (3 : ℝ) / 208
      < Real.log 2 * constantMargin p u (fixedCut p u) / chordBottom p u := by
    linarith [constantMargin_fixedCut_scalar h hv, log_three_bounds.2]
  linarith [(lt_div_iff₀ hD).mp hquot]

end StochasticToDeterministicLatents.Binary
