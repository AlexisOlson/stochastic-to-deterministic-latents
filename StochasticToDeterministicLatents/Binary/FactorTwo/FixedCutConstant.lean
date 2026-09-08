import StochasticToDeterministicLatents.Binary.FactorTwo.Strip
import StochasticToDeterministicLatents.Binary.FactorTwo.ChordScalars
import StochasticToDeterministicLatents.Binary.FactorTwo.ConstantRatio

/-!
# The constant margin at the fixed cut

This module carries the constant margin from the chord to the scalar bound of
`ConstantRatio`.  Three things happen here.

The chord's potential `Real.log 2 * Phi` is written as eight `xLogX` terms in
the small diagonal mass `d`, as `chordPotential`.  Its derivative vanishes at
the contact mass, which is the root identity of `Strip`, and its second
derivative is bounded below on the small half of the chord; so the potential's
decrease from the contact mass to the fixed cut is at most an explicit signed
combination of three elementary remainders, taken at the shifts zero,
`entryB p` and `entryC p`.  That is `chordPotential_remainder`.

The mutual information at the fixed cut is written out in the same terms, as
`log_two_mul_mutualInfo_fixedCut`, and the combination that appears in the
constant margin is `constantRatioTerm_affine`: after dividing by the contact
mass, the two cell terms of the estimate are exactly
`constantRatioTerm (entryB p / D)` and `constantRatioTerm (entryC p / D)`,
which is where the scalar bound enters.

Nothing here proves the estimate itself; a later module assembles these.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-! ## The chord's potential in the small diagonal mass -/

/-- The chord's potential `Real.log 2 * Phi`, as a function of the small
diagonal mass `d`.  The chord point is at `diagonalMass p - d`. -/
noncomputable def chordPotential (p : RealTable) (d : ℝ) : ℝ :=
  2 * (xLogX (diagonalMass p - d + entryB p) + xLogX (entryC p + d)
      + xLogX (diagonalMass p - d + entryC p) + xLogX (entryB p + d))
    - 3 * (xLogX (diagonalMass p - d) + xLogX (entryB p) + xLogX (entryC p) + xLogX d)

private theorem log_two_mul_phi_chordAt (h : ChordDomain p u) {d : ℝ}
    (hd : diagonalMass p - d ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * Phi (chordAt p (diagonalMass p - d)) = chordPotential p d := by
  have hexp : Real.log 2 * Phi (chordAt p (diagonalMass p - d))
      = 3 * (Real.log 2 * entropy (chordAt p (diagonalMass p - d)))
        - 2 * (Real.log 2 * entropy (stoch_to_det.mX (chordAt p (diagonalMass p - d))))
        - 2 * (Real.log 2 * entropy (stoch_to_det.mY (chordAt p (diagonalMass p - d)))) := by
    show Real.log 2 * stoch_to_det.Phi (chordAt p (diagonalMass p - d)) = _
    rw [stoch_to_det.Phi]
    ring
  rw [hexp, log_two_mul_entropy_chordAt h hd, log_two_mul_entropy_marginalX_chordAt h hd,
    log_two_mul_entropy_marginalY_chordAt h hd, chordPotential,
    show diagonalMass p - (diagonalMass p - d) = d from by ring]
  ring

theorem chordPotential_chordBottom (h : ChordDomain p u) :
    chordPotential p (chordBottom p u) = Real.log 2 * Phi (contactAt p u) := by
  have hsub : diagonalMass p - chordBottom p u = chordTop p u := by
    linarith [chordTop_add_chordBottom (p := p) (u := u)]
  have hmem : diagonalMass p - chordBottom p u ∈ Set.Icc (chordMidpoint p) (chordTop p u) := by
    rw [hsub]
    exact ⟨(chordMidpoint_lt_chordTop h).le, le_rfl⟩
  rw [← log_two_mul_phi_chordAt h hmem, hsub, chordAt_chordTop]

/-- The constant margin along the chord, in the small diagonal mass. -/
theorem log_two_mul_constantMargin_potential (h : ChordDomain p u) {d : ℝ}
    (hd : diagonalMass p - d ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * constantMargin p u (diagonalMass p - d)
      = Real.log 2 * (Psi (chordAt p (diagonalMass p - d)) - Phi (chordAt p (diagonalMass p - d)))
        + 2 * (chordPotential p d - chordPotential p (chordBottom p u)) := by
  rw [chordPotential_chordBottom h, ← log_two_mul_phi_chordAt h hd,
    constantMargin_eq_psi_add_phi]
  ring

/-! ## The potential's calculus -/

/-- The potential's derivative in the small diagonal mass. -/
private noncomputable def potentialDeriv (p : RealTable) (d : ℝ) : ℝ :=
  -3 * Real.log d + 3 * Real.log (diagonalMass p - d)
    - 2 * Real.log (diagonalMass p - d + entryB p)
    - 2 * Real.log (diagonalMass p - d + entryC p)
    + 2 * Real.log (d + entryB p) + 2 * Real.log (d + entryC p)

/-- The potential's second derivative in the small diagonal mass. -/
private noncomputable def potentialDeriv2 (p : RealTable) (d : ℝ) : ℝ :=
  -(3 / d) - 3 / (diagonalMass p - d) + 2 / (d + entryB p) + 2 / (d + entryC p)
    + 2 / (diagonalMass p - d + entryB p) + 2 / (diagonalMass p - d + entryC p)

private theorem chordPotential_hasDerivAt (h : ChordDomain p u) {d : ℝ}
    (hd : 0 < d) (hds : d < diagonalMass p) :
    HasDerivAt (chordPotential p) (potentialDeriv p d) d := by
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have ha : 0 < diagonalMass p - d := sub_pos.mpr hds
  have hd0 := Real.hasDerivAt_mul_log hd.ne'
  have ha0 := (Real.hasDerivAt_mul_log ha.ne').comp d
    ((hasDerivAt_const d (diagonalMass p)).sub (hasDerivAt_id d))
  have hab := (Real.hasDerivAt_mul_log (add_pos ha hb).ne').comp d
    (((hasDerivAt_const d (diagonalMass p)).sub (hasDerivAt_id d)).add_const (entryB p))
  have hac := (Real.hasDerivAt_mul_log (add_pos ha hc).ne').comp d
    (((hasDerivAt_const d (diagonalMass p)).sub (hasDerivAt_id d)).add_const (entryC p))
  have hdb := (Real.hasDerivAt_mul_log (add_pos hb hd).ne').comp d
    ((hasDerivAt_const d (entryB p)).add (hasDerivAt_id d))
  have hdc := (Real.hasDerivAt_mul_log (add_pos hc hd).ne').comp d
    ((hasDerivAt_const d (entryC p)).add (hasDerivAt_id d))
  have h2 := ((hab.add hdc).add hac).add hdb
  have h3 := ((ha0.add (hasDerivAt_const d (xLogX (entryB p)))).add
    (hasDerivAt_const d (xLogX (entryC p)))).add hd0
  have hraw := (h2.const_mul 2).sub (h3.const_mul 3)
  change HasDerivAt (chordPotential p) _ d at hraw
  refine hraw.congr_deriv ?_
  unfold potentialDeriv
  field_simp
  ring_nf

private theorem potentialDeriv_hasDerivAt (h : ChordDomain p u) {d : ℝ}
    (hd : 0 < d) (hds : d < diagonalMass p) :
    HasDerivAt (potentialDeriv p) (potentialDeriv2 p d) d := by
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have ha : 0 < diagonalMass p - d := sub_pos.mpr hds
  have hdt := Real.hasDerivAt_log hd.ne'
  have hda := (Real.hasDerivAt_log ha.ne').comp d
    ((hasDerivAt_const d (diagonalMass p)).sub (hasDerivAt_id d))
  have hdab := (Real.hasDerivAt_log (add_pos ha hb).ne').comp d
    (((hasDerivAt_const d (diagonalMass p)).sub (hasDerivAt_id d)).add_const (entryB p))
  have hdac := (Real.hasDerivAt_log (add_pos ha hc).ne').comp d
    (((hasDerivAt_const d (diagonalMass p)).sub (hasDerivAt_id d)).add_const (entryC p))
  have hdtb := (Real.hasDerivAt_log (add_pos hd hb).ne').comp d
    ((hasDerivAt_id d).add_const (entryB p))
  have hdtc := (Real.hasDerivAt_log (add_pos hd hc).ne').comp d
    ((hasDerivAt_id d).add_const (entryC p))
  have hraw := (((((hdt.const_mul (-3)).add (hda.const_mul 3)).sub
    (hdab.const_mul 2)).sub (hdac.const_mul 2)).add (hdtb.const_mul 2)).add
    (hdtc.const_mul 2)
  change HasDerivAt (potentialDeriv p) _ d at hraw
  refine hraw.congr_deriv ?_
  unfold potentialDeriv2
  field_simp
  ring

private theorem potentialDeriv_chordBottom (h : ChordDomain p u) :
    potentialDeriv p (chordBottom p u) = 0 := by
  have hD := chordBottom_pos h
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hA : 0 < chordTop p u := by
    have hmid := chordMidpoint_lt_chordTop h
    have hs0 := diagonalMass_pos h.fullSupport
    rw [chordMidpoint] at hmid
    linarith
  have hs : diagonalMass p - chordBottom p u = chordTop p u := by
    linarith [chordTop_add_chordBottom (p := p) (u := u)]
  have hid := contactEnds_log_eq h
  rw [Real.log_mul (add_pos hD hb).ne' (add_pos hD hc).ne',
    Real.log_mul (add_pos hA hb).ne' (add_pos hA hc).ne'] at hid
  rw [potentialDeriv, hs]
  linarith

private theorem potentialDeriv2_ge (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) {d : ℝ} (hdm : d ≤ chordMidpoint p) :
    0 ≤ potentialDeriv2 p d + 3 / d - 2 / (d + entryB p) - 2 / (d + entryC p) := by
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hvpos := offDiagonalMass_pos h.fullSupport
  have hs := diagonalMass_add_offDiagonalMass h.isPMF
  have ha : 0 < diagonalMass p - d := by
    rw [chordMidpoint] at hdm
    nlinarith
  have hav : 3 * offDiagonalMass p / 2 ≤ diagonalMass p - d := by
    rw [chordMidpoint] at hdm
    nlinarith
  have hsum : entryB p + entryC p = offDiagonalMass p := rfl
  have hrec1 : 8 / (2 * (diagonalMass p - d) + offDiagonalMass p)
      ≤ 2 / (diagonalMass p - d + entryB p) + 2 / (diagonalMass p - d + entryC p) := by
    have hp1 : 0 < diagonalMass p - d + entryB p := add_pos ha hb
    have hp2 : 0 < diagonalMass p - d + entryC p := add_pos ha hc
    have hp3 : 0 < 2 * (diagonalMass p - d) + offDiagonalMass p := by positivity
    have heq : 2 / (diagonalMass p - d + entryB p) + 2 / (diagonalMass p - d + entryC p) =
        (2 * (diagonalMass p - d + entryC p) + 2 * (diagonalMass p - d + entryB p)) /
          ((diagonalMass p - d + entryB p) * (diagonalMass p - d + entryC p)) := by
      field_simp
    rw [heq]
    apply (div_le_div_iff₀ hp3 (mul_pos hp1 hp2)).2
    rw [← hsum]
    nlinarith [sq_nonneg (entryB p - entryC p)]
  have hrec2 : 3 / (diagonalMass p - d) ≤ 8 / (2 * (diagonalMass p - d) + offDiagonalMass p) := by
    have hp3 : 0 < 2 * (diagonalMass p - d) + offDiagonalMass p := by positivity
    apply (div_le_div_iff₀ ha hp3).2
    nlinarith
  unfold potentialDeriv2
  linarith

/-! ## The elementary remainder -/

/-- One elementary remainder: the Kullback term of a mass moving from `D` to
`d`, shifted by `j`. -/
noncomputable def remainderTerm (D d j : ℝ) : ℝ :=
  (d + j) * Real.log ((d + j) / (D + j)) - d + D

private theorem remainderTerm_self (D j : ℝ) (hD : 0 < D + j) : remainderTerm D D j = 0 := by
  rw [remainderTerm, div_self hD.ne', Real.log_one]
  ring

private theorem remainderTerm_hasDerivAt {D d j : ℝ} (hD : 0 < D + j) (hd : 0 < d + j) :
    HasDerivAt (fun d => remainderTerm D d j) (Real.log ((d + j) / (D + j))) d := by
  have harg : HasDerivAt (fun x : ℝ => (x + j) / (D + j)) (1 / (D + j)) d := by
    simpa [one_div] using ((hasDerivAt_id d).add_const j).div_const (D + j)
  have hlog := (Real.hasDerivAt_log (div_ne_zero hd.ne' hD.ne')).comp d harg
  have hprod := ((hasDerivAt_id d).add_const j).mul hlog
  have hraw := (hprod.sub (hasDerivAt_id d)).add_const D
  change HasDerivAt (fun d => remainderTerm D d j) _ d at hraw
  refine hraw.congr_deriv ?_
  simp only [Function.comp_apply, id_eq]
  field_simp
  ring

private theorem ratioLog_hasDerivAt {D d j : ℝ} (hD : 0 < D + j) (hd : 0 < d + j) :
    HasDerivAt (fun x => Real.log ((x + j) / (D + j))) (1 / (d + j)) d := by
  have harg : HasDerivAt (fun x : ℝ => (x + j) / (D + j)) (1 / (D + j)) d := by
    simpa [one_div] using ((hasDerivAt_id d).add_const j).div_const (D + j)
  have hlog := (Real.hasDerivAt_log (div_ne_zero hd.ne' hD.ne')).comp d harg
  have heq : ((d + j) / (D + j))⁻¹ * (1 / (D + j)) = 1 / (d + j) := by
    field_simp
  change HasDerivAt (Real.log ∘ fun x : ℝ => (x + j) / (D + j)) (1 / (d + j)) d
  rw [← heq]
  exact hlog

/-- The slope of the gap between the potential's decrease and the combination
of three elementary remainders. -/
private noncomputable def remainderSlope (p : RealTable) (D d : ℝ) : ℝ :=
  -potentialDeriv p d - 3 * Real.log ((d + 0) / (D + 0))
    + 2 * Real.log ((d + entryB p) / (D + entryB p))
    + 2 * Real.log ((d + entryC p) / (D + entryC p))

private theorem remainderGap_antitoneOn (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    AntitoneOn (fun d => chordPotential p (chordBottom p u) - chordPotential p d
        - 3 * remainderTerm (chordBottom p u) d 0
        + 2 * remainderTerm (chordBottom p u) d (entryB p)
        + 2 * remainderTerm (chordBottom p u) d (entryC p))
      (Set.Icc (chordBottom p u) (3 * chordBottom p u)) := by
  have hgeom := fixedCut_mem_chord h hv
  have hD := chordBottom_pos h
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have h3mid : 3 * chordBottom p u < chordMidpoint p := by
    have hcut := hgeom.1
    rw [fixedCut, chordMidpoint] at hcut
    rw [chordMidpoint]
    linarith
  have h3s : 3 * chordBottom p u < diagonalMass p := by
    refine lt_trans h3mid ?_
    rw [chordMidpoint]
    exact half_lt_self (diagonalMass_pos h.fullSupport)
  have hslopeDeriv : ∀ d ∈ Set.Icc (chordBottom p u) (3 * chordBottom p u),
      HasDerivAt (remainderSlope p (chordBottom p u))
        (-potentialDeriv2 p d - 3 / d + 2 / (d + entryB p) + 2 / (d + entryC p)) d := by
    intro d hdmem
    have hd : 0 < d := lt_of_lt_of_le hD hdmem.1
    have hds : d < diagonalMass p := lt_of_le_of_lt hdmem.2 h3s
    have hqb := ratioLog_hasDerivAt (D := chordBottom p u) (d := d) (j := entryB p)
      (add_pos hD hb) (add_pos hd hb)
    have hqc := ratioLog_hasDerivAt (D := chordBottom p u) (d := d) (j := entryC p)
      (add_pos hD hc) (add_pos hd hc)
    have hq0 := ratioLog_hasDerivAt (D := chordBottom p u) (d := d) (j := 0)
      (by simpa using hD) (by simpa using hd)
    have hout := ((((potentialDeriv_hasDerivAt h hd hds).neg).sub
      (hq0.const_mul 3)).add (hqb.const_mul 2)).add (hqc.const_mul 2)
    change HasDerivAt (remainderSlope p (chordBottom p u)) _ d at hout
    refine hout.congr_deriv ?_
    simp only [add_zero]
    ring
  have hslopeNonpos : ∀ d ∈ Set.Icc (chordBottom p u) (3 * chordBottom p u),
      -potentialDeriv2 p d - 3 / d + 2 / (d + entryB p) + 2 / (d + entryC p) ≤ 0 := by
    intro d hdmem
    have hd : 0 < d := lt_of_lt_of_le hD hdmem.1
    have hdmid : d ≤ chordMidpoint p := le_trans hdmem.2 h3mid.le
    linarith [potentialDeriv2_ge h hv hdmid]
  have hslopeAnti : AntitoneOn (remainderSlope p (chordBottom p u))
      (Set.Icc (chordBottom p u) (3 * chordBottom p u)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · intro d hdmem
      exact (hslopeDeriv d hdmem).continuousAt.continuousWithinAt
    · intro d hdmem
      exact (hslopeDeriv d (interior_subset hdmem)).hasDerivWithinAt
    · intro d hdmem
      exact hslopeNonpos d (interior_subset hdmem)
  have hslopeD : remainderSlope p (chordBottom p u) (chordBottom p u) = 0 := by
    rw [remainderSlope, potentialDeriv_chordBottom h]
    simp [hD.ne', (add_pos hD hb).ne', (add_pos hD hc).ne']
  have hslopeLe : ∀ d ∈ Set.Icc (chordBottom p u) (3 * chordBottom p u),
      remainderSlope p (chordBottom p u) d ≤ 0 := by
    intro d hdmem
    rw [← hslopeD]
    exact hslopeAnti (Set.left_mem_Icc.mpr (by linarith)) hdmem hdmem.1
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := remainderSlope p (chordBottom p u)) (convex_Icc _ _)
  · intro d hdmem
    have hd : 0 < d := lt_of_lt_of_le hD hdmem.1
    have hds : d < diagonalMass p := lt_of_le_of_lt hdmem.2 h3s
    exact ((((((chordPotential_hasDerivAt h hd hds).neg).const_add
      (chordPotential p (chordBottom p u))).sub
      ((remainderTerm_hasDerivAt (D := chordBottom p u) (d := d) (j := 0)
        (by simpa using hD) (by simpa using hd)).const_mul 3)).add
      ((remainderTerm_hasDerivAt (D := chordBottom p u) (d := d) (j := entryB p)
        (add_pos hD hb) (add_pos hd hb)).const_mul 2)).add
      ((remainderTerm_hasDerivAt (D := chordBottom p u) (d := d) (j := entryC p)
        (add_pos hD hc) (add_pos hd hc)).const_mul 2)).continuousAt.continuousWithinAt
  · intro d hdmem
    have hdI := interior_subset hdmem
    have hd : 0 < d := lt_of_lt_of_le hD hdI.1
    have hds : d < diagonalMass p := lt_of_le_of_lt hdI.2 h3s
    have hder := (((((chordPotential_hasDerivAt h hd hds).neg).const_add
      (chordPotential p (chordBottom p u))).sub
      ((remainderTerm_hasDerivAt (D := chordBottom p u) (d := d) (j := 0)
        (by simpa using hD) (by simpa using hd)).const_mul 3)).add
      ((remainderTerm_hasDerivAt (D := chordBottom p u) (d := d) (j := entryB p)
        (add_pos hD hb) (add_pos hd hb)).const_mul 2)).add
      ((remainderTerm_hasDerivAt (D := chordBottom p u) (d := d) (j := entryC p)
        (add_pos hD hc) (add_pos hd hc)).const_mul 2)
    refine (hder.congr_deriv ?_).hasDerivWithinAt
    rw [remainderSlope]
  · intro d hdmem
    exact hslopeLe d (interior_subset hdmem)

/-- The potential's decrease from the contact mass to the fixed cut is at most
a signed combination of the three elementary remainders. -/
theorem chordPotential_remainder (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    chordPotential p (chordBottom p u) - chordPotential p (3 * chordBottom p u)
      ≤ 3 * remainderTerm (chordBottom p u) (3 * chordBottom p u) 0
        - 2 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryB p)
        - 2 * remainderTerm (chordBottom p u) (3 * chordBottom p u) (entryC p) := by
  have hD := chordBottom_pos h
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hanti := remainderGap_antitoneOn h hv
  have hle := hanti (Set.left_mem_Icc.mpr (by linarith))
    (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
  simp only at hle
  rw [remainderTerm_self _ _ (by simpa using hD), remainderTerm_self _ _ (add_pos hD hb),
    remainderTerm_self _ _ (add_pos hD hc)] at hle
  linarith

/-! ## The mutual information at the fixed cut -/

/-- Binary entropy in natural-log units. -/
noncomputable def binaryEntropyNat (d : ℝ) : ℝ := -xLogX d - xLogX (1 - d)

/-- The information one off-diagonal cell carries against a diagonal mass. -/
noncomputable def pairInfo (x y : ℝ) : ℝ := xLogX (x + y) - xLogX x - xLogX y

/-- The mutual information at the fixed cut, in the same terms as the
potential's increment. -/
theorem log_two_mul_mutualInfo_fixedCut (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    Real.log 2 * (Psi (chordAt p (fixedCut p u)) - Phi (chordAt p (fixedCut p u)))
      = binaryEntropyNat (3 * chordBottom p u)
        - pairInfo (3 * chordBottom p u) (entryB p)
        - pairInfo (3 * chordBottom p u) (entryC p)
        + cornerInfo (fixedCut p u) (entryB p) (entryC p) := by
  have hcut := fixedCut_mem_chord h hv
  have hmem : fixedCut p u ∈ Set.Icc (chordMidpoint p) (chordTop p u) := ⟨hcut.1.le, hcut.2.le⟩
  have hexp : Real.log 2 * (Psi (chordAt p (fixedCut p u)) - Phi (chordAt p (fixedCut p u)))
      = Real.log 2 * entropy (stoch_to_det.mX (chordAt p (fixedCut p u)))
        + Real.log 2 * entropy (stoch_to_det.mY (chordAt p (fixedCut p u)))
        - Real.log 2 * entropy (chordAt p (fixedCut p u)) := by
    show Real.log 2 * (stoch_to_det.Psi (chordAt p (fixedCut p u))
      - stoch_to_det.Phi (chordAt p (fixedCut p u))) = _
    rw [stoch_to_det.Psi, stoch_to_det.Phi]
    ring
  have hs : diagonalMass p - fixedCut p u = 3 * chordBottom p u := by
    rw [fixedCut]
    ring
  have htot := diagonalMass_add_offDiagonalMass h.isPMF
  have hone : 1 - 3 * chordBottom p u = fixedCut p u + entryB p + entryC p := by
    rw [fixedCut, offDiagonalMass] at *
    linarith
  rw [hexp, log_two_mul_entropy_chordAt h hmem, log_two_mul_entropy_marginalX_chordAt h hmem,
    log_two_mul_entropy_marginalY_chordAt h hmem, binaryEntropyNat, pairInfo, pairInfo,
    cornerInfo, hs, hone,
    show entryB p + 3 * chordBottom p u = 3 * chordBottom p u + entryB p from by ring,
    show entryC p + 3 * chordBottom p u = 3 * chordBottom p u + entryC p from by ring]
  ring

/-- The corner information of three positive cells is positive. -/
theorem cornerInfo_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < cornerInfo a b c :=
  lt_of_lt_of_le (by positivity) (cornerInfo_bounds ha hb hc).1

/-- A tangent bound on the binary entropy at a small mass. -/
theorem binaryEntropyNat_ge {d : ℝ} (hd1 : d < 1) :
    d * (-Real.log d + 1 - d) ≤ binaryEntropyNat d := by
  have hp : 0 < 1 - d := sub_pos.mpr hd1
  have hl := Real.log_le_sub_one_of_pos hp
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  unfold binaryEntropyNat xLogX
  nlinarith [hm]

/-! ## Where the scalar bound enters -/

/-- The estimate's cell terms, divided by the contact mass, are two copies of
the constant margin's ratio term. -/
theorem constantRatioTerm_affine {D b c : ℝ} (hD : 0 < D) (hb : 0 < b) (hc : 0 < c) :
    (-pairInfo (3 * D) b - pairInfo (3 * D) c - 6 * remainderTerm D (3 * D) 0
        + 4 * remainderTerm D (3 * D) b + 4 * remainderTerm D (3 * D) c) / D
      = constantRatioTerm (b / D) + constantRatioTerm (c / D)
        - 6 * Real.log (1 + b / D) - 6 * Real.log (1 + c / D) - 12 * Real.log 3 - 4 := by
  have hDn : D ≠ 0 := hD.ne'
  have hbn : b ≠ 0 := hb.ne'
  have hcn : c ≠ 0 := hc.ne'
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hDb : D + b ≠ 0 := (add_pos hD hb).ne'
  have hDc : D + c ≠ 0 := (add_pos hD hc).ne'
  have h3Db : 3 * D + b ≠ 0 := (add_pos (mul_pos (by norm_num) hD) hb).ne'
  have h3Dc : 3 * D + c ≠ 0 := (add_pos (mul_pos (by norm_num) hD) hc).ne'
  have h1b : 1 + b / D ≠ 0 := by positivity
  have h1c : 1 + c / D ≠ 0 := by positivity
  have h3b : 3 + b / D ≠ 0 := by positivity
  have h3c : 3 + c / D ≠ 0 := by positivity
  have l3D : Real.log (3 * D) = Real.log 3 + Real.log D := Real.log_mul h3 hDn
  have lb : Real.log b = Real.log D + Real.log (b / D) := by
    rw [Real.log_div hbn hDn]
    ring
  have lc : Real.log c = Real.log D + Real.log (c / D) := by
    rw [Real.log_div hcn hDn]
    ring
  have l3Db : Real.log (3 * D + b) = Real.log D + Real.log (3 + b / D) := by
    rw [show 3 * D + b = D * (3 + b / D) by field_simp, Real.log_mul hDn h3b]
  have l3Dc : Real.log (3 * D + c) = Real.log D + Real.log (3 + c / D) := by
    rw [show 3 * D + c = D * (3 + c / D) by field_simp, Real.log_mul hDn h3c]
  have lDb : Real.log (D + b) = Real.log D + Real.log (1 + b / D) := by
    rw [show D + b = D * (1 + b / D) by field_simp, Real.log_mul hDn h1b]
  have lDc : Real.log (D + c) = Real.log D + Real.log (1 + c / D) := by
    rw [show D + c = D * (1 + c / D) by field_simp, Real.log_mul hDn h1c]
  have lr0 : Real.log ((3 * D + 0) / (D + 0)) = Real.log 3 := by
    congr 1
    field_simp
    ring
  have lrb : Real.log ((3 * D + b) / (D + b)) =
      Real.log (3 + b / D) - Real.log (1 + b / D) := by
    rw [Real.log_div h3Db hDb, l3Db, lDb]
    ring
  have lrc : Real.log ((3 * D + c) / (D + c)) =
      Real.log (3 + c / D) - Real.log (1 + c / D) := by
    rw [Real.log_div h3Dc hDc, l3Dc, lDc]
    ring
  unfold pairInfo xLogX remainderTerm constantRatioTerm
  rw [l3D, lb, lc, l3Db, l3Dc, lr0, lrb, lrc]
  field_simp
  ring

end StochasticToDeterministicLatents.Binary
