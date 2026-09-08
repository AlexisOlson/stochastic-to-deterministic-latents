/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  One theorem of the private
working material is kept private here, its content surviving as half of the
coordinates theorem below.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterDictionary
import StochasticToDeterministicLatents.Binary.FactorTwo.Strip

/-!
# The seam, in the chart's radius

The seam is the locus of off-diagonal mass exactly `1 / 8`.  On it the chart's
two parameters collapse to one.  Write `r` for the radius, that is, the
off-diagonal mass over the top root.  Then the product parameter is forced to
`seamProduct r`, the root is `1 / (8 r)`, the mass is `1 / 8`, and the square
of the imbalance is `seamImbalanceSq r`.  The isolating code's margin at the
chord's midpoint is therefore a function of the radius alone, which is what
`seamSingletonScalar` names.

Every chord law of off-diagonal mass `1 / 8` has its radius in `(1 / 2, 1)`,
and the lower end of that interval is the statement that its top root lies
below `1 / 4`.

Nothing here bounds a margin and nothing here differentiates anything.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u r : ℝ}

/-! ## The seam's scalars -/

/-- The chart's product parameter along the seam, as a function of the radius
alone. -/
noncomputable def seamProduct (r : ℝ) : ℝ := (1 - r) / (1 + 7 * r)

/-- The square of the imbalance along the seam.  It is not nonnegative for
every radius; where it is, its square root is the imbalance. -/
noncomputable def seamImbalanceSq (r : ℝ) : ℝ := 1 - 4 * seamProduct r / r ^ 2

/-- The larger of the two rescaled off-diagonal cells on the seam. -/
noncomputable def seamCellB (r : ℝ) : ℝ :=
  r * (1 + Real.sqrt (seamImbalanceSq r)) / 2

/-- The smaller of the two rescaled off-diagonal cells on the seam. -/
noncomputable def seamCellC (r : ℝ) : ℝ :=
  r * (1 - Real.sqrt (seamImbalanceSq r)) / 2

/-- The isolating code's margin at the midpoint of the seam law of radius `r`,
as a function of that radius alone.  The contact's `Phi` in natural-log units
is minus the chart's height, as in `raySingletonScalar`. -/
noncomputable def seamSingletonScalar (r : ℝ) : ℝ :=
  centerSingletonScalar (1 / 8) (Real.sqrt (seamImbalanceSq r))
    (-chartHeight (seamCellB r) (seamCellC r))

/-- The centre law of off-diagonal mass `1 / 8` and imbalance `z`. -/
noncomputable def seamLaw (z : ℝ) : RealTable :=
  tableOfEntries (7 / 16) ((1 + z) / 16) ((1 - z) / 16) (7 / 16)

/-! ## The top root on the seam -/

/-- On the seam the top root lies below `1 / 4`.  This is the page's
assertion before its display (4.4); the proof evaluates the cubic at `1 / 4`
as that display does, but establishes only positivity and states no
constant. -/
private theorem seam_topRoot_lt_quarter (h : ChordDomain p u)
    (hv : offDiagonalMass p = 1 / 8) : u < 1 / 4 := by
  have hs : diagonalMass p = (7 : ℝ) / 8 := by
    have := diagonalMass_add_offDiagonalMass h.isPMF
    rw [hv] at this
    linarith
  have hw := offDiagonalProduct_le_sq_div_four p
  rw [hv] at hw
  have hc : 0 < cubic p ((1 : ℝ) / 4) := by
    unfold cubic
    rw [hv, hs]
    norm_num at hw ⊢
    linarith
  exact topRoot_lt_of_cubic_pos h (by norm_num) hc

/-! ## A balanced radius -/

/-- Some radius between `1 / 2` and `2 / 3` carries a balanced seam law.  The
page parametrises the seam by the difference of the two off-diagonal cells,
where the balanced law is that difference's vanishing and needs no existence
proof; here the seam runs in the radius, and the balanced radius has to be
found. -/
theorem exists_balanced_seamRadius :
    ∃ r ∈ Set.Ioo ((1 : ℝ) / 2) (2 / 3), seamImbalanceSq r = 0 := by
  have hcont : ContinuousOn seamImbalanceSq (Set.Icc ((1 : ℝ) / 2) (2 / 3)) := by
    unfold seamImbalanceSq seamProduct
    intro x hx
    have hx0 : x ≠ 0 := by norm_num at hx ⊢; linarith [hx.1]
    have hxden : 1 + 7 * x ≠ 0 := by norm_num at hx ⊢; linarith [hx.1]
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    fun_prop (disch := assumption)
  have hlo : seamImbalanceSq ((1 : ℝ) / 2) < 0 := by
    norm_num [seamImbalanceSq, seamProduct]
  have hhi : 0 < seamImbalanceSq ((2 : ℝ) / 3) := by
    norm_num [seamImbalanceSq, seamProduct]
  have hmem : (0 : ℝ) ∈ Set.Icc (seamImbalanceSq ((1 : ℝ) / 2))
      (seamImbalanceSq (2 / 3)) := ⟨hlo.le, hhi.le⟩
  obtain ⟨rb, hrb, hz⟩ :=
    intermediate_value_Icc (by norm_num : (1 : ℝ) / 2 ≤ 2 / 3) hcont hmem
  refine ⟨rb, ⟨?_, ?_⟩, hz⟩
  · rcases hrb.1.eq_or_lt with heq | hlt
    · subst rb; simp_all
    · exact hlt
  · rcases hrb.2.lt_or_eq with hlt | heq
    · exact hlt
    · subst rb; simp_all

/-! ## The ray, read on the seam -/

/-- **On the seam the chart's two parameters collapse to one.**  At a radius
between `1 / 2` and `1` whose squared imbalance is nonnegative, the imbalance
lies in `[0, 1)`, the pair of chart parameters lies in the chart domain, the
product parameter is `seamProduct` of the radius, the root is `1 / (8 r)`, the
off-diagonal mass is `1 / 8`, and the law is the seam law of that
imbalance. -/
theorem rayValues_of_seamRadius (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 ≤ seamImbalanceSq r) :
    let z := Real.sqrt (seamImbalanceSq r)
    z ∈ Set.Ico (0 : ℝ) 1 ∧ ChartDomain r (rayProductCoeff z * r ^ 2)
      ∧ rayProductCoeff z * r ^ 2 = seamProduct r
      ∧ rayRoot z r = 1 / (8 * r) ∧ rayMass z r = 1 / 8
      ∧ rayLaw z r = seamLaw z := by
  dsimp only
  have hr0 : 0 < r := by linarith [hr.1]
  have hd1 : 0 < 1 + 7 * r := by positivity
  have hp : 0 < seamProduct r := by
    unfold seamProduct
    exact div_pos (sub_pos.mpr hr.2) hd1
  have hzsq : (Real.sqrt (seamImbalanceSq r)) ^ 2 = seamImbalanceSq r :=
    Real.sq_sqrt hh
  have hzlt : Real.sqrt (seamImbalanceSq r) < 1 := by
    have hfrac : 0 < 4 * seamProduct r / r ^ 2 :=
      div_pos (mul_pos (by norm_num) hp) (by positivity)
    have hlt : seamImbalanceSq r < 1 := by unfold seamImbalanceSq; linarith
    nlinarith [Real.sqrt_nonneg (seamImbalanceSq r)]
  have hk : rayProductCoeff (Real.sqrt (seamImbalanceSq r)) * r ^ 2
      = seamProduct r := by
    unfold rayProductCoeff
    rw [hzsq]
    unfold seamImbalanceSq
    field_simp
    ring
  have hq : 0 < 1 - r - 3 * seamProduct r := by
    unfold seamProduct
    rw [show 1 - r - 3 * ((1 - r) / (1 + 7 * r))
        = (1 - r) * (7 * r - 2) / (1 + 7 * r) by field_simp; ring]
    exact div_pos (mul_pos (sub_pos.mpr hr.2) (by linarith [hr.1])) hd1
  have hD : ChartDomain r
      (rayProductCoeff (Real.sqrt (seamImbalanceSq r)) * r ^ 2) := by
    rw [hk]
    refine ⟨hp, hr0, hr.2, hq, ?_⟩
    have hrel : seamImbalanceSq r * r ^ 2 = r ^ 2 - 4 * seamProduct r := by
      unfold seamImbalanceSq
      field_simp
    nlinarith [mul_nonneg hh (sq_nonneg r)]
  have hU : rayRoot (Real.sqrt (seamImbalanceSq r)) r = 1 / (8 * r) := by
    unfold rayRoot chartRoot chartNorm
    rw [hk]
    unfold seamProduct
    have hrne : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr.2)
    field_simp [hr0.ne', hd1.ne', hrne]
    ring_nf
    exact mul_inv_cancel₀ hr0.ne'
  have hV : rayMass (Real.sqrt (seamImbalanceSq r)) r = 1 / 8 := by
    unfold rayMass chartOffDiagonalMass
    rw [show chartRoot r (rayProductCoeff (Real.sqrt (seamImbalanceSq r)) * r ^ 2)
        = rayRoot (Real.sqrt (seamImbalanceSq r)) r from rfl, hU]
    field_simp
  refine ⟨⟨Real.sqrt_nonneg _, hzlt⟩, hD, hk, hU, hV, ?_⟩
  funext a
  rcases a with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rayLaw, seamLaw, tableOfEntries, hV] <;> ring

/-! ## A chord law on the seam, in the radius -/

/-- **A chord law of off-diagonal mass `1 / 8`, read in the radius.**  Its
radius lies between `1 / 2` and `1`, the seam's product parameter at that
radius is the law's own off-diagonal product over the square of its root, the
seam's squared imbalance is the square of the law's own imbalance, and the
seam's singleton scalar is the law's isolating-code margin at the chord's
midpoint. -/
theorem chordDomain_seamCoordinates (h : ChordDomain p u)
    (hv : offDiagonalMass p = 1 / 8) :
    let r := offDiagonalMass p / u
    let z := (entryB p - entryC p) / offDiagonalMass p
    r ∈ Set.Ioo ((1 : ℝ) / 2) 1 ∧ seamProduct r = offDiagonalProduct p / u ^ 2
      ∧ seamImbalanceSq r = z ^ 2
      ∧ seamSingletonScalar r
          = Real.log 2 * singletonMargin p u (chordMidpoint p) := by
  dsimp only
  have hu : 0 < u := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hv0 : 0 < offDiagonalMass p := offDiagonalMass_pos h.fullSupport
  have hr0 : 0 < offDiagonalMass p / u := div_pos hv0 hu
  have hrhalf : (1 : ℝ) / 2 < offDiagonalMass p / u := by
    rw [hv]
    have hut := seam_topRoot_lt_quarter h hv
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hu]
    nlinarith
  have hr1 : offDiagonalMass p / u < 1 := by
    rw [div_lt_one hu]
    exact offDiagonalMass_lt_topRoot h.isPMF h.fullSupport h.topRoot
  have hs : diagonalMass p = (7 : ℝ) / 8 := by
    have := diagonalMass_add_offDiagonalMass h.isPMF
    rw [hv] at this
    linarith
  have hroot : cubic p u = 0 := h.topRoot.2.1
  have hpi : seamProduct (offDiagonalMass p / u) = offDiagonalProduct p / u ^ 2 := by
    unfold seamProduct
    have hden : 1 + 7 * (offDiagonalMass p / u) ≠ 0 := by positivity
    rw [hv]
    field_simp
    unfold cubic at hroot
    rw [hv, hs] at hroot
    nlinarith
  have hzsq : seamImbalanceSq (offDiagonalMass p / u)
      = ((entryB p - entryC p) / offDiagonalMass p) ^ 2 := by
    unfold seamImbalanceSq
    rw [hpi]
    field_simp
    rw [offDiagonalProduct_eq]
    unfold offDiagonalMass
    ring
  have hz0 : 0 ≤ (entryB p - entryC p) / offDiagonalMass p :=
    div_nonneg (sub_nonneg.mpr h.offDiagonal_le) hv0.le
  have hsqrt : Real.sqrt (seamImbalanceSq (offDiagonalMass p / u))
      = (entryB p - entryC p) / offDiagonalMass p := by
    rw [hzsq, Real.sqrt_sq hz0]
  have hT : seamSingletonScalar (offDiagonalMass p / u)
      = Real.log 2 * singletonMargin p u (chordMidpoint p) := by
    rw [← raySingletonScalar_eq h]
    unfold seamSingletonScalar raySingletonScalar seamCellB seamCellC
    rw [hsqrt]
    have hVcoord : rayMass ((entryB p - entryC p) / offDiagonalMass p)
        (offDiagonalMass p / u) = offDiagonalMass p :=
      (chordDomain_rayCoordinates h).2.2.2.1
    rw [hVcoord, hv]
    congr 2
    ring_nf
  exact ⟨⟨hrhalf, hr1⟩, hpi, hzsq, hT⟩

end StochasticToDeterministicLatents.Binary
