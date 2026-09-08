/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Renamed, restated over the
public interfaces of this library, and re-proved where the argument differs.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRaySeam
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRayBoundary

/-!
# The endpoint comparison at the centre of the chord

Both halves run the same way.  A chord domain sits at one radius on one ray of
fixed imbalance; the seam sits at another radius on that same ray; the margin's
slope is antitone between them; so the margin, corrected by an affine function
of the mass, is bounded below by the smaller of its two endpoint values, and
both endpoint values are already known.

**Small mass.**  Between the centre of the ray and the seam, the isolating
code's margin is corrected by `4/125` times the mass.  At the centre both terms
vanish; at the seam the margin exceeds `1/250` and the correction is exactly
`1/250`.  So the corrected quantity is nonnegative throughout, which is
`center_singletonMargin_ge`.

**Large mass.**  Between the seam and the critical radius, the constant code's
margin is corrected by the affine function through the two known endpoint
values.  At the seam the margin exceeds `1/100`, which is what that function
takes there; at the critical radius the function is zero and the margin is
nonnegative.  So the margin is at least
`(criticalMass z - v) / (100 * (criticalMass z - 1/8))` throughout, which is
`center_constantMargin_ge`.

**Where the strictness comes from.**  `center_constantMargin_pos` is strict
because that numerator is strict: the mass at any radius strictly inside the
ray is strictly below its value at the critical radius.  **It does not come
from the far endpoint**, which is only known to be nonnegative, so the
positivity the page states there is still not proved anywhere in this tree and
is still not needed.

**Units.**  `constantMargin` and `singletonMargin` are in bits, so every bound
below is in bits; the ray scalars they come from are in natural-log units, and
the `Real.log 2` in each denominator is that conversion.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-! ## Small mass: the isolating code -/

/-- **The isolating code's margin at the centre, for small off-diagonal mass.**
On a chord domain whose off-diagonal mass is at most `1/8`, the isolating
code's margin at the midpoint of the chord is at least `4 v / 125` natural-log
units, which is `4 v / (125 log 2)` bits. -/
theorem center_singletonMargin_ge (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ 1 / 8) :
    4 * offDiagonalMass p / (125 * Real.log 2)
      ≤ singletonMargin p u (chordMidpoint p) := by
  obtain ⟨hz, hr, -, hV, -⟩ := chordDomain_rayCoordinates h
  set z := (entryB p - entryC p) / offDiagonalMass p with hzdef
  set r := offDiagonalMass p / u with hrdef
  obtain ⟨rs, hrs, hVs⟩ := exists_raySeamRadius hz
  have hrrs : r ≤ rs := by
    by_contra hn
    have hlt := rayMass_strictMonoOn hz
      (show rs ∈ Set.Icc (0 : ℝ) (criticalRadius z) from ⟨hrs.1.le, hrs.2.le⟩)
      (show r ∈ Set.Icc (0 : ℝ) (criticalRadius z) from ⟨hr.1.le, hr.2.le⟩)
      (lt_of_not_ge hn)
    rw [hVs, hV] at hlt
    linarith
  have hmin := min_endpoints_le_of_antitoneSlope_affine 0 rs
    (raySingletonScalar z) (rayMass z) (rayMassDeriv z) (raySingletonSlope z)
    ((continuousOn_raySingletonScalar hz).mono
      (Set.Icc_subset_Icc_right hrs.2.le))
    ((continuousOn_rayMass hz).mono (Set.Icc_subset_Icc_right hrs.2.le))
    ((raySingletonSlope_antitoneOn hz).mono
      (Set.Ioo_subset_Ioo_right hrs.2.le))
    (fun t ht => hasDerivAt_raySingletonScalar hz ⟨ht.1, lt_trans ht.2 hrs.2⟩)
    (fun t ht => hasDerivAt_rayMass hz ⟨ht.1, lt_trans ht.2 hrs.2⟩)
    (fun t ht => rayMassDeriv_pos hz ⟨ht.1, lt_trans ht.2 hrs.2⟩)
    0 (4 / 125) (r := r) ⟨hr.1.le, hrrs⟩
  have hzeroV : rayMass z 0 = 0 := by
    unfold rayMass chartOffDiagonalMass
    ring
  have hleft : raySingletonScalar z 0 - 0 - (4 / 125 : ℝ) * rayMass z 0 = 0 := by
    rw [raySingletonScalar_zero, hzeroV]
    ring
  have hright : (0 : ℝ)
      ≤ raySingletonScalar z rs - 0 - (4 / 125 : ℝ) * rayMass z rs := by
    have hseam := (raySeam_margins_gt hz hrs hVs).2
    rw [hVs]
    linarith
  have hnonneg : (0 : ℝ)
      ≤ raySingletonScalar z r - 0 - (4 / 125 : ℝ) * rayMass z r :=
    le_trans (le_min hleft.ge hright) hmin
  have hFD : (4 / 125 : ℝ) * offDiagonalMass p ≤ raySingletonScalar z r := by
    rw [hV] at hnonneg
    linarith
  have ht := raySingletonScalar_eq h
  rw [← hzdef, ← hrdef] at ht
  rw [ht] at hFD
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  rw [mul_comm (Real.log 2)] at hFD
  rw [show 4 * offDiagonalMass p / (125 * Real.log 2)
      = ((4 / 125 : ℝ) * offDiagonalMass p) / Real.log 2 by ring]
  exact (div_le_iff₀ hlog).2 hFD

/-- **The isolating code's margin at the centre is nonnegative for small mass.**
This is the form the gate assembly consumes. -/
theorem center_singletonMargin_nonneg (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ 1 / 8) :
    0 ≤ singletonMargin p u (chordMidpoint p) := by
  have hp : 0 < offDiagonalMass p := offDiagonalMass_pos h.fullSupport
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  refine le_trans ?_ (center_singletonMargin_ge h hv)
  positivity

/-! ## Large mass: the constant code -/

/-- **The constant code's margin at the centre, for large off-diagonal mass.**
On a chord domain whose off-diagonal mass is at least `1/8`, the constant
code's margin at the midpoint is at least
`(criticalMass z - v) / (100 (criticalMass z - 1/8))` natural-log units, where
`z` is the law's imbalance.  The bound decreases to zero as the mass approaches
its value at the critical radius. -/
theorem center_constantMargin_ge (h : ChordDomain p u)
    (hv : 1 / 8 ≤ offDiagonalMass p) :
    (criticalMass ((entryB p - entryC p) / offDiagonalMass p)
          - offDiagonalMass p)
        / (100 * (criticalMass ((entryB p - entryC p) / offDiagonalMass p)
            - 1 / 8) * Real.log 2)
      ≤ constantMargin p u (chordMidpoint p) := by
  obtain ⟨hz, hr, -, hV, -⟩ := chordDomain_rayCoordinates h
  set z := (entryB p - entryC p) / offDiagonalMass p with hzdef
  set r := offDiagonalMass p / u with hrdef
  obtain ⟨rs, hrs, hVs⟩ := exists_raySeamRadius hz
  have hrsr : rs ≤ r := by
    by_contra hn
    have hlt := rayMass_strictMonoOn hz
      (show r ∈ Set.Icc (0 : ℝ) (criticalRadius z) from ⟨hr.1.le, hr.2.le⟩)
      (show rs ∈ Set.Icc (0 : ℝ) (criticalRadius z) from ⟨hrs.1.le, hrs.2.le⟩)
      (lt_of_not_ge hn)
    rw [hVs, hV] at hlt
    linarith
  have hden : 0 < 100 * (criticalMass z - 1 / 8) := by
    have hvc := (criticalRadius_spec hz).2.2.1
    linarith
  have hmin := min_endpoints_le_of_antitoneSlope_affine rs (criticalRadius z)
    (rayConstantScalar z) (rayMass z) (rayMassDeriv z) (rayConstantSlope z)
    ((continuousOn_rayConstantScalar hz).mono
      (Set.Icc_subset_Icc_left hrs.1.le))
    ((continuousOn_rayMass hz).mono (Set.Icc_subset_Icc_left hrs.1.le))
    ((rayConstantSlope_antitoneOn hz).mono
      (Set.Ioo_subset_Ioo_left hrs.1.le))
    (fun t ht => hasDerivAt_rayConstantScalar hz ⟨lt_trans hrs.1 ht.1, ht.2⟩)
    (fun t ht => hasDerivAt_rayMass hz ⟨lt_trans hrs.1 ht.1, ht.2⟩)
    (fun t ht => rayMassDeriv_pos hz ⟨lt_trans hrs.1 ht.1, ht.2⟩)
    (criticalMass z / (100 * (criticalMass z - 1 / 8)))
    (-1 / (100 * (criticalMass z - 1 / 8))) (r := r) ⟨hrsr, hr.2.le⟩
  have hleft : (0 : ℝ)
      ≤ rayConstantScalar z rs - criticalMass z / (100 * (criticalMass z - 1 / 8))
          - -1 / (100 * (criticalMass z - 1 / 8)) * rayMass z rs := by
    have hseam := rayConstantScalar_gt_of_seam hz hrs hVs
    have hcorr : criticalMass z / (100 * (criticalMass z - 1 / 8))
        + -1 / (100 * (criticalMass z - 1 / 8)) * (1 / 8) = 1 / 100 := by
      have e : criticalMass z / (100 * (criticalMass z - 1 / 8))
          + -1 / (100 * (criticalMass z - 1 / 8)) * (1 / 8)
          = (criticalMass z - 1 / 8) / (100 * (criticalMass z - 1 / 8)) := by
        ring
      rw [e, div_eq_iff (ne_of_gt hden)]
      ring
    rw [hVs]
    linarith
  have hright : (0 : ℝ)
      ≤ rayConstantScalar z (criticalRadius z)
          - criticalMass z / (100 * (criticalMass z - 1 / 8))
          - -1 / (100 * (criticalMass z - 1 / 8)) * rayMass z (criticalRadius z) := by
    have hb := rayConstantScalar_boundary_nonneg hz
    have hzero : criticalMass z / (100 * (criticalMass z - 1 / 8))
        + -1 / (100 * (criticalMass z - 1 / 8)) * criticalMass z = 0 := by
      ring
    rw [(ray_boundary_values hz).1]
    linarith
  have hbound : (criticalMass z - rayMass z r) / (100 * (criticalMass z - 1 / 8))
      ≤ rayConstantScalar z r := by
    have hstep := le_trans (le_min hleft hright) hmin
    have hsplit : criticalMass z / (100 * (criticalMass z - 1 / 8))
        + -1 / (100 * (criticalMass z - 1 / 8)) * rayMass z r
        = (criticalMass z - rayMass z r) / (100 * (criticalMass z - 1 / 8)) := by
      ring
    linarith
  rw [hV] at hbound
  have ht := rayConstantScalar_eq h
  rw [← hzdef, ← hrdef] at ht
  rw [ht] at hbound
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  rw [show (criticalMass z - offDiagonalMass p)
        / (100 * (criticalMass z - 1 / 8) * Real.log 2)
      = ((criticalMass z - offDiagonalMass p)
          / (100 * (criticalMass z - 1 / 8))) / Real.log 2 by
    rw [div_div]]
  rw [mul_comm (Real.log 2)] at hbound
  exact (div_le_iff₀ hlog).2 hbound

/-- **The constant code's margin at the centre is strictly positive for large
mass.**  The quantitative bound's numerator is strictly positive, because the
mass at a radius strictly inside the ray is strictly below its value at the
critical radius.  This is the form the gate assembly consumes. -/
theorem center_constantMargin_pos (h : ChordDomain p u)
    (hv : 1 / 8 ≤ offDiagonalMass p) :
    0 < constantMargin p u (chordMidpoint p) := by
  obtain ⟨hz, hr, -, hV, -⟩ := chordDomain_rayCoordinates h
  set z := (entryB p - entryC p) / offDiagonalMass p with hzdef
  set r := offDiagonalMass p / u with hrdef
  have hnum : 0 < criticalMass z - offDiagonalMass p := by
    rw [← hV, ← (ray_boundary_values hz).1]
    exact sub_pos.mpr (rayMass_strictMonoOn hz ⟨hr.1.le, hr.2.le⟩
      ⟨(criticalRadius_spec hz).1.le, le_rfl⟩ hr.2)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hden : 0 < 100 * (criticalMass z - 1 / 8) * Real.log 2 := by
    have hvc := (criticalRadius_spec hz).2.2.1
    have hpos : 0 < criticalMass z - (1 : ℝ) / 8 := by linarith
    positivity
  exact lt_of_lt_of_le (div_pos hnum hden) (center_constantMargin_ge h hv)

end StochasticToDeterministicLatents.Binary
