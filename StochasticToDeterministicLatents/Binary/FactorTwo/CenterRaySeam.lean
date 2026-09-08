/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Renamed, restated over the
public interfaces of this library, and re-proved where the argument differs.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRayMargins
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRayEnds
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterSeam
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterSeamMargin
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterEndpointMin

/-!
# The seam radius on a ray

Three facts about a single ray of fixed imbalance, all of them what the
endpoint comparison of the centre runs on.

`exists_raySeamRadius`: the seam meets every ray.  The mass starts at `0` and
reaches at least `1 / 4` at the critical radius, so some radius strictly
inside carries exactly `1 / 8`.  This is the page's remark that
`1/8 < 1/4 <= v_c(z)` puts the seam inside every ray.

`rayConstantSlope_antitoneOn` and `raySingletonSlope_antitoneOn`: the two
margin slopes decrease along the ray.  Their derivatives are the chart's
second-order expressions over the mass squared, times the mass's derivative;
the expressions are negative on the chart domain and the mass increases, so
the product is nonpositive.  **This is stated in the radius, not in the
mass.**  The page's Lemma 4.3 is concavity in the off-diagonal mass; the mass
is strictly increasing in the radius, but that change of variable is not
carried out here and no declaration in this tree states the concavity.

`rayConstantScalar_gt_of_seam` and `raySeam_margins_gt`: at a radius where the
mass is `1 / 8`, the two margins of the centre exceed `1 / 100` and `1 / 250`.
These are the seam bounds already admitted for an arbitrary chord domain,
read at the ray's own law through the coordinate identities of
`CenterDictionary`.

**One arm crosses units and the other does not, and the asymmetry is in this
tree rather than in the mathematics.**  `seam_constantMargin_center_gt` is
stated as `1/100 < Real.log 2 * constantMargin ...`, in natural-log units, so
the constant arm needs no conversion at all.  `seam_singletonMargin_gt` is
stated as `1/(250 * Real.log 2) < singletonMargin ...`, in bits, so the
isolating arm carries the step `1/250 = Real.log 2 * (1/(250 * Real.log 2))`.
Both were checked as scratch examples before this module was written.
-/

namespace StochasticToDeterministicLatents.Binary

variable {z r : ℝ}

/-! ## The seam meets every ray -/

/-- **Every ray crosses the seam.**  Some radius strictly between the centre
and the critical one carries off-diagonal mass exactly `1 / 8`.  The mass is
`0` at the centre, is at least `1 / 4` at the critical radius, and is
continuous between them. -/
theorem exists_raySeamRadius (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ∃ rs ∈ Set.Ioo (0 : ℝ) (criticalRadius z), rayMass z rs = 1 / 8 := by
  have hrc := criticalRadius_spec hz
  have hzero : rayMass z 0 = 0 := by
    unfold rayMass chartOffDiagonalMass
    ring
  have hend : (1 : ℝ) / 4 ≤ rayMass z (criticalRadius z) := by
    rw [(ray_boundary_values hz).1]
    exact hrc.2.2.1
  have hmem : (1 : ℝ) / 8
      ∈ Set.Icc (rayMass z 0) (rayMass z (criticalRadius z)) := by
    rw [hzero]
    exact ⟨by norm_num, by linarith⟩
  obtain ⟨rs, hrs, hV⟩ :=
    intermediate_value_Icc hrc.1.le (continuousOn_rayMass hz) hmem
  refine ⟨rs, ⟨?_, ?_⟩, hV⟩
  · rcases hrs.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hzero] at hV
      norm_num at hV
  · rcases hrs.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hV
      linarith

/-! ## The two slopes decrease along the ray -/

/-- **The constant code's margin slope is antitone strictly inside the ray.**
Its derivative is the mass's derivative, which is positive there, times a
negative chart expression over the mass squared. -/
theorem rayConstantSlope_antitoneOn (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    AntitoneOn (rayConstantSlope z) (Set.Ioo (0 : ℝ) (criticalRadius z)) := by
  refine antitoneOn_Ioo_of_hasDerivAt_nonpos 0 (criticalRadius z)
    (rayConstantSlope z)
    (fun t => rayMassDeriv z t
      * (chartConstantSecondOrder t (rayProductCoeff z * t ^ 2)
          / rayMass z t ^ 2))
    (fun t ht => hasDerivAt_rayConstantSlope hz ht) (fun t ht => ?_)
  exact mul_nonpos_of_nonneg_of_nonpos (rayMassDeriv_pos hz ht).le
    (div_nonpos_of_nonpos_of_nonneg
      (chartConstantSecondOrder_neg (chartDomain_ray hz ht)).le (sq_nonneg _))

/-- **The isolating code's margin slope is antitone strictly inside the ray.**
The same argument with the other second-order expression. -/
theorem raySingletonSlope_antitoneOn (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    AntitoneOn (raySingletonSlope z) (Set.Ioo (0 : ℝ) (criticalRadius z)) := by
  refine antitoneOn_Ioo_of_hasDerivAt_nonpos 0 (criticalRadius z)
    (raySingletonSlope z)
    (fun t => rayMassDeriv z t
      * (chartSingletonSecondOrder t (rayProductCoeff z * t ^ 2)
          / rayMass z t ^ 2))
    (fun t ht => hasDerivAt_raySingletonSlope hz ht) (fun t ht => ?_)
  exact mul_nonpos_of_nonneg_of_nonpos (rayMassDeriv_pos hz ht).le
    (div_nonpos_of_nonpos_of_nonneg
      (chartSingletonSecondOrder_neg (chartDomain_ray hz ht)).le (sq_nonneg _))

/-! ## The ray's law in its own coordinates

The two seam bounds are stated for an arbitrary chord domain, in the
coordinates that domain induces.  Reading them at the ray's own law needs
those coordinates back. -/

/-- The ray law's off-diagonal mass is the ray's mass. -/
private theorem rayLaw_offDiagonalMass (z r : ℝ) :
    offDiagonalMass (rayLaw z r) = rayMass z r := by
  show rayMass z r * (1 + z) / 2 + rayMass z r * (1 - z) / 2 = rayMass z r
  ring

/-- The ray law's imbalance is the ray's imbalance. -/
private theorem rayLaw_imbalance (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    (entryB (rayLaw z r) - entryC (rayLaw z r))
        / offDiagonalMass (rayLaw z r) = z := by
  have hv : 0 < rayMass z r := (chart_pos (chartDomain_ray hz hr)).2.2.2.1
  rw [rayLaw_offDiagonalMass]
  show (rayMass z r * (1 + z) / 2 - rayMass z r * (1 - z) / 2) / rayMass z r = z
  field_simp [hv.ne']
  ring

/-- The ray law's mass over the ray's root is the radius. -/
private theorem rayLaw_radius (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    offDiagonalMass (rayLaw z r) / rayRoot z r = r := by
  have hu : 0 < rayRoot z r := (chart_pos (chartDomain_ray hz hr)).2.1
  rw [rayLaw_offDiagonalMass]
  show r * rayRoot z r / rayRoot z r = r
  field_simp

/-! ## The two margins at a seam radius -/

/-- **At a seam radius the constant code's margin exceeds one hundredth.**
The bound is the one already admitted for every chord domain of mass `1 / 8`,
read at the ray's own law.  Both sides are in natural-log units. -/
theorem rayConstantScalar_gt_of_seam (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) (hv : rayMass z r = 1 / 8) :
    (1 : ℝ) / 100 < rayConstantScalar z r := by
  have hchord := chordDomain_rayLaw hz (chartDomain_ray hz hr)
  have hmass : offDiagonalMass (rayLaw z r) = (1 : ℝ) / 8 := by
    rw [rayLaw_offDiagonalMass, hv]
  have ht := rayConstantScalar_eq hchord
  rw [rayLaw_imbalance hz hr, rayLaw_radius hz hr] at ht
  rw [ht]
  exact seam_constantMargin_center_gt hchord hmass

/-- At a seam radius the isolating code's margin exceeds one part in two
hundred and fifty.  The admitted bound is in bits, so this one carries the
conversion factor explicitly. -/
private theorem raySingletonScalar_gt_of_seam (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) (hv : rayMass z r = 1 / 8) :
    (1 : ℝ) / 250 < raySingletonScalar z r := by
  have hchord := chordDomain_rayLaw hz (chartDomain_ray hz hr)
  have hmass : offDiagonalMass (rayLaw z r) = (1 : ℝ) / 8 := by
    rw [rayLaw_offDiagonalMass, hv]
  have ht := raySingletonScalar_eq hchord
  rw [rayLaw_imbalance hz hr, rayLaw_radius hz hr] at ht
  rw [ht]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  calc (1 : ℝ) / 250 = Real.log 2 * (1 / (250 * Real.log 2)) := by
        field_simp
    _ < Real.log 2 * singletonMargin (rayLaw z r) (rayRoot z r)
          (chordMidpoint (rayLaw z r)) :=
        mul_lt_mul_of_pos_left (seam_singletonMargin_gt hchord hmass) hlog

/-- **Both seam bounds on the ray.**  At a radius carrying mass `1 / 8` the
constant code's margin exceeds `1 / 100` and the isolating code's exceeds
`1 / 250`, both in natural-log units. -/
theorem raySeam_margins_gt (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) (hv : rayMass z r = 1 / 8) :
    (1 : ℝ) / 100 < rayConstantScalar z r
      ∧ (1 : ℝ) / 250 < raySingletonScalar z r :=
  ⟨rayConstantScalar_gt_of_seam hz hr hv, raySingletonScalar_gt_of_seam hz hr hv⟩

end StochasticToDeterministicLatents.Binary
