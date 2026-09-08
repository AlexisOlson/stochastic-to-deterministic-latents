/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  All four theorems of the
private working material are taken, and one definition it left in a second
private module is declared here, where it is first used.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRay

/-!
# The mass along the ray

Along a ray of fixed imbalance the chart's second parameter is
`rayProductCoeff z * r ^ 2`, so the root and the off-diagonal mass are rational
functions of the radius alone.  This module differentiates both and shows that
the mass increases strictly from the centre out to the critical radius.

That monotonicity is what lets a law be located on its ray by its off-diagonal
mass: the radius is recovered from the mass, so the seam, where the mass is one
eighth, meets each ray at most once.  That it meets each ray *at all* needs the
critical mass to reach one eighth, which is not proved here.

Nothing here is analytic.  The margins, their logarithms and their derivatives
belong to the modules above this one.
-/

namespace StochasticToDeterministicLatents.Binary

variable {z r : ℝ}

/-- The derivative of `rayMass` in the radius. -/
noncomputable def rayMassDeriv (z r : ℝ) : ℝ :=
  rayProductCoeff z * r ^ 2 * (3 - 2 * r - rayProductCoeff z * r ^ 2)
    / chartNorm r (rayProductCoeff z * r ^ 2) ^ 2

/-- Both factors of the chart's normalizer are positive from the centre out to
the critical radius, the closed interval included.  `chartFactors_pos` does
not serve here: it takes a `ChartDomain`, whose positive product fails at the
centre. -/
theorem rayNorm_factors_pos (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    0 < 1 - r ∧ 0 < 1 - rayProductCoeff z * r ^ 2 := by
  have hs := criticalRadius_spec hz
  have hr1 : r < 1 := lt_of_le_of_lt hr.2 hs.2.1
  have hk : 0 ≤ rayProductCoeff z := by
    unfold rayProductCoeff
    nlinarith [sq_nonneg z, mul_nonneg hz.1 (sub_nonneg.mpr (le_of_lt hz.2))]
  have hk_le : rayProductCoeff z ≤ 1 / 4 := by
    unfold rayProductCoeff
    nlinarith [sq_nonneg z]
  have hr_nonneg : 0 ≤ r := hr.1
  have hr_sq_lt : r ^ 2 < 1 := by
    nlinarith [mul_nonneg hr_nonneg (sub_nonneg.mpr (le_of_lt hr1))]
  refine ⟨sub_pos.mpr hr1, ?_⟩
  nlinarith [mul_nonneg hk (sq_nonneg r),
    mul_pos (sub_pos.mpr (show rayProductCoeff z < 1 by linarith))
      (sub_pos.mpr hr_sq_lt)]

/-! ## The two derivatives -/

/-- **The chart's root, differentiated along the ray.** -/
theorem hasDerivAt_rayRoot (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (rayRoot z)
      (rayProductCoeff z * r * (2 - r - rayProductCoeff z * r ^ 3)
        / chartNorm r (rayProductCoeff z * r ^ 2) ^ 2) r := by
  have hb := rayNorm_factors_pos hz ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hn : chartNorm r (rayProductCoeff z * r ^ 2) ≠ 0 := by
    unfold chartNorm
    exact mul_ne_zero (ne_of_gt hb.1) (ne_of_gt hb.2)
  have hnum : HasDerivAt (fun x : ℝ => rayProductCoeff z * x ^ 2)
      (2 * rayProductCoeff z * r) r := by
    convert (hasDerivAt_const r (rayProductCoeff z)).mul
      ((hasDerivAt_id r).pow 2) using 1 <;>
      first | rfl | (simp [id_eq]; ring)
  have hden : HasDerivAt
      (fun x : ℝ => (1 - x) * (1 - rayProductCoeff z * x ^ 2))
      (-1 - 2 * rayProductCoeff z * r + 3 * rayProductCoeff z * r ^ 2) r := by
    convert ((hasDerivAt_const r 1).sub (hasDerivAt_id r)).mul
      ((hasDerivAt_const r 1).sub hnum) using 1 <;>
      first | rfl | (simp [id_eq]; ring)
  simp only [chartNorm] at hn
  unfold rayRoot chartRoot chartNorm
  convert hnum.div hden hn using 1 <;> first | rfl | (field_simp [hn]; ring)

/-- **The off-diagonal mass, differentiated along the ray.** -/
theorem hasDerivAt_rayMass (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (rayMass z) (rayMassDeriv z r) r := by
  have hb := rayNorm_factors_pos hz ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hn : chartNorm r (rayProductCoeff z * r ^ 2) ≠ 0 := by
    unfold chartNorm
    exact mul_ne_zero (ne_of_gt hb.1) (ne_of_gt hb.2)
  have hnum : HasDerivAt (fun x : ℝ => rayProductCoeff z * x ^ 3)
      (3 * rayProductCoeff z * r ^ 2) r := by
    convert (hasDerivAt_const r (rayProductCoeff z)).mul
      ((hasDerivAt_id r).pow 3) using 1 <;>
      first | rfl | (simp [id_eq]; ring)
  have hinner : HasDerivAt (fun x : ℝ => rayProductCoeff z * x ^ 2)
      (2 * rayProductCoeff z * r) r := by
    convert (hasDerivAt_const r (rayProductCoeff z)).mul
      ((hasDerivAt_id r).pow 2) using 1 <;>
      first | rfl | (simp [id_eq]; ring)
  have hden : HasDerivAt
      (fun x : ℝ => (1 - x) * (1 - rayProductCoeff z * x ^ 2))
      (-1 - 2 * rayProductCoeff z * r + 3 * rayProductCoeff z * r ^ 2) r := by
    convert ((hasDerivAt_const r 1).sub (hasDerivAt_id r)).mul
      ((hasDerivAt_const r 1).sub hinner) using 1 <;>
      first | rfl | (simp [id_eq]; ring)
  simp only [chartNorm] at hn
  unfold rayMass chartOffDiagonalMass chartRoot rayMassDeriv chartNorm
  convert hnum.div hden hn using 1 <;> try rfl
  · funext x
    change x * (rayProductCoeff z * x ^ 2
        / ((1 - x) * (1 - rayProductCoeff z * x ^ 2)))
      = rayProductCoeff z * x ^ 3
        / ((1 - x) * (1 - rayProductCoeff z * x ^ 2))
    ring
  · field_simp [hn]
    ring

/-! ## The mass increases -/

/-- **The mass's derivative is positive** strictly inside the ray. -/
theorem rayMassDeriv_pos (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) : 0 < rayMassDeriv z r := by
  have hb := rayNorm_factors_pos hz ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hk : 0 < rayProductCoeff z := by
    unfold rayProductCoeff
    nlinarith [mul_pos (show 0 < 1 + z by linarith [hz.1]) (sub_pos.mpr hz.2)]
  have hkr : rayProductCoeff z * r ^ 2 < 1 := sub_pos.mp hb.2
  have hc : 0 < 3 - 2 * r - rayProductCoeff z * r ^ 2 := by
    have hs := criticalRadius_spec hz
    nlinarith [hr.1, lt_trans hr.2 hs.2.1, hkr]
  have hn : 0 < chartNorm r (rayProductCoeff z * r ^ 2) := by
    unfold chartNorm
    exact mul_pos hb.1 hb.2
  unfold rayMassDeriv
  exact div_pos (mul_pos (mul_pos hk (sq_pos_of_pos hr.1)) hc) (sq_pos_of_pos hn)

/-- **The mass increases strictly from the centre to the critical radius.**
A law on the ray is therefore located by its off-diagonal mass alone. -/
theorem rayMass_strictMonoOn (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    StrictMonoOn (rayMass z) (Set.Icc (0 : ℝ) (criticalRadius z)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) (criticalRadius z))
  · intro r hr
    have hb := rayNorm_factors_pos hz hr
    have hn : chartNorm r (rayProductCoeff z * r ^ 2) ≠ 0 := by
      unfold chartNorm
      exact mul_ne_zero (ne_of_gt hb.1) (ne_of_gt hb.2)
    unfold rayMass chartOffDiagonalMass chartRoot chartNorm
    apply ContinuousWithinAt.mul continuousWithinAt_id
    apply ContinuousWithinAt.div
    · exact continuousWithinAt_const.mul (continuousWithinAt_id.pow 2)
    · exact (continuousWithinAt_const.sub continuousWithinAt_id).mul
        (continuousWithinAt_const.sub
          (continuousWithinAt_const.mul (continuousWithinAt_id.pow 2)))
    · exact hn
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_rayMass hz hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact rayMassDeriv_pos hz hr

end StochasticToDeterministicLatents.Binary
