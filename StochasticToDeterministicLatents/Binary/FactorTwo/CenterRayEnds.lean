/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Renamed, restated over the
public interfaces of this library, and re-proved where the argument differs.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRayMass
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterDictionary

/-!
# The ray, out to its ends

Every **derivative** of this arm is taken strictly inside the ray, on the open
interval `(0, r_c)`, because that is where the chart's interior condition
holds; the mass's strict monotonicity and the chart normalizer's positivity
already hold on the closed interval `[0, r_c]`.  What the endpoint arguments
still need is the contact height and the two margins at the ends themselves,
and this module puts them there: the root and the mass are continuous up to
both ends, and so are the height and the two margins.

Two facts are worth separating.

* `raySingletonScalar_zero` is the isolating code's margin at the centre of the
  chart, radius zero, and it is `0`.  **That value is the `0 log 0 = 0`
  convention, not a limit**: at radius zero the mass and the root are zero, so
  every entropy term carrying either of them is `xLogX 0` and vanishes by the
  convention, while the terms that remain all have argument `1 / 2` and
  cancel, their coefficients summing to zero.  What makes it the
  endpoint value the page's argument uses is the pair of this equality with
  `continuousOn_raySingletonScalar` on the closed interval; neither half says
  it alone.
* `rayHeight_eq` rewrites the contact height along the ray into the ray's own
  coordinates, with the root and the mass as the only nonpolynomial pieces.
  Every continuity proof below runs through it.

**No bound is proved here, and nothing is differentiated.**  The module states
continuity and one value.
-/

namespace StochasticToDeterministicLatents.Binary

variable {z r : ℝ}

/-! ## Positivity on the closed interval -/

/-- The chart's normalizer is positive from the centre out to the critical
radius, the closed interval included. -/
theorem rayNorm_pos (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    0 < chartNorm r (rayProductCoeff z * r ^ 2) := by
  obtain ⟨ha, hb⟩ := rayNorm_factors_pos hz hr
  unfold chartNorm
  exact mul_pos ha hb

/-- The two rescaled cells stay below one on the closed interval. -/
private theorem rayCells_lt_one (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    0 < 1 - (1 + z) * r / 2 ∧ 0 < 1 - (1 - z) * r / 2 := by
  have hr1 : r < 1 := lt_of_le_of_lt hr.2 (criticalRadius_spec hz).2.1
  constructor
  · nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr (le_of_lt hz.2))]
  · nlinarith [mul_nonneg hz.1 hr.1]

/-- The ray's root is nonnegative on the closed interval. -/
private theorem rayRoot_nonneg (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) : 0 ≤ rayRoot z r := by
  have hk : 0 ≤ rayProductCoeff z := by
    unfold rayProductCoeff
    nlinarith [sq_nonneg z, mul_nonneg hz.1 (sub_nonneg.mpr (le_of_lt hz.2))]
  unfold rayRoot chartRoot
  exact div_nonneg (mul_nonneg hk (sq_nonneg r)) (rayNorm_pos hz hr).le

/-- The ray's off-diagonal mass stays below one on the closed interval. -/
private theorem rayMass_lt_one (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) : rayMass z r < 1 := by
  have hm := (rayMass_strictMonoOn hz).monotoneOn hr
    (show criticalRadius z ∈ Set.Icc (0 : ℝ) (criticalRadius z) from
      ⟨(criticalRadius_spec hz).1.le, le_rfl⟩) hr.2
  rw [(ray_boundary_values hz).1] at hm
  linarith [(criticalRadius_spec hz).2.2.2.1]

/-- The diagonal certificate value is positive along the ray. -/
private theorem rayCertDiagonal_pos (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    0 < certDiagonal (1 - rayMass z r) (rayRoot z r) := by
  have hU := rayRoot_nonneg hz hr
  have hV := rayMass_lt_one hz hr
  have hr1 : r < 1 := lt_of_le_of_lt hr.2 (criticalRadius_spec hz).2.1
  have hVU : rayMass z r = r * rayRoot z r := rfl
  unfold certDiagonal
  rw [hVU] at hV ⊢
  apply div_pos
  · nlinarith
  · exact pow_pos (by nlinarith) 2

/-! ## The height in the ray's coordinates -/

/-- The contact height along the ray, written in the ray's own coordinates.
The root and the mass are the only nonpolynomial pieces, which is what makes
the continuity proofs below assemblies of standard combinators. -/
theorem rayHeight_eq (z r : ℝ) :
    chartHeight ((1 + z) * r / 2) ((1 - z) * r / 2)
      = -(1 - rayMass z r)
          * Real.log (certDiagonal (1 - rayMass z r) (rayRoot z r))
        + xLogX ((1 + z) * r / 2 * rayRoot z r)
        + xLogX ((1 - z) * r / 2 * rayRoot z r)
        + 2 * rayMass z r * Real.log (1 - r)
        - 2 * ((1 + z) * r / 2 * rayRoot z r) * Real.log (1 - (1 + z) * r / 2)
        - 2 * ((1 - z) * r / 2 * rayRoot z r) * Real.log (1 - (1 - z) * r / 2) := by
  have hsum : (1 + z) * r / 2 + (1 - z) * r / 2 = r := by ring
  have hprod : (1 + z) * r / 2 * ((1 - z) * r / 2) = rayProductCoeff z * r ^ 2 := by
    unfold rayProductCoeff
    ring
  unfold chartHeight rayMass rayRoot chartDiagonalMass chartOffDiagonalMass
  rw [hsum, hprod]

/-! ## Continuity up to both ends -/

/-- The ray's root is continuous on the closed interval. -/
private theorem continuousOn_rayRoot (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousOn (rayRoot z) (Set.Icc (0 : ℝ) (criticalRadius z)) := by
  unfold rayRoot chartRoot chartNorm
  apply ContinuousOn.div
  · exact continuousOn_const.mul (continuousOn_id.pow 2)
  · exact (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2)))
  · intro r hr
    exact (rayNorm_pos hz hr).ne'

/-- The ray's off-diagonal mass is continuous on the closed interval, which is
what the height and the two margins below are composed through. -/
theorem continuousOn_rayMass (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousOn (rayMass z) (Set.Icc (0 : ℝ) (criticalRadius z)) := by
  unfold rayMass chartOffDiagonalMass
  exact continuousOn_id.mul (continuousOn_rayRoot hz)

/-- The contact height is continuous along the ray on the closed interval. -/
private theorem continuousOn_rayHeight (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousOn (fun r => chartHeight ((1 + z) * r / 2) ((1 - z) * r / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) := by
  rw [show (fun r => chartHeight ((1 + z) * r / 2) ((1 - z) * r / 2)) =
      fun r => -(1 - rayMass z r)
          * Real.log (certDiagonal (1 - rayMass z r) (rayRoot z r))
        + xLogX ((1 + z) * r / 2 * rayRoot z r)
        + xLogX ((1 - z) * r / 2 * rayRoot z r)
        + 2 * rayMass z r * Real.log (1 - r)
        - 2 * ((1 + z) * r / 2 * rayRoot z r) * Real.log (1 - (1 + z) * r / 2)
        - 2 * ((1 - z) * r / 2 * rayRoot z r) * Real.log (1 - (1 - z) * r / 2) by
      funext r; exact rayHeight_eq z r]
  have hU := continuousOn_rayRoot hz
  have hV := continuousOn_rayMass hz
  have hs : ContinuousOn (fun r => 1 - rayMass z r)
      (Set.Icc (0 : ℝ) (criticalRadius z)) := continuousOn_const.sub hV
  have hK : ContinuousOn
      (fun r => certDiagonal (1 - rayMass z r) (rayRoot z r))
      (Set.Icc (0 : ℝ) (criticalRadius z)) := by
    unfold certDiagonal
    refine (hs.add (continuousOn_const.mul hU)).div ((hs.add hU).pow 2) ?_
    intro r hr
    refine (pow_pos ?_ 2).ne'
    have hv := rayMass_lt_one hz hr
    have hu := rayRoot_nonneg hz hr
    have hVU : rayMass z r = r * rayRoot z r := rfl
    rw [hVU] at hv
    nlinarith
  have hlogK := hK.log (fun r hr => (rayCertDiagonal_pos hz hr).ne')
  have ha : ContinuousOn (fun r => (1 + z) * r / 2 * rayRoot z r)
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    (((continuousOn_const.add continuousOn_const).mul
      continuousOn_id).div_const 2).mul hU
  have hb : ContinuousOn (fun r => (1 - z) * r / 2 * rayRoot z r)
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    (((continuousOn_const.sub continuousOn_const).mul
      continuousOn_id).div_const 2).mul hU
  have hlr : ContinuousOn (fun r : ℝ => Real.log (1 - r))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    (continuousOn_const.sub continuousOn_id).log
      (fun r hr => (rayNorm_factors_pos hz hr).1.ne')
  have hlx : ContinuousOn (fun r : ℝ => Real.log (1 - (1 + z) * r / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    (continuousOn_const.sub
      (((continuousOn_const.add continuousOn_const).mul
        continuousOn_id).div_const 2)).log
      (fun r hr => (rayCells_lt_one hz hr).1.ne')
  have hly : ContinuousOn (fun r : ℝ => Real.log (1 - (1 - z) * r / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    (continuousOn_const.sub
      (((continuousOn_const.sub continuousOn_const).mul
        continuousOn_id).div_const 2)).log
      (fun r hr => (rayCells_lt_one hz hr).2.ne')
  exact ((((hs.neg.mul hlogK).add (continuousOn_xLogX ha)).add
    (continuousOn_xLogX hb)).add
    ((continuousOn_const.mul hV).mul hlr)).sub
    ((continuousOn_const.mul ha).mul hlx) |>.sub
    ((continuousOn_const.mul hb).mul hly)

/-! ## The two margins on the closed interval -/

/-- The constant code's margin along the ray is continuous on the closed
interval. -/
theorem continuousOn_rayConstantScalar (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousOn (rayConstantScalar z) (Set.Icc (0 : ℝ) (criticalRadius z)) := by
  have hV := continuousOn_rayMass hz
  have hk := continuousOn_rayHeight hz
  have e1 : ContinuousOn (fun r => xLogX ((1 - rayMass z r) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX ((continuousOn_const.sub hV).div_const 2)
  have e2 : ContinuousOn (fun r => xLogX (rayMass z r * (1 + z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX ((hV.mul continuousOn_const).div_const 2)
  have e3 : ContinuousOn (fun r => xLogX (rayMass z r * (1 - z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX ((hV.mul continuousOn_const).div_const 2)
  have e4 : ContinuousOn (fun r => xLogX ((1 + rayMass z r * z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX
      ((continuousOn_const.add (hV.mul continuousOn_const)).div_const 2)
  have e5 : ContinuousOn (fun r => xLogX ((1 - rayMass z r * z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX
      ((continuousOn_const.sub (hV.mul continuousOn_const)).div_const 2)
  unfold rayConstantScalar centerConstantScalar centerLogEntropy
    centerMarginalEntropy
  exact ((continuousOn_const.mul
    ((((continuousOn_const.mul e1).add e2).add e3).neg)).sub
    (continuousOn_const.mul (e4.add e5).neg)).sub
    (continuousOn_const.mul hk.neg)

/-- The isolating code's margin along the ray is continuous on the closed
interval. -/
theorem continuousOn_raySingletonScalar (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousOn (raySingletonScalar z) (Set.Icc (0 : ℝ) (criticalRadius z)) := by
  have hV := continuousOn_rayMass hz
  have hk := continuousOn_rayHeight hz
  have e1 : ContinuousOn (fun r => xLogX ((1 - rayMass z r) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX ((continuousOn_const.sub hV).div_const 2)
  have e2 : ContinuousOn (fun r => xLogX (rayMass z r * (1 + z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX ((hV.mul continuousOn_const).div_const 2)
  have e3 : ContinuousOn (fun r => xLogX (rayMass z r * (1 - z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX ((hV.mul continuousOn_const).div_const 2)
  have e4 : ContinuousOn (fun r => xLogX ((1 + rayMass z r * z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX
      ((continuousOn_const.add (hV.mul continuousOn_const)).div_const 2)
  have e5 : ContinuousOn (fun r => xLogX ((1 - rayMass z r * z) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX
      ((continuousOn_const.sub (hV.mul continuousOn_const)).div_const 2)
  have e6 : ContinuousOn (fun r => xLogX ((1 + rayMass z r) / 2))
      (Set.Icc (0 : ℝ) (criticalRadius z)) :=
    continuousOn_xLogX ((continuousOn_const.add hV).div_const 2)
  unfold raySingletonScalar centerSingletonScalar centerLogEntropy
    centerMarginalEntropy
  exact ((((continuousOn_const.mul
    ((((continuousOn_const.mul e1).add e2).add e3).neg)).sub
    (continuousOn_const.mul (e4.add e5).neg)).sub
    (continuousOn_const.mul hk.neg)).sub e1).sub e6

/-! ## The value at the centre -/

/-- The isolating code's margin is zero at the centre of the chart.  The mass
and the root vanish there, so every entropy term carrying either of them is
`xLogX 0` and **this rests on the `0 log 0 = 0` convention, not on a limit**;
the terms that remain have argument `1 / 2` and cancel, their coefficients
summing to zero.  Paired with `continuousOn_raySingletonScalar` it is the endpoint
value the ray's argument uses. -/
theorem raySingletonScalar_zero (z : ℝ) : raySingletonScalar z 0 = 0 := by
  simp [raySingletonScalar, centerSingletonScalar, centerLogEntropy,
    centerMarginalEntropy, chartHeight, rayMass, chartRoot, chartNorm,
    chartDiagonalMass, chartOffDiagonalMass, certDiagonal, xLogX,
    rayProductCoeff]
  ring

end StochasticToDeterministicLatents.Binary
