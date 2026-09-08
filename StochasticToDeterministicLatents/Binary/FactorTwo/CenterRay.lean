/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  The private working
material's cell constructor is dropped: it is the public `tableOfEntries`,
with the same row-major order.
-/
import StochasticToDeterministicLatents.Binary.Chart
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterCurvature

/-!
# The ray of fixed imbalance, and its critical radius

The centre argument runs outward along a ray of laws of fixed imbalance `z`,
parametrised by a radius `r`.  This module defines that family and the radius
at which it leaves the chart's interior, and proves four things about it: the
critical radius lies in `(0, 1)` and its mass in `[1/4, 1/3)`; a radius is
below the critical one exactly when the chart's interior condition holds; the
root and mass take stated values at the critical radius; and every law on the
closed ray is a probability law, with full support at positive radius.

This is the first module of the centre's chart apparatus that mentions a law.
It says which laws the chart's two parameters describe -- those with
`omega = kappa(z) r^2` -- and nothing about any margin, derivative, or bound.
-/

namespace StochasticToDeterministicLatents.Binary

variable {z r : ℝ}

/-! ## The ray -/

/-- The coefficient carrying the chart's second parameter along a ray of
imbalance `z`, so that `omega = rayProductCoeff z * r ^ 2`.  It is a
coefficient, not a curvature. -/
noncomputable def rayProductCoeff (z : ℝ) : ℝ := (1 - z ^ 2) / 4

/-- The radius at which the ray leaves the chart's interior. -/
noncomputable def criticalRadius (z : ℝ) : ℝ :=
  2 / (1 + Real.sqrt (4 - 3 * z ^ 2))

/-- The off-diagonal mass at the critical radius. -/
noncomputable def criticalMass (z : ℝ) : ℝ :=
  1 / (2 + Real.sqrt (4 - 3 * z ^ 2))

/-- The chart's root, along the ray. -/
noncomputable def rayRoot (z r : ℝ) : ℝ :=
  chartRoot r (rayProductCoeff z * r ^ 2)

/-- The chart's off-diagonal mass, along the ray. -/
noncomputable def rayMass (z r : ℝ) : ℝ :=
  chartOffDiagonalMass r (rayProductCoeff z * r ^ 2)

/-- The law at radius `r` on the ray of imbalance `z`: off-diagonal mass
`rayMass z r`, split in the ratio `1 + z` to `1 - z`, and the rest divided
equally between the two diagonal cells. -/
noncomputable def rayLaw (z r : ℝ) : RealTable :=
  tableOfEntries ((1 - rayMass z r) / 2) (rayMass z r * (1 + z) / 2)
    (rayMass z r * (1 - z) / 2) ((1 - rayMass z r) / 2)

/-! ## The critical radius -/

private theorem sqrt_bounds (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    1 < Real.sqrt (4 - 3 * z ^ 2) ∧ Real.sqrt (4 - 3 * z ^ 2) ≤ 2
      ∧ Real.sqrt (4 - 3 * z ^ 2) ^ 2 = 4 - 3 * z ^ 2 := by
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z < 1 := hz.2
  have hzsq : z ^ 2 < 1 := by
    nlinarith [mul_nonneg hz0 (by linarith : (0 : ℝ) ≤ 1 - z)]
  have ha : (0 : ℝ) ≤ 4 - 3 * z ^ 2 := by nlinarith
  refine ⟨?_, ?_, Real.sq_sqrt ha⟩
  · nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg (4 - 3 * z ^ 2)]
  · rw [Real.sqrt_le_iff]
    constructor <;> nlinarith

/-- The critical radius lies in `(0, 1)`, its mass in `[1/4, 1/3)`, and the
chart's interior condition vanishes there. -/
theorem criticalRadius_spec (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    0 < criticalRadius z ∧ criticalRadius z < 1
      ∧ (1 : ℝ) / 4 ≤ criticalMass z ∧ criticalMass z < 1 / 3
      ∧ 1 - criticalRadius z
          - 3 * rayProductCoeff z * criticalRadius z ^ 2 = 0 := by
  obtain ⟨hs1, hs2, hsq⟩ := sqrt_bounds hz
  have hd1 : 0 < 1 + Real.sqrt (4 - 3 * z ^ 2) := by linarith
  have hd2 : 0 < 2 + Real.sqrt (4 - 3 * z ^ 2) := by linarith
  unfold criticalRadius criticalMass rayProductCoeff
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_one hd1]
    linarith
  · rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hd2]
    linarith
  · rw [div_lt_div_iff₀ hd2 (by norm_num : (0 : ℝ) < 3)]
    linarith
  · field_simp
    nlinarith

/-- A radius is below the critical one exactly when the chart's interior
condition holds at it. -/
theorem radius_lt_criticalRadius_iff (hz : z ∈ Set.Ico (0 : ℝ) 1) (hr : 0 < r)
    (hr1 : r < 1) :
    r < criticalRadius z ↔ 0 < 1 - r - 3 * rayProductCoeff z * r ^ 2 := by
  obtain ⟨hc0, -, -, -, hvanish⟩ := criticalRadius_spec hz
  have hk : 0 ≤ rayProductCoeff z := by
    unfold rayProductCoeff
    nlinarith [sq_nonneg z, mul_nonneg hz.1 (sub_nonneg.mpr hz.2.le)]
  have hfac : 0 < 1 + 3 * rayProductCoeff z * (r + criticalRadius z) := by
    nlinarith [mul_nonneg hk (add_pos hr hc0).le]
  have hid : 1 - r - 3 * rayProductCoeff z * r ^ 2
      - (1 - criticalRadius z
          - 3 * rayProductCoeff z * criticalRadius z ^ 2)
      = (criticalRadius z - r)
        * (1 + 3 * rayProductCoeff z * (r + criticalRadius z)) := by ring
  rw [hvanish] at hid
  constructor <;> intro h <;> nlinarith [mul_pos (sub_pos.mpr h) hfac]

/-- The ray's mass and root at the critical radius. -/
theorem ray_boundary_values (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    rayMass z (criticalRadius z) = criticalMass z
      ∧ rayRoot z (criticalRadius z) = (1 - criticalMass z) / 2 := by
  obtain ⟨hc0, hc1, -, -, hvanish⟩ := criticalRadius_spec hz
  have hp : rayProductCoeff z * criticalRadius z ^ 2
      = (1 - criticalRadius z) / 3 := by nlinarith [hvanish]
  have hR1 : 0 < 1 - criticalRadius z := sub_pos.mpr hc1
  have hP1 : 0 < 1 - rayProductCoeff z * criticalRadius z ^ 2 := by
    rw [hp]; linarith
  have hn : 0 < (1 - criticalRadius z)
      * (1 - rayProductCoeff z * criticalRadius z ^ 2) := mul_pos hR1 hP1
  have hRden : 0 < 2 + criticalRadius z := by linarith
  have hvc : criticalMass z = criticalRadius z / (2 + criticalRadius z) := by
    obtain ⟨hs1, hs2, hsq⟩ := sqrt_bounds hz
    unfold criticalMass criticalRadius
    field_simp
    nlinarith
  have hd : 3 - (1 - criticalRadius z) ≠ 0 := by nlinarith
  constructor
  · unfold rayMass chartOffDiagonalMass chartRoot chartNorm
    rw [hp, hvc]
    field_simp [hn.ne', hc0.ne', hd]
    ring
  · unfold rayRoot chartRoot chartNorm
    rw [hp, hvc]
    field_simp [hn.ne', hc0.ne', hd]
    ring

/-! ## The ray carries probability laws -/

/-- Every law on the closed ray is a probability law, and every one at
positive radius has full support. -/
theorem rayLaw_isPMF (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    IsPMF (rayLaw z r) ∧ (0 < r → FullSupport (rayLaw z r)) := by
  obtain ⟨-, hc1, -, -, hvanish⟩ := criticalRadius_spec hz
  have hk : 0 ≤ rayProductCoeff z := by
    unfold rayProductCoeff
    nlinarith [sq_nonneg z, mul_nonneg hz.1 (sub_nonneg.mpr hz.2.le)]
  have hr1 : r < 1 := lt_of_le_of_lt hr.2 hc1
  have hq : 0 ≤ 1 - r - 3 * rayProductCoeff z * r ^ 2 := by
    rcases eq_or_lt_of_le hr.1 with h | hr0
    · subst h; simp
    · rcases lt_or_eq_of_le hr.2 with h | h
      · exact ((radius_lt_criticalRadius_iff hz hr0 hr1).mp h).le
      · subst h; exact hvanish.symm.le
  have hn : 0 < (1 - r) * (1 - rayProductCoeff z * r ^ 2) := by
    have hlt : rayProductCoeff z * r ^ 2 < 1 := by nlinarith [hr.1]
    exact mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hlt)
  have hv0 : 0 ≤ rayMass z r := by
    unfold rayMass chartOffDiagonalMass chartRoot chartNorm
    exact mul_nonneg hr.1 (div_nonneg (mul_nonneg hk (sq_nonneg r)) hn.le)
  have hv1 : rayMass z r < 1 := by
    unfold rayMass chartOffDiagonalMass chartRoot chartNorm
    rw [show r * (rayProductCoeff z * r ^ 2
        / ((1 - r) * (1 - rayProductCoeff z * r ^ 2)))
      = r * rayProductCoeff z * r ^ 2
        / ((1 - r) * (1 - rayProductCoeff z * r ^ 2)) by ring, div_lt_one hn]
    nlinarith
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hzminus : 0 < 1 - z := sub_pos.mpr hz.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a
    rcases a with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [rayLaw, tableOfEntries] <;>
      nlinarith [mul_nonneg hv0 hzplus.le, mul_nonneg hv0 hzminus.le]
  · change (∑ a : Cell, rayLaw z r a) = 1
    simp [rayLaw, tableOfEntries, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  · intro hr0 a
    have hvpos : 0 < rayMass z r := by
      unfold rayMass chartOffDiagonalMass chartRoot chartNorm
      have hkpos : 0 < rayProductCoeff z := by
        unfold rayProductCoeff
        nlinarith [mul_pos hzplus hzminus]
      positivity
    rcases a with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [rayLaw, tableOfEntries] <;>
      nlinarith [mul_pos hvpos hzplus, mul_pos hvpos hzminus]

end StochasticToDeterministicLatents.Binary
