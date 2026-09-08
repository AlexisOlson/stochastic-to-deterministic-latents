/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  The private working material
carried these second-order expressions across three modules; they are merged
here, five of their statements are dropped as unused, and two positivity facts
are taken from the chart modules rather than proved again.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterFractions

/-!
# The chart's second-order expressions along a ray

Moving out along a ray of fixed imbalance, the page writes a second-order
expression for each of the two centre margins, and both are built from a single
coefficient attached to the contact correction.  This module carries the three
expressions in the contact chart, proves the coefficient equal to the radial
derivative of the tangent coefficient, proves it strictly below the ratio of
off-diagonal to diagonal mass, and concludes that both margin expressions are
negative on the chart domain.

**What is not stated here.**  Nothing in this file differentiates anything.
That these expressions are the second derivatives of the two margins, and hence
that the margins are concave along a ray, is analytic content no declaration in
this tree yet has.  What is proved is that explicit rational functions of the
two chart parameters stand in the stated order.
-/

namespace StochasticToDeterministicLatents.Binary

variable {r omega : ℝ}

/-! ## The three expressions -/

/-- The mass-weighted sum of the two contact masses' logarithmic radial
derivatives, which the page subtracts twice in its display (3.9). -/
noncomputable def chartWeightedLogDeriv (r omega : ℝ) : ℝ :=
  (chartCommonDeriv r omega
        * (chartDeterminant r omega * chartOffDiagonalMass r omega
            + 2 * chartOffDiagonalProduct r omega)
      + chartDeterminant r omega
          * (chartOffDiagonalMass r omega ^ 2
              - 2 * chartOffDiagonalProduct r omega)
      + chartOffDiagonalProduct r omega * chartOffDiagonalMass r omega)
    / (chartDeterminant r omega ^ 2
        + chartDeterminant r omega * chartOffDiagonalMass r omega
        + chartOffDiagonalProduct r omega)

/-- The page's second-order coefficient for the contact correction, as the
right side of its display (3.9).  That this expression is the second radial
difference the page defines it to be is not stated here. -/
noncomputable def chartContactSecondOrder (r omega : ℝ) : ℝ :=
  chartOffDiagonalMass r omega * chartLogKDeriv r omega
    + 3 * chartOffDiagonalMass r omega - 2 * chartWeightedLogDeriv r omega

/-- The page's second-order expression for the constant margin.  That it is
that margin's second radial derivative is not stated here. -/
noncomputable def chartConstantSecondOrder (r omega : ℝ) : ℝ :=
  -5 * chartOffDiagonalMass r omega / chartDiagonalMass r omega
    + 6 * chartDiscriminant r omega / (1 - chartDiscriminant r omega)
    + 2 * chartContactSecondOrder r omega

/-- The page's second-order expression for the isolating code's margin.  That
it is that margin's second radial derivative is not stated here. -/
noncomputable def chartSingletonSecondOrder (r omega : ℝ) : ℝ :=
  -3 * chartOffDiagonalMass r omega / chartDiagonalMass r omega
    + 4 * chartDiscriminant r omega / (1 - chartDiscriminant r omega)
    - chartOffDiagonalMass r omega ^ 2 / (1 - chartOffDiagonalMass r omega ^ 2)
    + 2 * chartContactSecondOrder r omega

/-! ## The chart's two mass ratios -/

private theorem chartNorm_ne (h : ChartDomain r omega) :
    ((1 : ℝ) - r) * (1 - omega) ≠ 0 := by
  obtain ⟨ha, hb, -, -, -⟩ := chartFactors_pos h
  exact (mul_pos ha hb).ne'

private theorem mass_mul_norm (h : ChartDomain r omega) :
    chartOffDiagonalMass r omega * ((1 - r) * (1 - omega)) = omega * r := by
  rw [chartOffDiagonalMass_eq]
  exact div_mul_cancel₀ _ (chartNorm_ne h)

private theorem diagonalMass_eq (h : ChartDomain r omega) :
    chartDiagonalMass r omega = (1 - r - omega) / ((1 - r) * (1 - omega)) := by
  rw [(chart_identities h).1]
  rfl

private theorem chartMassRatio_eq (h : ChartDomain r omega) :
    chartOffDiagonalMass r omega / chartDiagonalMass r omega
      = omega * r / (1 - r - omega) := by
  obtain ⟨ha, hb, hc, -, -⟩ := chartFactors_pos h
  have hdiag : chartDiagonalMass r omega * ((1 - r) * (1 - omega))
      = 1 - r - omega := by
    rw [diagonalMass_eq h]
    exact div_mul_cancel₀ _ (chartNorm_ne h)
  have hdiag_pos : 0 < chartDiagonalMass r omega := by
    rw [diagonalMass_eq h]
    exact div_pos hc (mul_pos ha hb)
  rw [div_eq_div_iff hdiag_pos.ne' hc.ne']
  refine mul_right_cancel₀ (chartNorm_ne h) ?_
  linear_combination (1 - r - omega) * mass_mul_norm h - (omega * r) * hdiag

/-- The off-diagonal mass is below one third on the chart domain. -/
theorem chartOffDiagonalMass_lt_third (h : ChartDomain r omega) :
    chartOffDiagonalMass r omega < 1 / 3 := by
  obtain ⟨ha, hb, -, -, -⟩ := chartFactors_pos h
  rw [chartOffDiagonalMass_eq, div_lt_iff₀ (mul_pos ha hb)]
  have hpr : 0 < omega * (1 - r) := mul_pos h.product_pos ha
  nlinarith [h.interior]

/-! ## The weighted sum in closed form -/

private theorem weighted_numerator_left (h : ChartDomain r omega) :
    chartDeterminant r omega * chartOffDiagonalMass r omega
        + 2 * chartOffDiagonalProduct r omega
      = omega ^ 3 * (1 - omega) * (2 - r) / ((1 - r) * (1 - omega)) ^ 3 := by
  rw [chartDeterminant_eq, chartOffDiagonalMass_eq, chartOffDiagonalProduct_eq]
  have hn := chartNorm_ne h
  field_simp [hn]
  ring

private theorem mass_sq_sub_two_product (h : ChartDomain r omega) :
    chartOffDiagonalMass r omega ^ 2 - 2 * chartOffDiagonalProduct r omega
      = omega ^ 2 * (r ^ 2 - 2 * omega) / ((1 - r) * (1 - omega)) ^ 2 := by
  rw [chartOffDiagonalMass_eq, chartOffDiagonalProduct_eq]
  have hn := chartNorm_ne h
  field_simp [hn]

private theorem weighted_numerator_right (h : ChartDomain r omega) :
    chartDeterminant r omega
          * (chartOffDiagonalMass r omega ^ 2
              - 2 * chartOffDiagonalProduct r omega)
        + chartOffDiagonalProduct r omega * chartOffDiagonalMass r omega
      = omega ^ 4 * (1 - omega) * (r - 2 * omega)
        / ((1 - r) * (1 - omega)) ^ 4 := by
  rw [chartDeterminant_eq, mass_sq_sub_two_product h, chartOffDiagonalProduct_eq,
    chartOffDiagonalMass_eq]
  have hn := chartNorm_ne h
  field_simp [hn]
  ring

private theorem weighted_numerator (h : ChartDomain r omega) :
    chartCommonDeriv r omega
          * (chartDeterminant r omega * chartOffDiagonalMass r omega
              + 2 * chartOffDiagonalProduct r omega)
        + chartDeterminant r omega
            * (chartOffDiagonalMass r omega ^ 2
                - 2 * chartOffDiagonalProduct r omega)
        + chartOffDiagonalProduct r omega * chartOffDiagonalMass r omega
      = omega ^ 4 * (1 - omega) ^ 2
          * (-2 * omega ^ 2 - omega * r ^ 2 + omega * r + 2 * omega
              + 2 * r ^ 3 - 5 * r ^ 2 + 3 * r)
        / (((1 - r) * (1 - omega)) ^ 5 * (3 - 2 * r - omega)) := by
  obtain ⟨-, -, -, -, hf⟩ := chartFactors_pos h
  rw [chartCommonDeriv_eq h, weighted_numerator_left h]
  calc
    _ = 2 * omega ^ 2 * (1 - omega) * (2 - r - omega)
          / (((1 - r) * (1 - omega)) ^ 2 * (3 - 2 * r - omega))
          * (omega ^ 3 * (1 - omega) * (2 - r) / ((1 - r) * (1 - omega)) ^ 3)
        + (chartDeterminant r omega
              * (chartOffDiagonalMass r omega ^ 2
                  - 2 * chartOffDiagonalProduct r omega)
            + chartOffDiagonalProduct r omega
                * chartOffDiagonalMass r omega) := by ring
    _ = _ := by
      rw [weighted_numerator_right h]
      have hn := chartNorm_ne h
      field_simp [hn, hf.ne']
      ring

private theorem weighted_denominator (h : ChartDomain r omega) :
    chartDeterminant r omega ^ 2
        + chartDeterminant r omega * chartOffDiagonalMass r omega
        + chartOffDiagonalProduct r omega
      = omega ^ 3 * (1 - omega) ^ 2 * (1 - r + omega)
        / ((1 - r) * (1 - omega)) ^ 4 := by
  rw [chartDeterminant_eq, chartOffDiagonalMass_eq, chartOffDiagonalProduct_eq]
  have hn := chartNorm_ne h
  field_simp [hn]
  ring

private theorem chartWeightedLogDeriv_eq (h : ChartDomain r omega) :
    chartWeightedLogDeriv r omega
      = omega * (-2 * omega ^ 2 - omega * r ^ 2 + omega * r + 2 * omega
            + 2 * r ^ 3 - 5 * r ^ 2 + 3 * r)
        / ((1 - r) * (1 - omega) * (1 - r + omega) * (3 - 2 * r - omega)) := by
  obtain ⟨-, hb, -, hA, hf⟩ := chartFactors_pos h
  unfold chartWeightedLogDeriv
  rw [weighted_numerator h, weighted_denominator h]
  have hn := chartNorm_ne h
  field_simp [hn, hA.ne', hf.ne', h.product_pos.ne', hb.ne']

/-! ## The contact coefficient -/

/-- The page's step from display (3.9) to display (3.7): its second-order
coefficient for the contact correction is the radial derivative of the tangent
coefficient.  The page reaches this by simplifying a factor `v + s` to one;
here both sides are carried to the same closed form instead. -/
theorem chartContactSecondOrder_eq_logKDeriv (h : ChartDomain r omega) :
    chartContactSecondOrder r omega = chartLogKDeriv r omega := by
  obtain ⟨-, -, -, hA, hf⟩ := chartFactors_pos h
  have hn := chartNorm_ne h
  have hlog : chartLogKDeriv r omega * ((1 - r + omega) * (3 - 2 * r - omega))
      = omega * (3 * omega * r - 4 * omega - 2 * r ^ 2 + 3 * r) := by
    rw [chartLogKDeriv_eq h]
    exact div_mul_cancel₀ _ (mul_ne_zero hA.ne' hf.ne')
  have hweight : chartWeightedLogDeriv r omega
        * ((1 - r) * (1 - omega) * (1 - r + omega) * (3 - 2 * r - omega))
      = omega * (-2 * omega ^ 2 - omega * r ^ 2 + omega * r + 2 * omega
          + 2 * r ^ 3 - 5 * r ^ 2 + 3 * r) := by
    rw [chartWeightedLogDeriv_eq h]
    exact div_mul_cancel₀ _
      (mul_ne_zero (mul_ne_zero (chartNorm_ne h) hA.ne') hf.ne')
  unfold chartContactSecondOrder
  refine mul_left_cancel₀ hn ?_
  refine mul_left_cancel₀ (mul_ne_zero hA.ne' hf.ne') ?_
  linear_combination
    ((1 - r) * (1 - omega) * chartOffDiagonalMass r omega
        - (1 - r) * (1 - omega)) * hlog
      + (omega * (3 * omega * r - 4 * omega - 2 * r ^ 2 + 3 * r)
          + 3 * ((1 - r + omega) * (3 - 2 * r - omega))) * mass_mul_norm h
      - 2 * hweight

/-- The page's display (3.8): the contact correction's second-order coefficient
is strictly below the ratio of off-diagonal to diagonal mass, the difference
being an explicit positive quantity. -/
theorem chartContactSecondOrder_lt (h : ChartDomain r omega) :
    chartContactSecondOrder r omega
      < chartOffDiagonalMass r omega / chartDiagonalMass r omega := by
  obtain ⟨-, hb, hc, hA, hf⟩ := chartFactors_pos h
  rw [chartContactSecondOrder_eq_logKDeriv h, chartLogKDeriv_eq h,
    chartMassRatio_eq h, div_lt_div_iff₀ (mul_pos hA hf) hc]
  have key : omega * r * ((1 - r + omega) * (3 - 2 * r - omega))
      - omega * (3 * omega * r - 4 * omega - 2 * r ^ 2 + 3 * r) * (1 - r - omega)
      = 2 * omega ^ 2 * (1 - omega) * (2 - r) := by ring
  rw [← sub_pos, key]
  have hsq : 0 < omega ^ 2 := pow_pos h.product_pos 2
  have hr2 : 0 < 2 - r := by linarith [h.sum_lt_one]
  exact mul_pos (mul_pos (mul_pos (by norm_num) hsq) hb) hr2

/-! ## Both margin expressions are negative -/

private theorem chartB_pos (h : ChartDomain r omega) :
    0 < 2 * omega * r - omega - r + 1 := by
  obtain ⟨ha, hb, -, -, -⟩ := chartFactors_pos h
  have hn : 0 < (1 - r) * (1 - omega) := mul_pos ha hb
  have hpr : 0 < omega * r := mul_pos h.product_pos h.sum_pos
  nlinarith

private theorem one_sub_mass_sq_eq (h : ChartDomain r omega) :
    1 - chartOffDiagonalMass r omega ^ 2
      = (1 - r - omega) * (2 * omega * r - omega - r + 1)
        / ((1 - r) * (1 - omega)) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 (chartNorm_ne h))]
  nlinarith [congrArg (fun x : ℝ => x ^ 2) (mass_mul_norm h)]

private theorem one_sub_mass_sq_pos (h : ChartDomain r omega) :
    0 < 1 - chartOffDiagonalMass r omega ^ 2 := by
  obtain ⟨ha, hb, hc, -, -⟩ := chartFactors_pos h
  rw [one_sub_mass_sq_eq h]
  exact div_pos (mul_pos hc (chartB_pos h)) (pow_pos (mul_pos ha hb) 2)

private theorem discriminant_le_mass_sq (h : ChartDomain r omega) :
    chartDiscriminant r omega ≤ chartOffDiagonalMass r omega ^ 2 := by
  unfold chartDiscriminant chartOffDiagonalMass
  nlinarith [mul_nonneg h.product_pos.le (sq_nonneg (chartRoot r omega))]

private theorem discriminant_ratio_le (h : ChartDomain r omega) :
    chartDiscriminant r omega / (1 - chartDiscriminant r omega)
      ≤ chartOffDiagonalMass r omega ^ 2
        / (1 - chartOffDiagonalMass r omega ^ 2) := by
  obtain ⟨-, -, -, -, -, -, hd⟩ := chart_pos h
  rw [div_le_div_iff₀ hd (one_sub_mass_sq_pos h)]
  nlinarith [discriminant_le_mass_sq h]

private theorem key_constant (v : ℝ) (hv0 : 0 < v) (hv3 : v < 1 / 3) :
    -3 * (v / (1 - v)) + 6 * (v ^ 2 / (1 - v ^ 2)) < 0 := by
  have hm : (1 : ℝ) - v ≠ 0 := by linarith
  have hp : (1 : ℝ) + v ≠ 0 := by linarith
  have hsq : (1 : ℝ) - v ^ 2 ≠ 0 := by nlinarith
  have e : -3 * (v / (1 - v)) + 6 * (v ^ 2 / (1 - v ^ 2)) = -3 * v / (1 + v) := by
    field_simp
    ring
  rw [e]
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

private theorem key_singleton (v : ℝ) (hv0 : 0 < v) (hv3 : v < 1 / 3) :
    -(v / (1 - v)) + 3 * (v ^ 2 / (1 - v ^ 2)) < 0 := by
  have hm : (1 : ℝ) - v ≠ 0 := by linarith
  have hsq : (0 : ℝ) < 1 - v ^ 2 := by nlinarith
  have e : -(v / (1 - v)) + 3 * (v ^ 2 / (1 - v ^ 2))
      = -(v * (1 - 2 * v)) / (1 - v ^ 2) := by
    field_simp
    ring
  rw [e]
  have hnum : 0 < v * (1 - 2 * v) := mul_pos hv0 (by linarith)
  exact div_neg_of_neg_of_pos (by linarith) hsq

private theorem diagonalMass_eq_one_sub (r omega : ℝ) :
    chartDiagonalMass r omega = 1 - chartOffDiagonalMass r omega := rfl

/-- The constant margin's second-order expression is negative on the chart
domain: the page's first line of display (4.3), without its identification of
the expression with a second derivative. -/
theorem chartConstantSecondOrder_neg (h : ChartDomain r omega) :
    chartConstantSecondOrder r omega < 0 := by
  obtain ⟨-, -, -, hv0, -, -, -⟩ := chart_pos h
  have hkey := key_constant _ hv0 (chartOffDiagonalMass_lt_third h)
  rw [← diagonalMass_eq_one_sub r omega] at hkey
  have e : chartConstantSecondOrder r omega
      = -5 * (chartOffDiagonalMass r omega / chartDiagonalMass r omega)
        + 6 * (chartDiscriminant r omega / (1 - chartDiscriminant r omega))
        + 2 * chartContactSecondOrder r omega := by
    unfold chartConstantSecondOrder
    ring
  rw [e]
  linarith [chartContactSecondOrder_lt h, discriminant_ratio_le h, hkey]

/-- The isolating code's margin has a negative second-order expression on the
chart domain: the page's second line of display (4.3), again without the
identification with a second derivative. -/
theorem chartSingletonSecondOrder_neg (h : ChartDomain r omega) :
    chartSingletonSecondOrder r omega < 0 := by
  obtain ⟨-, -, -, hv0, -, -, -⟩ := chart_pos h
  have hkey := key_singleton _ hv0 (chartOffDiagonalMass_lt_third h)
  rw [← diagonalMass_eq_one_sub r omega] at hkey
  have e : chartSingletonSecondOrder r omega
      = -3 * (chartOffDiagonalMass r omega / chartDiagonalMass r omega)
        + 4 * (chartDiscriminant r omega / (1 - chartDiscriminant r omega))
        - chartOffDiagonalMass r omega ^ 2
            / (1 - chartOffDiagonalMass r omega ^ 2)
        + 2 * chartContactSecondOrder r omega := by
    unfold chartSingletonSecondOrder
    ring
  rw [e]
  linarith [chartContactSecondOrder_lt h, discriminant_ratio_le h, hkey]

end StochasticToDeterministicLatents.Binary
