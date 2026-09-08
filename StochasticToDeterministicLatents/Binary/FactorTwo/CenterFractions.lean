/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Modified: the chart's
positivity facts are taken from `CenterChart` rather than re-derived, the
diagonal mass's fraction form is `chart_identities` rather than a second proof
of it, and the scalars are named for the quantities of the page's Lemma 3.4
whose chart forms they are.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterChart

/-!
# The chart's radial derivatives, in closed form

Moving along a ray of fixed imbalance, the contact's data has derivatives that
the page computes from the cubic.  This module carries them in the chart of
[CenterChart](CenterChart.lean): five scalars, and each one as an explicit
fraction in `r` and `omega`.

## The scalars

* `chartCubicDeriv` is `3 u ^ 2 - 2 v u - w`, the cubic's derivative in `u`,
  which the page writes `f'(u_0)`;
* `chartDeterminant` is `u ^ 2 - w`.  At a contact law the diagonal cells
  multiply to `u ^ 2`, so this is that law's determinant; **that identification
  is not stated here**, and nothing in this module mentions a law;
* `chartRootDeriv` is the root's radial derivative, the quotient the page gets
  by differentiating the cubic along the ray;
* `chartCommonDeriv` is the part of the two contact masses' radial derivatives
  that does not depend on which cell is taken;
* `chartLogKDeriv` is the radial derivative of `log K`.

## What is proved

Each scalar in closed form.  The last of them, `chartLogKDeriv_eq`, is the
page's display (3.7): the radial curvature of the contact correction, as a
ratio of two explicit polynomials in `r` and `omega`.  The three denominators
that appear -- `1 - r - omega`, `1 - r + omega` and `3 - 2 r - omega` -- are
positive on the chart's domain, which is the page's own list, and that is
`chartFactors_pos`.

Nothing here bounds anything.  The comparison that makes the centre's margins
concave is the next step and is not stated.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and module
boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {r omega : ℝ}

/-! ## The scalars -/

/-- The cubic's derivative in `u`, `3 u ^ 2 - 2 v u - w`. -/
noncomputable def chartCubicDeriv (r omega : ℝ) : ℝ :=
  3 * chartRoot r omega ^ 2 - 2 * chartOffDiagonalMass r omega * chartRoot r omega
    - chartOffDiagonalProduct r omega

/-- `u ^ 2 - w`.  At a contact law this is the determinant; that is not stated
here. -/
noncomputable def chartDeterminant (r omega : ℝ) : ℝ :=
  chartRoot r omega ^ 2 - chartOffDiagonalProduct r omega

/-- The root's radial derivative. -/
noncomputable def chartRootDeriv (r omega : ℝ) : ℝ :=
  (chartOffDiagonalMass r omega * chartDeterminant r omega
      + 2 * chartOffDiagonalProduct r omega
        * (chartRoot r omega + chartDiagonalMass r omega))
    / chartCubicDeriv r omega

/-- The cell-independent part of the contact masses' radial derivatives. -/
noncomputable def chartCommonDeriv (r omega : ℝ) : ℝ :=
  2 * chartRoot r omega * chartRootDeriv r omega
    - 2 * chartOffDiagonalProduct r omega

/-- The radial derivative of `log K`. -/
noncomputable def chartLogKDeriv (r omega : ℝ) : ℝ :=
  (-chartOffDiagonalMass r omega + 2 * chartRootDeriv r omega)
      / (chartDiagonalMass r omega + 2 * chartRoot r omega)
    - 2 * (-chartOffDiagonalMass r omega + chartRootDeriv r omega)
      / (chartDiagonalMass r omega + chartRoot r omega)

/-! ## The positive factors -/

/-- **The page's list of positive factors.**  Every denominator below is one of
these. -/
theorem chartFactors_pos (h : ChartDomain r omega) :
    0 < 1 - r ∧ 0 < 1 - omega ∧ 0 < 1 - r - omega ∧ 0 < 1 - r + omega
      ∧ 0 < 3 - 2 * r - omega := by
  have ha : 0 < 1 - r := sub_pos.mpr h.sum_lt_one
  have hb : 0 < 1 - omega := by
    have := h.interior
    have := h.sum_pos
    linarith
  refine ⟨ha, hb, ?_, by linarith [h.product_pos], by linarith⟩
  have := h.interior
  have := h.product_pos
  linarith

/-! ## The scalars in closed form -/

private theorem chartRoot_eq (r omega : ℝ) :
    chartRoot r omega = omega / ((1 - r) * (1 - omega)) := rfl

private theorem chartRoot_sq_eq (r omega : ℝ) :
    chartRoot r omega ^ 2 = omega ^ 2 / ((1 - r) * (1 - omega)) ^ 2 := by
  rw [chartRoot_eq]
  field_simp

/-- The off-diagonal mass, as display (3.4) writes it. -/
theorem chartOffDiagonalMass_eq (r omega : ℝ) :
    chartOffDiagonalMass r omega = omega * r / ((1 - r) * (1 - omega)) := by
  rw [chartOffDiagonalMass, chartRoot_eq]
  ring

/-- The off-diagonal product, in closed form. -/
theorem chartOffDiagonalProduct_eq (r omega : ℝ) :
    chartOffDiagonalProduct r omega
      = omega ^ 3 / ((1 - r) * (1 - omega)) ^ 2 := by
  rw [chartOffDiagonalProduct, chartRoot_sq_eq r omega]
  ring

/-- The discriminant, in closed form. -/
theorem chartDiscriminant_frac (r omega : ℝ) :
    chartDiscriminant r omega
      = omega ^ 2 * (r ^ 2 - 4 * omega) / ((1 - r) * (1 - omega)) ^ 2 := by
  rw [chartDiscriminant, chartRoot_sq_eq r omega]
  ring

private theorem chartDiagonalMass_add_root (h : ChartDomain r omega) :
    chartDiagonalMass r omega + chartRoot r omega
      = (1 - r) / ((1 - r) * (1 - omega)) := by
  rw [(chart_identities h).1, chartRoot_eq, chartNorm]
  ring

private theorem chartDiagonalMass_add_two_root (h : ChartDomain r omega) :
    chartDiagonalMass r omega + 2 * chartRoot r omega
      = (1 - r + omega) / ((1 - r) * (1 - omega)) := by
  rw [(chart_identities h).1, chartRoot_eq, chartNorm]
  ring

/-- The cubic's derivative, in closed form. -/
theorem chartCubicDeriv_eq (h : ChartDomain r omega) :
    chartCubicDeriv r omega
      = omega ^ 2 * (3 - 2 * r - omega) / ((1 - r) * (1 - omega)) ^ 2 := by
  obtain ⟨ha, hb, -, -, -⟩ := chartFactors_pos h
  have hn : ((1 : ℝ) - r) * (1 - omega) ≠ 0 := (mul_pos ha hb).ne'
  rw [chartCubicDeriv, chartRoot_sq_eq r omega, chartOffDiagonalMass_eq,
    chartOffDiagonalProduct_eq r omega, chartRoot_eq]
  field_simp

/-- `u ^ 2 - w`, in closed form. -/
theorem chartDeterminant_eq (r omega : ℝ) :
    chartDeterminant r omega
      = omega ^ 2 * (1 - omega) / ((1 - r) * (1 - omega)) ^ 2 := by
  rw [chartDeterminant, chartRoot_sq_eq r omega, chartOffDiagonalProduct_eq r omega]
  ring

private theorem chartRootDeriv_num (h : ChartDomain r omega) :
    chartOffDiagonalMass r omega * chartDeterminant r omega
        + 2 * chartOffDiagonalProduct r omega
          * (chartRoot r omega + chartDiagonalMass r omega)
      = omega ^ 3 * (2 - r - omega * r) / ((1 - r) * (1 - omega)) ^ 3 := by
  obtain ⟨ha, hb, -, -, -⟩ := chartFactors_pos h
  have hn : ((1 : ℝ) - r) * (1 - omega) ≠ 0 := (mul_pos ha hb).ne'
  rw [chartOffDiagonalMass_eq, chartDeterminant_eq r omega,
    chartOffDiagonalProduct_eq r omega, add_comm (chartRoot r omega),
    chartDiagonalMass_add_root h]
  field_simp
  ring

/-- The root's radial derivative, in closed form. -/
theorem chartRootDeriv_eq (h : ChartDomain r omega) :
    chartRootDeriv r omega
      = omega * (2 - r - omega * r)
        / (((1 - r) * (1 - omega)) * (3 - 2 * r - omega)) := by
  obtain ⟨ha, hb, -, -, hf⟩ := chartFactors_pos h
  have hn : ((1 : ℝ) - r) * (1 - omega) ≠ 0 := (mul_pos ha hb).ne'
  rw [chartRootDeriv, chartRootDeriv_num h, chartCubicDeriv_eq h]
  field_simp [hf.ne', h.product_pos.ne']

private theorem chartLogKDeriv_left (h : ChartDomain r omega) :
    (-chartOffDiagonalMass r omega + 2 * chartRootDeriv r omega)
        / (chartDiagonalMass r omega + 2 * chartRoot r omega)
      = omega * (4 - 5 * r + 2 * r ^ 2 - omega * r)
        / ((1 - r + omega) * (3 - 2 * r - omega)) := by
  obtain ⟨ha, hb, -, hA, hf⟩ := chartFactors_pos h
  have hn : (0 : ℝ) < (1 - r) * (1 - omega) := mul_pos ha hb
  rw [chartOffDiagonalMass_eq, chartRootDeriv_eq h,
    chartDiagonalMass_add_two_root h]
  have hden : ((1 : ℝ) - r + omega) / ((1 - r) * (1 - omega)) ≠ 0 :=
    div_ne_zero hA.ne' hn.ne'
  rw [div_eq_iff hden]
  have hcore : -r + 2 * (2 - r - omega * r) / (3 - 2 * r - omega)
      = (4 - 5 * r + 2 * r ^ 2 - omega * r) / (3 - 2 * r - omega) := by
    have hr : -r = -r * (3 - 2 * r - omega) / (3 - 2 * r - omega) := by
      rw [mul_div_assoc, div_self hf.ne', mul_one]
    rw [hr]
    field_simp
    ring
  have hterm : omega * (2 - r - omega * r)
        / (((1 - r) * (1 - omega)) * (3 - 2 * r - omega))
      = omega / ((1 - r) * (1 - omega)) * ((2 - r - omega * r) / (3 - 2 * r - omega)) := by
    rw [div_mul_div_comm]
  calc
    -(omega * r / ((1 - r) * (1 - omega)))
        + 2 * (omega * (2 - r - omega * r)
          / (((1 - r) * (1 - omega)) * (3 - 2 * r - omega)))
        = omega / ((1 - r) * (1 - omega))
          * (-r + 2 * (2 - r - omega * r) / (3 - 2 * r - omega)) := by
          rw [hterm]; ring
    _ = omega / ((1 - r) * (1 - omega))
          * ((4 - 5 * r + 2 * r ^ 2 - omega * r) / (3 - 2 * r - omega)) := by
          rw [hcore]
    _ = omega * (4 - 5 * r + 2 * r ^ 2 - omega * r)
          / ((1 - r + omega) * (3 - 2 * r - omega))
        * ((1 - r + omega) / ((1 - r) * (1 - omega))) := by
      rw [div_mul_div_comm, div_mul_div_comm]
      exact (div_eq_div_iff (mul_ne_zero hn.ne' hf.ne')
        (mul_ne_zero (mul_ne_zero hA.ne' hf.ne') hn.ne')).2 (by ring)

private theorem chartLogKDeriv_right (h : ChartDomain r omega) :
    2 * (-chartOffDiagonalMass r omega + chartRootDeriv r omega)
        / (chartDiagonalMass r omega + chartRoot r omega)
      = 4 * omega * (1 - r) / (3 - 2 * r - omega) := by
  obtain ⟨ha, hb, -, -, hf⟩ := chartFactors_pos h
  have hn : ((1 : ℝ) - r) * (1 - omega) ≠ 0 := (mul_pos ha hb).ne'
  rw [chartOffDiagonalMass_eq, chartRootDeriv_eq h, chartDiagonalMass_add_root h]
  field_simp [ha.ne', hb.ne', hf.ne']
  ring

/-- **Display (3.7).**  The radial derivative of `log K`, as a ratio of two
explicit polynomials in the chart's parameters. -/
theorem chartLogKDeriv_eq (h : ChartDomain r omega) :
    chartLogKDeriv r omega
      = omega * (3 * omega * r - 4 * omega - 2 * r ^ 2 + 3 * r)
        / ((1 - r + omega) * (3 - 2 * r - omega)) := by
  obtain ⟨-, -, -, hA, hf⟩ := chartFactors_pos h
  rw [chartLogKDeriv, chartLogKDeriv_left h, chartLogKDeriv_right h]
  field_simp [hf.ne', hA.ne']
  ring

/-- The cell-independent part of the masses' radial derivatives, in closed
form. -/
theorem chartCommonDeriv_eq (h : ChartDomain r omega) :
    chartCommonDeriv r omega
      = 2 * omega ^ 2 * (1 - omega) * (2 - r - omega)
        / (((1 - r) * (1 - omega)) ^ 2 * (3 - 2 * r - omega)) := by
  obtain ⟨ha, hb, -, -, hf⟩ := chartFactors_pos h
  have hn : ((1 : ℝ) - r) * (1 - omega) ≠ 0 := (mul_pos ha hb).ne'
  rw [chartCommonDeriv, chartRootDeriv_eq h, chartOffDiagonalProduct_eq r omega,
    chartRoot_eq]
  field_simp
  ring

end StochasticToDeterministicLatents.Binary
