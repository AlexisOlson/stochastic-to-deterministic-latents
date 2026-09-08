/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Modified: the chart's
identities are stated as the page's display (3.4) rather than left implicit in
the definitions, the diagonal mass is carried in the page's closed form as well
as the definitional one, and the rational-certificate polynomials of the source
module are dropped, being consumed by nothing.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.Defs

/-!
# The contact chart

Along the contact chord the cubic's positive root `u` can be used to rescale
the two off-diagonal cells.  Writing `x = b / u` and `y = c / u`, everything in
the centre's argument depends on the pair only through

```
r = x + y,    omega = x * y,
```

and this module is the resulting two-parameter chart: its domain, its six
scalars, and the identities that make it a chart.

## What the chart is for

`chartRoot` is not *asserted* to solve the cubic -- it solves it by
construction.  With `chartNorm r omega = (1 - r) * (1 - omega)` and
`chartRoot = omega / chartNorm`,

```
u ^ 3 - v * u ^ 2 - w * u - w * s = u ^ 2 * (u * chartNorm - omega) = 0,
```

which is `chartRoot_cubic`, and the polynomial on the left is `cubic` written
out in `offDiagonalMass`, `offDiagonalProduct` and `diagonalMass`.  So the
chart's scalars are those three quantities and the cubic's root, in
coordinates, and `chartDiscriminant` is the cubic's discriminant `v ^ 2 - 4 w`.

Nothing here mentions a law: the identification of these scalars with the cells
of a chord domain is a separate step, and no declaration in this module is
evidence about any law.

## Against the page

This is the contact chart and Lemma 3.3 of the factor-two page.
`ChartDomain` is that lemma's set -- `x, y > 0` with `r + 3 omega < 1`, carried
in the symmetric functions, together with the condition `4 omega <= r ^ 2` that
makes `x` and `y` real.  `chart_identities` is its display (3.4): the first
entry is `chartRoot`'s definition, the second is that definition up to
associating a product, and the remaining three are proved.  The page derives
`u * n = omega` from the cubic; here that equation is the definition and the
cubic's vanishing is what follows, which is the lemma's converse direction.
The page writes the second parameter `omega`; this module does the same.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and module
boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {r omega : ℝ}

/-! ## The chart's domain -/

/-- The chart's parameter set: the symmetric functions of two positive
rescaled cells, inside the region where the contact chord's root stays below
the diagonal cell.  `real_factors` is what makes `x` and `y` real. -/
structure ChartDomain (r omega : ℝ) : Prop where
  /-- The rescaled cells have positive product. -/
  product_pos : 0 < omega
  /-- The rescaled cells have positive sum. -/
  sum_pos : 0 < r
  /-- The sum stays below one. -/
  sum_lt_one : r < 1
  /-- The root stays below the diagonal cell: the page's `r + 3 omega < 1`. -/
  interior : 0 < 1 - r - 3 * omega
  /-- The two rescaled cells are real. -/
  real_factors : 4 * omega ≤ r ^ 2

/-! ## The scalars -/

/-- The chart's normalizer, `(1 - r)(1 - omega)`. -/
noncomputable def chartNorm (r omega : ℝ) : ℝ := (1 - r) * (1 - omega)

/-- The cubic's positive root, in the chart. -/
noncomputable def chartRoot (r omega : ℝ) : ℝ := omega / chartNorm r omega

/-- The off-diagonal mass `v = b + c`, in the chart. -/
noncomputable def chartOffDiagonalMass (r omega : ℝ) : ℝ := r * chartRoot r omega

/-- The diagonal mass `s = a + d`, in the chart. -/
noncomputable def chartDiagonalMass (r omega : ℝ) : ℝ :=
  1 - chartOffDiagonalMass r omega

/-- The off-diagonal product `w = b * c`, in the chart. -/
noncomputable def chartOffDiagonalProduct (r omega : ℝ) : ℝ :=
  omega * chartRoot r omega ^ 2

/-- The cubic's discriminant `v ^ 2 - 4 w`, in the chart. -/
noncomputable def chartDiscriminant (r omega : ℝ) : ℝ :=
  (r ^ 2 - 4 * omega) * chartRoot r omega ^ 2

/-! ## The chart is a chart -/

/-- The second parameter is below one, which is what makes the normalizer
positive. -/
private theorem product_lt_one (h : ChartDomain r omega) : omega < 1 := by
  have := h.interior
  have := h.sum_pos
  linarith

private theorem chartNorm_pos (h : ChartDomain r omega) : 0 < chartNorm r omega :=
  mul_pos (sub_pos.mpr h.sum_lt_one) (sub_pos.mpr (product_lt_one h))

/-- **The root solves the cubic, by construction.**  The polynomial is `cubic`
written out in the three quantities the chart supplies. -/
theorem chartRoot_cubic (h : ChartDomain r omega) :
    chartRoot r omega ^ 3
        - chartOffDiagonalMass r omega * chartRoot r omega ^ 2
        - chartOffDiagonalProduct r omega * chartRoot r omega
        - chartOffDiagonalProduct r omega * chartDiagonalMass r omega = 0 := by
  have hn := chartNorm_pos h
  have hun : chartRoot r omega * chartNorm r omega = omega := by
    rw [chartRoot]
    field_simp
  have key : chartRoot r omega ^ 3
        - chartOffDiagonalMass r omega * chartRoot r omega ^ 2
        - chartOffDiagonalProduct r omega * chartRoot r omega
        - chartOffDiagonalProduct r omega * chartDiagonalMass r omega
      = chartRoot r omega ^ 2
          * (chartRoot r omega * chartNorm r omega - omega) := by
    simp only [chartOffDiagonalMass, chartDiagonalMass, chartOffDiagonalProduct,
      chartNorm]
    ring
  rw [key, hun, sub_self, mul_zero]

/-- **The discriminant is the cubic's.** -/
theorem chartDiscriminant_eq (r omega : ℝ) :
    chartDiscriminant r omega
      = chartOffDiagonalMass r omega ^ 2 - 4 * chartOffDiagonalProduct r omega := by
  simp only [chartDiscriminant, chartOffDiagonalMass, chartOffDiagonalProduct]
  ring

/-- **Display (3.4).**  The three identities of the page's chart lemma that are
not definitional here: the diagonal mass in closed form, the gap between the
root and the off-diagonal mass, and the gap to twice the root. -/
theorem chart_identities (h : ChartDomain r omega) :
    chartDiagonalMass r omega = (1 - r - omega) / chartNorm r omega
      ∧ chartRoot r omega - chartOffDiagonalMass r omega = omega / (1 - omega)
      ∧ chartDiagonalMass r omega - 2 * chartRoot r omega
          = (1 - r - 3 * omega) / chartNorm r omega := by
  have hn := chartNorm_pos h
  have hw : (1 : ℝ) - omega ≠ 0 := sub_ne_zero.mpr (product_lt_one h).ne'
  have hr : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr h.sum_lt_one.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp only [chartDiagonalMass, chartOffDiagonalMass, chartRoot, chartNorm]
    field_simp
    ring
  · simp only [chartOffDiagonalMass, chartRoot, chartNorm]
    field_simp
  · simp only [chartDiagonalMass, chartOffDiagonalMass, chartRoot, chartNorm]
    field_simp
    ring

/-! ## Positivity on the domain -/

/-- **The chart's positivity, proved once.**  Every module above this one works
on a `ChartDomain`, and each of these is wanted there. -/
theorem chart_pos (h : ChartDomain r omega) :
    0 < chartNorm r omega ∧ 0 < chartRoot r omega ∧ chartRoot r omega < 1
      ∧ 0 < chartOffDiagonalMass r omega ∧ 0 < chartDiagonalMass r omega
      ∧ 0 < chartOffDiagonalProduct r omega
      ∧ 0 < 1 - chartDiscriminant r omega := by
  have hn := chartNorm_pos h
  have hu : 0 < chartRoot r omega := div_pos h.product_pos hn
  have homega : omega < chartNorm r omega := by
    have := h.interior
    have := h.sum_pos
    have := mul_pos h.sum_pos h.product_pos
    simp only [chartNorm]
    nlinarith
  have hu1 : chartRoot r omega < 1 := (div_lt_one hn).2 homega
  have hv : 0 < chartOffDiagonalMass r omega :=
    mul_pos h.sum_pos hu
  have hv1 : chartOffDiagonalMass r omega < 1 := by
    simp only [chartOffDiagonalMass]
    nlinarith [h.sum_lt_one, h.sum_pos]
  have hs : 0 < chartDiagonalMass r omega := by
    simp only [chartDiagonalMass]; linarith
  have hw : 0 < chartOffDiagonalProduct r omega := by
    simp only [chartOffDiagonalProduct]
    exact mul_pos h.product_pos (pow_pos hu 2)
  refine ⟨hn, hu, hu1, hv, hs, hw, ?_⟩
  have hd : chartDiscriminant r omega
      ≤ chartOffDiagonalMass r omega ^ 2 := by
    rw [chartDiscriminant_eq]; linarith
  nlinarith [hv, hv1]

end StochasticToDeterministicLatents.Binary
