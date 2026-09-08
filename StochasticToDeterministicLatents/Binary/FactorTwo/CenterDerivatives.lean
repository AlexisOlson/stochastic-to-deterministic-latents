/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Two theorems of the private
working material are merged into one here, and the diagonal mass is written
throughout with the public `chartDiagonalMass` rather than with the private
module's expanded expression.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterLaws

/-!
# Derivatives in the contact chart

Move along a path in the chart, that is, let the two rescaled off-diagonal
cells `x` and `y` be differentiable functions of a real parameter.  This
module differentiates the chart's quantities along such a path: the root, the
diagonal certificate value's logarithm, and the height.

The height's derivative is the page's display **(3.3)** contracted against the
path's velocity in the contact's two off-diagonal cells: the coefficient of
the first is `log K + log L_b` and the coefficient of the second is
`log K + log L_c`.  The page states (3.3) inside a lemma that also asserts
smoothness in those cells by the implicit function theorem; **neither that
smoothness nor differentiability in the cells themselves is stated here**,
since the chart's inverse is not shown to be differentiable.

`CenterFractions` defines `chartRootDeriv`, `chartCommonDeriv` and
`chartLogKDeriv` as radial *expressions* and does not claim that they are
derivatives.  The theorems below are about an **arbitrary** differentiable
path, and their values are the quotient rule's, not those expressions.
Nothing here connects the two; `CenterRayMargins` connects `chartRootDeriv`,
along the ray.
-/

namespace StochasticToDeterministicLatents.Binary

variable {X Y : ℝ → ℝ} {t dx dy du : ℝ}

/-! ## The root along a path -/

private theorem chartDiagonalMass_eq (x y : ℝ) :
    chartDiagonalMass (x + y) (x * y)
      = 1 - x * chartRoot (x + y) (x * y) - y * chartRoot (x + y) (x * y) := by
  unfold chartDiagonalMass chartOffDiagonalMass
  ring

/-- The chart's root has a derivative along any differentiable path with
positive coordinates below the boundary, and its value is the quotient rule's.
This is not `chartRootDeriv`: that expression is the root's derivative in the
off-diagonal mass times that mass, which `CenterRayMargins` proves and this
module does not. -/
theorem hasDerivAt_chartRoot (hX : HasDerivAt X dx t) (hY : HasDerivAt Y dy t)
    (hx : 0 < X t) (hy : 0 < Y t) (hr : X t + Y t < 1) :
    HasDerivAt (fun s => chartRoot (X s + Y s) (X s * Y s))
      (((dx * Y t + X t * dy) * chartNorm (X t + Y t) (X t * Y t)
          + X t * Y t * ((dx + dy) * (1 - X t * Y t)
            + (1 - (X t + Y t)) * (dx * Y t + X t * dy)))
        / chartNorm (X t + Y t) (X t * Y t) ^ 2) t := by
  have hplt : X t * Y t < 1 := by
    have hxlt : X t < 1 := by linarith
    have hylt : Y t < 1 := by linarith
    nlinarith [mul_pos hx (sub_pos.mpr hxlt), mul_pos hy (sub_pos.mpr hylt)]
  have hn : chartNorm (X t + Y t) (X t * Y t) ≠ 0 := by
    unfold chartNorm
    exact mul_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
  have hr' : HasDerivAt (fun s => X s + Y s) (dx + dy) t := hX.add hY
  have hp : HasDerivAt (fun s => X s * Y s) (dx * Y t + X t * dy) t := hX.mul hY
  have hn' : HasDerivAt
      (fun s => chartNorm (X s + Y s) (X s * Y s))
      (-(dx + dy) * (1 - X t * Y t)
        + (1 - (X t + Y t)) * (-(dx * Y t + X t * dy))) t := by
    change HasDerivAt
      (fun s => (1 - (X s + Y s)) * (1 - X s * Y s)) _ t
    exact (hr'.const_sub 1).mul (hp.const_sub 1)
  change HasDerivAt
    (fun s => (X s * Y s)
      / ((1 - (X s + Y s)) * (1 - X s * Y s))) _ t
  have hq := hp.div hn' hn
  have hfun : ((fun s => X s * Y s)
      / fun s => chartNorm (X s + Y s) (X s * Y s))
      = (fun s => (X s * Y s)
        / ((1 - (X s + Y s)) * (1 - X s * Y s))) := by
    funext s
    simp [chartNorm]
  rw [hfun] at hq
  have hd :
      ((dx * Y t + X t * dy) * chartNorm (X t + Y t) (X t * Y t)
          + X t * Y t * ((dx + dy) * (1 - X t * Y t)
            + (1 - (X t + Y t)) * (dx * Y t + X t * dy)))
        / chartNorm (X t + Y t) (X t * Y t) ^ 2
      = ((dx * Y t + X t * dy) * chartNorm (X t + Y t) (X t * Y t)
          - X t * Y t * (-(dx + dy) * (1 - X t * Y t)
            + (1 - (X t + Y t)) * (-(dx * Y t + X t * dy))))
        / chartNorm (X t + Y t) (X t * Y t) ^ 2 := by ring
  rw [hd]
  exact hq

/-- A cell of the contact, along the path. -/
private theorem hasDerivAt_chartCell {Z : ℝ → ℝ} {dz : ℝ}
    (hZ : HasDerivAt Z dz t)
    (hU : HasDerivAt (fun s => chartRoot (X s + Y s) (X s * Y s)) du t) :
    HasDerivAt (fun s => Z s * chartRoot (X s + Y s) (X s * Y s))
      (dz * chartRoot (X t + Y t) (X t * Y t) + Z t * du) t :=
  hZ.mul hU

/-- The diagonal mass along the path. -/
private theorem hasDerivAt_chartDiagonalMass {db dc : ℝ}
    (hb : HasDerivAt (fun q => X q * chartRoot (X q + Y q) (X q * Y q)) db t)
    (hc : HasDerivAt (fun q => Y q * chartRoot (X q + Y q) (X q * Y q)) dc t) :
    HasDerivAt (fun q => chartDiagonalMass (X q + Y q) (X q * Y q))
      (-(db + dc)) t := by
  simp only [chartDiagonalMass_eq]
  exact (((hasDerivAt_const t (1 : ℝ)).sub hb).sub hc).congr_deriv (by ring)

/-! ## The diagonal certificate value -/

/-- The logarithm of the diagonal certificate value, along the path. -/
theorem hasDerivAt_log_certDiagonal (hX : HasDerivAt X dx t)
    (hY : HasDerivAt Y dy t)
    (hU : HasDerivAt (fun s => chartRoot (X s + Y s) (X s * Y s)) du t)
    (hx : 0 < X t) (hy : 0 < Y t) (hr : X t + Y t < 1) :
    HasDerivAt
      (fun q => Real.log
        (certDiagonal (chartDiagonalMass (X q + Y q) (X q * Y q))
          (chartRoot (X q + Y q) (X q * Y q))))
      ((-(dx * chartRoot (X t + Y t) (X t * Y t) + X t * du
            + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)) + 2 * du)
          / (chartDiagonalMass (X t + Y t) (X t * Y t)
              + 2 * chartRoot (X t + Y t) (X t * Y t))
        - 2 * (-(dx * chartRoot (X t + Y t) (X t * Y t) + X t * du
              + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)) + du)
          / (chartDiagonalMass (X t + Y t) (X t * Y t)
              + chartRoot (X t + Y t) (X t * Y t))) t := by
  have hb := hasDerivAt_chartCell hX hU
  have hc := hasDerivAt_chartCell hY hU
  have hs := hasDerivAt_chartDiagonalMass hb hc
  have hplt : X t * Y t < 1 := by
    have hxlt : X t < 1 := by linarith
    have hylt : Y t < 1 := by linarith
    nlinarith [mul_pos hx (sub_pos.mpr hxlt), mul_pos hy (sub_pos.mpr hylt)]
  have hu0 : 0 ≤ chartRoot (X t + Y t) (X t * Y t) := by
    unfold chartRoot chartNorm
    exact div_nonneg (mul_nonneg hx.le hy.le)
      (mul_nonneg (by linarith) (by linarith))
  have hsu : 0 < chartDiagonalMass (X t + Y t) (X t * Y t)
      + chartRoot (X t + Y t) (X t * Y t) := by
    rw [chartDiagonalMass_eq]
    nlinarith [hu0]
  have hs2u : 0 < chartDiagonalMass (X t + Y t) (X t * Y t)
      + 2 * chartRoot (X t + Y t) (X t * Y t) := by
    rw [chartDiagonalMass_eq]
    nlinarith [hu0]
  have hnum : HasDerivAt
      (fun q => chartDiagonalMass (X q + Y q) (X q * Y q)
        + 2 * chartRoot (X q + Y q) (X q * Y q))
      (-(dx * chartRoot (X t + Y t) (X t * Y t) + X t * du
          + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)) + 2 * du) t :=
    hs.add (hU.const_mul 2)
  have hden : HasDerivAt
      (fun q => (chartDiagonalMass (X q + Y q) (X q * Y q)
        + chartRoot (X q + Y q) (X q * Y q)) ^ 2)
      (2 * (chartDiagonalMass (X t + Y t) (X t * Y t)
          + chartRoot (X t + Y t) (X t * Y t))
        * (-(dx * chartRoot (X t + Y t) (X t * Y t) + X t * du
            + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)) + du)) t :=
    ((hs.add hU).pow 2).congr_deriv (by simp only [Pi.add_apply]; ring)
  have hK := hnum.div hden (pow_ne_zero 2 hsu.ne')
  have hlog := hK.log (ne_of_gt (div_pos hs2u (pow_pos hsu 2)))
  change HasDerivAt
    (fun q => Real.log
      ((chartDiagonalMass (X q + Y q) (X q * Y q)
          + 2 * chartRoot (X q + Y q) (X q * Y q))
        / (chartDiagonalMass (X q + Y q) (X q * Y q)
            + chartRoot (X q + Y q) (X q * Y q)) ^ 2)) _ t
  have hs2u' : chartDiagonalMass (X t + Y t) (X t * Y t)
      + chartRoot (X t + Y t) (X t * Y t) * 2 ≠ 0 := by
    rw [mul_comm (chartRoot (X t + Y t) (X t * Y t)) 2]
    exact hs2u.ne'
  refine hlog.congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp [hsu.ne', hs2u.ne', hs2u']

/-! ## The height -/

/-- The identity the chain rule leaves over: the contact's own contribution
cancels against the marginals'. -/
private theorem chartDeriv_residual (x y dx dy : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hr : x + y < 1) :
    let n := (1 - (x + y)) * (1 - x * y)
    let u := x * y / n
    let du := ((dx * y + x * dy) * n + x * y * ((dx + dy) * (1 - x * y)
      + (1 - (x + y)) * (dx * y + x * dy))) / n ^ 2
    let b := x * u
    let c := y * u
    let db := dx * u + x * du
    let dc := dy * u + y * du
    let s := 1 - b - c
    let ds := -(db + dc)
    (-s * ((ds + 2 * du) / (s + 2 * u) - 2 * (ds + du) / (s + u))
      + (db + dc) - 2 * (b + c) * (dx + dy) / (1 - (x + y))
      + 2 * b * dx / (1 - x) + 2 * c * dy / (1 - y) = 0) := by
  dsimp only
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have hxylt : x * y < 1 := by
    nlinarith [mul_pos hx hx1, mul_pos hy hy1]
  have hr0 : 1 - (x + y) ≠ 0 := ne_of_gt (by linarith)
  have hxy0 : 1 - x * y ≠ 0 := ne_of_gt (by linarith)
  have hx0 : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have hy0 : 1 - y ≠ 0 := ne_of_gt (by linarith)
  have hn0 : (1 - (x + y)) * (1 - x * y) ≠ 0 := mul_ne_zero hr0 hxy0
  let n := (1 - (x + y)) * (1 - x * y)
  let u := x * y / n
  let du := ((dx * y + x * dy) * n + x * y * ((dx + dy) * (1 - x * y)
    + (1 - (x + y)) * (dx * y + x * dy))) / n ^ 2
  let b := x * u
  let c := y * u
  let db := dx * u + x * du
  let dc := dy * u + y * du
  let s := 1 - b - c
  let ds := -(db + dc)
  have hsu : s + u = 1 / (1 - x * y) := by
    dsimp [s, b, c, u, n]
    field_simp
    ring
  have hs2u : s + 2 * u
      = (1 - x) * (1 - y) / ((1 - (x + y)) * (1 - x * y)) := by
    dsimp [s, b, c, u, n]
    field_simp
    ring
  rw [hsu, hs2u]
  field_simp
  ring

/-- Collecting the chain rule's terms into the two cell coefficients. -/
private theorem chartHeightDeriv_collect (x y u du dx dy LK lb lc L1 Lx Ly : ℝ)
    (hres : -(1 - x * u - y * u)
        * ((-((dx * u + x * du) + (dy * u + y * du)) + 2 * du)
              / ((1 - x * u - y * u) + 2 * u)
            - 2 * (-((dx * u + x * du) + (dy * u + y * du)) + du)
              / ((1 - x * u - y * u) + u))
        + ((dx * u + x * du) + (dy * u + y * du))
        - 2 * (x * u + y * u) * (dx + dy) / (1 - (x + y))
        + 2 * (x * u) * dx / (1 - x) + 2 * (y * u) * dy / (1 - y) = 0) :
    -(-((dx * u + x * du) + (dy * u + y * du))) * LK
      + (-(1 - x * u - y * u))
        * ((-((dx * u + x * du) + (dy * u + y * du)) + 2 * du)
              / ((1 - x * u - y * u) + 2 * u)
            - 2 * (-((dx * u + x * du) + (dy * u + y * du)) + du)
              / ((1 - x * u - y * u) + u))
      + (lb + 1) * (dx * u + x * du) + (lc + 1) * (dy * u + y * du)
      + 2 * ((dx * u + x * du) + (dy * u + y * du)) * L1
        + 2 * (x * u + y * u) * (-(dx + dy) / (1 - (x + y)))
      - 2 * (dx * u + x * du) * Lx - 2 * (x * u) * (-dx / (1 - x))
      - 2 * (dy * u + y * du) * Ly - 2 * (y * u) * (-dy / (1 - y))
    = (LK + (lb + 2 * L1 - 2 * Lx)) * (dx * u + x * du)
      + (LK + (lc + 2 * L1 - 2 * Ly)) * (dy * u + y * du) := by
  linear_combination hres

/-- The height's derivative, before the two coefficients are recognized. -/
private theorem hasDerivAt_chartHeight_raw (hX : HasDerivAt X dx t)
    (hY : HasDerivAt Y dy t)
    (hU : HasDerivAt (fun s => chartRoot (X s + Y s) (X s * Y s)) du t)
    (hx : 0 < X t) (hy : 0 < Y t) (hr : X t + Y t < 1) :
    HasDerivAt (fun q => chartHeight (X q) (Y q))
      (-(-((dx * chartRoot (X t + Y t) (X t * Y t) + X t * du)
            + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)))
          * Real.log (certDiagonal (chartDiagonalMass (X t + Y t) (X t * Y t))
              (chartRoot (X t + Y t) (X t * Y t)))
        + (-chartDiagonalMass (X t + Y t) (X t * Y t))
          * ((-((dx * chartRoot (X t + Y t) (X t * Y t) + X t * du)
                  + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du))
                + 2 * du)
                / (chartDiagonalMass (X t + Y t) (X t * Y t)
                    + 2 * chartRoot (X t + Y t) (X t * Y t))
              - 2 * (-((dx * chartRoot (X t + Y t) (X t * Y t) + X t * du)
                    + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)) + du)
                / (chartDiagonalMass (X t + Y t) (X t * Y t)
                    + chartRoot (X t + Y t) (X t * Y t)))
        + (Real.log (X t * chartRoot (X t + Y t) (X t * Y t)) + 1)
            * (dx * chartRoot (X t + Y t) (X t * Y t) + X t * du)
        + (Real.log (Y t * chartRoot (X t + Y t) (X t * Y t)) + 1)
            * (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)
        + 2 * ((dx * chartRoot (X t + Y t) (X t * Y t) + X t * du)
            + (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du))
            * Real.log (1 - (X t + Y t))
        + 2 * (X t * chartRoot (X t + Y t) (X t * Y t)
            + Y t * chartRoot (X t + Y t) (X t * Y t))
            * (-(dx + dy) / (1 - (X t + Y t)))
        - 2 * (dx * chartRoot (X t + Y t) (X t * Y t) + X t * du)
            * Real.log (1 - X t)
        - 2 * (X t * chartRoot (X t + Y t) (X t * Y t)) * (-dx / (1 - X t))
        - 2 * (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)
            * Real.log (1 - Y t)
        - 2 * (Y t * chartRoot (X t + Y t) (X t * Y t))
            * (-dy / (1 - Y t))) t := by
  have hb := hasDerivAt_chartCell hX hU
  have hc := hasDerivAt_chartCell hY hU
  have hs := hasDerivAt_chartDiagonalMass hb hc
  have hK := hasDerivAt_log_certDiagonal hX hY hU hx hy hr
  have hplt : X t * Y t < 1 := by
    have hxlt : X t < 1 := by linarith
    have hylt : Y t < 1 := by linarith
    nlinarith [mul_pos hx (sub_pos.mpr hxlt), mul_pos hy (sub_pos.mpr hylt)]
  have hu0 : chartRoot (X t + Y t) (X t * Y t) ≠ 0 := by
    unfold chartRoot chartNorm
    exact div_ne_zero (mul_ne_zero hx.ne' hy.ne')
      (mul_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (by linarith)))
  have hb0 : X t * chartRoot (X t + Y t) (X t * Y t) ≠ 0 :=
    mul_ne_zero hx.ne' hu0
  have hc0 : Y t * chartRoot (X t + Y t) (X t * Y t) ≠ 0 :=
    mul_ne_zero hy.ne' hu0
  have hBlog := (hasDerivAt_xLogX hb0).comp t hb
  have hClog := (hasDerivAt_xLogX hc0).comp t hc
  have hL1 := ((hasDerivAt_const t (1 : ℝ)).sub (hX.add hY)).log (by
    simp only [Pi.sub_apply, Pi.add_apply]; linarith)
  have hLx := ((hasDerivAt_const t (1 : ℝ)).sub hX).log (by
    simp only [Pi.sub_apply]; linarith)
  have hLy := ((hasDerivAt_const t (1 : ℝ)).sub hY).log (by
    simp only [Pi.sub_apply]; linarith)
  have h0 := (hs.neg.mul hK).add hBlog
  have h1 := h0.add hClog
  have h2 := h1.add (((hb.add hc).const_mul 2).mul hL1)
  have h3 := h2.sub ((hb.const_mul 2).mul hLx)
  have h := h3.sub ((hc.const_mul 2).mul hLy)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with q
    simp only [chartHeight, chartOffDiagonalMass, xLogX, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, Function.comp_apply]
    ring_nf
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring_nf

/-- **The page's display (3.3), contracted against the path.**  The height's
derivative along a differentiable path in the chart is the gradient
`log K + log L` in each cell, paired with that cell's velocity.  The page
states (3.3) inside a lemma that also asserts smoothness in the cells; that
smoothness is not stated here. -/
theorem hasDerivAt_chartHeight (hX : HasDerivAt X dx t)
    (hY : HasDerivAt Y dy t)
    (hU : HasDerivAt (fun s => chartRoot (X s + Y s) (X s * Y s)) du t)
    (hx : 0 < X t) (hy : 0 < Y t) (hr : X t + Y t < 1) :
    HasDerivAt (fun q => chartHeight (X q) (Y q))
      ((Real.log (certDiagonal (chartDiagonalMass (X t + Y t) (X t * Y t))
            (chartRoot (X t + Y t) (X t * Y t)))
          + Real.log (certOffDiagonal (X t * chartRoot (X t + Y t) (X t * Y t))
              (Y t * chartRoot (X t + Y t) (X t * Y t))
              (chartRoot (X t + Y t) (X t * Y t))))
          * (dx * chartRoot (X t + Y t) (X t * Y t) + X t * du)
        + (Real.log (certDiagonal (chartDiagonalMass (X t + Y t) (X t * Y t))
              (chartRoot (X t + Y t) (X t * Y t)))
            + Real.log (certOffDiagonal
                (Y t * chartRoot (X t + Y t) (X t * Y t))
                (X t * chartRoot (X t + Y t) (X t * Y t))
                (chartRoot (X t + Y t) (X t * Y t))))
          * (dy * chartRoot (X t + Y t) (X t * Y t) + Y t * du)) t := by
  refine (hasDerivAt_chartHeight_raw hX hY hU hx hy hr).congr_deriv ?_
  obtain ⟨hKv, hLb, hLc⟩ := chart_certValues hx hy hr
  have hx1 : 0 < 1 - X t := by linarith
  have hy1 : 0 < 1 - Y t := by linarith
  have hr1 : 0 < 1 - (X t + Y t) := by linarith
  have hplt : X t * Y t < 1 := by
    have hxlt : X t < 1 := by linarith
    have hylt : Y t < 1 := by linarith
    nlinarith [mul_pos hx hx1, mul_pos hy hy1]
  have hu : 0 < chartRoot (X t + Y t) (X t * Y t) := by
    unfold chartRoot chartNorm
    exact div_pos (mul_pos hx hy) (mul_pos hr1 (sub_pos.mpr hplt))
  have hb : 0 < X t * chartRoot (X t + Y t) (X t * Y t) := mul_pos hx hu
  have hc : 0 < Y t * chartRoot (X t + Y t) (X t * Y t) := mul_pos hy hu
  have hLb_log : Real.log (certOffDiagonal
      (X t * chartRoot (X t + Y t) (X t * Y t))
      (Y t * chartRoot (X t + Y t) (X t * Y t))
      (chartRoot (X t + Y t) (X t * Y t)))
      = Real.log (X t * chartRoot (X t + Y t) (X t * Y t))
        + 2 * Real.log (1 - (X t + Y t)) - 2 * Real.log (1 - X t) := by
    rw [hLb, show 1 - X t - Y t = 1 - (X t + Y t) by ring,
      Real.log_div (mul_ne_zero hb.ne' (pow_ne_zero 2 hr1.ne'))
        (pow_ne_zero 2 hx1.ne'),
      Real.log_mul hb.ne' (pow_ne_zero 2 hr1.ne'), Real.log_pow, Real.log_pow]
    ring
  have hLc_log : Real.log (certOffDiagonal
      (Y t * chartRoot (X t + Y t) (X t * Y t))
      (X t * chartRoot (X t + Y t) (X t * Y t))
      (chartRoot (X t + Y t) (X t * Y t)))
      = Real.log (Y t * chartRoot (X t + Y t) (X t * Y t))
        + 2 * Real.log (1 - (X t + Y t)) - 2 * Real.log (1 - Y t) := by
    rw [hLc, show 1 - X t - Y t = 1 - (X t + Y t) by ring,
      Real.log_div (mul_ne_zero hc.ne' (pow_ne_zero 2 hr1.ne'))
        (pow_ne_zero 2 hy1.ne'),
      Real.log_mul hc.ne' (pow_ne_zero 2 hr1.ne'), Real.log_pow, Real.log_pow]
    ring
  rw [hLb_log, hLc_log]
  have hres := chartDeriv_residual (X t) (Y t) dx dy hx hy hr
  dsimp only at hres
  have hu_eq : chartRoot (X t + Y t) (X t * Y t)
      = X t * Y t / ((1 - (X t + Y t)) * (1 - X t * Y t)) := by
    unfold chartRoot chartNorm
    rfl
  have hdu : du
      = ((dx * Y t + X t * dy) * ((1 - (X t + Y t)) * (1 - X t * Y t))
        + X t * Y t * ((dx + dy) * (1 - X t * Y t)
          + (1 - (X t + Y t)) * (dx * Y t + X t * dy)))
        / ((1 - (X t + Y t)) * (1 - X t * Y t)) ^ 2 := by
    have hd := hU.unique (hasDerivAt_chartRoot hX hY hx hy hr)
    simpa only [chartNorm] using hd
  rw [← hu_eq, ← hdu] at hres
  rw [chartDiagonalMass_eq]
  exact chartHeightDeriv_collect (X t) (Y t)
    (chartRoot (X t + Y t) (X t * Y t)) du dx dy
    (Real.log (certDiagonal
      (1 - X t * chartRoot (X t + Y t) (X t * Y t)
        - Y t * chartRoot (X t + Y t) (X t * Y t))
      (chartRoot (X t + Y t) (X t * Y t))))
    (Real.log (X t * chartRoot (X t + Y t) (X t * Y t)))
    (Real.log (Y t * chartRoot (X t + Y t) (X t * Y t)))
    (Real.log (1 - (X t + Y t))) (Real.log (1 - X t)) (Real.log (1 - Y t)) hres
