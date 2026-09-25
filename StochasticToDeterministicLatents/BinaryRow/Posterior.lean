import StochasticToDeterministicLatents.BinaryRow.Presentation

/-!
# Row parameters, the row-one posterior, and the gap on `Bit × Y`

Facts about contacts and two-contact latents on `Bit × Y` that the presentation's consumers use:

* a table has at most one row cube parameter (`rowCubeParam_unique`), so tables with different
  parameters differ (`ne_of_rowCubeParam_ne`); this turns the order `s < t` of
  `rowTwoContact_presentation` into the distinctness that `rowTwoContact_det_pos`,
  `rowTwoContact_param_ineq` and `rowTwoContact_variance` assume;
* the row-one posterior of a contact at column `y` is `w(1,y) x² / (w(0,y) + w(1,y) x²)`
  (`rowContact_posterior`), and its mean under the contact's column law is the row-one mass
  (`rowContact_posterior_mean`);
* for `0 < s < t`, the gap `1 - s³/(1 + s³) - 1/(1 + t³)` is positive (`twoContact_gap_pos`);
* in a `Bit`-labelled latent with positive priors, each prior is below one
  (`bitLatent_prior_lt_one`).

These are identities and inequalities between probabilities; no information quantity appears.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose `Feasible`,
`IsContact` and `Latent` these statements use.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

variable {Y : Type} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
/-- The column coefficients are positive for a feasible kernel and a positive parameter. -/
private theorem colCoeff_pos_aux {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    {x : ℝ} (hx : 0 < x) (y : Y) : 0 < colCoeff w x y := by
  have h0 := hw.1 (0, y) (mem_univ _)
  have h1 := hw.1 (1, y) (mem_univ _)
  unfold colCoeff
  positivity

omit [DecidableEq Y] in
/-- If `x` and `y` are both row cube parameters of the same table `q` (each positive, with
`rowMass q 0 = 1/(1 + ·³)`), then `x = y`. -/
theorem rowCubeParam_unique {q : Bit × Y → ℝ} {x y : ℝ} (hx : RowCubeParam q x)
    (hy : RowCubeParam q y) : x = y := by
  obtain ⟨hx0, hx1, -⟩ := hx
  obtain ⟨hy0, hy1, -⟩ := hy
  have h : 1 / (1 + x ^ 3) = 1 / (1 + y ^ 3) := hx1.symm.trans hy1
  have hx3 : 0 < 1 + x ^ 3 := by positivity
  have hy3 : 0 < 1 + y ^ 3 := by positivity
  have h3 : x ^ 3 = y ^ 3 := by
    rw [div_eq_div_iff hx3.ne' hy3.ne'] at h
    linarith
  exact (pow_left_inj₀ hx0.le hy0.le (by norm_num)).mp h3

omit [DecidableEq Y] in
/-- Tables `q` and `r` with row cube parameters `s` and `t` are different whenever `s ≠ t`. -/
theorem ne_of_rowCubeParam_ne {q r : Bit × Y → ℝ} {s t : ℝ} (hs : RowCubeParam q s)
    (ht : RowCubeParam r t) (hst : s ≠ t) : q ≠ r := by
  rintro rfl
  exact hst (rowCubeParam_unique hs ht)

/-- For a contact `q` of a feasible kernel `w` on `Bit × Y` with row cube parameter `x`, the
posterior probability of row one given column `y`, `q(1,y) / colMass q y`, equals
`w(1,y) x² / (w(0,y) + w(1,y) x²)`. -/
theorem rowContact_posterior {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {x : ℝ} (hx : RowCubeParam q x) (y : Y) :
    q (1, y) / colMass q y = w (1, y) * x ^ 2 / colCoeff w x y := by
  have hxp : 0 < x := hx.1
  have hc : colCoeff w x y ≠ 0 := (colCoeff_pos_aux hw hxp y).ne'
  have hU : 1 + x ^ 3 ≠ 0 := by positivity
  rw [(rowContact_entry hw hq hx y).2, rowContact_colMass hw hq hx y]
  field_simp

/-- For a contact `q` of a feasible kernel on `Bit × Y`, the row-one posterior
`q(1,y) / colMass q y` averaged under the contact's column law `colMass q` is the row-one mass
`rowMass q 1`. -/
theorem rowContact_posterior_mean {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q) :
    ∑ y, colMass q y * (q (1, y) / colMass q y) = rowMass q 1 := by
  show _ = ∑ y, q (1, y)
  refine Finset.sum_congr rfl fun y _ => ?_
  have h := (rowContact_colMass_pos hw hq y).ne'
  field_simp

/-- For row parameters `0 < s < t`, with `a = s³/(1 + s³)` and `b = 1/(1 + t³)`, the gap
`1 - a - b` is strictly positive. -/
theorem twoContact_gap_pos {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    0 < 1 - s ^ 3 / (1 + s ^ 3) - 1 / (1 + t ^ 3) := by
  have ht : 0 < t := hs.trans hst
  have h3 : s ^ 3 < t ^ 3 := pow_lt_pow_left₀ hst hs.le (by norm_num)
  have hU : 0 < 1 + s ^ 3 := by positivity
  have hV : 0 < 1 + t ^ 3 := by positivity
  have he : 1 - s ^ 3 / (1 + s ^ 3) - 1 / (1 + t ^ 3) =
      (t ^ 3 - s ^ 3) / ((1 + s ^ 3) * (1 + t ^ 3)) := by
    field_simp
    ring
  rw [he]
  exact div_pos (by linarith) (mul_pos hU hV)

omit [DecidableEq Y] in
/-- In a latent whose labels are identified with `Bit` by `e` and whose priors are all positive,
the prior of each label `e.symm i` is strictly less than one. -/
theorem bitLatent_prior_lt_one {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    (hpos : ∀ v, 0 < V.prior v) (i : Bit) : V.prior (e.symm i) < 1 := by
  have hsum := bitLatent_prior_sum V e
  have h0 := hpos (e.symm 0)
  have h1 := hpos (e.symm 1)
  fin_cases i
  · show V.prior (e.symm 0) < 1
    linarith
  · show V.prior (e.symm 1) < 1
    linarith

end

end BinaryRow

end StochasticToDeterministicLatents
