/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  One theorem of the private
working material is dropped as dead, and one numeric positivity lemma is taken
from a second private module, which this completes.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterSeamPositivity

/-!
# The seam's derivative

The isolating code's margin at the chord's midpoint is a function of the
radius alone, `seamSingletonScalar`.  This module differentiates it.

Two things are needed and both are here.  The squared imbalance is
differentiable in the radius, with derivative `seamImbalanceSqDeriv`, and is
strictly increasing across the seam's interval.  And the height at the seam's
two cells, which is where every logarithm in the margin lives, is
differentiable, by way of a closed form for it that names the certificate value
at the seam's root.

The margin's derivative is then the imbalance's derivative times the logarithm
whose positivity `seam_logRatio_pos` supplies, so **the margin increases with
the radius**, though no declaration here says so: this module supplies the
derivative and `CenterSeamMargin` draws the conclusion.

**The route is not the page's.**  Proposition 4.6 differentiates in the
difference of the two off-diagonal cells; this differentiates in the radius.
-/

namespace StochasticToDeterministicLatents.Binary

variable {r : ℝ}

/-! ## The squared imbalance -/

/-- The derivative of `seamImbalanceSq`. -/
noncomputable def seamImbalanceSqDeriv (r : ℝ) : ℝ :=
  8 * (1 + 10 * r - 7 * r ^ 2) / (r ^ 3 * (1 + 7 * r) ^ 2)

private theorem seamImbalanceSqDeriv_num_pos (r : ℝ) (h0 : 1 / 2 < r)
    (h1 : r < 1) : 0 < 1 + 10 * r - 7 * r ^ 2 := by
  have hr : 0 < r := by linarith
  nlinarith [mul_pos hr (sub_pos.mpr h1)]

theorem hasDerivAt_seamImbalanceSq (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    HasDerivAt seamImbalanceSq (seamImbalanceSqDeriv r) r := by
  have hr0 : r ≠ 0 := by linarith [hr.1]
  have hd : 1 + 7 * r ≠ 0 := by linarith [hr.1]
  have hpi : HasDerivAt seamProduct (-8 / (1 + 7 * r) ^ 2) r := by
    unfold seamProduct
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun x : ℝ => 1 + 7 * x) 7 r := by
      simpa using ((hasDerivAt_id r).const_mul 7).const_add (1 : ℝ)
    exact (h1.div h2 hd).congr_deriv (by field_simp [hd]; ring)
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  unfold seamImbalanceSq
  have hraw := ((hpi.const_mul 4).div hsq (pow_ne_zero 2 hr0)).const_sub (1 : ℝ)
  exact hraw.congr_deriv
    (by unfold seamImbalanceSqDeriv seamProduct; field_simp [hr0, hd]; ring)

/-- **The squared imbalance increases with the radius.** -/
theorem seamImbalanceSq_strictMonoOn :
    StrictMonoOn seamImbalanceSq (Set.Ioo ((1 : ℝ) / 2) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo ((1 : ℝ) / 2) 1)
  · intro x hx
    exact (hasDerivAt_seamImbalanceSq hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_seamImbalanceSq hx).deriv]
    unfold seamImbalanceSqDeriv
    have hn := seamImbalanceSqDeriv_num_pos x hx.1 hx.2
    have hx0 : 0 < x := by linarith [hx.1]
    apply div_pos
    · exact mul_pos (by norm_num) hn
    · positivity

/-! ## The height at the seam's two cells -/

/-- **The height at the seam's two cells, with the root evaluated.**  Every
logarithm the margin carries is on the right, and the radius appears only
through the squared imbalance and the two cells.  The hypothesis is that the
squared imbalance is nonnegative, so this holds at the balanced radius as
well, where the margin's derivative does not exist. -/
theorem seamHeight_eq (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 ≤ seamImbalanceSq r) :
    chartHeight (seamCellB r) (seamCellC r)
      = -(7 / 8) * Real.log (certDiagonal (7 / 8) (1 / (8 * r)))
        + xLogX ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
        + xLogX ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
        + (1 / 4) * Real.log (1 - r)
        - 2 * ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
            * Real.log (1 - seamCellB r)
        - 2 * ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
            * Real.log (1 - seamCellC r) := by
  obtain ⟨_, _, _, hU, _, _⟩ := rayValues_of_seamRadius hr hh
  have hr0 : r ≠ 0 := by linarith [hr.1]
  have hxy : seamCellB r + seamCellC r = r := by
    unfold seamCellB seamCellC; ring
  have hprod : seamCellB r * seamCellC r
      = rayProductCoeff (Real.sqrt (seamImbalanceSq r)) * r ^ 2 := by
    unfold seamCellB seamCellC rayProductCoeff
    ring
  unfold chartHeight
  rw [hxy, hprod]
  unfold chartDiagonalMass chartOffDiagonalMass
  rw [show chartRoot r (rayProductCoeff (Real.sqrt (seamImbalanceSq r)) * r ^ 2)
      = rayRoot (Real.sqrt (seamImbalanceSq r)) r from rfl]
  rw [hU, show r * (1 / (8 * r)) = 1 / 8 from by field_simp,
    show (1 : ℝ) - 1 / 8 = 7 / 8 from by norm_num]
  have hx : seamCellB r * (1 / (8 * r))
      = (1 + Real.sqrt (seamImbalanceSq r)) / 16 := by
    unfold seamCellB
    field_simp [hr0]
    ring
  have hy : seamCellC r * (1 / (8 * r))
      = (1 - Real.sqrt (seamImbalanceSq r)) / 16 := by
    unfold seamCellC
    field_simp [hr0]
    ring
  rw [hx, hy]
  ring

/-! ## Two identities the collapse needs -/

private theorem seam_log_bridge (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    (8 + Real.sqrt (seamImbalanceSq r)) * (1 - seamCellC r)
        * (1 - seamCellB r - 2 * seamProduct r)
      = (8 - Real.sqrt (seamImbalanceSq r)) * (1 - seamCellB r)
        * (1 - seamCellC r - 2 * seamProduct r) := by
  set Z := Real.sqrt (seamImbalanceSq r) with hZdef
  have hr0 : r ≠ 0 := by linarith [hr.1]
  have h7 : 1 + 7 * r ≠ 0 := by linarith [hr.1]
  have h7' : 1 + r * 7 ≠ 0 := by linarith [hr.1]
  have hZ2 : Z ^ 2 = seamImbalanceSq r := Real.sq_sqrt hh.le
  have hrel : Z ^ 2 * r ^ 2 * (1 + 7 * r)
      - (r ^ 2 * (1 + 7 * r) - 4 * (1 - r)) = 0 := by
    rw [hZ2]
    unfold seamImbalanceSq seamProduct
    field_simp [hr0, h7, h7']
    ring
  have hA : (1 + 7 * r) * (1 - seamCellB r - 2 * seamProduct r)
      = (1 + 7 * r) * (1 - seamCellB r) - 2 * (1 - r) := by
    unfold seamProduct
    field_simp [h7]
  have hB : (1 + 7 * r) * (1 - seamCellC r - 2 * seamProduct r)
      = (1 + 7 * r) * (1 - seamCellC r) - 2 * (1 - r) := by
    unfold seamProduct
    field_simp [h7]
  apply mul_left_cancel₀ h7
  rw [show (1 + 7 * r) * ((8 + Z) * (1 - seamCellC r)
        * (1 - seamCellB r - 2 * seamProduct r))
      = (8 + Z) * (1 - seamCellC r)
        * ((1 + 7 * r) * (1 - seamCellB r - 2 * seamProduct r)) by ring, hA]
  rw [show (1 + 7 * r) * ((8 - Z) * (1 - seamCellB r)
        * (1 - seamCellC r - 2 * seamProduct r))
      = (8 - Z) * (1 - seamCellB r)
        * ((1 + 7 * r) * (1 - seamCellC r - 2 * seamProduct r)) by ring, hB]
  unfold seamCellB seamCellC
  rw [← hZdef]
  linear_combination (-(Z / 2)) * hrel

private theorem seam_rational_vanish (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    -(7 / 8) * (1 / r + 7 / (7 * r + 2) - 14 / (7 * r + 1)) - 1 / (4 * (1 - r))
      + 2 * ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
          * ((1 + Real.sqrt (seamImbalanceSq r)) / 2
            + r * (seamImbalanceSqDeriv r
              / (2 * Real.sqrt (seamImbalanceSq r))) / 2) / (1 - seamCellB r)
      + 2 * ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
          * ((1 - Real.sqrt (seamImbalanceSq r)) / 2
            - r * (seamImbalanceSqDeriv r
              / (2 * Real.sqrt (seamImbalanceSq r))) / 2) / (1 - seamCellC r)
      = 0 := by
  set Z := Real.sqrt (seamImbalanceSq r) with hZdef
  have hr0 : r ≠ 0 := by linarith [hr.1]
  have hr1 : 1 - r ≠ 0 := by linarith [hr.2]
  have h7 : 7 * r + 1 ≠ 0 := by linarith [hr.1]
  have h72 : 7 * r + 2 ≠ 0 := by linarith [hr.1]
  have h72' : 2 + r * 7 ≠ 0 := by linarith [hr.1]
  have h17 : 1 + 7 * r ≠ 0 := by linarith [hr.1]
  have hdenP : 1 + 7 * r + 1 ≠ 0 := by linarith [hr.1]
  have hZ2 : Z ^ 2 = seamImbalanceSq r := Real.sq_sqrt hh.le
  have hZ0 : Z ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  obtain ⟨hy, hyx, hx1, hApos, hBpos⟩ := seamCells_pos hr hh
  have hnx : 1 - seamCellB r ≠ 0 := by linarith
  have hny : 1 - seamCellC r ≠ 0 := by linarith
  have hpipos : 0 < seamProduct r := by
    unfold seamProduct
    exact div_pos (by linarith [hr.2]) (by linarith [hr.1])
  have hP : 1 - r + seamProduct r ≠ 0 :=
    (add_pos (sub_pos.mpr hr.2) hpipos).ne'
  have hPu : (1 - r) * (1 + 7 * r) + (1 - r) ≠ 0 := by
    have h17pos : 0 < 1 + 7 * r := by linarith [hr.1]
    have hmul : 0 < (1 - r) * (1 + 7 * r) := mul_pos (sub_pos.mpr hr.2) h17pos
    have : 0 < (1 - r) * (1 + 7 * r) + (1 - r) := by linarith [hr.2]
    exact this.ne'
  have hZ2r : r ^ 2 * Z ^ 2 = r ^ 2 - 4 * seamProduct r := by
    rw [hZ2]
    unfold seamImbalanceSq
    field_simp [hr0]
  have hprod : (1 - seamCellB r) * (1 - seamCellC r) = 1 - r + seamProduct r := by
    unfold seamCellB seamCellC
    rw [← hZdef]
    linear_combination (-(1 : ℝ) / 4) * hZ2r
  have hnum : (1 + Z) ^ 2 * (1 - seamCellC r) + (1 - Z) ^ 2 * (1 - seamCellB r)
      = 2 - r + (2 + r) * Z ^ 2 := by
    unfold seamCellB seamCellC
    rw [← hZdef]
    ring
  have hdZ :
      (1 + Z) * r * (seamImbalanceSqDeriv r / (2 * Z)) / (16 * (1 - seamCellB r))
        - (1 - Z) * r * (seamImbalanceSqDeriv r / (2 * Z))
          / (16 * (1 - seamCellC r))
      = r * seamImbalanceSqDeriv r
          / (16 * ((1 - seamCellB r) * (1 - seamCellC r))) := by
    field_simp [hZ0, hnx, hny]
    unfold seamCellB seamCellC
    rw [← hZdef]
    ring
  have key :
      -(7 / 8) * (1 / r + 7 / (7 * r + 2) - 14 / (7 * r + 1)) - 1 / (4 * (1 - r))
        + (2 - r + (2 + r) * seamImbalanceSq r) / (16 * (1 - r + seamProduct r))
        + r * seamImbalanceSqDeriv r / (16 * (1 - r + seamProduct r)) = 0 := by
    unfold seamImbalanceSq seamImbalanceSqDeriv seamProduct
    field_simp [hr0, hr1, h7, h72, h72', h17, hdenP, hP, hPu]
    ring
  have split :
      -(7 / 8) * (1 / r + 7 / (7 * r + 2) - 14 / (7 * r + 1)) - 1 / (4 * (1 - r))
        + 2 * ((1 + Z) / 16) * ((1 + Z) / 2
            + r * (seamImbalanceSqDeriv r / (2 * Z)) / 2) / (1 - seamCellB r)
        + 2 * ((1 - Z) / 16) * ((1 - Z) / 2
            - r * (seamImbalanceSqDeriv r / (2 * Z)) / 2) / (1 - seamCellC r)
      = (-(7 / 8) * (1 / r + 7 / (7 * r + 2) - 14 / (7 * r + 1))
            - 1 / (4 * (1 - r)))
        + ((1 + Z) ^ 2 / (16 * (1 - seamCellB r))
            + (1 - Z) ^ 2 / (16 * (1 - seamCellC r)))
        + ((1 + Z) * r * (seamImbalanceSqDeriv r / (2 * Z))
              / (16 * (1 - seamCellB r))
            - (1 - Z) * r * (seamImbalanceSqDeriv r / (2 * Z))
              / (16 * (1 - seamCellC r))) := by
    field_simp [hZ0, hnx, hny]
    ring
  have two : (1 + Z) ^ 2 / (16 * (1 - seamCellB r))
      + (1 - Z) ^ 2 / (16 * (1 - seamCellC r))
      = (2 - r + (2 + r) * seamImbalanceSq r)
        / (16 * (1 - r + seamProduct r)) := by
    rw [← hZ2, ← hprod]
    field_simp [hnx, hny]
    linear_combination hnum
  rw [split, two, hdZ, hprod]
  exact key

private theorem seam_log_collapse (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    3 * Real.log ((1 - Real.sqrt (seamImbalanceSq r))
        / (1 + Real.sqrt (seamImbalanceSq r)))
      - 4 * Real.log ((8 - Real.sqrt (seamImbalanceSq r))
        / (8 + Real.sqrt (seamImbalanceSq r)))
      + 2 * (Real.log ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
        - Real.log ((1 - Real.sqrt (seamImbalanceSq r)) / 16))
      - 4 * (Real.log (1 - seamCellB r) - Real.log (1 - seamCellC r))
      = Real.log ((seamCellC r * (1 - seamCellC r - 2 * seamProduct r) ^ 4)
        / (seamCellB r * (1 - seamCellB r - 2 * seamProduct r) ^ 4)) := by
  set Z := Real.sqrt (seamImbalanceSq r) with hZdef
  have hrpos : 0 < r := by linarith [hr.1]
  have hZ2 : Z ^ 2 = seamImbalanceSq r := Real.sq_sqrt hh.le
  have hZ2r : r ^ 2 * Z ^ 2 = r ^ 2 - 4 * seamProduct r := by
    rw [hZ2]
    unfold seamImbalanceSq
    field_simp [hrpos.ne']
  have hZrange := (rayValues_of_seamRadius hr hh.le).1
  have hp1 : 0 < 1 + Z := by linarith [hZrange.1]
  have hm1 : 0 < 1 - Z := by linarith [hZrange.2]
  have hp8 : 0 < 8 + Z := by linarith
  have hm8 : 0 < 8 - Z := by linarith
  obtain ⟨hy, hyx, hxlt, hA, hB⟩ := seamCells_pos hr hh
  have hx : 0 < seamCellB r := lt_trans hy hyx
  have hx1 : 0 < 1 - seamCellB r := sub_pos.mpr hxlt
  have hy1 : 0 < 1 - seamCellC r := by linarith
  have hxy1 : seamCellB r + seamCellC r < 1 := by
    have : seamCellB r + seamCellC r = r := by unfold seamCellB seamCellC; ring
    linarith [hr.2]
  have h2xy : 2 * seamCellB r * seamCellC r = 2 * seamProduct r := by
    unfold seamCellB seamCellC
    rw [← hZdef]
    linear_combination (-(1 : ℝ) / 2) * hZ2r
  have hid := seam_log_identity (seamCellB r) (seamCellC r) hx hy hxy1
      (by rw [h2xy]; exact hA) (by rw [h2xy]; exact hB)
  simp only [] at hid
  rw [h2xy] at hid
  have hxylog : Real.log (seamCellB r) - Real.log (seamCellC r)
      = Real.log (1 + Z) - Real.log (1 - Z) := by
    unfold seamCellB seamCellC
    rw [← hZdef]
    rw [Real.log_div (mul_ne_zero hrpos.ne' hp1.ne') (by norm_num),
      Real.log_div (mul_ne_zero hrpos.ne' hm1.ne') (by norm_num),
      Real.log_mul hrpos.ne' hp1.ne', Real.log_mul hrpos.ne' hm1.ne']
    ring
  have hb := congrArg Real.log (seam_log_bridge hr hh)
  rw [← hZdef] at hb
  rw [Real.log_mul (mul_ne_zero hp8.ne' hy1.ne') hA.ne',
    Real.log_mul hp8.ne' hy1.ne',
    Real.log_mul (mul_ne_zero hm8.ne' hx1.ne') hB.ne',
    Real.log_mul hm8.ne' hx1.ne'] at hb
  rw [← hid]
  rw [Real.log_div hm1.ne' hp1.ne', Real.log_div hm8.ne' hp8.ne',
    Real.log_div hp1.ne' (by norm_num : (16 : ℝ) ≠ 0),
    Real.log_div hm1.ne' (by norm_num : (16 : ℝ) ≠ 0),
    Real.log_div hx.ne' hy.ne',
    Real.log_div (mul_ne_zero hx1.ne' hB.ne') (mul_ne_zero hy1.ne' hA.ne'),
    Real.log_mul hx1.ne' hB.ne', Real.log_mul hy1.ne' hA.ne',
    Real.log_div (mul_ne_zero hx.ne' hx1.ne') (mul_ne_zero hy.ne' hy1.ne'),
    Real.log_mul hx.ne' hx1.ne', Real.log_mul hy.ne' hy1.ne']
  linear_combination 4 * hb + hxylog

/-! ## The pieces, differentiated -/

private theorem hasDerivAt_seamCellB (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt seamCellB
      ((1 + Real.sqrt (seamImbalanceSq r)) / 2
        + r * (seamImbalanceSqDeriv r
          / (2 * Real.sqrt (seamImbalanceSq r))) / 2) r := by
  have hZ := (hasDerivAt_seamImbalanceSq hr).sqrt hh.ne'
  unfold seamCellB
  apply (((hasDerivAt_id r).mul
    ((hasDerivAt_const r 1).add hZ)).div_const 2).congr_deriv
  dsimp
  ring

private theorem hasDerivAt_seamCellC (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt seamCellC
      ((1 - Real.sqrt (seamImbalanceSq r)) / 2
        - r * (seamImbalanceSqDeriv r
          / (2 * Real.sqrt (seamImbalanceSq r))) / 2) r := by
  have hZ := (hasDerivAt_seamImbalanceSq hr).sqrt hh.ne'
  unfold seamCellC
  apply (((hasDerivAt_id r).mul
    ((hasDerivAt_const r 1).sub hZ)).div_const 2).congr_deriv
  dsimp
  ring

private theorem hasDerivAt_xLogX_comp {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun t => xLogX (f t)) (f' * (Real.log (f x) + 1)) x := by
  unfold xLogX
  exact ((Real.hasDerivAt_mul_log hne).comp x hf).congr_deriv (by ring)

private theorem hasDerivAt_seamLogEntropy {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasDerivAt (fun z => centerLogEntropy (1 / 8) z)
      ((1 / 16) * Real.log ((1 - z) / (1 + z))) z := by
  have hp : HasDerivAt (fun t : ℝ => (1 / 8) * (1 + t) / 2) (1 / 16) z :=
    ((((hasDerivAt_const z 1).add (hasDerivAt_id z)).const_mul
      (1 / 8)).div_const 2).congr_deriv (by ring)
  have hm : HasDerivAt (fun t : ℝ => (1 / 8) * (1 - t) / 2) (-1 / 16) z :=
    ((((hasDerivAt_const z 1).sub (hasDerivAt_id z)).const_mul
      (1 / 8)).div_const 2).congr_deriv (by ring)
  have hp0 : (1 / 8 : ℝ) * (1 + z) / 2 ≠ 0 := by positivity
  have hm0 : (1 / 8 : ℝ) * (1 - z) / 2 ≠ 0 := by positivity
  have h := (((hasDerivAt_const z (2 * xLogX ((1 - (1 / 8 : ℝ)) / 2))).add
    (hasDerivAt_xLogX_comp hp hp0)).add (hasDerivAt_xLogX_comp hm hm0)).neg
  unfold centerLogEntropy
  refine h.congr_deriv ?_
  rw [show (1 / 8 : ℝ) * (1 + z) / 2 = (1 + z) / 16 by ring,
    show (1 / 8 : ℝ) * (1 - z) / 2 = (1 - z) / 16 by ring,
    Real.log_div (by linarith) (by norm_num : (16 : ℝ) ≠ 0),
    Real.log_div (by linarith) (by norm_num : (16 : ℝ) ≠ 0),
    Real.log_div (by linarith) (by linarith)]
  ring

private theorem hasDerivAt_seamMarginalEntropy {z : ℝ} (hz : |z| < 8) :
    HasDerivAt (fun z => centerMarginalEntropy (1 / 8) z)
      ((1 / 16) * Real.log ((8 - z) / (8 + z))) z := by
  have hp : HasDerivAt (fun t : ℝ => (1 + (1 / 8) * t) / 2) (1 / 16) z :=
    (((hasDerivAt_const z 1).add
      ((hasDerivAt_id z).const_mul (1 / 8))).div_const 2).congr_deriv (by ring)
  have hm : HasDerivAt (fun t : ℝ => (1 - (1 / 8) * t) / 2) (-1 / 16) z :=
    (((hasDerivAt_const z 1).sub
      ((hasDerivAt_id z).const_mul (1 / 8))).div_const 2).congr_deriv (by ring)
  have hp0 : (1 + (1 / 8 : ℝ) * z) / 2 ≠ 0 := by rw [abs_lt] at hz; linarith
  have hm0 : (1 - (1 / 8 : ℝ) * z) / 2 ≠ 0 := by rw [abs_lt] at hz; linarith
  have h := ((hasDerivAt_xLogX_comp hp hp0).add
    (hasDerivAt_xLogX_comp hm hm0)).neg
  unfold centerMarginalEntropy
  refine h.congr_deriv ?_
  rw [show (1 + (1 / 8 : ℝ) * z) / 2 = (8 + z) / 16 by ring,
    show (1 - (1 / 8 : ℝ) * z) / 2 = (8 - z) / 16 by ring]
  rw [abs_lt] at hz
  rw [Real.log_div (by linarith) (by norm_num : (16 : ℝ) ≠ 0),
    Real.log_div (by linarith) (by norm_num : (16 : ℝ) ≠ 0),
    Real.log_div (by linarith) (by linarith)]
  ring

private theorem hasDerivAt_seam_logCertDiagonal
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    HasDerivAt (fun t => Real.log (certDiagonal (7 / 8) (1 / (8 * t))))
      (1 / r + 7 / (7 * r + 2) - 14 / (7 * r + 1)) r := by
  have hKeq : ∀ t : ℝ, t ≠ 0 → 7 * t + 1 ≠ 0 →
      certDiagonal (7 / 8) (1 / (8 * t)) = 8 * t * (7 * t + 2) / (7 * t + 1) ^ 2 := by
    intro t ht ht7
    unfold certDiagonal
    field_simp [ht, ht7]
    try ring
  have hev : (fun t => Real.log (certDiagonal (7 / 8) (1 / (8 * t)))) =ᶠ[nhds r]
      (fun t => Real.log (8 * t * (7 * t + 2) / (7 * t + 1) ^ 2)) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    rw [hKeq t (by linarith [ht.1]) (by linarith [ht.1])]
  have h1 : HasDerivAt (fun t : ℝ => 8 * t * (7 * t + 2))
      (8 * (7 * r + 2) + 8 * r * 7) r := by
    have h := ((hasDerivAt_id r).const_mul 8).mul
      (((hasDerivAt_id r).const_mul 7).add_const 2)
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall
        (fun t => by simp only [Pi.mul_apply, id_eq]; try ring)
    · simp only [id_eq]
      ring
  have h2 : HasDerivAt (fun t : ℝ => (7 * t + 1) ^ 2)
      (2 * (7 * r + 1) * 7) r := by
    have h := (((hasDerivAt_id r).const_mul 7).add_const 1).pow 2
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall
        (fun t => by simp only [Pi.pow_apply, id_eq])
    · simp only [id_eq]
      ring
  have hq := h1.div h2 (pow_ne_zero 2 (by linarith [hr.1]))
  have hnum : 8 * r * (7 * r + 2) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by linarith [hr.1])
    · linarith [hr.1]
  have hden : (7 * r + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [hr.1])
  have hl := hq.log (div_ne_zero hnum hden)
  have hr0 : r ≠ 0 := by linarith [hr.1]
  have h71 : 7 * r + 1 ≠ 0 := by linarith [hr.1]
  have h72 : 7 * r + 2 ≠ 0 := by linarith [hr.1]
  refine (hl.congr_of_eventuallyEq hev).congr_deriv ?_
  try simp only [Pi.div_apply]
  field_simp [hnum, hden, hr0, h71, h72]
  try ring

private theorem hasDerivAt_seam_xLogX_plus (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt (fun t => xLogX ((1 + Real.sqrt (seamImbalanceSq t)) / 16))
      ((Real.log ((1 + Real.sqrt (seamImbalanceSq r)) / 16) + 1) *
        (seamImbalanceSqDeriv r
          / (2 * Real.sqrt (seamImbalanceSq r)) / 16)) r := by
  have hZ := (hasDerivAt_seamImbalanceSq hr).sqrt hh.ne'
  have hne : (1 + Real.sqrt (seamImbalanceSq r)) / 16 ≠ 0 := by positivity
  unfold xLogX
  have h := (Real.hasDerivAt_mul_log hne).comp r
    (((hasDerivAt_const r 1).add hZ).div_const 16)
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_seam_xLogX_minus (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt (fun t => xLogX ((1 - Real.sqrt (seamImbalanceSq t)) / 16))
      ((Real.log ((1 - Real.sqrt (seamImbalanceSq r)) / 16) + 1) *
        (-seamImbalanceSqDeriv r
          / (2 * Real.sqrt (seamImbalanceSq r)) / 16)) r := by
  have hZ := (hasDerivAt_seamImbalanceSq hr).sqrt hh.ne'
  have hZrange := (rayValues_of_seamRadius hr hh.le).1
  have hne : (1 - Real.sqrt (seamImbalanceSq r)) / 16 ≠ 0 := by
    have : Real.sqrt (seamImbalanceSq r) < 1 := hZrange.2
    positivity
  unfold xLogX
  have h := (Real.hasDerivAt_mul_log hne).comp r
    (((hasDerivAt_const r 1).sub hZ).div_const 16)
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_seam_log1B (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt (fun t => Real.log (1 - seamCellB t))
      (-((1 + Real.sqrt (seamImbalanceSq r)) / 2
        + r * (seamImbalanceSqDeriv r
          / (2 * Real.sqrt (seamImbalanceSq r))) / 2)
        / (1 - seamCellB r)) r := by
  have hx := (seamCells_pos hr hh).2.2.1
  have h := ((hasDerivAt_const r 1).sub (hasDerivAt_seamCellB hr hh)).log
    (by linarith : 1 - seamCellB r ≠ 0)
  exact h.congr_deriv (by simp only [Pi.sub_apply]; ring)

private theorem hasDerivAt_seam_log1C (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt (fun t => Real.log (1 - seamCellC t))
      (-((1 - Real.sqrt (seamImbalanceSq r)) / 2
        - r * (seamImbalanceSqDeriv r
          / (2 * Real.sqrt (seamImbalanceSq r))) / 2)
        / (1 - seamCellC r)) r := by
  obtain ⟨hc, hcb, hx, -, -⟩ := seamCells_pos hr hh
  have hy : seamCellC r < 1 := lt_trans hcb hx
  have h := ((hasDerivAt_const r 1).sub (hasDerivAt_seamCellC hr hh)).log
    (by linarith : 1 - seamCellC r ≠ 0)
  exact h.congr_deriv (by simp only [Pi.sub_apply]; ring)

private theorem hasDerivAt_seamHeight (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt (fun t => chartHeight (seamCellB t) (seamCellC t))
      (-(7 / 8) * (1 / r + 7 / (7 * r + 2) - 14 / (7 * r + 1))
        + (Real.log ((1 + Real.sqrt (seamImbalanceSq r)) / 16) + 1)
          * (seamImbalanceSqDeriv r / (2 * Real.sqrt (seamImbalanceSq r)) / 16)
        - (Real.log ((1 - Real.sqrt (seamImbalanceSq r)) / 16) + 1)
          * (seamImbalanceSqDeriv r / (2 * Real.sqrt (seamImbalanceSq r)) / 16)
        - 1 / (4 * (1 - r))
        - 2 * ((seamImbalanceSqDeriv r
              / (2 * Real.sqrt (seamImbalanceSq r)) / 16)
            * Real.log (1 - seamCellB r)
          + ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
            * (-((1 + Real.sqrt (seamImbalanceSq r)) / 2
              + r * (seamImbalanceSqDeriv r
                / (2 * Real.sqrt (seamImbalanceSq r))) / 2)
              / (1 - seamCellB r)))
        - 2 * ((-(seamImbalanceSqDeriv r
              / (2 * Real.sqrt (seamImbalanceSq r)) / 16))
            * Real.log (1 - seamCellC r)
          + ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
            * (-((1 - Real.sqrt (seamImbalanceSq r)) / 2
              - r * (seamImbalanceSqDeriv r
                / (2 * Real.sqrt (seamImbalanceSq r))) / 2)
              / (1 - seamCellC r)))) r := by
  have hZ := (hasDerivAt_seamImbalanceSq hr).sqrt hh.ne'
  have hbplus : HasDerivAt (fun t => (1 + Real.sqrt (seamImbalanceSq t)) / 16)
      (seamImbalanceSqDeriv r / (2 * Real.sqrt (seamImbalanceSq r)) / 16) r :=
    (((hasDerivAt_const r 1).add hZ).div_const 16).congr_deriv (by ring)
  have hbminus : HasDerivAt (fun t => (1 - Real.sqrt (seamImbalanceSq t)) / 16)
      (-seamImbalanceSqDeriv r / (2 * Real.sqrt (seamImbalanceSq r)) / 16) r :=
    (((hasDerivAt_const r 1).sub hZ).div_const 16).congr_deriv (by ring)
  have hlogr : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - r)) r := by
    have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) r :=
      ((hasDerivAt_const r 1).sub (hasDerivAt_id r)).congr_deriv (by ring)
    exact hsub.log (by linarith [hr.2])
  have hexp : HasDerivAt
      (fun t => -(7 / 8) * Real.log (certDiagonal (7 / 8) (1 / (8 * t)))
        + xLogX ((1 + Real.sqrt (seamImbalanceSq t)) / 16)
        + xLogX ((1 - Real.sqrt (seamImbalanceSq t)) / 16)
        + (1 / 4) * Real.log (1 - t)
        - 2 * ((1 + Real.sqrt (seamImbalanceSq t)) / 16)
            * Real.log (1 - seamCellB t)
        - 2 * ((1 - Real.sqrt (seamImbalanceSq t)) / 16)
            * Real.log (1 - seamCellC t))
      (-(7 / 8) * (1 / r + 7 / (7 * r + 2) - 14 / (7 * r + 1))
        + (Real.log ((1 + Real.sqrt (seamImbalanceSq r)) / 16) + 1)
          * (seamImbalanceSqDeriv r / (2 * Real.sqrt (seamImbalanceSq r)) / 16)
        - (Real.log ((1 - Real.sqrt (seamImbalanceSq r)) / 16) + 1)
          * (seamImbalanceSqDeriv r / (2 * Real.sqrt (seamImbalanceSq r)) / 16)
        - 1 / (4 * (1 - r))
        - 2 * ((seamImbalanceSqDeriv r
              / (2 * Real.sqrt (seamImbalanceSq r)) / 16)
            * Real.log (1 - seamCellB r)
          + ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
            * (-((1 + Real.sqrt (seamImbalanceSq r)) / 2
              + r * (seamImbalanceSqDeriv r
                / (2 * Real.sqrt (seamImbalanceSq r))) / 2)
              / (1 - seamCellB r)))
        - 2 * ((-(seamImbalanceSqDeriv r
              / (2 * Real.sqrt (seamImbalanceSq r)) / 16))
            * Real.log (1 - seamCellC r)
          + ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
            * (-((1 - Real.sqrt (seamImbalanceSq r)) / 2
              - r * (seamImbalanceSqDeriv r
                / (2 * Real.sqrt (seamImbalanceSq r))) / 2)
              / (1 - seamCellC r)))) r := by
    have h := (((((hasDerivAt_seam_logCertDiagonal hr).const_mul (-(7 / 8))).add
      (hasDerivAt_seam_xLogX_plus hr hh)).add
      (hasDerivAt_seam_xLogX_minus hr hh)).add (hlogr.const_mul (1 / 4))).sub
      ((hbplus.mul (hasDerivAt_seam_log1B hr hh)).const_mul 2) |>.sub
      ((hbminus.mul (hasDerivAt_seam_log1C hr hh)).const_mul 2)
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun t => by
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
        ring)
    · field_simp [show 1 - r ≠ 0 by linarith [hr.2]]
      try ring
  have hev : (fun t => chartHeight (seamCellB t) (seamCellC t)) =ᶠ[nhds r]
      (fun t => -(7 / 8) * Real.log (certDiagonal (7 / 8) (1 / (8 * t)))
        + xLogX ((1 + Real.sqrt (seamImbalanceSq t)) / 16)
        + xLogX ((1 - Real.sqrt (seamImbalanceSq t)) / 16)
        + (1 / 4) * Real.log (1 - t)
        - 2 * ((1 + Real.sqrt (seamImbalanceSq t)) / 16)
            * Real.log (1 - seamCellB t)
        - 2 * ((1 - Real.sqrt (seamImbalanceSq t)) / 16)
            * Real.log (1 - seamCellC t)) := by
    have h1 : ∀ᶠ t in nhds r, t ∈ Set.Ioo ((1 : ℝ) / 2) 1 := Ioo_mem_nhds hr.1 hr.2
    have h2 : ∀ᶠ t in nhds r, 0 < seamImbalanceSq t :=
      (hasDerivAt_seamImbalanceSq hr).continuousAt.eventually (lt_mem_nhds hh)
    filter_upwards [h1, h2] with t ht1 ht2
    exact seamHeight_eq ht1 ht2.le
  exact (hexp.congr_of_eventuallyEq hev).congr_deriv (by try ring)

/-! ## The margin's derivative -/

/-- **The isolating code's margin at the seam, differentiated in the radius.**
Its derivative is the squared imbalance's derivative, over four times the
imbalance, times the logarithm `seam_logRatio_pos` puts above zero. -/
theorem hasDerivAt_seamSingletonScalar (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 < seamImbalanceSq r) :
    HasDerivAt seamSingletonScalar
      (seamImbalanceSqDeriv r / (32 * Real.sqrt (seamImbalanceSq r))
        * Real.log ((seamCellC r * (1 - seamCellC r - 2 * seamProduct r) ^ 4)
          / (seamCellB r * (1 - seamCellB r - 2 * seamProduct r) ^ 4))) r := by
  have hZ : HasDerivAt (fun t => Real.sqrt (seamImbalanceSq t))
      (seamImbalanceSqDeriv r / (2 * Real.sqrt (seamImbalanceSq r))) r :=
    (hasDerivAt_seamImbalanceSq hr).sqrt hh.ne'
  have hZ0 : 0 < Real.sqrt (seamImbalanceSq r) := Real.sqrt_pos.2 hh
  have hZ1 : Real.sqrt (seamImbalanceSq r) < 1 :=
    (rayValues_of_seamRadius hr hh.le).1.2
  have hJ := (hasDerivAt_seamLogEntropy (Real.sqrt_nonneg _) hZ1).comp r hZ
  have hR := (hasDerivAt_seamMarginalEntropy
    (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith)).comp r hZ
  have hk := hasDerivAt_seamHeight hr hh
  have hexp := (((((hJ.const_mul 3).sub (hR.const_mul 4)).sub
    (hk.neg.const_mul 2)).sub
    (hasDerivAt_const r (xLogX ((1 - (1 / 8 : ℝ)) / 2)))).sub
    (hasDerivAt_const r (xLogX ((1 + (1 / 8 : ℝ)) / 2))))
  unfold seamSingletonScalar centerSingletonScalar
  refine hexp.congr_deriv ?_
  have hrat := seam_rational_vanish hr hh
  have hlog := seam_log_collapse hr hh
  linear_combination 2 * hrat
    + (seamImbalanceSqDeriv r / (32 * Real.sqrt (seamImbalanceSq r))) * hlog

end StochasticToDeterministicLatents.Binary
