import StochasticToDeterministicLatents.Binary.ScalarEstimates

/-!
# The nonpositive phase on a scalar contact chart

On a strict scalar contact chart whose phase reward is nonpositive, the
observable information is at most eight times the mixing sum.  The proof
captures the observable information by sixteen copies of the mixing term at
the contact midpoint, separately below and above `x = 3 / 10`, and then uses a
contact-fibre comparison to pay two midpoint terms from the mixing sum.

All scalar entropy expressions in this module are in natural-log units, as in
`Binary.ContactChart` and `Binary.ScalarEstimates`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

open scoped BigOperators Topology

namespace StochasticToDeterministicLatents.Binary

noncomputable section

open Filter MeasureTheory Set

/-! ## Rational-kernel capture -/

private lemma tendsto_neg_reciprocal_add_atTop (e : ℝ) :
    Tendsto (fun t : ℝ => -(t + e)⁻¹) atTop (nhds 0) := by
  have hadd : Tendsto (fun t : ℝ => t + e) atTop atTop :=
    tendsto_atTop_add_const_right atTop e tendsto_id
  have h := hadd.inv_tendsto_atTop.neg
  simp only [neg_zero] at h
  refine h.congr' (Filter.Eventually.of_forall (fun _ => ?_))
  rfl

/-- The equal-pole rational kernel has total mass `e⁻¹`. -/
theorem integral_Ioi_equal_pole_formula {e : ℝ} (he : 0 < e) :
    (∫ t in Ioi 0, 1 / ((t + e) * (t + e))) = 1 / e := by
  let F : ℝ → ℝ := fun t => -(t + e)⁻¹
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F (1 / ((t + e) * (t + e))) t := by
    intro t ht
    have ht0 : 0 ≤ t := mem_Ici.mp ht
    have hne : t + e ≠ 0 := (by positivity : 0 < t + e).ne'
    have hraw := (((hasDerivAt_id t).add_const e).inv hne).neg
    have hshape := hraw.congr_of_eventuallyEq
      (f₁ := fun s : ℝ => -(s + e)⁻¹) (Filter.Eventually.of_forall (fun _ => rfl))
    exact hshape.congr_deriv (by
      simp only [id_eq]
      field_simp [hne])
  have hlim : Tendsto F atTop (nhds 0) := tendsto_neg_reciprocal_add_atTop e
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / ((t + e) * (t + e)) := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    positivity
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg hlim
  calc
    (∫ t in Ioi 0, 1 / ((t + e) * (t + e))) = 0 - F 0 := h
    _ = 1 / e := by dsimp only [F]; field_simp [he.ne']; ring

private lemma tendsto_log_add_ratio_atTop (e ell : ℝ) :
    Tendsto (fun t : ℝ => Real.log ((t + e) / (t + ell))) atTop (nhds 0) := by
  have hell : Tendsto (fun t : ℝ => t + ell) atTop atTop :=
    tendsto_atTop_add_const_right atTop ell tendsto_id
  have hsmall : Tendsto (fun t : ℝ => (e - ell) / (t + ell)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hell
  have hone : Tendsto (fun t : ℝ => 1 + (e - ell) / (t + ell)) atTop (nhds 1) := by
    simpa only [add_zero] using hsmall.const_add 1
  have hratio : Tendsto (fun t : ℝ => (t + e) / (t + ell)) atTop (nhds 1) := by
    apply hone.congr'
    filter_upwards [Ioi_mem_atTop (-ell)] with t ht
    have ht' : -ell < t := mem_Ioi.mp ht
    have hne : t + ell ≠ 0 := by linarith
    field_simp [hne]
    ring
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  have hlog' : Tendsto (fun t : ℝ => Real.log ((t + e) / (t + ell))) atTop
      (nhds (Real.log 1)) := by
    apply hlog.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  simpa only [Real.log_one] using hlog'

/-- The strict two-pole rational kernel has its logarithmic closed form. -/
theorem integral_Ioi_strict_poles_formula {e ell : ℝ} (he : 0 < e)
    (helt : e < ell) :
    (∫ t in Ioi 0, 1 / ((t + e) * (t + ell))) =
      Real.log (ell / e) / (ell - e) := by
  let F : ℝ → ℝ := fun t =>
    (Real.log (t + e) - Real.log (t + ell)) / (ell - e)
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F (1 / ((t + e) * (t + ell))) t := by
    intro t ht
    have ht0 : 0 ≤ t := mem_Ici.mp ht
    have hte : t + e ≠ 0 := (by positivity : 0 < t + e).ne'
    have hell0 : 0 < ell := lt_trans he helt
    have htl : t + ell ≠ 0 := (by positivity : 0 < t + ell).ne'
    have hd : ell - e ≠ 0 := (sub_pos.mpr helt).ne'
    have hraw := (((((hasDerivAt_id t).add_const e).log hte).sub
      (((hasDerivAt_id t).add_const ell).log htl)).div_const (ell - e))
    have hshape := hraw.congr_of_eventuallyEq
      (f₁ := fun s : ℝ =>
        (Real.log (s + e) - Real.log (s + ell)) / (ell - e))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact hshape.congr_deriv (by
      simp only [id_eq]
      field_simp [hte, htl, hd]
      ring)
  have hlim : Tendsto F atTop (nhds 0) := by
    have hratio := (tendsto_log_add_ratio_atTop e ell).div_const (ell - e)
    have hrewrite : Filter.Eventually (fun t =>
        Real.log ((t + e) / (t + ell)) / (ell - e) = F t) atTop := by
      filter_upwards [Ioi_mem_atTop (max (-e) (-ell))] with t ht
      have hte : t + e ≠ 0 := by
        have : -e < t := lt_of_le_of_lt (le_max_left _ _) ht
        linarith
      have htl : t + ell ≠ 0 := by
        have : -ell < t := lt_of_le_of_lt (le_max_right _ _) ht
        linarith
      rw [Real.log_div hte htl]
    simpa only [zero_div] using hratio.congr' hrewrite
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / ((t + e) * (t + ell)) := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have hell0 : 0 < ell := lt_trans he helt
    positivity
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg hlim
  have hell0 : 0 < ell := lt_trans he helt
  have hlog : Real.log (ell / e) = Real.log ell - Real.log e := by
    rw [Real.log_div hell0.ne' he.ne']
  calc
    (∫ t in Ioi 0, 1 / ((t + e) * (t + ell))) = 0 - F 0 := h
    _ = Real.log (ell / e) / (ell - e) := by
      dsimp only [F]
      rw [hlog]
      ring_nf

/-- The equal-pole kernel mass captured on `(0, m]`. -/
theorem integral_Ioc_equal_pole_formula {e m : ℝ} (he : 0 < e) (hm : 0 < m) :
    (∫ t in Ioc 0 m, 1 / ((t + e) * (t + e))) = 1 / e - 1 / (m + e) := by
  rw [← intervalIntegral.integral_of_le hm.le]
  let F : ℝ → ℝ := fun t => -(t + e)⁻¹
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) m,
      HasDerivAt F (1 / ((t + e) * (t + e))) t := by
    intro t ht
    rw [uIcc_of_le hm.le] at ht
    have ht0 : 0 ≤ t := ht.1
    have hne : t + e ≠ 0 := (by positivity : 0 < t + e).ne'
    have hraw := (((hasDerivAt_id t).add_const e).inv hne).neg
    have hshape := hraw.congr_of_eventuallyEq
      (f₁ := fun s : ℝ => -(s + e)⁻¹) (Filter.Eventually.of_forall (fun _ => rfl))
    exact hshape.congr_deriv (by simp only [id_eq]; field_simp [hne])
  have hint : IntervalIntegrable (fun t : ℝ => 1 / ((t + e) * (t + e))) volume 0 m := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hm.le] at ht
    have ht0 : 0 ≤ t := ht.1
    have hne : t + e ≠ 0 := (by positivity : 0 < t + e).ne'
    exact (continuousAt_const.div
      ((continuousAt_id.add continuousAt_const).mul
        (continuousAt_id.add continuousAt_const)) (mul_ne_zero hne hne)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [F]
  field_simp [he.ne', (by positivity : m + e ≠ 0)]
  ring

/-- The strict-pole kernel mass captured on `(0, m]`. -/
theorem integral_Ioc_strict_poles_formula {e ell m : ℝ} (he : 0 < e)
    (helt : e < ell)
    (hm : 0 < m) :
    (∫ t in Ioc 0 m, 1 / ((t + e) * (t + ell))) =
      (Real.log (ell / e) - Real.log ((m + ell) / (m + e))) / (ell - e) := by
  rw [← intervalIntegral.integral_of_le hm.le]
  let F : ℝ → ℝ := fun t =>
    (Real.log (t + e) - Real.log (t + ell)) / (ell - e)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) m,
      HasDerivAt F (1 / ((t + e) * (t + ell))) t := by
    intro t ht
    rw [uIcc_of_le hm.le] at ht
    have ht0 : 0 ≤ t := ht.1
    have hell0 : 0 < ell := lt_trans he helt
    have hte : t + e ≠ 0 := (by positivity : 0 < t + e).ne'
    have htl : t + ell ≠ 0 := (by positivity : 0 < t + ell).ne'
    have hd : ell - e ≠ 0 := (sub_pos.mpr helt).ne'
    have hraw := (((((hasDerivAt_id t).add_const e).log hte).sub
      (((hasDerivAt_id t).add_const ell).log htl)).div_const (ell - e))
    have hshape := hraw.congr_of_eventuallyEq
      (f₁ := fun s : ℝ =>
        (Real.log (s + e) - Real.log (s + ell)) / (ell - e))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact hshape.congr_deriv (by
      simp only [id_eq]
      field_simp [hte, htl, hd]
      ring)
  have hint : IntervalIntegrable (fun t : ℝ => 1 / ((t + e) * (t + ell))) volume 0 m := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hm.le] at ht
    have ht0 : 0 ≤ t := ht.1
    have hell0 : 0 < ell := lt_trans he helt
    have hte : t + e ≠ 0 := (by positivity : 0 < t + e).ne'
    have htl : t + ell ≠ 0 := (by positivity : 0 < t + ell).ne'
    exact (continuousAt_const.div
      ((continuousAt_id.add continuousAt_const).mul
        (continuousAt_id.add continuousAt_const)) (mul_ne_zero hte htl)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [F]
  have hell0 : 0 < ell := lt_trans he helt
  have hme : 0 < m + e := by positivity
  have hml : 0 < m + ell := by positivity
  rw [Real.log_div hell0.ne' he.ne', Real.log_div hml.ne' hme.ne']
  ring_nf

/-- Sixteen-fold capture of a positive two-pole rational kernel. -/
theorem integral_rationalKernel_le_sixteen_mul_integral {e ell m : ℝ}
    (he : 0 < e) (hel : e ≤ ell) (hm : 0 < m) (hpow : e ^ 3 * ell ≤ (9 * m) ^ 4) :
    (∫ t in Ioi 0, 1 / ((t + e) * (t + ell))) ≤
      16 * ∫ t in Ioc 0 m, 1 / ((t + e) * (t + ell)) := by
  rcases hel.eq_or_lt with rfl | helt
  · have hem : e ≤ 9 * m := by
      apply (pow_le_pow_iff_left₀ he.le (by positivity : 0 ≤ 9 * m)
        (by norm_num : (4 : ℕ) ≠ 0)).mp
      rw [show e ^ 4 = e ^ 3 * e by ring]
      exact hpow
    rw [integral_Ioi_equal_pole_formula he, integral_Ioc_equal_pole_formula he hm]
    have he0 : e ≠ 0 := he.ne'
    have hme : 0 < m + e := by positivity
    field_simp [he0, hme.ne']
    nlinarith
  · let q : ℝ := ell / e
    let a : ℝ := q ^ ((16 : ℝ)⁻¹)
    have hq1 : 1 ≤ q := by
      dsimp only [q]
      exact (le_div_iff₀ he).2 (by linarith)
    have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
    have ha1 : 1 ≤ a := by
      dsimp only [a]
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hq1
        (by norm_num : (0 : ℝ) ≤ (16 : ℝ)⁻¹)
      norm_num at h ⊢
      exact h
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    have ha16 : a ^ 16 = q := by
      dsimp only [a]
      exact Real.rpow_inv_natCast_pow hq0.le (by norm_num)
    have hell : ell = e * a ^ 16 := by
      rw [ha16]
      dsimp only [q]
      field_simp [he.ne']
    have hfourth : (e * a ^ 4) ^ 4 ≤ (9 * m) ^ 4 := by
      calc
        (e * a ^ 4) ^ 4 = e ^ 3 * ell := by rw [hell]; ring
        _ ≤ (9 * m) ^ 4 := hpow
    have hem : e * a ^ 4 ≤ 9 * m := by
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity)
        (by norm_num : (4 : ℕ) ≠ 0)).mp hfourth
    have hsum := nine_mul_pow_eleven_le_sum_range_fifteen ha1
    have hmass : e * a ^ 15 ≤ m * ∑ k ∈ Finset.range 15, a ^ k := by
      calc
        e * a ^ 15 = (e * a ^ 4) * a ^ 11 := by ring
        _ ≤ (9 * m) * a ^ 11 := by gcongr
        _ ≤ m * ∑ k ∈ Finset.range 15, a ^ k := by nlinarith
    have hratio_alg : (m + ell) / (m + e) ≤ a ^ 15 := by
      apply (div_le_iff₀ (by positivity : 0 < m + e)).2
      rw [hell]
      have hgeom := geom_sum_mul_of_one_le ha1 15
      nlinarith [mul_nonneg (show 0 ≤ e * a ^ 15 by positivity) (sub_nonneg.mpr ha1)]
    have hell0 : 0 < ell := lt_trans he helt
    have hratio0 : 0 < (m + ell) / (m + e) := by positivity
    have hloga : Real.log ((m + ell) / (m + e)) ≤ Real.log (a ^ 15) :=
      Real.strictMonoOn_log.monotoneOn (mem_Ioi.mpr hratio0)
        (mem_Ioi.mpr (by positivity)) hratio_alg
    have hloga15 : Real.log (a ^ 15) = (15 / 16 : ℝ) * Real.log q := by
      dsimp only [a]
      rw [Real.log_pow, Real.log_rpow hq0]
      ring
    have hlogbound : 16 * Real.log ((m + ell) / (m + e)) ≤
        15 * Real.log (ell / e) := by
      rw [hloga15] at hloga
      change 16 * Real.log ((m + ell) / (m + e)) ≤ 15 * Real.log q
      dsimp only [q]
      linarith
    rw [integral_Ioi_strict_poles_formula he helt,
      integral_Ioc_strict_poles_formula he helt hm]
    have hd : 0 < ell - e := sub_pos.mpr helt
    apply (div_le_iff₀ hd).2
    field_simp [hd.ne']
    linarith

/-! ## Contact midpoint and phase reward -/

/-- The repeated diagonal coordinate at the balanced point of a contact fibre. -/
def ScalarContactChart.contactMidpoint (C : ScalarContactChart) : ℝ :=
  StochasticToDeterministicLatents.Binary.contactMidpoint C.x

/-- Reward with the contact sum exposed as a free scalar coordinate. -/
def exposedPhaseReward (C : ScalarContactChart) (s : ℝ) : ℝ :=
  pairEntropy C.e (C.ell + s) -
    4 * ((1 - C.pi) * pairEntropy C.r (1 + s) +
      C.pi * pairEntropy 1 (C.r + s))

/-- The exposed reward agrees with the chart ledger at its contact coordinate. -/
theorem exposedPhaseReward_at_contact (C : ScalarContactChart) :
    exposedPhaseReward C C.s = C.phaseReward := by
  rfl

/-- Positivity of the balanced contact coordinate. -/
theorem ScalarContactChart.contactMidpoint_pos (C : ScalarContactChart) :
    0 < C.contactMidpoint := by
  unfold ScalarContactChart.contactMidpoint
  unfold StochasticToDeterministicLatents.Binary.contactMidpoint contactDenominator
  have hden : 0 < 1 + C.x + C.x ^ 2 := by
    nlinarith [C.x_pos, sq_nonneg C.x]
  exact div_pos (pow_pos C.x_pos 3) hden

/-- The midpoint solves the diagonal contact equation. -/
theorem ScalarContactChart.contactMidpoint_contact (C : ScalarContactChart) :
    (1 + C.y + C.r) * C.contactMidpoint ^ 2 =
      C.r * (C.y - 2 * C.contactMidpoint) := by
  unfold ScalarContactChart.contactMidpoint
  unfold StochasticToDeterministicLatents.Binary.contactMidpoint contactDenominator
    ScalarContactChart.y ScalarContactChart.r
  have hden : 1 + C.x + C.x ^ 2 ≠ 0 := by
    nlinarith [C.x_pos, sq_nonneg C.x]
  field_simp [hden]
  ring

private theorem hasDerivAt_exposedPhaseReward (C : ScalarContactChart) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (exposedPhaseReward C)
      (Real.log ((C.e + (C.ell + s)) / (C.ell + s)) -
        4 * ((1 - C.pi) * Real.log ((C.r + (1 + s)) / (1 + s)) +
          C.pi * Real.log ((1 + (C.r + s)) / (C.r + s)))) s := by
  change HasDerivAt
    (fun z : ℝ => pairEntropy C.e (C.ell + z) -
      4 * ((1 - C.pi) * pairEntropy C.r (1 + z) +
        C.pi * pairEntropy 1 (C.r + z)))
    (Real.log ((C.e + (C.ell + s)) / (C.ell + s)) -
      4 * ((1 - C.pi) * Real.log ((C.r + (1 + s)) / (1 + s)) +
        C.pi * Real.log ((1 + (C.r + s)) / (C.r + s)))) s
  have h₁ : HasDerivAt (fun z : ℝ => pairEntropy C.e (C.ell + z))
      (Real.log ((C.e + (C.ell + s)) / (C.ell + s))) s := by
    have h := (hasDerivAt_pairEntropy_right C.e_pos (add_pos C.ell_pos hs)).comp s
      ((hasDerivAt_const s C.ell).add (hasDerivAt_id s))
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun z : ℝ => pairEntropy C.e (C.ell + z))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact h'.congr_deriv (by ring)
  have h₂ : HasDerivAt (fun z : ℝ => pairEntropy C.r (1 + z))
      (Real.log ((C.r + (1 + s)) / (1 + s))) s := by
    have h := (hasDerivAt_pairEntropy_right C.r_pos (by linarith : 0 < 1 + s)).comp s
      ((hasDerivAt_const s 1).add (hasDerivAt_id s))
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun z : ℝ => pairEntropy C.r (1 + z))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact h'.congr_deriv (by ring)
  have h₃ : HasDerivAt (fun z : ℝ => pairEntropy 1 (C.r + z))
      (Real.log ((1 + (C.r + s)) / (C.r + s))) s := by
    have h := (hasDerivAt_pairEntropy_right (by norm_num : (0 : ℝ) < 1)
      (add_pos C.r_pos hs)).comp s ((hasDerivAt_const s C.r).add (hasDerivAt_id s))
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun z : ℝ => pairEntropy 1 (C.r + z))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact h'.congr_deriv (by ring)
  exact h₁.sub ((h₂.const_mul (1 - C.pi)).add (h₃.const_mul C.pi) |>.const_mul 4)

private theorem exposedPhaseReward_deriv_neg (C : ScalarContactChart)
    (hpi : 0 < C.pi) {s : ℝ} (hs : 0 < s) :
    deriv (exposedPhaseReward C) s < 0 := by
  have hder := hasDerivAt_exposedPhaseReward C hs
  rw [hder.deriv]
  have hp0 : 0 ≤ C.pi := hpi.le
  have hp1 : 0 ≤ 1 - C.pi := by linarith [C.pi_le_half]
  have hsum : (1 - C.pi) + C.pi = 1 := by ring
  have h1s : 0 < 1 + s := by linarith
  have hrs : 0 < C.r + s := add_pos C.r_pos hs
  have hells : 0 < C.ell + s := add_pos C.ell_pos hs
  have htot : 0 < 1 + C.r + s := by linarith [C.r_pos]
  have hj := strictConcaveOn_log_Ioi.concaveOn.2 h1s hrs hp1 hp0 hsum
  have haffine : (1 - C.pi) * (1 + s) + C.pi * (C.r + s) = C.ell + s := by
    unfold ScalarContactChart.ell
    ring
  have hj' :
      (1 - C.pi) * Real.log (1 + s) + C.pi * Real.log (C.r + s) ≤
        Real.log (C.ell + s) := by
    simpa only [smul_eq_mul, haffine] using hj
  have hell_lt : C.ell + s < 1 + C.r + s := by
    have he := C.e_pos
    have hesum := C.e_add_ell
    linarith
  have hlog_lt : Real.log (C.ell + s) < Real.log (1 + C.r + s) :=
    Real.strictMonoOn_log hells htot hell_lt
  rw [show C.e + (C.ell + s) = 1 + C.r + s by linarith [C.e_add_ell],
    show C.r + (1 + s) = 1 + C.r + s by ring,
    show 1 + (C.r + s) = 1 + C.r + s by ring,
    Real.log_div htot.ne' hells.ne', Real.log_div htot.ne' h1s.ne',
    Real.log_div htot.ne' hrs.ne']
  nlinarith

/-- The phase reward strictly decreases along the strict contact interval. -/
theorem exposedPhaseReward_strictAntiOn (C : ScalarContactChart)
    (hC : C.StrictInterior) :
    StrictAntiOn (exposedPhaseReward C) (Icc (2 * C.contactMidpoint) C.y) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (2 * C.contactMidpoint) C.y)
  · intro s hs
    have hs0 : 0 < s := by
      have hm := C.contactMidpoint_pos
      linarith [hs.1]
    exact (hasDerivAt_exposedPhaseReward C hs0).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 * C.contactMidpoint) C.y := interior_subset hs
    have hs0 : 0 < s := by
      have hm := C.contactMidpoint_pos
      linarith [hs'.1]
    exact exposedPhaseReward_deriv_neg C hC.2.1 hs0

/-! ## Moving endpoints on a contact fibre -/

/-- The upper contact endpoint as a rational function of the lower endpoint. -/
def movingContactEndpoint (C : ScalarContactChart) (lowMass : ℝ) : ℝ :=
  C.r * (C.y - lowMass) / ((1 + C.y + C.r) * lowMass + C.r)

/-- The rational endpoint formula recovers the chart's high endpoint. -/
theorem movingContactEndpoint_lowMass (C : ScalarContactChart) :
    movingContactEndpoint C C.lowMass = C.highMass := by
  have hden : 0 < (1 + C.y + C.r) * C.lowMass + C.r :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg C.denominator_pos.le C.lowMass_nonneg) C.r_pos
  unfold movingContactEndpoint
  apply (div_eq_iff (by nlinarith [hden] :
    (1 + C.y + C.r) * C.lowMass + C.r ≠ 0)).2
  have h := C.contact
  change (1 + C.y + C.r) * C.lowMass * C.highMass =
    C.r * (C.y - (C.lowMass + C.highMass)) at h
  nlinarith

/-- The contact midpoint is the fixed point of the moving endpoint map. -/
theorem movingContactEndpoint_midpoint (C : ScalarContactChart) :
    movingContactEndpoint C C.contactMidpoint = C.contactMidpoint := by
  have hmid := C.contactMidpoint_contact
  have hm : 0 < C.contactMidpoint := C.contactMidpoint_pos
  have hden : 0 < (1 + C.y + C.r) * C.contactMidpoint + C.r :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg C.denominator_pos.le hm.le) C.r_pos
  unfold movingContactEndpoint
  apply (div_eq_iff hden.ne').2
  nlinarith [hmid]

/-- The exact endpoint identity used to normalize the derivative bound. -/
theorem contactMidpoint_linear_square (C : ScalarContactChart) :
    ((1 + C.y + C.r) * C.contactMidpoint + C.r) ^ 2 =
      C.r * (C.r + (1 + C.y + C.r) * C.y) := by
  unfold ScalarContactChart.contactMidpoint
  unfold StochasticToDeterministicLatents.Binary.contactMidpoint contactDenominator
    ScalarContactChart.y ScalarContactChart.r
  have hden : 1 + C.x + C.x ^ 2 ≠ 0 := by
    nlinarith [C.x_pos, sq_nonneg C.x]
  field_simp [hden]
  ring

/-- Below the midpoint, the squared linear denominator is bounded by its
midpoint value. -/
theorem contact_linear_square_le_at_midpoint (C : ScalarContactChart) {lowMass : ℝ}
    (hlow0 : 0 ≤ lowMass) (hlowm : lowMass ≤ C.contactMidpoint) :
    ((1 + C.y + C.r) * lowMass + C.r) ^ 2 ≤
      C.r * (C.r + (1 + C.y + C.r) * C.y) := by
  have hQ : 0 ≤ 1 + C.y + C.r := C.denominator_pos.le
  have hlin0 : 0 ≤ (1 + C.y + C.r) * lowMass + C.r :=
    add_nonneg (mul_nonneg hQ hlow0) C.r_pos.le
  have hlinm : 0 ≤ (1 + C.y + C.r) * C.contactMidpoint + C.r :=
    add_nonneg (mul_nonneg hQ C.contactMidpoint_pos.le) C.r_pos.le
  have hlin_le :
      (1 + C.y + C.r) * lowMass + C.r ≤
        (1 + C.y + C.r) * C.contactMidpoint + C.r := by
    gcongr
  rw [← contactMidpoint_linear_square C]
  nlinarith [sq_nonneg
    ((1 + C.y + C.r) * C.contactMidpoint + C.r -
      ((1 + C.y + C.r) * lowMass + C.r))]

/-- Derivative of the rational moving contact endpoint. -/
theorem hasDerivAt_movingContactEndpoint (C : ScalarContactChart) (lowMass : ℝ)
    (hden : (1 + C.y + C.r) * lowMass + C.r ≠ 0) :
    HasDerivAt (movingContactEndpoint C)
      (-C.r * (C.r + (1 + C.y + C.r) * C.y) /
        ((1 + C.y + C.r) * lowMass + C.r) ^ 2) lowMass := by
  let Q : ℝ := 1 + C.y + C.r
  have hn0 := (hasDerivAt_const lowMass C.r).mul
    ((hasDerivAt_const lowMass C.y).sub (hasDerivAt_id lowMass))
  have hn1 := hn0.congr_of_eventuallyEq
    (f₁ := fun z : ℝ => C.r * (C.y - z))
    (Filter.Eventually.of_forall (fun _ => rfl))
  have hn : HasDerivAt (fun z : ℝ => C.r * (C.y - z)) (-C.r) lowMass :=
    hn1.congr_deriv (by ring)
  have hd0 := (hasDerivAt_const lowMass Q).mul (hasDerivAt_id lowMass) |>.add_const C.r
  have hd1 := hd0.congr_of_eventuallyEq (f₁ := fun z : ℝ => Q * z + C.r)
    (Filter.Eventually.of_forall (fun _ => rfl))
  have hd : HasDerivAt (fun z : ℝ => Q * z + C.r) Q lowMass :=
    hd1.congr_deriv (by ring)
  have hq := hn.div hd (by simpa [Q] using hden)
  apply hq.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun _ => by rfl)) |>.congr_deriv
  dsimp [Q]
  field_simp [hden]
  ring

/-- On the lower half of a contact fibre the moving endpoint has slope at
most `-1`. -/
theorem movingContactEndpoint_deriv_le_neg_one (C : ScalarContactChart) {lowMass : ℝ}
    (hlow0 : 0 ≤ lowMass) (hlowm : lowMass ≤ C.contactMidpoint) :
    -C.r * (C.r + (1 + C.y + C.r) * C.y) /
        ((1 + C.y + C.r) * lowMass + C.r) ^ 2 ≤ -1 := by
  have hdenpos : 0 < (1 + C.y + C.r) * lowMass + C.r :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg C.denominator_pos.le hlow0) C.r_pos
  have hsquarepos : 0 < ((1 + C.y + C.r) * lowMass + C.r) ^ 2 :=
    sq_pos_of_pos hdenpos
  have hsq := contact_linear_square_le_at_midpoint C hlow0 hlowm
  apply (div_le_iff₀ hsquarepos).2
  nlinarith

/-- Cancellation of the two endpoint kernels on the contact locus. -/
theorem movingEndpoint_kernel_identity (C : ScalarContactChart)
    {lowMass highMass c : ℝ}
    (hcontact : (1 + C.y + C.r) * lowMass * highMass =
      C.r * (C.y - (lowMass + highMass))) :
    (highMass + C.r / (1 + C.y + C.r)) *
        (((lowMass + C.r) * (lowMass + 1)) + c) -
      (lowMass + C.r / (1 + C.y + C.r)) *
        (((highMass + C.r) * (highMass + 1)) + c) =
          (highMass - lowMass) * c := by
  have hQ : 1 + C.y + C.r ≠ 0 := C.denominator_pos.ne'
  field_simp [hQ]
  linear_combination (lowMass - highMass) * hcontact

/-! ## Moving-endpoint kernel comparison -/

/-- The rectangle supporting the finite mixing-kernel integral is integrable. -/
theorem mixingKernel_rectangle_integrable (C : ScalarContactChart) {z : ℝ}
    (hz : 0 ≤ z) :
    IntegrableOn (Function.uncurry (fun c t : ℝ =>
      1 / (((t + C.r) * (t + 1)) + c)))
      (uIoc 0 (mixingGap C) ×ˢ uIoc 0 z) := by
  have hcont : ContinuousOn (Function.uncurry (fun c t : ℝ =>
      1 / (((t + C.r) * (t + 1)) + c)))
      (Icc 0 (mixingGap C) ×ˢ Icc 0 z) := by
    apply ContinuousOn.div
      (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (1 : ℝ)) _)
      (((continuousOn_snd.add continuousOn_const).mul
        (continuousOn_snd.add continuousOn_const)).add continuousOn_fst)
    rintro ⟨c, t⟩ ⟨hc, ht⟩ hzero
    change 0 ≤ c ∧ c ≤ mixingGap C at hc
    change 0 ≤ t ∧ t ≤ z at ht
    have hden : 0 < (t + C.r) * (t + 1) + c := by
      have htr : 0 < t + C.r := add_pos_of_nonneg_of_pos ht.1 C.r_pos
      have ht1 : 0 < t + 1 := by linarith
      exact add_pos_of_pos_of_nonneg (mul_pos htr ht1) hc.1
    exact hden.ne' hzero
  apply (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  rintro ⟨c, t⟩ ⟨hc, ht⟩
  rw [uIoc_of_le (mixingGap_nonnegative C)] at hc
  rw [uIoc_of_le hz] at ht
  exact ⟨⟨hc.1.le, hc.2⟩, ⟨ht.1.le, ht.2⟩⟩

/-- Differentiation of the finite rational kernel at a positive endpoint. -/
theorem hasDerivAt_mixingKernelBelow (C : ScalarContactChart) (c z : ℝ)
    (hc : 0 ≤ c) (hz : 0 < z) :
    HasDerivAt (mixingKernelBelow C c)
      (1 / (((z + C.r) * (z + 1)) + c)) z := by
  let f : ℝ → ℝ := fun t => 1 / (((t + C.r) * (t + 1)) + c)
  have hcont : ContinuousOn f (uIcc 0 z) := by
    rw [uIcc_of_le hz.le]
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_id.add continuousOn_const).mul
        (continuousOn_id.add continuousOn_const) |>.add continuousOn_const)
    intro t ht hzero
    have htr : 0 < t + C.r := add_pos_of_nonneg_of_pos ht.1 C.r_pos
    have ht1 : 0 < t + 1 := by linarith [ht.1]
    have hden : 0 < (t + C.r) * (t + 1) + c :=
      add_pos_of_pos_of_nonneg (mul_pos htr ht1) hc
    exact hden.ne' hzero
  have hint : IntervalIntegrable f volume 0 z := hcont.intervalIntegrable
  have hcontz : ContinuousAt f z := by
    apply ContinuousAt.div continuousAt_const
      ((continuousAt_id.add continuousAt_const).mul
        (continuousAt_id.add continuousAt_const) |>.add continuousAt_const)
    have hden : 0 < (z + C.r) * (z + 1) + c :=
      add_pos_of_pos_of_nonneg
        (mul_pos (add_pos hz C.r_pos) (by linarith)) hc
    exact hden.ne'
  have hmeas : StronglyMeasurableAtFilter f (nhds z) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun t ht => by
        change 0 < t at ht
        apply ContinuousAt.div continuousAt_const
          ((continuousAt_id.add continuousAt_const).mul
            (continuousAt_id.add continuousAt_const) |>.add continuousAt_const)
        have hden : 0 < (t + C.r) * (t + 1) + c :=
          add_pos_of_pos_of_nonneg
            (mul_pos (add_pos ht C.r_pos) (by linarith)) hc
        exact hden.ne') z hz
  have hder := intervalIntegral.integral_hasDerivAt_right hint hmeas hcontz
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hz] with u hu
  symm
  exact intervalIntegral.integral_of_le hu.le

/-- The finite mixing kernel is monotone in its positive endpoint. -/
theorem mixingKernelBelow_mono_of_pos (C : ScalarContactChart) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) :
    mixingKernelBelow C c a ≤ mixingKernelBelow C c b := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro z hz
    exact (hasDerivAt_mixingKernelBelow C c z hc
      (ha.trans_le hz.1)).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    exact (hasDerivAt_mixingKernelBelow C c z hc
      (ha.trans_le hz'.1)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hasDerivAt_mixingKernelBelow C c z hc (ha.trans_le hz'.1)).deriv]
    exact one_div_nonneg.mpr (by
      have hzr : 0 < z + C.r := add_pos (ha.trans_le hz'.1) C.r_pos
      have hz1 : 0 < z + 1 := by linarith [ha.trans_le hz'.1]
      exact (add_pos_of_pos_of_nonneg (mul_pos hzr hz1) hc).le)
  · exact ⟨le_rfl, hab⟩
  · exact ⟨hab, le_rfl⟩
  · exact hab

/-- Twice the finite kernel at the contact midpoint is bounded by the sum at
the two contact endpoints. -/
theorem two_mul_mixingKernelBelow_midpoint_le_endpoints
    (C : ScalarContactChart) (hC : C.StrictInterior) (c : ℝ) (hc : 0 ≤ c) :
    2 * mixingKernelBelow C c C.contactMidpoint ≤
      mixingKernelBelow C c C.lowMass + mixingKernelBelow C c C.highMass := by
  let m := C.contactMidpoint
  let F := mixingKernelBelow C c
  by_cases hlowm : C.lowMass ≤ m
  · have hlowpos : 0 < C.lowMass := by
      have hslt : C.lowMass + C.highMass < C.y := hC.2.2.2.1
      have hcontact := C.contact_eq
      by_contra hn
      have hlowz : C.lowMass = 0 :=
        le_antisymm (le_of_not_gt hn) C.lowMass_nonneg
      rw [hlowz, zero_mul] at hcontact
      have hy : C.y = C.s := by
        rcases mul_eq_zero.mp hcontact.symm with hr | hy
        · exact False.elim (C.ratio_pos.ne' hr)
        · exact sub_eq_zero.mp hy
      change C.lowMass + C.highMass < C.y at hslt
      dsimp [ScalarContactChart.s] at hy
      linarith
    have hmpos : 0 < m := C.contactMidpoint_pos
    let Dof := movingContactEndpoint C
    let G : ℝ → ℝ := fun lowMass => F lowMass + F (Dof lowMass) - 2 * F m
    have hDof_pos : ∀ {lowMass : ℝ}, lowMass ∈ Icc C.lowMass m →
        0 < Dof lowMass := by
      intro lowMass hlow
      have hlowy : lowMass < C.y := by
        have hm_lt_y : m < C.y := by
          have hmid := C.contactMidpoint_contact
          have hm0 : 0 < m := C.contactMidpoint_pos
          have hleft : 0 < (1 + C.y + C.r) * m ^ 2 :=
            mul_pos C.denominator_pos (sq_pos_of_pos hm0)
          nlinarith [C.r_pos]
        exact hlow.2.trans_lt hm_lt_y
      have hden : 0 < (1 + C.y + C.r) * lowMass + C.r :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg C.denominator_pos.le (hlowpos.le.trans hlow.1)) C.r_pos
      dsimp [Dof, movingContactEndpoint]
      exact div_pos (mul_pos C.r_pos (sub_pos.mpr hlowy)) hden
    have hanti : AntitoneOn G (Icc C.lowMass m) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc C.lowMass m)
      · intro lowMass hlow
        have hlowp : 0 < lowMass := hlowpos.trans_le hlow.1
        have hDp : 0 < Dof lowMass := hDof_pos hlow
        have hp : 0 < (1 + C.y + C.r) * lowMass + C.r :=
          add_pos_of_nonneg_of_pos
            (mul_nonneg C.denominator_pos.le hlowp.le) C.r_pos
        have h₁ := hasDerivAt_mixingKernelBelow C c lowMass hc hlowp
        have h₂ := (hasDerivAt_mixingKernelBelow C c (Dof lowMass) hc hDp).comp lowMass
          (hasDerivAt_movingContactEndpoint C lowMass hp.ne')
        exact ((h₁.add h₂).sub_const (2 * F m)).continuousAt.continuousWithinAt
      · intro lowMass hlow
        have hlowi : lowMass ∈ Icc C.lowMass m := interior_subset hlow
        have hlowp : 0 < lowMass := hlowpos.trans_le hlowi.1
        have hDp : 0 < Dof lowMass := hDof_pos hlowi
        have hp : 0 < (1 + C.y + C.r) * lowMass + C.r :=
          add_pos_of_nonneg_of_pos
            (mul_nonneg C.denominator_pos.le hlowp.le) C.r_pos
        have h₁ := hasDerivAt_mixingKernelBelow C c lowMass hc hlowp
        have h₂ := (hasDerivAt_mixingKernelBelow C c (Dof lowMass) hc hDp).comp lowMass
          (hasDerivAt_movingContactEndpoint C lowMass hp.ne')
        exact ((h₁.add h₂).sub_const (2 * F m)).differentiableAt.differentiableWithinAt
      · intro lowMass hlow
        have hlowi : lowMass ∈ Icc C.lowMass m := interior_subset hlow
        have hlowp : 0 < lowMass := hlowpos.trans_le hlowi.1
        have hDp : 0 < Dof lowMass := hDof_pos hlowi
        have hden : 0 < (1 + C.y + C.r) * lowMass + C.r :=
          add_pos_of_nonneg_of_pos
            (mul_nonneg C.denominator_pos.le hlowp.le) C.r_pos
        let d : ℝ := -C.r * (C.r + (1 + C.y + C.r) * C.y) /
          ((1 + C.y + C.r) * lowMass + C.r) ^ 2
        have hder : HasDerivAt G
            (1 / (((lowMass + C.r) * (lowMass + 1)) + c) +
              1 / ((((Dof lowMass) + C.r) * ((Dof lowMass) + 1)) + c) * d) lowMass := by
          have h₁ := hasDerivAt_mixingKernelBelow C c lowMass hc hlowp
          have h₂ := (hasDerivAt_mixingKernelBelow C c (Dof lowMass) hc hDp).comp lowMass
            (hasDerivAt_movingContactEndpoint C lowMass hden.ne')
          exact (h₁.add h₂).sub_const (2 * F m)
        rw [hder.deriv]
        have hd : d ≤ -1 :=
          movingContactEndpoint_deriv_le_neg_one C hlowp.le hlowi.2
        have hDA : lowMass ≤ Dof lowMass := by
          dsimp [Dof, movingContactEndpoint]
          rw [le_div_iff₀ hden]
          have hmid := C.contactMidpoint_contact
          have hlin := contact_linear_square_le_at_midpoint C hlowp.le hlowi.2
          have hfactor :
              C.r * (C.r + (1 + C.y + C.r) * C.y) -
                  ((1 + C.y + C.r) * lowMass + C.r) ^ 2 =
                (1 + C.y + C.r) *
                  (C.r * (C.y - lowMass) -
                    lowMass * ((1 + C.y + C.r) * lowMass + C.r)) := by
            ring
          have hcore : 0 ≤ C.r * (C.y - lowMass) -
              lowMass * ((1 + C.y + C.r) * lowMass + C.r) := by
            have hq := C.denominator_pos
            nlinarith
          nlinarith
        have hcontact : (1 + C.y + C.r) * lowMass * Dof lowMass =
            C.r * (C.y - (lowMass + Dof lowMass)) := by
          dsimp [Dof, movingContactEndpoint]
          field_simp [hden.ne']
          ring
        have hid := movingEndpoint_kernel_identity C (c := c) hcontact
        have hgA : 0 < ((lowMass + C.r) * (lowMass + 1)) + c :=
          add_pos_of_pos_of_nonneg
            (mul_pos (add_pos hlowp C.r_pos) (by linarith)) hc
        have hgD : 0 < (((Dof lowMass + C.r) * (Dof lowMass + 1)) + c) :=
          add_pos_of_pos_of_nonneg
            (mul_pos (add_pos hDp C.r_pos) (by linarith)) hc
        have hrhoA : 0 < lowMass + C.r / (1 + C.y + C.r) :=
          add_pos hlowp (div_pos C.r_pos C.denominator_pos)
        have hrhoD : 0 < Dof lowMass + C.r / (1 + C.y + C.r) :=
          add_pos hDp (div_pos C.r_pos C.denominator_pos)
        have hd_eq : d = -(Dof lowMass + C.r / (1 + C.y + C.r)) /
            (lowMass + C.r / (1 + C.y + C.r)) := by
          dsimp [d, Dof, movingContactEndpoint]
          field_simp [hden.ne', C.denominator_pos.ne']
          ring
        rw [hd_eq]
        have hcharge : 0 ≤ (Dof lowMass - lowMass) * c :=
          mul_nonneg (sub_nonneg.mpr hDA) hc
        field_simp [hgA.ne', hgD.ne', hrhoA.ne']
        nlinarith [hid, hcharge]
    have hG := hanti ⟨le_rfl, hlowm⟩ ⟨hlowm, le_rfl⟩ hlowm
    dsimp [G, F, Dof, m] at hG ⊢
    rw [movingContactEndpoint_lowMass, movingContactEndpoint_midpoint] at hG
    linarith
  · have hmA : m < C.lowMass := lt_of_not_ge hlowm
    have hmpos : 0 < m := C.contactMidpoint_pos
    have hFA := mixingKernelBelow_mono_of_pos C hc hmpos hmA.le
    have hFD := mixingKernelBelow_mono_of_pos C hc hmpos
      (hmA.le.trans C.lowMass_le_highMass)
    dsimp [F, m] at hFA hFD ⊢
    linarith

private theorem mixingKernelBelow_integrableInMixingParameter
    (C : ScalarContactChart) {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun c => mixingKernelBelow C c z) (Ioc 0 (mixingGap C)) := by
  have hrect := mixingKernel_rectangle_integrable C hz
  have hr : Integrable (Function.uncurry (fun c t : ℝ =>
      1 / (((t + C.r) * (t + 1)) + c)))
      ((volume.restrict (Ioc 0 (mixingGap C))).prod
        (volume.restrict (Ioc 0 z))) := by
    change Integrable _ ((volume.prod volume).restrict
      (uIoc 0 (mixingGap C) ×ˢ uIoc 0 z)) at hrect
    rw [Measure.prod_restrict]
    simpa [uIoc_of_le (mixingGap_nonnegative C), uIoc_of_le hz] using hrect
  have hi := hr.integral_prod_left
  change Integrable (fun c => mixingKernelBelow C c z)
    (volume.restrict (Ioc 0 (mixingGap C)))
  apply hi.congr
  filter_upwards [] with c
  rfl

/-- The mixing sum pays twice the mixing term at the contact midpoint. -/
theorem ScalarContactChart.two_mul_midpointMixing_le_mixingSum
    (C : ScalarContactChart) (hC : C.StrictInterior) :
    2 * C.mixingTerm (StochasticToDeterministicLatents.Binary.contactMidpoint C.x) ≤
      C.mixingSum := by
  have hm0 : 0 ≤ StochasticToDeterministicLatents.Binary.contactMidpoint C.x :=
    C.contactMidpoint_pos.le
  unfold ScalarContactChart.mixingSum
  rw [mixingTerm_eq_integral_kernel C hm0,
    mixingTerm_eq_integral_kernel C C.lowMass_nonneg,
    mixingTerm_eq_integral_kernel C C.highMass_nonneg]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add]
  · apply MeasureTheory.integral_mono_ae
    · exact (mixingKernelBelow_integrableInMixingParameter C hm0).const_mul 2
    · exact (mixingKernelBelow_integrableInMixingParameter C C.lowMass_nonneg).add
        (mixingKernelBelow_integrableInMixingParameter C C.highMass_nonneg)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with c hcset
      exact two_mul_mixingKernelBelow_midpoint_le_endpoints C hC c (le_of_lt hcset.1)
  · exact mixingKernelBelow_integrableInMixingParameter C C.lowMass_nonneg
  · exact mixingKernelBelow_integrableInMixingParameter C C.highMass_nonneg

/-! ## The small-parameter prior gate -/

/-- At the upper endpoint of a contact fibre, the exposed phase reward is the
edge reward with row ratio `C.x ^ 2`. -/
theorem exposedPhaseReward_at_y_eq_edgeReward (C : ScalarContactChart) :
    exposedPhaseReward C C.y = edgeReward (C.x ^ 2) C.pi := by
  unfold exposedPhaseReward edgeReward
  dsimp
  simp only [ScalarContactChart.y, ScalarContactChart.r, ScalarContactChart.e,
    ScalarContactChart.ell]
  congr 1 <;> ring_nf

/-- For a nondegenerate row ratio, the edge reward is strictly concave in the
prior on the canonical prior interval. -/
theorem strictConcaveOn_edgeReward_prior {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    StrictConcaveOn ℝ (Icc 0 (1 / 2)) (fun pi => edgeReward q pi) := by
  let Q : ℝ := 1 + q + q ^ 2
  let p : ℝ → ℝ := fun pi => (q ^ 2 + pi * (1 - q ^ 2)) / Q
  have hq_nonneg : 0 ≤ q := hq0.le
  have hq_le : q ≤ 1 := hq1.le
  have hq2_nonneg : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2_le : q ^ 2 ≤ 1 := by nlinarith [sq_nonneg (q - 1)]
  have hQ : 0 < Q := by dsimp [Q]; nlinarith
  have hnormalize : ∀ pi ∈ Icc (0 : ℝ) (1 / 2),
      edgeReward q pi =
        Q * Real.binEntropy (p pi) -
          4 * ((1 - pi) * pairEntropy (q ^ 2) (1 + q) +
            pi * pairEntropy 1 (q ^ 2 + q)) := by
    intro pi hpi
    have he0 : 0 ≤ q ^ 2 + pi * (1 - q ^ 2) :=
      add_nonneg hq2_nonneg (mul_nonneg hpi.1 (sub_nonneg.mpr hq2_le))
    have hell0 : 0 ≤ 1 - pi + pi * q ^ 2 + q := by nlinarith [hpi.2]
    have hsum : 0 <
        (q ^ 2 + pi * (1 - q ^ 2)) + (1 - pi + pi * q ^ 2 + q) := by
      rw [show (q ^ 2 + pi * (1 - q ^ 2)) +
          (1 - pi + pi * q ^ 2 + q) = Q by
        dsimp [Q]
        ring]
      exact hQ
    unfold edgeReward
    dsimp
    rw [pairEntropy_eq_mass_mul_binEntropy he0 hell0 hsum]
    change
      ((q ^ 2 + pi * (1 - q ^ 2)) + (1 - pi + pi * q ^ 2 + q)) *
          Real.binEntropy
            ((q ^ 2 + pi * (1 - q ^ 2)) /
              ((q ^ 2 + pi * (1 - q ^ 2)) + (1 - pi + pi * q ^ 2 + q))) - _ = _
    rw [show (q ^ 2 + pi * (1 - q ^ 2)) +
        (1 - pi + pi * q ^ 2 + q) = Q by
      dsimp [Q]
      ring]
  refine ⟨convex_Icc 0 (1 / 2), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hmix : a * x + b * y ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hp_mem : ∀ t ∈ Icc (0 : ℝ) (1 / 2), p t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    dsimp [p]
    constructor
    · exact div_nonneg
        (add_nonneg hq2_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr hq2_le))) hQ.le
    · apply (div_le_one hQ).2
      dsimp [Q]
      nlinarith [ht.2]
  have hp_ne : p x ≠ p y := by
    intro heq
    dsimp [p] at heq
    have hQne := hQ.ne'
    field_simp [hQne] at heq
    have hcoeff : 0 < 1 - q ^ 2 := by nlinarith
    apply hxy
    nlinarith
  have hstrict := Real.strictConcave_binEntropy.2
    (hp_mem x hx) (hp_mem y hy) hp_ne ha hb hab
  dsimp only [smul_eq_mul] at hstrict ⊢
  have hp_mix : a * p x + b * p y = p (a * x + b * y) := by
    dsimp [p]
    field_simp [hQ.ne']
    nlinarith
  rw [hp_mix] at hstrict
  have hscaled :
      Q * (a * Real.binEntropy (p x) + b * Real.binEntropy (p y)) <
        Q * Real.binEntropy (p (a * x + b * y)) :=
    mul_lt_mul_of_pos_left hstrict hQ
  have hone_mix : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
    nlinarith
  calc
    a * edgeReward q x + b * edgeReward q y =
        Q * (a * Real.binEntropy (p x) + b * Real.binEntropy (p y)) -
          4 * ((1 - (a * x + b * y)) * pairEntropy (q ^ 2) (1 + q) +
            (a * x + b * y) * pairEntropy 1 (q ^ 2 + q)) := by
      rw [hnormalize x hx, hnormalize y hy, hone_mix]
      ring
    _ < Q * Real.binEntropy (p (a * x + b * y)) -
          4 * ((1 - (a * x + b * y)) * pairEntropy (q ^ 2) (1 + q) +
            (a * x + b * y) * pairEntropy 1 (q ^ 2 + q)) := by
      linarith
    _ = edgeReward q (a * x + b * y) := by
      rw [hnormalize (a * x + b * y) hmix]

/-- At balanced prior, the edge reward is the balanced-edge scalar reward. -/
theorem edgeReward_half_eq_balancedEdgeScalarReward {q : ℝ} (hq : 0 < q) :
    edgeReward q (1 / 2) = balancedEdgeScalarReward q := by
  unfold edgeReward balancedEdgeScalarReward pairEntropy xLogX
  dsimp
  have hq1 : 0 < 1 + q := by positivity
  have hq2 : 0 < 1 + q ^ 2 := by positivity
  rw [show q ^ 2 + 1 / 2 * (1 - q ^ 2) = (1 + q ^ 2) / 2 by ring,
    show 1 - 1 / 2 + 1 / 2 * q ^ 2 + q = (1 + q) ^ 2 / 2 by ring,
    show (1 + q ^ 2) / 2 + (1 + q) ^ 2 / 2 = 1 + q + q ^ 2 by ring,
    show q ^ 2 + (1 + q) = 1 + q + q ^ 2 by ring,
    show 1 + (q ^ 2 + q) = 1 + q + q ^ 2 by ring,
    show q ^ 2 + q = q * (1 + q) by ring,
    Real.log_div hq2.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (sq_pos_of_pos hq1).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_pow q 2, Real.log_pow (1 + q) 2,
    Real.log_mul hq.ne' hq1.ne']
  simp only [Real.log_one, mul_zero]
  ring

/-- The balanced-prior edge reward is positive on the small interval. -/
theorem edgeReward_half_pos_of_le_nine_hundredths {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 9 / 100) :
    0 < edgeReward q (1 / 2) := by
  have hanti : StrictAntiOn balancedEdgeScalarReward (Icc q (9 / 100 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc q (9 / 100 : ℝ))
    · intro z hz
      exact (hasDerivAt_balancedEdgeScalarReward
        (hq0.trans_le hz.1)).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : z ∈ Icc q (9 / 100 : ℝ) := interior_subset hz
      rw [(hasDerivAt_balancedEdgeScalarReward (hq0.trans_le hz'.1)).deriv]
      exact balancedEdgeDerivative_neg (hq0.trans_le hz'.1) hz'.2
  have hend := (balancedEdgeExactLedger hq0 hq1).2.2
  have hreward : balancedEdgeScalarReward (9 / 100) ≤ balancedEdgeScalarReward q := by
    by_cases hqeq : q = 9 / 100
    · simp [hqeq]
    · exact (hanti ⟨le_rfl, hq1⟩ ⟨hq1, le_rfl⟩
        (lt_of_le_of_ne hq1 hqeq)).le
  rw [edgeReward_half_eq_balancedEdgeScalarReward hq0]
  linarith

/-- In the small-contact regime, nonpositive phase reward forces the prior
below ten times the fourth-power mass. -/
theorem ScalarContactChart.prior_lt_ten_mul_r_of_phaseReward_nonpos
    (C : ScalarContactChart) (hC : C.StrictInterior)
    (hx : C.x ≤ 3 / 10) (hR : C.phaseReward ≤ 0) :
    C.pi < 10 * C.r := by
  by_contra hgate
  have hten : 10 * C.r ≤ C.pi := le_of_not_gt hgate
  have hs_mem : C.s ∈ Icc (2 * C.contactMidpoint) C.y :=
    ⟨hC.2.2.1, hC.2.2.2.1.le⟩
  have hy_mem : C.y ∈ Icc (2 * C.contactMidpoint) C.y :=
    ⟨hC.2.2.1.trans hC.2.2.2.1.le, le_rfl⟩
  have hanti := exposedPhaseReward_strictAntiOn C hC
  have hy_lt_s : exposedPhaseReward C C.y < exposedPhaseReward C C.s :=
    hanti hs_mem hy_mem hC.2.2.2.1
  have hedge_nonpos : edgeReward (C.x ^ 2) C.pi ≤ 0 := by
    rw [← exposedPhaseReward_at_y_eq_edgeReward C]
    rw [exposedPhaseReward_at_contact] at hy_lt_s
    linarith
  have hq0 : 0 < C.x ^ 2 := sq_pos_of_pos C.x_pos
  have hq1 : C.x ^ 2 < 1 := by nlinarith [C.x_pos]
  have hqsmall : C.x ^ 2 ≤ 9 / 100 := by
    nlinarith [mul_self_le_mul_self C.x_pos.le hx]
  have hleft_pos : 0 < edgeReward (C.x ^ 2) (10 * (C.x ^ 2) ^ 2) := by
    have hledger := (smallPriorExactLedger hq0 hqsmall).2.2
    have hcoeff : 0 < (74007309 : ℝ) / 200000000 := by norm_num
    nlinarith
  have hright_pos : 0 < edgeReward (C.x ^ 2) (1 / 2) :=
    edgeReward_half_pos_of_le_nine_hundredths hq0 hqsmall
  have hconc := (strictConcaveOn_edgeReward_prior hq0 hq1).concaveOn
  have hq_sq_le : (C.x ^ 2) ^ 2 ≤ C.x ^ 2 := by nlinarith
  have hleft_le_pi : 10 * (C.x ^ 2) ^ 2 ≤ C.pi := by
    dsimp only [ScalarContactChart.r] at hten
    nlinarith
  have hleft_mem : 10 * (C.x ^ 2) ^ 2 ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨mul_nonneg (by norm_num) (sq_nonneg _), hleft_le_pi.trans C.pi_le_half⟩
  have hright_mem : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by norm_num
  have hpi_mem : C.pi ∈ Icc (10 * (C.x ^ 2) ^ 2) (1 / 2) :=
    ⟨hleft_le_pi, C.pi_le_half⟩
  have hminimum := hconc.min_le_of_mem_Icc hleft_mem hright_mem hpi_mem
  have hmin_pos : 0 < min (edgeReward (C.x ^ 2) (10 * (C.x ^ 2) ^ 2))
      (edgeReward (C.x ^ 2) (1 / 2)) := lt_min hleft_pos hright_pos
  linarith

/-! ## Free-prior capture -/

/-- Replace only the prior coordinate of a scalar contact chart. -/
def ScalarContactChart.withPriorValue (C : ScalarContactChart) (pi : ℝ)
    (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1 / 2) : ScalarContactChart where
  x := C.x
  pi := pi
  lowMass := C.lowMass
  highMass := C.highMass
  x_pos := C.x_pos
  x_le_one := C.x_le_one
  pi_nonneg := hpi0
  pi_le_half := hpi1
  lowMass_nonneg := C.lowMass_nonneg
  lowMass_le_highMass := C.lowMass_le_highMass
  contact := C.contact

/-- Observable-information capture term at free chart coordinates. -/
def captureObservableInfo (x pi : ℝ) : ℝ :=
  pairEntropy (freeLowerMixtureMass x pi) (freeUpperMixtureMass x pi) -
    pairEntropy (x ^ 4) 1

/-- The factor-sixteen capture gap. -/
def sixteenFoldCaptureGap (x pi : ℝ) : ℝ :=
  16 * freeMixingTerm x pi
      (StochasticToDeterministicLatents.Binary.contactMidpoint x) -
    captureObservableInfo x pi

/-- The free-prior odd-log coordinate. -/
def priorOddLogCoordinate (x pi : ℝ) : ℝ :=
  (1 - x ^ 4) * (1 - 2 * pi) / (1 + x ^ 4)

/-- The contact contraction coefficient. -/
def contactContraction (x : ℝ) : ℝ :=
  (1 + x ^ 4) /
    (1 + x ^ 4 +
      2 * StochasticToDeterministicLatents.Binary.contactMidpoint x)

/-- Upper endpoint certificate for the remaining-range product. -/
theorem remainingRangeProduct_one_half_capture :
    Real.log 2 ≤ 16 * remainingRangeProduct (1 / 2) := by
  have hpow : (2 : ℝ) ^ 47 ≤ 3 ^ 32 := by norm_num
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show (2 : ℝ) ^ 47 ∈ Ioi 0 by norm_num)
    (show (3 : ℝ) ^ 32 ∈ Ioi 0 by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have hL : Real.log (81 / 32 : ℝ) = 4 * Real.log 3 - 5 * Real.log 2 := by
    rw [show (81 / 32 : ℝ) = 3 ^ 4 / 2 ^ 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  norm_num [remainingRangeProduct, StochasticToDeterministicLatents.Binary.contactMidpoint,
    remainingLogFactor, contactDenominator]
  rw [hL]
  nlinarith

/-- Lower endpoint certificate for the remaining-range product. -/
theorem remainingRangeProduct_three_tenths_capture :
    Real.log 2 ≤ 16 * remainingRangeProduct (3 / 10) := by
  have hrat : (39 / 4 : ℝ) < 1054729 / 108000 := by norm_num
  have hlogRat := Real.strictMonoOn_log
    (show (39 / 4 : ℝ) ∈ Ioi 0 by norm_num)
    (show (1054729 / 108000 : ℝ) ∈ Ioi 0 by norm_num) hrat
  have hpow : (2 : ℝ) ^ 47 < 39 ^ 9 := by norm_num
  have hlogPow := Real.strictMonoOn_log
    (show (2 : ℝ) ^ 47 ∈ Ioi 0 by norm_num)
    (show (39 : ℝ) ^ 9 ∈ Ioi 0 by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlogPow
  norm_num at hlogPow
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog39 : 9 * Real.log (39 / 4 : ℝ) > 29 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4]
    nlinarith
  norm_num [remainingRangeProduct, StochasticToDeterministicLatents.Binary.contactMidpoint,
    remainingLogFactor, contactDenominator]
  norm_num at hlogRat hlog39 ⊢
  have hL : (29 / 9 : ℝ) * Real.log 2 < Real.log (1054729 / 108000) := by
    linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

/-- At balanced prior, the capture term is at most one bit in natural-log
units. -/
theorem balanced_captureObservableInfo_le_log_two {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    captureObservableInfo x (1 / 2) ≤ Real.log 2 := by
  have hr0 : 0 ≤ x ^ 4 := by positivity
  have hr1 : x ^ 4 ≤ 1 := pow_le_one₀ hx0.le hx1
  have hsuper := pairEntropy_superadditive hr0 hr0
    (by norm_num : (0 : ℝ) ≤ 0) (sub_nonneg.mpr hr1)
  have hrr : pairEntropy (x ^ 4) (x ^ 4) = 2 * x ^ 4 * Real.log 2 := by
    have hrp : 0 < x ^ 4 := by positivity
    rw [pairEntropy_eq_sum_logs hrp hrp]
    have hratio : (x ^ 4 + x ^ 4) / x ^ 4 = 2 := by
      field_simp [hrp.ne']
      norm_num
    rw [hratio]
    ring
  have hzero : pairEntropy 0 (1 - x ^ 4) = 0 := by
    simp [pairEntropy, xLogX]
  have hmid : freeLowerMixtureMass x (1 / 2) = (1 + x ^ 4) / 2 := by
    unfold freeLowerMixtureMass
    ring
  have hell : freeUpperMixtureMass x (1 / 2) = (1 + x ^ 4) / 2 := by
    unfold freeUpperMixtureMass
    ring
  have hmm : pairEntropy ((1 + x ^ 4) / 2) ((1 + x ^ 4) / 2) =
      (1 + x ^ 4) * Real.log 2 := by
    have hm0 : 0 < (1 + x ^ 4) / 2 := by positivity
    rw [pairEntropy_eq_sum_logs hm0 hm0]
    have hratio : (((1 + x ^ 4) / 2) + ((1 + x ^ 4) / 2)) /
        ((1 + x ^ 4) / 2) = 2 := by
      field_simp [hm0.ne']
      norm_num
    rw [hratio]
    ring
  rw [hrr, hzero] at hsuper
  simp only [add_zero] at hsuper
  rw [show x ^ 4 + (1 - x ^ 4) = 1 by ring] at hsuper
  unfold captureObservableInfo
  rw [hmid, hell, hmm]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The factor-sixteen capture gap vanishes at prior zero. -/
theorem sixteenFoldCaptureGap_zero {x : ℝ} : sixteenFoldCaptureGap x 0 = 0 := by
  simp [sixteenFoldCaptureGap, captureObservableInfo, freeMixingTerm,
    freeLowerMixtureMass, freeUpperMixtureMass, pairEntropy, xLogX]

/-- On the upper half of the contact range, the balanced mixture mass obeys
the fourth-power kernel-capture inequality. -/
theorem balanced_cube_le_nine_mul_contactMidpoint_pow_four {x : ℝ}
    (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    ((1 + x ^ 4) / 2) ^ 3 ≤
      (9 * StochasticToDeterministicLatents.Binary.contactMidpoint x) ^ 4 := by
  have hx : 0 ≤ x := by linarith
  have hd : 0 < contactDenominator x := by
    unfold contactDenominator
    nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have hfactor :
      238 * x ^ 3 - 16 * (1 + x + x ^ 2) * (1 + x ^ 4) =
        -2 * (x - 2) * (2 * x - 1) *
          (4 * x ^ 4 + 14 * x ^ 3 + 35 * x ^ 2 + 14 * x + 4) := by
    ring
  have hpoly : 0 ≤ 4 * x ^ 4 + 14 * x ^ 3 + 35 * x ^ 2 + 14 * x + 4 := by
    positivity
  have hxminus : x - 2 ≤ 0 := by linarith
  have htwox : 0 ≤ 2 * x - 1 := by linarith
  have hmain : 16 * contactDenominator x * (1 + x ^ 4) ≤ 238 * x ^ 3 := by
    rw [show contactDenominator x = 1 + x + x ^ 2 by rfl]
    have hfirst : 0 ≤ -2 * (x - 2) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num) hxminus
    have hnonneg : 0 ≤ -2 * (x - 2) * (2 * x - 1) *
        (4 * x ^ 4 + 14 * x ^ 3 + 35 * x ^ 2 + 14 * x + 4) :=
      mul_nonneg (mul_nonneg hfirst htwox) hpoly
    linarith
  let y : ℝ := (1 + x ^ 4) / 2
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy : 17 / 32 ≤ y := by
    dsimp [y]
    nlinarith [sq_nonneg (x ^ 2 - 1 / 4),
      mul_nonneg (sub_nonneg.mpr hx0) (show 0 ≤ x + 1 / 2 by linarith)]
  have hm : (16 / 119 : ℝ) * y ≤
      StochasticToDeterministicLatents.Binary.contactMidpoint x := by
    dsimp [y]
    unfold StochasticToDeterministicLatents.Binary.contactMidpoint
    apply (le_div_iff₀ hd).2
    norm_num at hmain ⊢
    linarith
  have hscaled : (144 / 119 : ℝ) * y ≤
      9 * StochasticToDeterministicLatents.Binary.contactMidpoint x := by
    nlinarith
  have hcoef : (0 : ℝ) ≤ 144 / 119 := by norm_num
  have hpow := pow_le_pow_left₀ (mul_nonneg hcoef hy0) hscaled 4
  have hconstant : (1 : ℝ) ≤ (144 / 119) ^ 4 * y := by
    calc
      (1 : ℝ) ≤ (144 / 119) ^ 4 * (17 / 32) := by norm_num
      _ ≤ (144 / 119) ^ 4 * y :=
        mul_le_mul_of_nonneg_left hy (pow_nonneg hcoef 4)
  calc
    ((1 + x ^ 4) / 2) ^ 3 = y ^ 3 := by rfl
    _ ≤ ((144 / 119) * y) ^ 4 := by
      rw [mul_pow]
      rw [show (144 / 119 : ℝ) ^ 4 * y ^ 4 =
        y ^ 3 * ((144 / 119) ^ 4 * y) by ring]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hconstant (pow_nonneg hy0 3)
    _ ≤ (9 * StochasticToDeterministicLatents.Binary.contactMidpoint x) ^ 4 := hpow

/-- At balanced prior, midpoint mixing dominates the remaining-range tangent
payment. -/
theorem remainingRangeProduct_le_balanced_midpointMixing {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    remainingRangeProduct x ≤
      freeMixingTerm x (1 / 2)
        (StochasticToDeterministicLatents.Binary.contactMidpoint x) := by
  have hxle : x ≤ 1 := hx1.le
  have hd : 0 < contactDenominator x := by
    unfold contactDenominator
    nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have hm0 : 0 < StochasticToDeterministicLatents.Binary.contactMidpoint x := by
    unfold StochasticToDeterministicLatents.Binary.contactMidpoint
    positivity
  let C : ScalarContactChart := {
    x := x
    pi := 1 / 2
    lowMass := StochasticToDeterministicLatents.Binary.contactMidpoint x
    highMass := StochasticToDeterministicLatents.Binary.contactMidpoint x
    x_pos := hx0
    x_le_one := hxle
    pi_nonneg := by norm_num
    pi_le_half := by norm_num
    lowMass_nonneg := hm0.le
    lowMass_le_highMass := le_rfl
    contact := by
      unfold StochasticToDeterministicLatents.Binary.contactMidpoint contactDenominator
      field_simp
      ring }
  have hCpi : C.pi = 1 / 2 := by rfl
  have hCx : C.x = x := by rfl
  have hCm : C.lowMass =
      StochasticToDeterministicLatents.Binary.contactMidpoint x := by rfl
  have hnegconv : ConvexOn ℝ (Ici 0) (fun z => -C.mixingTerm z) :=
    (mixingTerm_concave C).neg
  have hderiv : HasDerivAt (fun z => -C.mixingTerm z)
      (-mixingSlope C (StochasticToDeterministicLatents.Binary.contactMidpoint x))
      (StochasticToDeterministicLatents.Binary.contactMidpoint x) := by
    change HasDerivAt (-C.mixingTerm)
      (-mixingSlope C (StochasticToDeterministicLatents.Binary.contactMidpoint x))
      (StochasticToDeterministicLatents.Binary.contactMidpoint x)
    exact (hasDerivAt_mixingTerm C hm0).neg
  have hslope := hnegconv.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show StochasticToDeterministicLatents.Binary.contactMidpoint x ∈ Ici 0
      by exact hm0.le)
    hm0 hderiv
  have htangent :
      StochasticToDeterministicLatents.Binary.contactMidpoint x *
          mixingSlope C (StochasticToDeterministicLatents.Binary.contactMidpoint x) ≤
        C.mixingTerm (StochasticToDeterministicLatents.Binary.contactMidpoint x) := by
    rw [slope, mixingTerm_zero] at hslope
    simp only [vsub_eq_sub, sub_zero, neg_zero, smul_eq_mul] at hslope
    change (StochasticToDeterministicLatents.Binary.contactMidpoint x)⁻¹ *
        (-C.mixingTerm (StochasticToDeterministicLatents.Binary.contactMidpoint x)) ≤
      -mixingSlope C (StochasticToDeterministicLatents.Binary.contactMidpoint x) at hslope
    rw [← div_eq_inv_mul] at hslope
    have hmul := (div_le_iff₀ hm0).1 hslope
    linarith
  have hbeta :
      mixingSlope C (StochasticToDeterministicLatents.Binary.contactMidpoint x) =
        remainingLogFactor x := by
    rw [mixingSlope_eq_log_product_ratio C hm0]
    unfold remainingLogFactor
    congr 1
    simp only [ScalarContactChart.e, ScalarContactChart.ell,
      ScalarContactChart.r, hCpi, hCx]
    unfold StochasticToDeterministicLatents.Binary.contactMidpoint contactDenominator
    field_simp
    ring
  rw [remainingRangeProduct, ← hbeta]
  rw [freeMixingTerm_eq_mixingTerm C
    (StochasticToDeterministicLatents.Binary.contactMidpoint x)]
  exact htangent

/-- Exact derivative of the free-prior factor-sixteen capture gap. -/
theorem hasDerivAt_sixteenFoldCaptureGap {x pi : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hpi0 : 0 < pi) (hpi1 : pi < 1 / 2) :
    HasDerivAt (sixteenFoldCaptureGap x)
      (2 * (1 - x ^ 4) *
        (15 * atanhLog (priorOddLogCoordinate x pi) -
          16 * atanhLog (contactContraction x * priorOddLogCoordinate x pi))) pi := by
  let r : ℝ := x ^ 4
  let m : ℝ := StochasticToDeterministicLatents.Binary.contactMidpoint x
  let e : ℝ := freeLowerMixtureMass x pi
  let ell : ℝ := freeUpperMixtureMass x pi
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hm0 : 0 < m := by
    dsimp [m, StochasticToDeterministicLatents.Binary.contactMidpoint,
      contactDenominator]
    positivity
  have he0 : 0 < e := by
    dsimp [e, freeLowerMixtureMass, r]
    nlinarith [mul_pos (sub_pos.mpr hpi1) hr0]
  have hell0 : 0 < ell := by
    dsimp [ell, freeUpperMixtureMass, r]
    nlinarith [mul_pos hpi0 hr0]
  have haffE : HasDerivAt (fun p : ℝ => freeLowerMixtureMass x p) (1 - r) pi := by
    have hb := ((hasDerivAt_id pi).mul_const (1 - r)).const_add r
    apply (hb.congr_deriv (by ring)).congr_of_eventuallyEq
      (f₁ := fun p : ℝ => freeLowerMixtureMass x p)
    filter_upwards with p
    unfold freeLowerMixtureMass
    dsimp [r]
    ring
  have haffL : HasDerivAt (fun p : ℝ => freeUpperMixtureMass x p) (-(1 - r)) pi := by
    have hb := ((hasDerivAt_id pi).mul_const (-(1 - r))).const_add 1
    apply (hb.congr_deriv (by ring)).congr_of_eventuallyEq
      (f₁ := fun p : ℝ => freeUpperMixtureMass x p)
    filter_upwards with p
    unfold freeUpperMixtureMass
    dsimp [r]
    ring
  have hphiE := (hasDerivAt_xLogX he0.ne').comp pi haffE
  have hphiL := (hasDerivAt_xLogX hell0.ne').comp pi haffL
  have hME : HasDerivAt (fun p : ℝ => m + freeLowerMixtureMass x p) (1 - r) pi := by
    convert haffE.const_add m using 1
  have hML : HasDerivAt (fun p : ℝ => m + freeUpperMixtureMass x p)
      (-(1 - r)) pi := by
    convert haffL.const_add m using 1
  have hphiME := (hasDerivAt_xLogX (add_pos hm0 he0).ne').comp pi hME
  have hphiML := (hasDerivAt_xLogX (add_pos hm0 hell0).ne').comp pi hML
  have hraw := (((hphiME.sub hphiE).add (hphiML.sub hphiL)).const_mul 16).sub
    (hphiE.neg.add hphiL.neg)
  let c : ℝ := -16 * xLogX (m + r) + 15 * xLogX r -
    16 * xLogX (m + 1) + 15 * xLogX 1
  have hrawFull := hraw.const_add c
  have hgapRaw : HasDerivAt (sixteenFoldCaptureGap x)
      ((1 - r) * (16 * Real.log (m + e) - 15 * Real.log e -
        16 * Real.log (m + ell) + 15 * Real.log ell)) pi := by
    let draw : ℝ := 16 *
        ((Real.log (m + e) + 1) * (1 - r) - (Real.log e + 1) * (1 - r) +
          ((Real.log (m + ell) + 1) * -(1 - r) -
            (Real.log ell + 1) * -(1 - r))) -
        (-((Real.log e + 1) * (1 - r)) +
          -((Real.log ell + 1) * -(1 - r)))
    have hfun : HasDerivAt (sixteenFoldCaptureGap x) draw pi := by
      dsimp [draw]
      apply hrawFull.congr_of_eventuallyEq
      filter_upwards with p
      simp only [sixteenFoldCaptureGap, captureObservableInfo, freeMixingTerm,
        pairEntropy, Function.comp_apply, m, r, c, Pi.sub_apply,
        Pi.add_apply, Pi.neg_apply, freeLowerMixtureMass,
        freeUpperMixtureMass]
      ring_nf
    exact hfun.congr_deriv (by dsimp [draw]; ring)
  apply hgapRaw.congr_deriv
  have hq0 : 0 < priorOddLogCoordinate x pi := by
    unfold priorOddLogCoordinate
    exact div_pos (mul_pos (sub_pos.mpr hr1) (by linarith)) (by positivity)
  have hq1 : priorOddLogCoordinate x pi < 1 := by
    unfold priorOddLogCoordinate
    have hden : 0 < 1 + x ^ 4 := by positivity
    rw [div_lt_one hden]
    nlinarith [mul_pos (sub_pos.mpr hr1) hpi0]
  have hq : (1 + priorOddLogCoordinate x pi) /
      (1 - priorOddLogCoordinate x pi) = ell / e := by
    apply (div_eq_div_iff (sub_pos.mpr hq1).ne' he0.ne').2
    dsimp [priorOddLogCoordinate, ell, e, freeUpperMixtureMass,
      freeLowerMixtureMass]
    field_simp [ne_of_gt (by positivity : 0 < 1 + x ^ 4)]
    ring
  have hk0 : 0 < contactContraction x := by
    unfold contactContraction
    positivity
  have hk1 : contactContraction x < 1 := by
    unfold contactContraction
    apply (div_lt_one (by positivity :
      0 < 1 + x ^ 4 +
        2 * StochasticToDeterministicLatents.Binary.contactMidpoint x)).2
    nlinarith [hm0]
  have hkq1 : contactContraction x * priorOddLogCoordinate x pi < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hk1) hq0,
      mul_pos hk0 (sub_pos.mpr hq1)]
  have hkq : (1 + contactContraction x * priorOddLogCoordinate x pi) /
      (1 - contactContraction x * priorOddLogCoordinate x pi) =
        (m + ell) / (m + e) := by
    apply (div_eq_div_iff (sub_pos.mpr hkq1).ne' (add_pos hm0 he0).ne').2
    dsimp [contactContraction, priorOddLogCoordinate, m, ell, e,
      freeUpperMixtureMass, freeLowerMixtureMass]
    field_simp [ne_of_gt (by positivity : 0 < 1 + x ^ 4),
      ne_of_gt (by positivity :
        0 < 1 + x ^ 4 +
          2 * StochasticToDeterministicLatents.Binary.contactMidpoint x)]
    ring
  rw [atanhLog, atanhLog, hq, hkq,
    Real.log_div hell0.ne' he0.ne',
    Real.log_div (add_pos hm0 hell0).ne' (add_pos hm0 he0).ne']
  ring

/-- The free-prior factor-sixteen capture gap is bounded below by one of its
two endpoint values. -/
theorem sixteenFoldCaptureGap_ge_min_endpoints {x pi : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1 / 2) :
    min (sixteenFoldCaptureGap x 0) (sixteenFoldCaptureGap x (1 / 2)) ≤
      sixteenFoldCaptureGap x pi := by
  rcases hpi0.eq_or_lt with hpi | hpi0
  · subst pi
    exact min_le_left _ _
  rcases hpi1.eq_or_lt with hpi | hpi1
  · subst pi
    exact min_le_right _ _
  let q : ℝ → ℝ := fun p => priorOddLogCoordinate x p
  let k : ℝ := contactContraction x
  let F : ℝ → ℝ := fun p =>
    15 * atanhLog (q p) - 16 * atanhLog (k * q p)
  have hr1 : x ^ 4 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hm0 : 0 < StochasticToDeterministicLatents.Binary.contactMidpoint x := by
    unfold StochasticToDeterministicLatents.Binary.contactMidpoint contactDenominator
    positivity
  have hk0 : 0 < k := by
    dsimp [k, contactContraction]
    exact div_pos (by positivity) (by positivity)
  have hk1 : k < 1 := by
    dsimp [k, contactContraction]
    apply (div_lt_one (by positivity :
      0 < 1 + x ^ 4 +
        2 * StochasticToDeterministicLatents.Binary.contactMidpoint x)).2
    nlinarith
  have hqmem : ∀ {p : ℝ}, 0 ≤ p → p < 1 / 2 → q p ∈ Ioo 0 1 := by
    intro p hp0 hp1
    have hden : 0 < 1 + x ^ 4 := by positivity
    constructor
    · dsimp [q, priorOddLogCoordinate]
      exact div_pos (mul_pos (sub_pos.mpr hr1) (by linarith)) hden
    · dsimp [q, priorOddLogCoordinate]
      rw [div_lt_one hden]
      have hpos : 0 < x ^ 4 + p * (1 - x ^ 4) := by positivity
      nlinarith
  have hqanti : ∀ {a b : ℝ}, a ≤ b → q b ≤ q a := by
    intro a b hab
    dsimp [q, priorOddLogCoordinate]
    have hden : 0 < 1 + x ^ 4 := by positivity
    apply (div_le_div_iff_of_pos_right hden).2
    nlinarith [sub_pos.mpr hr1]
  have hratio := atanhLog_ratio_antitoneOn hk0 hk1
  have hecont : Continuous (fun p : ℝ => freeLowerMixtureMass x p) := by
    unfold freeLowerMixtureMass
    fun_prop
  have hlcont : Continuous (fun p : ℝ => freeUpperMixtureMass x p) := by
    unfold freeUpperMixtureMass
    fun_prop
  have hpair (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun p => pairEntropy (f p) (g p)) :=
    continuous_pairEntropy.comp (hf.prodMk hg)
  have hcont : Continuous (sixteenFoldCaptureGap x) := by
    unfold sixteenFoldCaptureGap captureObservableInfo freeMixingTerm
    exact (((((hpair
      (fun _ => StochasticToDeterministicLatents.Binary.contactMidpoint x)
      (freeLowerMixtureMass x) continuous_const hecont).add
      (hpair (fun _ => StochasticToDeterministicLatents.Binary.contactMidpoint x)
        (freeUpperMixtureMass x) continuous_const hlcont)).sub
      (hpair (fun _ => StochasticToDeterministicLatents.Binary.contactMidpoint x)
        (fun _ => x ^ 4) continuous_const continuous_const)).sub
      (hpair (fun _ => StochasticToDeterministicLatents.Binary.contactMidpoint x)
        (fun _ => 1) continuous_const continuous_const)).const_mul 16).sub
      ((hpair (freeLowerMixtureMass x) (freeUpperMixtureMass x) hecont hlcont).sub
        (hpair (fun _ => x ^ 4) (fun _ => 1) continuous_const continuous_const))
  by_cases hs : 0 ≤ F pi
  · apply le_trans (min_le_left _ _) ?_
    have hmono : MonotoneOn (sixteenFoldCaptureGap x) (Icc 0 pi) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) pi)
      · intro y hy
        exact hcont.continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Ioo (0 : ℝ) pi := by simpa [interior_Icc] using hy
        exact (hasDerivAt_sixteenFoldCaptureGap hx0 hx1 hy'.1
          (hy'.2.trans hpi1)).differentiableAt.differentiableWithinAt
      · intro y hy
        have hy' : y ∈ Ioo (0 : ℝ) pi := by simpa [interior_Icc] using hy
        have hqy := hqmem hy'.1.le (hy'.2.trans hpi1)
        have hqpi : q pi ∈ Ioo 0 1 := hqmem hpi0.le hpi1
        have hApos := atanhLog_pos_on_unitInterval hqpi
        have hcoef : 0 ≤ 15 - 16 * (atanhLog (k * q pi) / atanhLog (q pi)) := by
          have hrewrite : F pi = atanhLog (q pi) *
              (15 - 16 * (atanhLog (k * q pi) / atanhLog (q pi))) := by
            dsimp [F]
            field_simp [hApos.ne']
          rw [hrewrite] at hs
          rw [mul_comm] at hs
          exact nonneg_of_mul_nonneg_left hs hApos
        have hrat := hratio hqpi hqy (hqanti hy'.2.le)
        have hcoefy : 0 ≤
            15 - 16 * (atanhLog (k * q y) / atanhLog (q y)) := by
          linarith
        have hFy : 0 ≤ F y := by
          have hAy := atanhLog_pos_on_unitInterval hqy
          have hrewrite : F y = atanhLog (q y) *
              (15 - 16 * (atanhLog (k * q y) / atanhLog (q y))) := by
            dsimp [F]
            field_simp [hAy.ne']
          rw [hrewrite]
          positivity
        rw [(hasDerivAt_sixteenFoldCaptureGap hx0 hx1 hy'.1
          (hy'.2.trans hpi1)).deriv]
        dsimp [F, q, k] at hFy ⊢
        positivity
    exact hmono ⟨le_rfl, hpi0.le⟩ ⟨hpi0.le, le_rfl⟩ hpi0.le
  · apply le_trans (min_le_right _ _) ?_
    have hs' : F pi < 0 := lt_of_not_ge hs
    have hanti : AntitoneOn (sixteenFoldCaptureGap x) (Icc pi (1 / 2)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc pi (1 / 2 : ℝ))
      · intro y hy
        exact hcont.continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y ∈ Ioo pi (1 / 2 : ℝ) := by simpa [interior_Icc] using hy
        exact (hasDerivAt_sixteenFoldCaptureGap hx0 hx1
          (hpi0.trans hy'.1) hy'.2).differentiableAt.differentiableWithinAt
      · intro y hy
        have hy' : y ∈ Ioo pi (1 / 2 : ℝ) := by simpa [interior_Icc] using hy
        have hqy := hqmem (hpi0.le.trans hy'.1.le) hy'.2
        have hqpi : q pi ∈ Ioo 0 1 := hqmem hpi0.le hpi1
        have hApos := atanhLog_pos_on_unitInterval hqpi
        have hcoef : 15 - 16 * (atanhLog (k * q pi) / atanhLog (q pi)) < 0 := by
          have hrewrite : F pi = atanhLog (q pi) *
              (15 - 16 * (atanhLog (k * q pi) / atanhLog (q pi))) := by
            dsimp [F]
            field_simp [hApos.ne']
          rw [hrewrite] at hs'
          by_contra hc
          exact (not_lt_of_ge (mul_nonneg hApos.le (le_of_not_gt hc))) hs'
        have hrat := hratio hqy hqpi (hqanti hy'.1.le)
        have hcoefy :
            15 - 16 * (atanhLog (k * q y) / atanhLog (q y)) ≤ 0 := by
          linarith
        have hFy : F y ≤ 0 := by
          have hAy := atanhLog_pos_on_unitInterval hqy
          have hrewrite : F y = atanhLog (q y) *
              (15 - 16 * (atanhLog (k * q y) / atanhLog (q y))) := by
            dsimp [F]
            field_simp [hAy.ne']
          rw [hrewrite]
          exact mul_nonpos_of_nonneg_of_nonpos hAy.le hcoefy
        rw [(hasDerivAt_sixteenFoldCaptureGap hx0 hx1
          (hpi0.trans hy'.1) hy'.2).deriv]
        dsimp [F, q, k] at hFy ⊢
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hFy
    exact hanti ⟨le_rfl, hpi1.le⟩ ⟨hpi1.le, le_rfl⟩ hpi1.le

/-! ## Sixteen-fold midpoint capture -/

/-- In the small-contact, small-prior regime, observable information is
captured by sixteen midpoint mixing terms. -/
theorem ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_contact_le
    (C : ScalarContactChart) (hC : C.StrictInterior)
    (hx : C.x ≤ 3 / 10) (hpi : C.pi ≤ 10 * C.r) :
    C.observableInfo ≤
      16 * C.mixingTerm (StochasticToDeterministicLatents.Binary.contactMidpoint C.x) := by
  have hx0 : 0 < C.x := C.x_pos
  have hx1 : C.x < 1 := hC.1
  have hm0 : 0 < StochasticToDeterministicLatents.Binary.contactMidpoint C.x :=
    C.contactMidpoint_pos
  rw [observableInfo_eq_integral_kernel C,
    mixingTerm_eq_integral_kernel C hm0.le]
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with c hc
    exact mixingKernelTotal_nonnegative C hc.1.le
  · exact (mixingKernelBelow_integrableInMixingParameter C hm0.le).const_mul 16
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with c hc
    let f : ℝ → ℝ := fun theta => theta * (1 - theta) * (1 - C.r) ^ 2
    have hcont : ContinuousOn f (Icc 0 C.pi) := by
      dsimp [f]
      fun_prop
    have hcI : c ∈ Icc (f 0) (f C.pi) := by
      dsimp [f]
      rw [← mixingGap_eq_prior_factorization C]
      constructor
      · simpa [f] using hc.1.le
      · simpa [f] using hc.2
    obtain ⟨theta, htheta, hctheta⟩ :=
      intermediate_value_Icc C.pi_nonneg hcont hcI
    let e : ℝ := C.r + theta * (1 - C.r)
    let ell : ℝ := 1 - theta * (1 - C.r)
    have htheta_pi : theta ≤ C.pi := htheta.2
    have htheta0 : 0 ≤ theta := htheta.1
    have htheta_half : theta ≤ 1 / 2 := htheta_pi.trans C.pi_le_half
    have hr0 : 0 < C.r := C.r_pos
    have hr1 : C.r ≤ 1 := by
      unfold ScalarContactChart.r
      exact pow_le_one₀ C.x_pos.le C.x_le_one
    have he0 : 0 < e := by dsimp [e]; nlinarith
    have heel : e ≤ ell := by dsimp [e, ell]; nlinarith
    have he11 : e ≤ 11 * C.r := by dsimp [e]; nlinarith
    have hell1 : ell ≤ 1 := by dsimp [ell]; nlinarith
    have hd34 : 1 + C.x + C.x ^ 2 ≤ 7 / 5 := by
      nlinarith [sq_nonneg C.x]
    have hden0 : 0 < 1 + C.x + C.x ^ 2 := by
      nlinarith [sq_nonneg C.x]
    have hm : C.contactMidpoint = C.x ^ 3 / (1 + C.x + C.x ^ 2) := rfl
    have hmargin := fourthPowerCapture_integer_margin
    have hpow : e ^ 3 * ell ≤ (9 * C.contactMidpoint) ^ 4 := by
      have hepow : e ^ 3 ≤ (11 * C.r) ^ 3 :=
        pow_le_pow_left₀ he0.le he11 3
      have hleft : e ^ 3 * ell ≤ (11 * C.r) ^ 3 := by
        calc
          e ^ 3 * ell ≤ (11 * C.r) ^ 3 * ell :=
            mul_le_mul_of_nonneg_right hepow (by dsimp [ell]; nlinarith)
          _ ≤ (11 * C.r) ^ 3 * 1 :=
            mul_le_mul_of_nonneg_left hell1 (pow_nonneg (by positivity) 3)
          _ = (11 * C.r) ^ 3 := by ring
      rw [ScalarContactChart.r] at hleft
      rw [hm]
      have hdenpow : (1 + C.x + C.x ^ 2) ^ 4 ≤ (7 / 5 : ℝ) ^ 4 :=
        pow_le_pow_left₀ hden0.le hd34 4
      have hxpow : 0 < C.x ^ 12 := by positivity
      apply le_trans hleft
      have hfrac : (9 * (C.x ^ 3 / (1 + C.x + C.x ^ 2))) ^ 4 =
          6561 * C.x ^ 12 / (1 + C.x + C.x ^ 2) ^ 4 := by
        field_simp [hden0.ne']
        ring
      rw [show (11 * C.x ^ 4) ^ 3 = 1331 * C.x ^ 12 by ring, hfrac]
      apply (le_div_iff₀ (pow_pos hden0 4)).2
      have hcoef : (1331 : ℝ) * (7 / 5) ^ 4 < 6561 := by
        norm_num at hmargin ⊢
      nlinarith [mul_le_mul_of_nonneg_left hdenpow
        (show (0 : ℝ) ≤ 1331 by norm_num)]
    have hden : ∀ t : ℝ,
        (t + C.r) * (t + 1) + c = (t + e) * (t + ell) := by
      intro t
      dsimp [e, ell]
      rw [hctheta.symm]
      dsimp [f]
      ring
    have hcap := integral_rationalKernel_le_sixteen_mul_integral he0 heel hm0 hpow
    simpa only [mixingKernelTotal, mixingKernelBelow, hden] using hcap

private theorem balanced_capture_of_half_le_contact (C : ScalarContactChart)
    (hx : 1 / 2 ≤ C.x) (hx1 : C.x < 1) :
    captureObservableInfo C.x (1 / 2) ≤
      16 * freeMixingTerm C.x (1 / 2)
        (StochasticToDeterministicLatents.Binary.contactMidpoint C.x) := by
  let Cp := C.withPriorValue (1 / 2) (by norm_num) (by norm_num)
  have hm0 : 0 < StochasticToDeterministicLatents.Binary.contactMidpoint C.x := by
    unfold StochasticToDeterministicLatents.Binary.contactMidpoint contactDenominator
    positivity
  have hk : captureObservableInfo C.x (1 / 2) = Cp.observableInfo := by
    rfl
  have hb : freeMixingTerm C.x (1 / 2)
      (StochasticToDeterministicLatents.Binary.contactMidpoint C.x) =
        Cp.mixingTerm (StochasticToDeterministicLatents.Binary.contactMidpoint C.x) := by
    rfl
  rw [hk, hb, observableInfo_eq_integral_kernel Cp,
    mixingTerm_eq_integral_kernel Cp hm0.le]
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with c hc
    exact mixingKernelTotal_nonnegative Cp hc.1.le
  · exact (mixingKernelBelow_integrableInMixingParameter Cp hm0.le).const_mul 16
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with c hc
    let f : ℝ → ℝ := fun theta => theta * (1 - theta) * (1 - Cp.r) ^ 2
    have hcont : ContinuousOn f (Icc 0 (1 / 2)) := by
      dsimp [f]
      fun_prop
    have hcI : c ∈ Icc (f 0) (f (1 / 2)) := by
      constructor
      · simpa [f] using hc.1.le
      · have hmix : f (1 / 2) = mixingGap Cp := by
          rw [mixingGap_eq_prior_factorization]
          rfl
        rw [hmix]
        exact hc.2
    obtain ⟨theta, htheta, hctheta⟩ :=
      intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hcont hcI
    let e : ℝ := Cp.r + theta * (1 - Cp.r)
    let ell : ℝ := 1 - theta * (1 - Cp.r)
    let y : ℝ := (1 + C.x ^ 4) / 2
    have hr0 : 0 < Cp.r := Cp.r_pos
    have hr1 : Cp.r ≤ 1 := by
      unfold ScalarContactChart.r
      exact pow_le_one₀ Cp.x_pos.le Cp.x_le_one
    have he0 : 0 < e := by dsimp [e]; nlinarith [htheta.1]
    have heel : e ≤ ell := by dsimp [e, ell]; nlinarith [htheta.2]
    have hell0 : 0 ≤ ell := he0.le.trans heel
    have hell1 : ell ≤ 1 := by dsimp [ell]; nlinarith [htheta.1]
    have hey : e ≤ y := by
      change C.x ^ 4 + theta * (1 - C.x ^ 4) ≤ (1 + C.x ^ 4) / 2
      have hrC : C.x ^ 4 ≤ 1 := pow_le_one₀ C.x_pos.le C.x_le_one
      nlinarith [mul_nonneg (sub_nonneg.mpr htheta.2) (sub_nonneg.mpr hrC)]
    have hy0 : 0 ≤ y := by dsimp [y]; positivity
    have hepow : e ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ he0.le hey 3
    have hpre : e ^ 3 * ell ≤ y ^ 3 := by
      calc
        e ^ 3 * ell ≤ y ^ 3 * ell := mul_le_mul_of_nonneg_right hepow hell0
        _ ≤ y ^ 3 * 1 := mul_le_mul_of_nonneg_left hell1 (pow_nonneg hy0 3)
        _ = y ^ 3 := by ring
    have hpow : e ^ 3 * ell ≤
        (9 * StochasticToDeterministicLatents.Binary.contactMidpoint C.x) ^ 4 :=
      hpre.trans (balanced_cube_le_nine_mul_contactMidpoint_pow_four hx C.x_le_one)
    have hden : ∀ t : ℝ,
        (t + Cp.r) * (t + 1) + c = (t + e) * (t + ell) := by
      intro t
      dsimp [e, ell]
      rw [hctheta.symm]
      dsimp [f]
      ring
    have hcap := integral_rationalKernel_le_sixteen_mul_integral he0 heel hm0 hpow
    simpa only [mixingKernelTotal, mixingKernelBelow, hden] using hcap

/-- Above the three-tenths split, observable information is captured by
sixteen midpoint mixing terms for every prior. -/
theorem ScalarContactChart.observableInfo_le_sixteen_mul_midpointMixing_of_le_contact
    (C : ScalarContactChart) (hC : C.StrictInterior) (hx : 3 / 10 ≤ C.x) :
    C.observableInfo ≤
      16 * C.mixingTerm (StochasticToDeterministicLatents.Binary.contactMidpoint C.x) := by
  have hx0 : 0 < C.x := C.x_pos
  have hx1 : C.x < 1 := hC.1
  have hgapMin := sixteenFoldCaptureGap_ge_min_endpoints
    hx0 hx1 C.pi_nonneg C.pi_le_half
  have hgap0 : sixteenFoldCaptureGap C.x 0 = 0 := sixteenFoldCaptureGap_zero
  have hbalanced : 0 ≤ sixteenFoldCaptureGap C.x (1 / 2) := by
    by_cases hhalf : C.x ≤ 1 / 2
    · have hproduct := remainingRangeProduct_ge_min_endpoints hx hhalf
      have hlog : Real.log 2 ≤ 16 * remainingRangeProduct C.x := by
        have hlow := remainingRangeProduct_three_tenths_capture
        have hhigh := remainingRangeProduct_one_half_capture
        rcases le_total (remainingRangeProduct (3 / 10))
            (remainingRangeProduct (1 / 2)) with hle | hle
        · rw [min_eq_left hle] at hproduct
          linarith
        · rw [min_eq_right hle] at hproduct
          linarith
      have hk := balanced_captureObservableInfo_le_log_two hx0 C.x_le_one
      have hb := remainingRangeProduct_le_balanced_midpointMixing hx0 hx1
      unfold sixteenFoldCaptureGap
      linarith
    · have hlarge : 1 / 2 ≤ C.x := le_of_not_ge hhalf
      exact sub_nonneg.mpr (balanced_capture_of_half_le_contact C hlarge hx1)
  rw [hgap0, min_eq_left hbalanced] at hgapMin
  have hgap : 0 ≤ sixteenFoldCaptureGap C.x C.pi := hgapMin
  unfold sixteenFoldCaptureGap captureObservableInfo at hgap
  rw [freeLowerMixtureMass_eq_e C, freeUpperMixtureMass_eq_ell C,
    freeMixingTerm_eq_mixingTerm C] at hgap
  change C.observableInfo ≤
    16 * C.mixingTerm
      (StochasticToDeterministicLatents.Binary.contactMidpoint C.x)
  exact sub_nonneg.mp hgap

/-! ## Nonpositive-phase assembly -/

/-- On a strict scalar contact chart with nonpositive phase reward, observable
information is at most eight times the mixing sum. -/
theorem ScalarContactChart.observableInfo_le_eight_mul_mixingSum_of_phaseReward_nonpos
    (C : ScalarContactChart)
    (hC : C.StrictInterior)
    (hR : C.phaseReward ≤ 0) :
    C.observableInfo ≤ 8 * C.mixingSum := by
  have hcapture : C.observableInfo ≤
      16 * C.mixingTerm
        (StochasticToDeterministicLatents.Binary.contactMidpoint C.x) := by
    by_cases hx : C.x ≤ 3 / 10
    · exact C.observableInfo_le_sixteen_mul_midpointMixing_of_contact_le hC hx
        (le_of_lt (C.prior_lt_ten_mul_r_of_phaseReward_nonpos hC hx hR))
    · exact C.observableInfo_le_sixteen_mul_midpointMixing_of_le_contact hC
        (le_of_not_ge hx)
  have hfibre := C.two_mul_midpointMixing_le_mixingSum hC
  linarith

end

end StochasticToDeterministicLatents.Binary
