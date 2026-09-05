import StochasticToDeterministicLatents.Binary.FactorNine.PositivePhase

/-!
# The two seam endpoints of the positive phase

Each proof reduces positivity to a scalar function that decreases on
`(0, 2/5]` and has a positive rational margin at `2/5`. This discharges the
seam hypotheses of the positive-phase argument. The analytic estimates use
natural logarithms; their terminal consequences give the scalar arm and the
cost bound for a supplied strict contact chart.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

open scoped BigOperators Topology

namespace StochasticToDeterministicLatents.Binary

noncomputable section

open Set Filter MeasureTheory

/-! ## Balanced seam: the midpoint payment -/

theorem mixingTerm_eq_integral_mixingSlope (C : ScalarContactChart) {z : ℝ} (hz : 0 ≤ z) :
    ScalarContactChart.mixingTerm C z = ∫ t in Ioc 0 z, mixingSlope C t := by
  rw [← intervalIntegral.integral_of_le hz]
  have hi : IntervalIntegrable (mixingSlope C) volume 0 z := by
    rw [intervalIntegrable_iff, uIoc_of_le hz]
    exact (integrableOn_mixingSlope_Ioi C).mono_set Ioc_subset_Ioi_self
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz
    (continuous_mixingTerm C).continuousOn
    (fun t ht => hasDerivAt_mixingTerm C ht.1) hi
  simpa using h.symm

theorem bridgeDerivative_at_balancedMidpoint {x : ℝ} (hx : 0 < x) :
    bridgeDerivative x (1 / 2) (contactMidpoint x) = remainingLogFactor x := by
  have hd : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1 / 2)]
  have hx3 : x ^ 3 ≠ 0 := (pow_pos hx 3).ne'
  have h1x3 : 1 + x ^ 3 ≠ 0 := by positivity
  unfold bridgeDerivative contactMidpoint contactDenominator remainingLogFactor
  rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = 1 / 4 by norm_num]
  congr 1
  field_simp [hd.ne', hx.ne', hx3, h1x3]
  ring

theorem fourthPower_div_contactMidpoint {x : ℝ} (hx : 0 < x) :
    x ^ 4 / contactMidpoint x = x + x ^ 2 + x ^ 3 := by
  have hd : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1 / 2)]
  unfold contactMidpoint contactDenominator
  field_simp [hd.ne', hx.ne']

theorem two_mul_contactMidpoint_div_fourthPower {x : ℝ} (hx : 0 < x) :
    (2 * contactMidpoint x) / x ^ 4 = 2 / (x * (1 + x + x ^ 2)) := by
  have hd : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1 / 2)]
  unfold contactMidpoint contactDenominator
  field_simp [hd.ne', hx.ne']

theorem seamNorm_div_contactMidpoint_eq_exp_remainingLogFactor {x : ℝ} (hx : 0 < x) :
    (1 + x ^ 4 + 2 * contactMidpoint x) / contactMidpoint x =
      Real.exp (remainingLogFactor x) * (4 * (1 + x) * (1 + x ^ 2) / (1 + x ^ 3)) := by
  have hd : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1 / 2)]
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have h1x3 : 0 < 1 + x ^ 3 := by positivity
  have hexp : Real.exp (remainingLogFactor x) = (1 + x ^ 3) ^ 2 / (4 * x ^ 3) := by
    unfold remainingLogFactor
    rw [Real.exp_log]
    positivity
  rw [hexp]
  unfold contactMidpoint contactDenominator
  field_simp [hd.ne', hx3.ne', h1x3.ne']
  ring

private def balancedSeamChart (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) : ScalarContactChart where
  x := x
  pi := 1 / 2
  lowMass := contactMidpoint x
  highMass := contactMidpoint x
  x_pos := hx0
  x_le_one := by linarith
  pi_nonneg := by norm_num
  pi_le_half := by norm_num
  lowMass_nonneg := by unfold contactMidpoint contactDenominator; positivity
  lowMass_le_highMass := le_rfl
  contact := by
    have hd : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1 / 2)]
    unfold contactMidpoint contactDenominator
    field_simp [hd.ne']
    ring

private theorem mixingSlope_balancedSeamChart (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) {z : ℝ}
    (hz : 0 < z) : mixingSlope (balancedSeamChart x hx0 hx1) z = bridgeDerivative x (1 / 2) z := by
  rw [mixingSlope_eq_log_product_ratio _ hz, mixing_product_ratio_eq_one_add _ hz, mixingGap_eq_prior_factorization]
  rfl

theorem bridge_ge_midpoint_payment_at_balancedSeam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    2 * contactMidpoint x * bridgeDerivative x (1 / 2) (contactMidpoint x) ≤
      freeMixingTerm x (1 / 2) (2 * contactMidpoint x) := by
  let C := balancedSeamChart x hx0 hx1
  let s : ℝ := 2 * contactMidpoint x
  let μ : Measure ℝ := volume.restrict (Ioc 0 s)
  have hm : 0 < contactMidpoint x := by unfold contactMidpoint contactDenominator; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hμ : μ (Set.univ) = ENNReal.ofReal s := by
    simp [μ, Real.volume_Ioc, hs.le]
  letI : MeasureTheory.IsFiniteMeasure μ := MeasureTheory.IsFiniteMeasure.mk (by rw [hμ]; exact ENNReal.ofReal_lt_top)
  have hμ0 : μ ≠ 0 := by
    intro hz
    have := congrArg (fun ν : Measure ℝ => ν Set.univ) hz
    rw [hμ] at this
    exact (not_le_of_gt hs) (by simpa [ENNReal.ofReal_eq_zero] using this)
  letI : NeZero μ := ⟨hμ0⟩
  let k : ℝ → ℝ := fun z => Real.log (1 + mixingGap C / ((z + C.r) * (z + 1)))
  have hconv : ConvexOn ℝ (Ici 0) k := mixingSlopeKernel_convex C
  have hcont : ContinuousOn k (Ici 0) := by
    intro z hz
    have hzr : 0 < z + C.r := add_pos_of_nonneg_of_pos hz C.r_pos
    have hz1 : 0 < z + 1 := add_pos_of_nonneg_of_pos hz (by norm_num)
    apply ContinuousAt.continuousWithinAt
    dsimp [k]
    have hden : 0 < (z + C.r) * (z + 1) := mul_pos hzr hz1
    have harg : 0 < 1 + mixingGap C / ((z + C.r) * (z + 1)) := by
      have := mixingGap_nonnegative C
      positivity
    exact (Real.continuousAt_log harg.ne').comp_of_eq
      (continuousAt_const.add
        ((continuousAt_const.div
          ((continuousAt_id.add continuousAt_const).mul
            (continuousAt_id.add continuousAt_const)) hden.ne')))
      rfl
  have hIocIcc : Ioc 0 s ⊆ Icc 0 s := fun z hz => ⟨hz.1.le, hz.2⟩
  have hIccIci : Icc 0 s ⊆ Ici 0 := fun z hz => hz.1
  have hid : Integrable id μ :=
    continuousOn_id.integrableOn_Icc.mono_set hIocIcc
  have hk : Integrable (k ∘ id) μ := by
    change IntegrableOn (k ∘ id) (Ioc 0 s)
    exact ((hcont.mono hIccIci).comp continuousOn_id (fun z hz => hz)).integrableOn_Icc.mono_set hIocIcc
  have hj := hconv.map_average_le hcont isClosed_Ici
    (μ := μ) (f := id)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz; exact hz.1.le)
    hid hk
  have havg : (⨍ z, id z ∂μ) = contactMidpoint x := by
    rw [MeasureTheory.average, hμ, integral_smul_measure, ENNReal.toReal_inv]
    dsimp [μ]
    change (ENNReal.ofReal s).toReal⁻¹ • (∫ z in Ioc 0 s, id z) = contactMidpoint x
    rw [ENNReal.toReal_ofReal hs.le]
    change s⁻¹ * (∫ z in Ioc 0 s, id z) = contactMidpoint x
    simp only [id_eq]
    rw [← intervalIntegral.integral_of_le hs.le, integral_id]
    dsimp [s]
    field_simp [hm.ne']
    ring
  rw [havg] at hj
  have hk_mid : k (contactMidpoint x) = bridgeDerivative x (1 / 2) (contactMidpoint x) := by
    have hb := mixingSlope_balancedSeamChart x hx0 hx1 hm
    rw [mixingSlope_eq_log_product_ratio C hm, mixing_product_ratio_eq_one_add C hm] at hb
    exact hb
  have hint_congr : (∫ z in Ioc 0 s, k z) =
      ∫ z in Ioc 0 s, bridgeDerivative x (1 / 2) z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hb := mixingSlope_balancedSeamChart x hx0 hx1 hz.1
    rw [mixingSlope_eq_log_product_ratio C hz.1, mixing_product_ratio_eq_one_add C hz.1] at hb
    exact hb
  have hj' : bridgeDerivative x (1 / 2) (contactMidpoint x) ≤
      s⁻¹ * ∫ z in Ioc 0 s, bridgeDerivative x (1 / 2) z := by
    rw [MeasureTheory.average, hμ, integral_smul_measure, ENNReal.toReal_inv] at hj
    dsimp [μ] at hj
    change k (contactMidpoint x) ≤ (ENNReal.ofReal s).toReal⁻¹ •
      (∫ z in Ioc 0 s, k z) at hj
    rw [ENNReal.toReal_ofReal hs.le] at hj
    change k (contactMidpoint x) ≤ s⁻¹ * ∫ z in Ioc 0 s, k z at hj
    simpa only [hk_mid, hint_congr] using hj
  rw [show freeMixingTerm x (1 / 2) s = ScalarContactChart.mixingTerm C s by
    simpa [C, balancedSeamChart] using (freeMixingTerm_eq_mixingTerm C s),
    mixingTerm_eq_integral_mixingSlope C hs.le]
  have hmul := mul_le_mul_of_nonneg_left hj' hs.le
  have hcancel : s * (s⁻¹ * ∫ z in Ioc 0 s, bridgeDerivative x (1 / 2) z) =
      ∫ z in Ioc 0 s, bridgeDerivative x (1 / 2) z := by field_simp [hs.ne']
  rw [hcancel] at hmul
  have hint_beta : (∫ z in Ioc 0 s, mixingSlope C z) =
      ∫ z in Ioc 0 s, bridgeDerivative x (1 / 2) z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact mixingSlope_balancedSeamChart x hx0 hx1 hz.1
  rw [hint_beta]
  simpa [s] using hmul

/-! ## Balanced seam: the entropy bound -/

/-- The fourth-power mass divided by the contact midpoint. -/
def balancedSeamMassRatio (x : ℝ) : ℝ := x + x ^ 2 + x ^ 3

/-- The normalized factor in the balanced-seam entropy estimate. -/
def balancedSeamNormFactor (x : ℝ) : ℝ := 4 * (1 + x) * (1 + x ^ 2) / (1 + x ^ 3)

/-- The equal-mass contact width divided by the fourth-power mass. -/
def seamWidthRatio (x : ℝ) : ℝ := 2 / (x * (1 + x + x ^ 2))

/-- A natural-log entropy envelope at balanced prior. -/
def balancedSeamEntropyEnvelope (x : ℝ) : ℝ :=
  let r := x ^ 4
  let s := 2 * contactMidpoint x
  let Q := 1 + r + s
  (1 / 2) * (1 + Real.log (Q / r)) +
    ((1 + seamWidthRatio x) / 2) * (1 + Real.log (Q / (r + s)))

theorem highArmEntropy_le_at_balancedSeam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    highArmEntropy x (1 / 2) (2 * contactMidpoint x) ≤ x ^ 4 * balancedSeamEntropyEnvelope x := by
  let r : ℝ := x ^ 4
  let s : ℝ := 2 * contactMidpoint x
  let q : ℝ := r + s
  let Q : ℝ := 1 + q
  rw [highArmEntropy, pairEntropy_comm 1 (x ^ 4 + 2 * contactMidpoint x)]
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s, contactMidpoint, contactDenominator]; positivity
  have hq : 0 < q := add_pos hr hs
  have hleft := pairEntropy_le_left_log hr (show 0 ≤ 1 + s by positivity)
  have hright := pairEntropy_le_left_log hq (show 0 ≤ (1 : ℝ) by norm_num)
  have hleft' := mul_le_mul_of_nonneg_left hleft (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hright' := mul_le_mul_of_nonneg_left hright (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hQ1 : r + (1 + s) = Q := by dsimp [Q, q]; ring
  have hQ2 : q + 1 = Q := by dsimp [Q]; ring
  rw [hQ1] at hleft'
  rw [hQ2] at hright'
  have ht : s / r = seamWidthRatio x := by
    simpa [s, r, seamWidthRatio] using two_mul_contactMidpoint_div_fourthPower (x := x) hx0
  change (1 - 1 / 2) * pairEntropy (x ^ 4) (1 + 2 * contactMidpoint x) +
    (1 / 2) * pairEntropy (x ^ 4 + 2 * contactMidpoint x) 1 ≤ x ^ 4 * balancedSeamEntropyEnvelope x
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
  calc
    (1 / 2) * pairEntropy (x ^ 4) (1 + 2 * contactMidpoint x) +
        (1 / 2) * pairEntropy (x ^ 4 + 2 * contactMidpoint x) 1 ≤
        (1 / 2) * (r * (1 + Real.log (Q / r))) +
          (1 / 2) * (q * (1 + Real.log (Q / q))) := by
      convert add_le_add hleft' hright' using 1 <;> dsimp [r, s, q, Q] <;> norm_num
    _ = x ^ 4 * balancedSeamEntropyEnvelope x := by
      unfold balancedSeamEntropyEnvelope
      dsimp [r, s, q, Q] at ht ⊢
      rw [← ht]
      field_simp [hr.ne']
      ring_nf

theorem balancedSeamEntropyEnvelope_identity {x : ℝ} (hx0 : 0 < x) :
    (5 / 2 : ℝ) * (2 * contactMidpoint x * remainingLogFactor x) - x ^ 4 * balancedSeamEntropyEnvelope x =
      contactMidpoint x * (balancedSeamScalar x + remainingLogFactor x) := by
  have hm : 0 < contactMidpoint x := by unfold contactMidpoint contactDenominator; positivity
  have hr : 0 < x ^ 4 := by positivity
  have ha : 0 < balancedSeamMassRatio x := by unfold balancedSeamMassRatio; positivity
  have hap : 0 < balancedSeamMassRatio x + 2 := by positivity
  have hh : 0 < balancedSeamNormFactor x := by unfold balancedSeamNormFactor; positivity
  have hQ : 0 < 1 + x ^ 4 + 2 * contactMidpoint x := by positivity
  have hra := fourthPower_div_contactMidpoint (x := x) hx0
  have hsm := two_mul_contactMidpoint_div_fourthPower (x := x) hx0
  have hprod := seamNorm_div_contactMidpoint_eq_exp_remainingLogFactor (x := x) hx0
  have hra' : x ^ 4 / contactMidpoint x = balancedSeamMassRatio x := by simpa [balancedSeamMassRatio] using hra
  have hsm' : (2 * contactMidpoint x) / x ^ 4 = seamWidthRatio x := by simpa [seamWidthRatio] using hsm
  have hprod' : (1 + x ^ 4 + 2 * contactMidpoint x) / contactMidpoint x = Real.exp (remainingLogFactor x) * balancedSeamNormFactor x := by
    simpa [balancedSeamNormFactor] using hprod
  have hQr : (1 + x ^ 4 + 2 * contactMidpoint x) / x ^ 4 =
      (Real.exp (remainingLogFactor x) * balancedSeamNormFactor x) / balancedSeamMassRatio x := by
    rw [← hprod', ← hra']
    field_simp [hm.ne', hr.ne']
  have hQq : (1 + x ^ 4 + 2 * contactMidpoint x) / (x ^ 4 + 2 * contactMidpoint x) =
      (Real.exp (remainingLogFactor x) * balancedSeamNormFactor x) / (balancedSeamMassRatio x + 2) := by
    rw [← hprod', ← hra']
    field_simp [hm.ne', hr.ne']
  have hlogQr : Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / x ^ 4) =
      remainingLogFactor x + Real.log (balancedSeamNormFactor x) - Real.log (balancedSeamMassRatio x) := by
    rw [hQr, Real.log_div (mul_pos (Real.exp_pos _) hh).ne' ha.ne',
      Real.log_mul (Real.exp_pos _).ne' hh.ne', Real.log_exp]
  have hlogQq : Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / (x ^ 4 + 2 * contactMidpoint x)) =
      remainingLogFactor x + Real.log (balancedSeamNormFactor x) - Real.log (balancedSeamMassRatio x + 2) := by
    rw [hQq, Real.log_div (mul_pos (Real.exp_pos _) hh).ne' hap.ne',
      Real.log_mul (Real.exp_pos _).ne' hh.ne', Real.log_exp]
  have hg : balancedSeamScalar x =
      (3 - balancedSeamMassRatio x) * remainingLogFactor x -
        (1 + balancedSeamMassRatio x) * (1 + Real.log (balancedSeamNormFactor x)) +
        (1 / 2) * (balancedSeamMassRatio x * Real.log (balancedSeamMassRatio x) +
          (balancedSeamMassRatio x + 2) * Real.log (balancedSeamMassRatio x + 2)) := by
    unfold balancedSeamScalar balancedSeamMassRatio balancedSeamNormFactor remainingLogFactor
    rfl
  rw [hg]
  unfold balancedSeamEntropyEnvelope
  dsimp
  rw [hlogQr, hlogQq]
  have htalpha : seamWidthRatio x * balancedSeamMassRatio x = 2 := by
    unfold seamWidthRatio balancedSeamMassRatio
    field_simp [hx0.ne']
  have hmalpha : contactMidpoint x * balancedSeamMassRatio x = x ^ 4 := by
    apply (div_eq_iff hm.ne').mp at hra'
    nlinarith
  have htdiv : seamWidthRatio x = 2 / balancedSeamMassRatio x := by
    apply (eq_div_iff ha.ne').2
    nlinarith [htalpha]
  rw [← hmalpha, htdiv]
  field_simp [ha.ne']
  ring

theorem proxy_ge_at_balancedSeam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    strictProxy x (1 / 2) (2 * contactMidpoint x) ≥ contactMidpoint x * (balancedSeamScalar x + remainingLogFactor x) := by
  have hp := bridge_ge_midpoint_payment_at_balancedSeam hx0 hx1
  rw [bridgeDerivative_at_balancedMidpoint hx0] at hp
  have hA := highArmEntropy_le_at_balancedSeam hx0 hx1
  have hid := balancedSeamEntropyEnvelope_identity hx0
  unfold strictProxy
  nlinarith

/-! ## Balanced seam: monotonicity and its rational endpoint -/

theorem balancedSeamScalar_eq (x : ℝ) : balancedSeamScalar x =
    (3 - (x + x^2 + x^3)) * Real.log ((1 + x^3)^2 / (4*x^3)) -
      (1 + (x + x^2 + x^3)) * (1 + Real.log (4*(1+x)*(1+x^2)/(1+x^3))) +
      (1/2) * ((x + x^2 + x^3) * Real.log (x + x^2 + x^3) +
        ((x + x^2 + x^3) + 2) * Real.log ((x + x^2 + x^3) + 2)) := rfl

/-- The derivative of the scalar controlling the balanced seam. -/
def balancedSeamScalarDerivative (x : ℝ) : ℝ :=
      ((-(1 + 2*x + 3*x^2)) * remainingLogFactor x +
          (3 - (x + x^2 + x^3)) * (-3 * (1-x^3)/(x*(1+x^3)))) -
        ((1 + 2*x + 3*x^2) * (1 + Real.log (4*(1+x)*(1+x^2)/(1+x^3))) +
          (1 + (x+x^2+x^3)) *
            ((1-x^2)/((1+x^2)*(1-x+x^2)))) +
        (1/2) * ((1 + 2*x + 3*x^2) * (Real.log (x+x^2+x^3) + 1) +
          (1 + 2*x + 3*x^2) * (Real.log ((x+x^2+x^3)+2) + 1))

theorem hasDerivAt_balancedSeamScalar {x : ℝ} (hx : 0 < x) :
    HasDerivAt balancedSeamScalar (balancedSeamScalarDerivative x) x := by
  have hx3 : 0 < x^3 := by positivity
  have h1x3 : 0 < 1+x^3 := by positivity
  have ha0 : 0 < x+x^2+x^3 := by positivity
  have hap0 : 0 < (x+x^2+x^3)+2 := by positivity
  have h1x : 0 < 1+x := by positivity
  have h1x2 : 0 < 1+x^2 := by positivity
  have hquad : 0 < 1-x+x^2 := by nlinarith [sq_nonneg (x-1/2)]
  have hden : 4*x^3 ≠ 0 := mul_ne_zero (by norm_num) hx3.ne'
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hx2 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
  have hx3d : HasDerivAt (fun y : ℝ => y^3) (3*x^2) x := by simpa using hasDerivAt_pow 3 x
  have haRaw := (hid.add hx2).add hx3d
  have ha : HasDerivAt (fun y : ℝ => y+y^2+y^3) (1+2*x+3*x^2) x := by
    apply haRaw.congr_deriv <;> ring
  have hL := hasDerivAt_remainingLogFactor hx
  have hn1 := (hid.const_add 1).mul (hx2.const_add 1)
  have hn := hn1.const_mul 4
  have hd := hx3d.const_add 1
  have hhraw := hn.div hd h1x3.ne'
  have hhshape := hhraw.congr_of_eventuallyEq (f₁ := fun y : ℝ =>
      4*(1+y)*(1+y^2)/(1+y^3)) (by
    filter_upwards with y
    simp only [Pi.div_apply, Pi.mul_apply]
    ring)
  have hh : HasDerivAt (fun y : ℝ => 4*(1+y)*(1+y^2)/(1+y^3))
      (4*(1+x)*(1-x^2)/((1+x^3)*(1-x+x^2))) x := by
    apply hhshape.congr_deriv
    simp only [Pi.mul_apply]
    field_simp [h1x3.ne', hquad.ne']
    ring
  have hhpos : 0 < 4*(1+x)*(1+x^2)/(1+x^3) := by positivity
  have hloghRaw := (Real.hasDerivAt_log hhpos.ne').comp x hh
  have hlogh : HasDerivAt (fun y : ℝ => Real.log (4*(1+y)*(1+y^2)/(1+y^3)))
      ((1-x^2)/((1+x^2)*(1-x+x^2))) x := by
    apply hloghRaw.congr_deriv
    field_simp [h1x.ne', h1x2.ne', h1x3.ne', hquad.ne']
  have hphiA := (hasDerivAt_xLogX ha0.ne').comp x ha
  have ha2 : HasDerivAt (fun y : ℝ => (y+y^2+y^3)+2) (1+2*x+3*x^2) x := ha.add_const 2
  have hphiA2 := (hasDerivAt_xLogX hap0.ne').comp x ha2
  have hfirst := ((ha.const_sub 3).mul hL)
  have hsecond := ((ha.const_add 1).mul (hlogh.const_add 1))
  have hthird := (hphiA.add hphiA2).const_mul (1/2 : ℝ)
  have hnative := (hfirst.sub hsecond).add hthird
  have hnative' : HasDerivAt
      (((fun x => 3-(x+x^2+x^3))*remainingLogFactor -
        (fun x => 1+(x+x^2+x^3)) *
          (fun x => 1+Real.log (4*(1+x)*(1+x^2)/(1+x^3)))) +
        (fun x => (1/2) * (xLogX (x+x^2+x^3) + xLogX ((x+x^2+x^3)+2))))
      (balancedSeamScalarDerivative x) x := by
    apply hnative.congr_deriv
    unfold balancedSeamScalarDerivative
    ring
  apply hnative'.congr_of_eventuallyEq
  filter_upwards with y
  rw [balancedSeamScalar_eq]
  change
    (3-(y+y^2+y^3))*remainingLogFactor y -
      (1+(y+y^2+y^3))*(1+Real.log (4*(1+y)*(1+y^2)/(1+y^3))) +
      (1/2)*(xLogX (y+y^2+y^3) + xLogX ((y+y^2+y^3)+2)) = _
  rfl

theorem balancedSeamScalarDerivative_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2/5) : balancedSeamScalarDerivative x < 0 := by
  let a : ℝ := x+x^2+x^3
  let ap : ℝ := 1+2*x+3*x^2
  let h : ℝ := 4*(1+x)*(1+x^2)/(1+x^3)
  let q : ℝ := ((1+x^3)^2/(4*x^3))*h
  have hxlt : x < 1 := lt_of_le_of_lt hx1 (by norm_num)
  have hxhalf : x < 1/2 := lt_of_le_of_lt hx1 (by norm_num)
  have hx3 : 0 < x^3 := by positivity
  have h1x3 : 0 < 1+x^3 := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hap : 0 < a+2 := by positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have haprime : 0 < ap := by dsimp [ap]; positivity
  have hx2lt : x^2 < 1/4 := by nlinarith [sq_nonneg x, sq_nonneg (x-1/2)]
  have hx3lt : x^3 < 1/8 := by
    nlinarith [mul_pos hx0 (sub_pos.mpr hx2lt), mul_pos hx0 (sub_pos.mpr hxhalf)]
  have halt : a < 1 := by
    dsimp [a]
    have hxle : x ≤ 2/5 := hx1
    have hx2le : x^2 ≤ (2/5 : ℝ)^2 := by nlinarith [sq_nonneg (x-2/5)]
    norm_num at hx2le hx3lt ⊢
    linarith
  have haProd : a*(a+2) < 3 := by nlinarith
  have hqgt : 2 < q := by
    dsimp [q, h]
    rw [show (1+x^3)^2 = (1+x^3)*(1+x^3) by ring]
    field_simp [hx3.ne', h1x3.ne']
    nlinarith [mul_pos (show 0 < 1+x by positivity) (show 0 < 1+x^2 by positivity)]
  have hqSq : 3 < q^2 := by nlinarith
  have hprod : a*(a+2) < q^2 := lt_trans haProd hqSq
  have hlogprod : Real.log (a*(a+2)) < Real.log (q^2) :=
    Real.log_lt_log (mul_pos ha hap) hprod
  have hqeq : q = Real.exp (remainingLogFactor x) * h := by
    dsimp [q]
    rw [remainingLogFactor, Real.exp_log]
    positivity
  have hlogq : Real.log q = remainingLogFactor x + Real.log h := by
    rw [hqeq, Real.log_mul (Real.exp_pos _).ne' hh.ne', Real.log_exp]
  have hbracket : (1/2:ℝ)*(Real.log a + Real.log (a+2)) - remainingLogFactor x - Real.log h < 0 := by
    rw [Real.log_mul ha.ne' hap.ne', Real.log_pow] at hlogprod
    rw [hlogq] at hlogprod
    norm_num at hlogprod
    linarith
  have hLprime : -3*(1-x^3)/(x*(1+x^3)) < 0 := by
    have hn : 0 < 1-x^3 := sub_pos.mpr (lt_trans hx3lt (by norm_num))
    have hd : 0 < x*(1+x^3) := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hn) hd
  have hthree : 0 < 3-a := by linarith
  have hloghprime : 0 < (1-x^2)/((1+x^2)*(1-x+x^2)) := by
    have hn : 0 < 1-x^2 := by nlinarith [sq_nonneg x]
    have hquad : 0 < 1-x+x^2 := by nlinarith [sq_nonneg (x-1/2)]
    positivity
  have honea : 0 < 1+a := by positivity
  have hform : balancedSeamScalarDerivative x =
      (3-a)*(-3*(1-x^3)/(x*(1+x^3))) -
      (1+a)*((1-x^2)/((1+x^2)*(1-x+x^2))) +
      ap*((1/2)*(Real.log a + Real.log (a+2))-remainingLogFactor x-Real.log h) := by
    unfold balancedSeamScalarDerivative
    dsimp [a, ap, h]
    ring
  rw [hform]
  have hfirst : (3-a)*(-3*(1-x^3)/(x*(1+x^3))) < 0 := mul_neg_of_pos_of_neg hthree hLprime
  have hsecond : 0 < (1+a)*((1-x^2)/((1+x^2)*(1-x+x^2))) := mul_pos honea hloghprime
  have hthird : ap*((1/2)*(Real.log a+Real.log (a+2))-remainingLogFactor x-Real.log h) < 0 :=
    mul_neg_of_pos_of_neg haprime hbracket
  linarith

theorem balancedSeamScalar_antitoneOn : AntitoneOn balancedSeamScalar (Set.Ioc 0 (2/5)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 (2/5))
  · intro x hx
    exact (hasDerivAt_balancedSeamScalar hx.1).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hasDerivAt_balancedSeamScalar hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hasDerivAt_balancedSeamScalar hx.1).deriv]
    exact (balancedSeamScalarDerivative_neg hx.1 hx.2.le).le

theorem remainingLogFactor_pos_on_seam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) : 0 < remainingLogFactor x := by
  have hu0 : 0 < x ^ 3 := by positivity
  have hult : x ^ 3 < 1 := by
    have hxlt : x < 1 := lt_of_le_of_lt hx1 (by norm_num)
    nlinarith [sq_nonneg x, mul_pos hx0 (sub_pos.mpr hxlt)]
  have hne : 1 - x ^ 3 ≠ 0 := by linarith
  have hsq : 0 < (1 - x ^ 3) ^ 2 := sq_pos_of_ne_zero hne
  have hdiff : 0 < (1 + x ^ 3) ^ 2 - 4 * x ^ 3 := by
    nlinarith
  have hratio : 1 < (1 + x ^ 3) ^ 2 / (4 * x ^ 3) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * x ^ 3)).2
    nlinarith
  unfold remainingLogFactor
  exact Real.log_pos hratio

theorem proxy_pos_at_balancedSeam :
    StrictProxyPositiveAtBalancedSeam := by
  intro x hx0 hx1
  have hanti := balancedSeamScalar_antitoneOn
  have hxmem : x ∈ Set.Ioc (0 : ℝ) (2 / 5) := ⟨hx0, hx1⟩
  have hendmem : (2 / 5 : ℝ) ∈ Set.Ioc 0 (2 / 5) := by norm_num
  have hgmono : balancedSeamScalar (2 / 5) ≤ balancedSeamScalar x := hanti hxmem hendmem hx1
  have hledger : (3597 : ℝ) / 62500 < balancedSeamScalar (2 / 5) :=
    balancedSeamEndpointLogLedger.2.2.2.2
  have hgpos : 0 < balancedSeamScalar x := by
    have hrat : (0 : ℝ) < 3597 / 62500 := by norm_num
    exact lt_of_lt_of_le (lt_trans hrat hledger) hgmono
  have hLpos : 0 < remainingLogFactor x := remainingLogFactor_pos_on_seam hx0 hx1
  have hsum : 0 < balancedSeamScalar x + remainingLogFactor x := add_pos hgpos hLpos
  have hmpos : 0 < contactMidpoint x := by
    unfold contactMidpoint contactDenominator
    positivity
  have hprod : 0 < contactMidpoint x * (balancedSeamScalar x + remainingLogFactor x) := mul_pos hmpos hsum
  have hbridge : contactMidpoint x * (balancedSeamScalar x + remainingLogFactor x) ≤
      strictProxy x (1 / 2) (2 * contactMidpoint x) := proxy_ge_at_balancedSeam hx0 hx1
  exact lt_of_lt_of_le hprod hbridge

/-! ## Low-prior seam: scalar estimates -/

theorem lowPriorSeamPolynomial_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    0 < lowPriorSeamPolynomial x := by
  have hxnonneg : 0 ≤ x := le_of_lt hx0
  have hx2 : x ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by nlinarith
  have hx3 : x ^ 3 ≤ (2 / 5 : ℝ) ^ 3 := by nlinarith
  have hfactor : 51 + 34 * x + 17 * x ^ 2 ≤ (1683 : ℝ) / 25 := by
    nlinarith
  have hprod : x ^ 3 * (51 + 34 * x + 17 * x ^ 2) ≤
      (13464 : ℝ) / 3125 := by
    nlinarith [mul_nonneg hxnonneg
      (show 0 ≤ 51 + 34 * x + 17 * x ^ 2 by positivity),
      mul_nonneg (sub_nonneg.mpr hx3)
        (show 0 ≤ 51 + 34 * x + 17 * x ^ 2 by positivity),
      mul_nonneg (show 0 ≤ x ^ 3 by positivity) (sub_nonneg.mpr hfactor)]
  unfold lowPriorSeamPolynomial
  nlinarith

/-- The scalar margin for the low-prior mixing-gap estimate. -/
def lowPriorSeamMixingMargin (x : ℝ) : ℝ :=
  3 * (1 - 3 * x ^ 4) * (1 - x ^ 4) ^ 2 -
    (12 / 5) * (1 + 2 * contactMidpoint x)

theorem lowPriorSeamMixingMargin_antitoneOn : AntitoneOn lowPriorSeamMixingMargin (Ioc (0 : ℝ) (2 / 5)) := by
  have hcont : ContinuousOn lowPriorSeamMixingMargin (Ioc (0 : ℝ) (2 / 5)) := by
    intro x hx
    have hmcont : ContinuousAt contactMidpoint x := (hasDerivAt_contactMidpoint hx.1).continuousAt
    unfold lowPriorSeamMixingMargin
    fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Ioc (0 : ℝ) (2 / 5)) hcont
  · intro x hx
    rw [interior_Ioc] at hx
    have hx0 : 0 < x := hx.1
    exact (by
      have hx4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
        simpa using hasDerivAt_pow 4 x
      have hfirst := (((hx4.const_mul 3).const_sub 1).const_mul 3).mul
        ((hx4.const_sub 1).pow 2)
      have hsecond := (((hasDerivAt_contactMidpoint hx0).const_mul 2).const_add 1).const_mul
        (12 / 5)
      exact (hfirst.sub hsecond).differentiableAt.differentiableWithinAt)
  · intro x hx
    rw [interior_Ioc] at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 2 / 5 := hx.2
    have hx4lt : x ^ 4 < (2 / 5 : ℝ) ^ 4 := by
      have hx2 : x ^ 2 < (2 / 5 : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_pos (show 0 < x ^ 2 by positivity) (sub_pos.mpr hx2)]
    have hr1 : 0 < 1 - x ^ 4 := by nlinarith
    have hr3 : 0 < 1 - 3 * x ^ 4 := by norm_num at hx4lt ⊢; nlinarith
    have hm : 0 < contactMidpointDerivative x := contactMidpointDerivative_pos hx0
    have hx4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
      simpa using hasDerivAt_pow 4 x
    have hfirst := (((hx4.const_mul 3).const_sub 1).const_mul 3).mul
      ((hx4.const_sub 1).pow 2)
    have hsecond := (((hasDerivAt_contactMidpoint hx0).const_mul 2).const_add 1).const_mul
      (12 / 5)
    have hd := hfirst.sub hsecond
    change HasDerivAt lowPriorSeamMixingMargin _ x at hd
    rw [hd.deriv]
    dsimp [lowPriorSeamMixingMargin]
    have hA : 3 * (-(3 * (4 * x ^ 3))) * (1 - x ^ 4) ^ 2 ≤ 0 := by
      have : 0 ≤ 36 * x ^ 3 * (1 - x ^ 4) ^ 2 := by positivity
      nlinarith
    have hB : 3 * (1 - 3 * x ^ 4) *
        (2 * (1 - x ^ 4) * (-(4 * x ^ 3))) ≤ 0 := by
      have : 0 ≤ 24 * (1 - 3 * x ^ 4) * (1 - x ^ 4) * x ^ 3 := by
        positivity
      nlinarith
    have hC : 0 ≤ (12 / 5 : ℝ) * (2 * contactMidpointDerivative x) := by positivity
    convert (show
      3 * (-(3 * (4 * x ^ 3))) * (1 - x ^ 4) ^ 2 +
          3 * (1 - 3 * x ^ 4) * (2 * (1 - x ^ 4) * (-(4 * x ^ 3))) -
          (12 / 5) * (2 * contactMidpointDerivative x) ≤ 0 by linarith) using 1 <;> ring

theorem lowPriorSeamMixingMargin_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    0 < lowPriorSeamMixingMargin x := by
  have hend : lowPriorSeamMixingMargin (2 / 5) = (103747643 : ℝ) / 3173828125 := by
    unfold lowPriorSeamMixingMargin contactMidpoint contactDenominator
    norm_num
  have hmono := lowPriorSeamMixingMargin_antitoneOn ⟨hx0, hx1⟩
    ⟨by norm_num, le_rfl⟩ hx1
  rw [hend] at hmono
  exact lt_of_lt_of_le lowPriorSeamEndpointLedger.1 hmono

theorem mixingGap_ge_at_lowPriorSeam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    (12 / 5 : ℝ) * x ^ 4 * (1 + 2 * contactMidpoint x) ≤
      3 * x ^ 4 * (1 - 3 * x ^ 4) * (1 - x ^ 4) ^ 2 := by
  have h := (lowPriorSeamMixingMargin_pos hx0 hx1).le
  unfold lowPriorSeamMixingMargin at h
  nlinarith [show 0 ≤ x ^ 4 by positivity]

/-- A natural-log entropy envelope at prior three times the fourth-power mass. -/
def lowPriorSeamEntropyEnvelope (x : ℝ) : ℝ :=
  let r := x ^ 4
  let s := 2 * contactMidpoint x
  let q := r + s
  let Q := 1 + q
  (1 - 3 * r) * (Real.log (Q / r) + 1) +
    3 * q * (Real.log (Q / q) + 1)

theorem highArmEntropy_le_at_lowPriorSeam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    highArmEntropy x (3 * x ^ 4) (2 * contactMidpoint x) ≤ x ^ 4 * lowPriorSeamEntropyEnvelope x := by
  let r : ℝ := x ^ 4
  let s : ℝ := 2 * contactMidpoint x
  let q : ℝ := r + s
  let Q : ℝ := 1 + q
  rw [highArmEntropy, pairEntropy_comm 1 (x ^ 4 + 2 * contactMidpoint x)]
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by
    dsimp [s, contactMidpoint, contactDenominator]
    positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hcoef : 0 ≤ 1 - 3 * r := by
    have hx2 : x ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by nlinarith
    have hx4 : x ^ 4 ≤ (2 / 5 : ℝ) ^ 4 := by nlinarith
    dsimp [r]
    norm_num at hx4 ⊢
    nlinarith
  have hleft := pairEntropy_le_left_log hr (show 0 ≤ 1 + s by positivity)
  have hright := pairEntropy_le_left_log hq (show 0 ≤ (1 : ℝ) by norm_num)
  have hleft' := mul_le_mul_of_nonneg_left hleft hcoef
  have hright' := mul_le_mul_of_nonneg_left hright (show 0 ≤ 3 * r by positivity)
  have hQ1 : r + (1 + s) = Q := by dsimp [Q, q]; ring
  have hQ2 : q + 1 = Q := by dsimp [Q]; ring
  rw [hQ1] at hleft'
  rw [hQ2] at hright'
  unfold lowPriorSeamEntropyEnvelope
  dsimp [r, s, q, Q] at hleft' hright' ⊢
  nlinarith

/-! ## Low-prior seam: the integrated lower bound -/

/-- The explicit natural-log primitive used in the low-prior mixing bound. -/
def lowPriorSeamIntegral (u : ℝ) : ℝ :=
  (u + 17 / 5) * Real.log (u + 17 / 5) -
    (17 / 5) * Real.log (17 / 5) -
    (u + 1) * Real.log (u + 1)

/-- The difference between the integrated mixing bound and the entropy envelope. -/
def lowPriorSeamGap (x : ℝ) : ℝ := (5 / 2) * lowPriorSeamIntegral (seamWidthRatio x) - lowPriorSeamEntropyEnvelope x

theorem bridgeDerivative_ge_at_lowPriorSeam {x z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5)
    (hz0 : 0 ≤ z) (hzs : z ≤ 2 * contactMidpoint x) :
    Real.log (1 + (12 / 5) * x ^ 4 / (z + x ^ 4)) ≤
      bridgeDerivative x (3 * x ^ 4) z := by
  have hr : 0 < x ^ 4 := by positivity
  have hs : 0 < 2 * contactMidpoint x := by unfold contactMidpoint contactDenominator; positivity
  have hz1 : 0 < z + 1 := by linarith
  have hzr : 0 < z + x ^ 4 := by positivity
  have hpay := mixingGap_ge_at_lowPriorSeam hx0 hx1
  have hden : 0 < (z + x ^ 4) * (z + 1) := mul_pos hzr hz1
  have hzbound : z + 1 ≤ 1 + 2 * contactMidpoint x := by linarith
  have hnum : (12 / 5 : ℝ) * x ^ 4 * (z + 1) ≤
      3 * x ^ 4 * (1 - 3 * x ^ 4) * (1 - x ^ 4) ^ 2 := by
    calc
      _ ≤ (12 / 5) * x ^ 4 * (1 + 2 * contactMidpoint x) :=
        mul_le_mul_of_nonneg_left hzbound (by positivity)
      _ ≤ _ := hpay
  have hfrac : (12 / 5 : ℝ) * x ^ 4 / (z + x ^ 4) ≤
      (3 * x ^ 4) * (1 - 3 * x ^ 4) * (1 - x ^ 4) ^ 2 /
        ((z + x ^ 4) * (z + 1)) := by
    apply (div_le_div_iff₀ hzr hden).2
    calc
      (12 / 5 : ℝ) * x ^ 4 * ((z + x ^ 4) * (z + 1)) =
          ((12 / 5) * x ^ 4 * (z + 1)) * (z + x ^ 4) := by ring
      _ ≤ (3 * x ^ 4 * (1 - 3 * x ^ 4) * (1 - x ^ 4) ^ 2) *
          (z + x ^ 4) := mul_le_mul_of_nonneg_right hnum hzr.le
      _ = 3 * x ^ 4 * (1 - 3 * x ^ 4) * (1 - x ^ 4) ^ 2 *
          (z + x ^ 4) := by ring
  unfold bridgeDerivative
  apply Real.strictMonoOn_log.monotoneOn
  · simp only [mem_Ioi]; positivity
  · simp only [mem_Ioi]
    have hx4 : x ^ 4 ≤ (2 / 5 : ℝ) ^ 4 := by
      have hx2 : x ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hpi : 0 ≤ (3 * x ^ 4) * (1 - 3 * x ^ 4) := by
      have hfactor : 0 ≤ 1 - 3 * x ^ 4 := by
        norm_num at hx4 ⊢
        nlinarith
      positivity
    positivity
  · simpa [add_comm] using add_le_add_left hfrac 1

theorem hasDerivAt_scaled_lowPriorSeamIntegral {x z : ℝ} (hx0 : 0 < x) (hz0 : 0 ≤ z) :
    HasDerivAt (fun w => x ^ 4 * lowPriorSeamIntegral (w / x ^ 4))
      (Real.log (1 + (12 / 5) * x ^ 4 / (z + x ^ 4))) z := by
  have hr : 0 < x ^ 4 := by positivity
  have ha : 0 < z / x ^ 4 + 17 / 5 := by positivity
  have hb : 0 < z / x ^ 4 + 1 := by positivity
  have hA := (Real.hasDerivAt_mul_log ha.ne').comp z
    (((hasDerivAt_id z).div_const (x ^ 4)).add_const (17 / 5))
  have hB := (Real.hasDerivAt_mul_log hb.ne').comp z
    (((hasDerivAt_id z).div_const (x ^ 4)).add_const 1)
  have hraw := ((hA.sub_const ((17 / 5) * Real.log (17 / 5))).sub hB).const_mul (x ^ 4)
  have hshape := hraw.congr_of_eventuallyEq
    (f₁ := fun w => x ^ 4 * lowPriorSeamIntegral (w / x ^ 4))
    (Filter.Eventually.of_forall (fun w => by
      unfold lowPriorSeamIntegral
      rfl))
  apply hshape.congr_deriv
  rw [show 1 + (12 / 5 : ℝ) * x ^ 4 / (z + x ^ 4) =
      (z / x ^ 4 + 17 / 5) / (z / x ^ 4 + 1) by field_simp; ring,
    Real.log_div ha.ne' hb.ne']
  field_simp
  ring

theorem hasDerivAt_freeMixingTerm_at_lowPriorSeam {x z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5)
    (hz : 0 < z) :
    HasDerivAt (fun w => freeMixingTerm x (3 * x ^ 4) w)
      (bridgeDerivative x (3 * x ^ 4) z) z := by
  have hr : 0 < x ^ 4 := by positivity
  have hx4 : x ^ 4 ≤ (2 / 5 : ℝ) ^ 4 := by
    have hx2 : x ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by nlinarith
    nlinarith
  have he : 0 < freeLowerMixtureMass x (3 * x ^ 4) := by
    unfold freeLowerMixtureMass
    norm_num at hx4 ⊢
    nlinarith [mul_pos (show 0 < 1 - 3 * x ^ 4 by nlinarith) hr]
  have hell : 0 < freeUpperMixtureMass x (3 * x ^ 4) := by
    unfold freeUpperMixtureMass
    norm_num at hx4 ⊢
    nlinarith
  have hraw : HasDerivAt (fun w => freeMixingTerm x (3 * x ^ 4) w)
      (Real.log ((z + freeLowerMixtureMass x (3 * x ^ 4)) / z) +
        Real.log ((z + freeUpperMixtureMass x (3 * x ^ 4)) / z) -
        Real.log ((z + x ^ 4) / z) - Real.log ((z + 1) / z)) z := by
    unfold freeMixingTerm
    exact (((hasDerivAt_pairEntropy_left hz he).add
      (hasDerivAt_pairEntropy_left hz hell)).sub
      (hasDerivAt_pairEntropy_left hz hr)).sub
      (hasDerivAt_pairEntropy_left hz (by norm_num))
  apply hraw.congr_deriv
  have hse : z + freeLowerMixtureMass x (3 * x ^ 4) ≠ 0 := (add_pos hz he).ne'
  have hsl : z + freeUpperMixtureMass x (3 * x ^ 4) ≠ 0 := (add_pos hz hell).ne'
  have hsr : z + x ^ 4 ≠ 0 := (add_pos hz hr).ne'
  have hs1 : z + 1 ≠ 0 := (by positivity)
  rw [Real.log_div hse hz.ne', Real.log_div hsl hz.ne',
    Real.log_div hsr hz.ne', Real.log_div hs1 hz.ne']
  unfold bridgeDerivative
  rw [← freeMixture_product_ratio_eq_one_add (mul_ne_zero hsr hs1),
    Real.log_div (mul_ne_zero hse hsl) (mul_ne_zero hsr hs1),
    Real.log_mul hse hsl, Real.log_mul hsr hs1]
  ring

theorem freeMixingTerm_ge_at_lowPriorSeam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    x ^ 4 * lowPriorSeamIntegral (seamWidthRatio x) ≤ freeMixingTerm x (3 * x ^ 4) (2 * contactMidpoint x) := by
  let F : ℝ → ℝ := fun z =>
    x ^ 4 * lowPriorSeamIntegral (z / x ^ 4) - freeMixingTerm x (3 * x ^ 4) z
  have hs : 0 < 2 * contactMidpoint x := by unfold contactMidpoint contactDenominator; positivity
  have he : 0 < freeLowerMixtureMass x (3 * x ^ 4) := by
    unfold freeLowerMixtureMass
    have hx4 : x ^ 4 ≤ (2 / 5 : ℝ)^4 := by
      have hx2 : x^2 ≤ (2/5:ℝ)^2 := by nlinarith
      nlinarith
    norm_num at hx4 ⊢
    nlinarith [mul_pos (show 0 < 1 - 3*x^4 by nlinarith) (show 0 < x^4 by positivity)]
  have hell : 0 < freeUpperMixtureMass x (3 * x ^ 4) := by
    unfold freeUpperMixtureMass
    have hx4 : x ^ 4 ≤ (2 / 5 : ℝ)^4 := by
      have hx2 : x^2 ≤ (2/5:ℝ)^2 := by nlinarith
      nlinarith
    norm_num at hx4 ⊢
    nlinarith
  have hmono : AntitoneOn F (Icc 0 (2 * contactMidpoint x)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (2 * contactMidpoint x))
    · intro z hz
      unfold F lowPriorSeamIntegral freeMixingTerm pairEntropy xLogX
      fun_prop
    · intro z hz
      rw [interior_Icc] at hz
      exact ((hasDerivAt_scaled_lowPriorSeamIntegral hx0 hz.1.le).sub
        (hasDerivAt_freeMixingTerm_at_lowPriorSeam hx0 hx1 hz.1)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hlow := bridgeDerivative_ge_at_lowPriorSeam hx0 hx1 hz.1.le hz.2.le
      have hd := (hasDerivAt_scaled_lowPriorSeamIntegral hx0 hz.1.le).sub
        (hasDerivAt_freeMixingTerm_at_lowPriorSeam hx0 hx1 hz.1)
      change HasDerivAt F _ z at hd
      rw [hd.deriv]
      exact sub_nonpos.mpr hlow
  have h := hmono (show (0 : ℝ) ∈ Icc 0 (2 * contactMidpoint x) by constructor <;> linarith)
    (show 2 * contactMidpoint x ∈ Icc 0 (2 * contactMidpoint x) by constructor <;> linarith) hs.le
  have hzero : freeMixingTerm x (3 * x ^ 4) 0 = 0 := by
    simp [freeMixingTerm, pairEntropy, xLogX]
  have ht : (2 * contactMidpoint x) / x ^ 4 = seamWidthRatio x := by
    unfold contactMidpoint contactDenominator seamWidthRatio
    field_simp
  unfold F at h
  rw [hzero, ht] at h
  have hellzero : lowPriorSeamIntegral 0 = 0 := by simp [lowPriorSeamIntegral]
  simp only [zero_div, hellzero, mul_zero, sub_zero] at h
  linarith

theorem proxy_ge_at_lowPriorSeam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2 / 5) :
    x ^ 4 * lowPriorSeamGap x ≤ strictProxy x (3 * x ^ 4) (2 * contactMidpoint x) := by
  have hb := freeMixingTerm_ge_at_lowPriorSeam hx0 hx1
  have hA := highArmEntropy_le_at_lowPriorSeam hx0 hx1
  unfold strictProxy lowPriorSeamGap
  nlinarith

theorem lowPriorSeamEntropyEnvelope_eq (x : ℝ) : lowPriorSeamEntropyEnvelope x =
    (1 - 3 * x ^ 4) * (Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / x ^ 4) + 1) +
      3 * (x ^ 4 + 2 * contactMidpoint x) *
        (Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / (x ^ 4 + 2 * contactMidpoint x)) + 1) := by
  unfold lowPriorSeamEntropyEnvelope
  congr 3 <;> ring

theorem hasDerivAt_lowPriorSeamIntegral {u : ℝ} (hu : 0 < u + 1) :
    HasDerivAt lowPriorSeamIntegral (Real.log ((u + 17 / 5) / (u + 1))) u := by
  have hu17 : 0 < u + 17 / 5 := by linarith
  have hA := (Real.hasDerivAt_mul_log hu17.ne').comp u
    ((hasDerivAt_id u).add_const (17 / 5))
  have hB := (Real.hasDerivAt_mul_log hu.ne').comp u
    ((hasDerivAt_id u).add_const 1)
  have hraw := (hA.sub_const ((17 / 5) * Real.log (17 / 5))).sub hB
  have hshape := hraw.congr_of_eventuallyEq
    (f₁ := lowPriorSeamIntegral) (Filter.Eventually.of_forall (fun _ => rfl))
  apply hshape.congr_deriv
  rw [Real.log_div hu17.ne' hu.ne']
  ring

theorem lowPriorSeamEntropyEnvelope_eq_assoc (x : ℝ) : lowPriorSeamEntropyEnvelope x =
    (1 - 3 * x ^ 4) *
        (Real.log ((1 + (x ^ 4 + 2 * contactMidpoint x)) / x ^ 4) + 1) +
      3 * (x ^ 4 + 2 * contactMidpoint x) *
        (Real.log ((1 + (x ^ 4 + 2 * contactMidpoint x)) /
          (x ^ 4 + 2 * contactMidpoint x)) + 1) := by
  rw [lowPriorSeamEntropyEnvelope_eq]
  have hassoc : (1 : ℝ) + x ^ 4 + 2 * contactMidpoint x =
      1 + (x ^ 4 + 2 * contactMidpoint x) := by ring
  rw [hassoc]

/-! ## Low-prior seam: the two derivative estimates -/

theorem hasDerivAt_lowPriorSeamEntropyEnvelope {x : ℝ} (hx0 : 0 < x) :
    HasDerivAt lowPriorSeamEntropyEnvelope
      (-3 * (4 * x ^ 3) * Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / x ^ 4) - 4 / x +
       3 * (4 * x ^ 3 + 2 * contactMidpointDerivative x) *
         Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / (x ^ 4 + 2 * contactMidpoint x)) +
       (1 + 3 * (2 * contactMidpoint x)) * (4 * x ^ 3 + 2 * contactMidpointDerivative x) /
         (1 + x ^ 4 + 2 * contactMidpoint x)) x := by
  have hd : 0 < contactDenominator x := by unfold contactDenominator; nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have hr : 0 < x ^ 4 := by positivity
  have hm : 0 < contactMidpoint x := by unfold contactMidpoint; positivity
  have hq : 0 < x ^ 4 + 2 * contactMidpoint x := by positivity
  have hQ : 0 < 1 + x ^ 4 + 2 * contactMidpoint x := by positivity
  have hr' : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using hasDerivAt_pow 4 x
  have hs' : HasDerivAt (fun y : ℝ => 2 * contactMidpoint y) (2 * contactMidpointDerivative x) x :=
    (hasDerivAt_contactMidpoint hx0).const_mul 2
  have hq' := hr'.add hs'
  have hQ' := hq'.const_add 1
  have hQne : (fun y : ℝ => 1 + (y ^ 4 + 2 * contactMidpoint y)) x ≠ 0 := by
    show (1 : ℝ) + (x ^ 4 + 2 * contactMidpoint x) ≠ 0
    exact ne_of_gt (by linarith)
  have hqne : (fun y : ℝ => y ^ 4 + 2 * contactMidpoint y) x ≠ 0 := by
    change x ^ 4 + 2 * contactMidpoint x ≠ 0
    exact hq.ne'
  have hrne : (fun y : ℝ => y ^ 4) x ≠ 0 := by simpa using hr.ne'
  have hLr := (hQ'.div hr' hrne).log (div_ne_zero hQne hrne)
  have hLq := (hQ'.div hq' hqne).log (div_ne_zero hQne hqne)
  have hc' := (hr'.const_mul (-3)).const_add 1
  have hleft := hc'.mul (hLr.const_add 1)
  have hright := (hq'.mul (hLq.const_add 1)).const_mul 3
  have hraw := hleft.add hright
  have hshape := hraw.congr_of_eventuallyEq
    (f₁ := lowPriorSeamEntropyEnvelope) (Filter.Eventually.of_forall (fun y => by
      let Lr := Real.log ((1 + (y ^ 4 + 2 * contactMidpoint y)) / y ^ 4)
      let Lq := Real.log ((1 + (y ^ 4 + 2 * contactMidpoint y)) /
        (y ^ 4 + 2 * contactMidpoint y))
      have hUy : lowPriorSeamEntropyEnvelope y = (1 - 3 * y ^ 4) * (Lr + 1) +
          3 * (y ^ 4 + 2 * contactMidpoint y) * (Lq + 1) := by
        simpa [Lr, Lq] using lowPriorSeamEntropyEnvelope_eq_assoc y
      rw [hUy]
      change (1 - 3 * y ^ 4) * (Lr + 1) +
          3 * (y ^ 4 + 2 * contactMidpoint y) * (Lq + 1) =
        (1 + -3 * y ^ 4) * (1 + Lr) +
          3 * ((y ^ 4 + 2 * contactMidpoint y) * (1 + Lq))
      ring))
  apply hshape.congr_deriv
  have hassoc : (1 : ℝ) + x ^ 4 + 2 * contactMidpoint x =
      1 + (x ^ 4 + 2 * contactMidpoint x) := by ring
  rw [hassoc]
  simp only [Pi.add_apply]
  let q : ℝ := x ^ 4 + 2 * contactMidpoint x
  let Q : ℝ := 1 + q
  let qp : ℝ := 4 * x ^ 3 + 2 * contactMidpointDerivative x
  let Lr : ℝ := Real.log (Q / x ^ 4)
  let Lq : ℝ := Real.log (Q / q)
  have hxne : x ≠ 0 := hx0.ne'
  have qne : q ≠ 0 := by dsimp [q]; exact hq.ne'
  have Qne : Q ≠ 0 := by dsimp [Q, q]; exact ne_of_gt (by linarith)
  change
    -3 * (4 * x ^ 3) * (1 + Lr) +
        (1 + -3 * x ^ 4) *
          (((qp * x ^ 4 - Q * (4 * x ^ 3)) / (x ^ 4) ^ 2) / (Q / x ^ 4)) +
      3 * (qp * (1 + Lq) +
        q * (((qp * q - Q * qp) / q ^ 2) / (Q / q))) =
    -3 * (4 * x ^ 3) * Lr - 4 / x + 3 * qp * Lq +
      (1 + 3 * (2 * contactMidpoint x)) * qp / Q
  field_simp [hxne, qne, Qne]
  ring

theorem lowPriorSeamEntropyEnvelope_derivative_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2/5) :
    -(4/x) ≤
      -3 * (4 * x ^ 3) * Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / x ^ 4) - 4 / x +
      3 * (4 * x ^ 3 + 2 * contactMidpointDerivative x) *
        Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / (x ^ 4 + 2 * contactMidpoint x)) +
      (1 + 3 * (2 * contactMidpoint x)) * (4 * x ^ 3 + 2 * contactMidpointDerivative x) / (1 + x ^ 4 + 2 * contactMidpoint x) := by
  have hx : x ≠ 0 := hx0.ne'
  have hxnonneg : 0 ≤ x := hx0.le
  have hd : 0 < contactDenominator x := by unfold contactDenominator; nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have hr : 0 < x ^ 4 := by positivity
  have hm : 0 < contactMidpoint x := by unfold contactMidpoint; positivity
  have hmp : 0 < contactMidpointDerivative x := by unfold contactMidpointDerivative; positivity
  let r : ℝ := x ^ 4
  let s : ℝ := 2 * contactMidpoint x
  let q : ℝ := r + s
  let Q : ℝ := 1 + q
  let rp : ℝ := 4 * x ^ 3
  let sp : ℝ := 2 * contactMidpointDerivative x
  let Lr : ℝ := Real.log (Q / r)
  let Lq : ℝ := Real.log (Q / q)
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : 0 < q := by dsimp [q]; linarith
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hrp : 0 < rp := by dsimp [rp]; positivity
  have hsp : 0 < sp := by dsimp [sp]; positivity
  have hx2 : x ^ 2 ≤ (4 : ℝ) / 25 := by nlinarith
  have hx3 : x ^ 3 ≤ (2 / 5 : ℝ) * x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  have hdle : contactDenominator x ≤ (39 : ℝ) / 25 := by unfold contactDenominator; nlinarith
  have hx4le : x ^ 4 ≤ (4 / 25 : ℝ) * x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2)]
  have hx4d : 7 * x ^ 4 * contactDenominator x ≤ (1092 : ℝ) / 625 * x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx4le) hd.le,
      mul_nonneg (show 0 ≤ x ^ 4 by positivity) (sub_nonneg.mpr hdle)]
  have hpoly : 7 * x ^ 4 * contactDenominator x + 14 * x ^ 3 ≤ contactDenominator x := by
    unfold contactDenominator at *
    nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hx1)]
  have hqle : q ≤ (1 : ℝ) / 7 := by
    dsimp [q, r, s]
    unfold contactMidpoint
    rw [show x ^ 4 + 2 * (x ^ 3 / contactDenominator x) =
        (x ^ 4 * contactDenominator x + 2 * x ^ 3) / contactDenominator x by field_simp [hd.ne']]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hratio8 : (8 : ℝ) ≤ Q / q := by
    apply (le_div_iff₀ hq).2
    dsimp [Q]
    nlinarith
  have hlog8 : Real.log 8 ≤ Lq :=
    Real.strictMonoOn_log.monotoneOn (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show Q / q ∈ Set.Ioi 0 by exact div_pos hQ hq) hratio8
  have hlog2 : (56 : ℝ) / 81 ≤ Real.log 2 :=
    lowPriorSeamEndpointLedger.2.2.1
  have hlog8eq : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hLq : (56 : ℝ) / 27 ≤ Lq := by rw [hlog8eq] at hlog8; nlinarith
  have hden2 : 0 < 3 + 2*x + x^2 := by positivity
  have hneed : 4 * (1 + x + x^2) / (3 + 2*x + x^2) ≤ (56 : ℝ) / 27 := by
    apply (div_le_iff₀ hden2).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (show 0 ≤ 29 + 10*x by positivity)]
  have hkey : rp * s / r ≤ sp * Lq := by
    have hb := hneed.trans hLq
    dsimp [rp, r, s, sp]
    unfold contactMidpoint contactMidpointDerivative contactDenominator at *
    field_simp [hx] at *
    nlinarith
  have hlogdiff : Lr - Lq = Real.log (q / r) := by
    dsimp [Lr, Lq]
    rw [Real.log_div hQ.ne' hr.ne', Real.log_div hQ.ne' hq.ne',
      Real.log_div hq.ne' hr.ne']
    ring
  have hlogqr : Real.log (q / r) ≤ q / r - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hq hr)
  have hqr : q / r - 1 = s / r := by
    dsimp [q]
    calc
      (r + s) / r - 1 = (r + s) / r - r / r := by rw [div_self hr.ne']
      _ = s / r := by rw [add_div]; ring
  have hcore : 0 ≤ (rp + sp) * Lq - rp * Lr := by
    rw [show (rp + sp) * Lq - rp * Lr = sp * Lq - rp * (Lr - Lq) by ring,
      hlogdiff]
    have hlogqr' : Real.log (q / r) ≤ s / r := hlogqr.trans_eq hqr
    have hpaid : rp * Real.log (q / r) ≤ sp * Lq := calc
      _ ≤ rp * (s / r) := mul_le_mul_of_nonneg_left hlogqr' hrp.le
      _ = rp * s / r := by ring
      _ ≤ _ := hkey
    linarith
  have hlast : 0 ≤ (1 + 3 * s) * (rp + sp) / Q := by positivity
  dsimp [rp, Lr, Lq, sp, s, Q, q, r] at hcore hlast ⊢
  rw [show (1 : ℝ) + x ^ 4 + 2 * contactMidpoint x = 1 + (x ^ 4 + 2 * contactMidpoint x) by ring]
  nlinarith

theorem lowPriorSeamIntegral_derivative_term_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 2/5) :
    4/x ≤ (5/2) * (2*(1 + 2*x + 3*x^2)/(x + x^2 + x^3)^2) *
            Real.log ((seamWidthRatio x + 17/5)/(seamWidthRatio x + 1)) := by
  have hd : 0 < contactDenominator x := by unfold contactDenominator; nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have hxd : 0 < x * contactDenominator x := mul_pos hx0 hd
  have ht : 0 < seamWidthRatio x := by unfold seamWidthRatio; positivity
  have ht1 : 0 < seamWidthRatio x + 1 := by linarith
  have ht17 : 0 < seamWidthRatio x + 17/5 := by linarith
  have hy : 0 < (seamWidthRatio x + 17/5) / (seamWidthRatio x + 1) := div_pos ht17 ht1
  have hlog0 := Real.one_sub_inv_le_log_of_pos hy
  have hid : 1 - ((seamWidthRatio x + 17/5) / (seamWidthRatio x + 1))⁻¹ =
      (12/5 : ℝ) / (seamWidthRatio x + 17/5) := by
    field_simp [ht1.ne', ht17.ne']
    ring
  have hlog : (12/5 : ℝ) / (seamWidthRatio x + 17/5) ≤
      Real.log ((seamWidthRatio x + 17/5)/(seamWidthRatio x + 1)) := by rw [← hid]; exact hlog0
  have hcoef : 0 ≤ (5/2 : ℝ) *
      (2*(1 + 2*x + 3*x^2)/(x + x^2 + x^3)^2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hcoef
  have hp := lowPriorSeamPolynomial_pos hx0 hx1
  have hrat : 4/x ≤ (5/2 : ℝ) *
      (2*(1 + 2*x + 3*x^2)/(x + x^2 + x^3)^2) *
      ((12/5)/(seamWidthRatio x + 17/5)) := by
    unfold seamWidthRatio contactDenominator at *
    field_simp [hx0.ne'] at *
    unfold lowPriorSeamPolynomial at hp
    nlinarith
  exact hrat.trans hmul

theorem hasDerivAt_seamWidthRatio {x : ℝ} (hx0 : 0 < x) :
    HasDerivAt seamWidthRatio (-(2 * (1 + 2 * x + 3 * x ^ 2) /
      (x + x ^ 2 + x ^ 3) ^ 2)) x := by
  have hd34 : 0 < contactDenominator x := by
    unfold contactDenominator
    nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have hdenpos : 0 < x + x ^ 2 + x ^ 3 := by
    have : x + x ^ 2 + x ^ 3 = x * contactDenominator x := by
      unfold contactDenominator
      ring
    rw [this]
    exact mul_pos hx0 hd34
  have hdenne : x + x ^ 2 + x ^ 3 ≠ 0 := hdenpos.ne'
  have hdenNative := (hasDerivAt_id x).mul
    (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add
      (hasDerivAt_pow 2 x))
  have hdenNativeNe : x * (1 + x + x ^ 2) ≠ 0 := by
    have heq : x * (1 + x + x ^ 2) = x + x ^ 2 + x ^ 3 := by ring
    rw [heq]
    exact hdenne
  have hraw := (hasDerivAt_const x (2 : ℝ)).div hdenNative hdenNativeNe
  have hshape := hraw.congr_of_eventuallyEq
    (f₁ := seamWidthRatio) (Filter.Eventually.of_forall (fun y => by
      rfl))
  apply hshape.congr_deriv
  simp only [id_eq, Pi.add_apply, Pi.mul_apply]
  field_simp [hdenNativeNe, hdenne]
  ring

theorem hasDerivAt_lowPriorSeamGap {x : ℝ} (hx0 : 0 < x) :
    HasDerivAt lowPriorSeamGap
      ((5 / 2) * (Real.log ((seamWidthRatio x + 17 / 5) / (seamWidthRatio x + 1))) *
          (-(2 * (1 + 2 * x + 3 * x ^ 2) / (x + x ^ 2 + x ^ 3) ^ 2)) -
        (-3 * (4 * x ^ 3) * Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / x ^ 4) - 4 / x +
         3 * (4 * x ^ 3 + 2 * contactMidpointDerivative x) *
           Real.log ((1 + x ^ 4 + 2 * contactMidpoint x) / (x ^ 4 + 2 * contactMidpoint x)) +
         (1 + 3 * (2 * contactMidpoint x)) * (4 * x ^ 3 + 2 * contactMidpointDerivative x) /
           (1 + x ^ 4 + 2 * contactMidpoint x))) x := by
  have hd34 : 0 < contactDenominator x := by
    unfold contactDenominator
    nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  have ht3 : 0 < seamWidthRatio x := by
    unfold seamWidthRatio
    exact div_pos (by norm_num) (mul_pos hx0 hd34)
  have hell := (hasDerivAt_lowPriorSeamIntegral (u := seamWidthRatio x) (by linarith)).comp x
    (hasDerivAt_seamWidthRatio hx0)
  have hraw := (hell.const_mul (5 / 2)).sub (hasDerivAt_lowPriorSeamEntropyEnvelope hx0)
  have hshape := hraw.congr_of_eventuallyEq
    (f₁ := lowPriorSeamGap) (Filter.Eventually.of_forall (fun _ => rfl))
  apply hshape.congr_deriv
  ring

theorem lowPriorSeamGap_antitoneOn :
    AntitoneOn lowPriorSeamGap (Set.Ioc 0 (2 / 5)) := by
  have hU := fun (y : ℝ) (hy0 : 0 < y) (hy1 : y ≤ 2 / 5) =>
    lowPriorSeamEntropyEnvelope_derivative_ge hy0 hy1
  have hE := fun (y : ℝ) (hy0 : 0 < y) (hy1 : y ≤ 2 / 5) =>
    lowPriorSeamIntegral_derivative_term_ge hy0 hy1
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 (2 / 5))
  · intro y hy
    exact (hasDerivAt_lowPriorSeamGap hy.1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    exact (hasDerivAt_lowPriorSeamGap hy.1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    have hd := hasDerivAt_lowPriorSeamGap hy.1
    rw [hd.deriv]
    have hfirst :
        (5 / 2) * Real.log ((seamWidthRatio y + 17 / 5) / (seamWidthRatio y + 1)) *
            (-(2 * (1 + 2 * y + 3 * y ^ 2) / (y + y ^ 2 + y ^ 3) ^ 2)) ≤
          -(4 / y) := by
      calc
        _ = -((5 / 2) *
            (2 * (1 + 2 * y + 3 * y ^ 2) / (y + y ^ 2 + y ^ 3) ^ 2) *
              Real.log ((seamWidthRatio y + 17 / 5) / (seamWidthRatio y + 1))) := by ring
        _ ≤ -(4 / y) := neg_le_neg (hE y hy.1 hy.2.le)
    have hsecond := hU y hy.1 hy.2.le
    linarith

/-! ## Low-prior seam: an exact four-panel bound -/

theorem lowPriorSeamIntegral_panel_lower {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * Real.log (((a + b) / 2 + 17 / 5) / ((a + b) / 2 + 1)) ≤
      lowPriorSeamIntegral b - lowPriorSeamIntegral a := by
  let m : ℝ := (a + b) / 2
  let c₀ : ℝ := (b - a) / 2
  let h : ℝ → ℝ := fun c =>
    lowPriorSeamIntegral (m + c) - lowPriorSeamIntegral (m - c) -
      2 * c * Real.log ((m + 17 / 5) / (m + 1))
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; linarith
  have hmono : MonotoneOn h (Set.Icc 0 c₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) c₀)
    · intro c hc
      have hmc : 0 < m - c + 1 := by
        have hca : a ≤ m - c := by
          dsimp [m, c₀] at hc ⊢
          linarith [hc.2]
        linarith
      have hpc : 0 < m + c + 1 := by linarith [hc.1]
      have hdplus := (hasDerivAt_lowPriorSeamIntegral hpc).comp c
        ((hasDerivAt_const c m).add (hasDerivAt_id c))
      have hdminus := (hasDerivAt_lowPriorSeamIntegral hmc).comp c
        ((hasDerivAt_const c m).sub (hasDerivAt_id c))
      have hdlograw := ((hasDerivAt_id c).const_mul 2).mul_const
        (Real.log ((m + 17 / 5) / (m + 1)))
      have hdlog := hdlograw.congr_of_eventuallyEq
        (f₁ := fun z : ℝ => 2 * z * Real.log ((m + 17 / 5) / (m + 1)))
        (Filter.Eventually.of_forall (fun _ => rfl))
      exact ((hdplus.sub hdminus).sub hdlog).continuousAt.continuousWithinAt
    · intro c hc
      have hc' : c ∈ Set.Icc (0 : ℝ) c₀ := interior_subset hc
      have hmc : 0 < m - c + 1 := by
        have hca : a ≤ m - c := by
          dsimp [m, c₀] at hc' ⊢
          linarith [hc'.2]
        linarith
      have hpc : 0 < m + c + 1 := by linarith [hc'.1]
      have hdplus := (hasDerivAt_lowPriorSeamIntegral hpc).comp c
        ((hasDerivAt_const c m).add (hasDerivAt_id c))
      have hdminus := (hasDerivAt_lowPriorSeamIntegral hmc).comp c
        ((hasDerivAt_const c m).sub (hasDerivAt_id c))
      have hdlograw := ((hasDerivAt_id c).const_mul 2).mul_const
        (Real.log ((m + 17 / 5) / (m + 1)))
      have hdlog := hdlograw.congr_of_eventuallyEq
        (f₁ := fun z : ℝ => 2 * z * Real.log ((m + 17 / 5) / (m + 1)))
        (Filter.Eventually.of_forall (fun _ => rfl))
      exact ((hdplus.sub hdminus).sub hdlog).differentiableAt.differentiableWithinAt
    · intro c hc
      have hc' : c ∈ Set.Icc (0 : ℝ) c₀ := interior_subset hc
      have hca : a ≤ m - c := by
        dsimp [m, c₀] at hc' ⊢
        linarith [hc'.2]
      have hmc : 0 < m - c + 1 := by linarith
      have hpc : 0 < m + c + 1 := by linarith [hc'.1]
      have hm1 : 0 < m + 1 := by linarith
      have hm17 : 0 < m + 17 / 5 := by linarith
      have hp17 : 0 < m + c + 17 / 5 := by linarith
      have hn17 : 0 < m - c + 17 / 5 := by linarith
      let P : ℝ := (m + 17 / 5) ^ 2
      let Q : ℝ := (m + 1) ^ 2
      have hQmc : 0 < Q - c ^ 2 := by
        dsimp [Q]
        nlinarith [mul_pos hmc hpc]
      have hPmc : 0 < P - c ^ 2 := by
        dsimp [P]
        nlinarith [mul_pos hn17 hp17]
      have hQ : 0 < Q := by dsimp [Q]; positivity
      have hP : 0 < P := by dsimp [P]; positivity
      have hQP : Q ≤ P := by dsimp [P, Q]; nlinarith
      have hfrac : P / Q ≤ (P - c ^ 2) / (Q - c ^ 2) := by
        apply (div_le_div_iff₀ hQ hQmc).2
        nlinarith [sq_nonneg c, mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hQP)]
      have hlog := Real.log_le_log (div_pos hP hQ) hfrac
      have hidP : P - c ^ 2 = (m + c + 17 / 5) * (m - c + 17 / 5) := by
        dsimp [P]; ring
      have hidQ : Q - c ^ 2 = (m + c + 1) * (m - c + 1) := by
        dsimp [Q]; ring
      have hdplus := (hasDerivAt_lowPriorSeamIntegral hpc).comp c
        ((hasDerivAt_const c m).add (hasDerivAt_id c))
      have hdminus := (hasDerivAt_lowPriorSeamIntegral hmc).comp c
        ((hasDerivAt_const c m).sub (hasDerivAt_id c))
      have hdlograw := ((hasDerivAt_id c).const_mul 2).mul_const
        (Real.log ((m + 17 / 5) / (m + 1)))
      have hdlog := hdlograw.congr_of_eventuallyEq
        (f₁ := fun z : ℝ => 2 * z * Real.log ((m + 17 / 5) / (m + 1)))
        (Filter.Eventually.of_forall (fun _ => rfl))
      have hd := (hdplus.sub hdminus).sub hdlog
      change HasDerivAt h _ c at hd
      rw [hd.deriv]
      simp only [zero_add, one_mul, zero_sub, sub_neg_eq_add]
      rw [Real.log_div hp17.ne' hpc.ne', Real.log_div hn17.ne' hmc.ne',
        Real.log_div hm17.ne' hm1.ne']
      ring_nf
      have hPpair : Real.log (P - c ^ 2) =
          Real.log (m + c + 17 / 5) + Real.log (m - c + 17 / 5) := by
        rw [hidP, Real.log_mul hp17.ne' hn17.ne']
      have hQpair : Real.log (Q - c ^ 2) =
          Real.log (m + c + 1) + Real.log (m - c + 1) := by
        rw [hidQ, Real.log_mul hpc.ne' hmc.ne']
      have hPsq : Real.log P = 2 * Real.log (m + 17 / 5) := by
        dsimp [P]
        rw [pow_two, Real.log_mul hm17.ne' hm17.ne']
        ring
      have hQsq : Real.log Q = 2 * Real.log (m + 1) := by
        dsimp [Q]
        rw [pow_two, Real.log_mul hm1.ne' hm1.ne']
        ring
      rw [Real.log_div hP.ne' hQ.ne'] at hlog
      rw [Real.log_div hPmc.ne' hQmc.ne'] at hlog
      ring_nf at hPpair hQpair hPsq hQsq hlog
      have hPpair' : Real.log (P - c ^ 2) =
          Real.log (17 / 5 + m + c) + Real.log (17 / 5 + m - c) := by
        convert hPpair using 1 <;> ring
      have hQpair' : Real.log (Q - c ^ 2) =
          Real.log (1 + m + c) + Real.log (1 + m - c) := by
        convert hQpair using 1 <;> ring
      have hQpair'' : Real.log (-c ^ 2 + Q) =
          Real.log (1 + m + c) + Real.log (1 + m - c) := by
        convert hQpair' using 1 <;> ring
      have hlog' :
          2 * Real.log (17 / 5 + m) - 2 * Real.log (1 + m) ≤
            (Real.log (17 / 5 + m + c) + Real.log (17 / 5 + m - c)) -
              (Real.log (1 + m + c) + Real.log (1 + m - c)) := by
        calc
          _ = Real.log P - Real.log Q := by rw [hPsq, hQsq]; ring
          _ ≤ Real.log (P - c ^ 2) - Real.log (-c ^ 2 + Q) := hlog
          _ = _ := by rw [hPpair', hQpair'']
      linarith [hlog']
  have hh := hmono (show (0 : ℝ) ∈ Set.Icc 0 c₀ by exact ⟨le_rfl, hc₀⟩)
    (show c₀ ∈ Set.Icc 0 c₀ by exact ⟨hc₀, le_rfl⟩) hc₀
  have hz : h 0 = 0 := by dsimp [h]; ring
  rw [hz] at hh
  dsimp [h, m, c₀] at hh
  have hplus : (a + b) / 2 + (b - a) / 2 = b := by ring
  have hminus : (a + b) / 2 - (b - a) / 2 = a := by ring
  have hcoef : 2 * ((b - a) / 2) = b - a := by ring
  rw [hplus, hminus, hcoef] at hh
  exact sub_nonneg.mp hh

theorem lowPriorSeamIntegral_twoFifths_lower :
    (17500 : ℝ) / 3159 ≤ (5 / 2) * lowPriorSeamIntegral (seamWidthRatio (2 / 5)) := by
  have ht : seamWidthRatio (2 / 5) = (125 : ℝ) / 39 := by
    unfold seamWidthRatio
    norm_num
  have he0 : lowPriorSeamIntegral 0 = 0 := by
    unfold lowPriorSeamIntegral
    rw [show (0 : ℝ) + 1 = 1 by norm_num, Real.log_one]
    ring
  have h1 := lowPriorSeamIntegral_panel_lower (a := (0 : ℝ)) (b := 125 / 156)
    (by norm_num) (by norm_num)
  have h2 := lowPriorSeamIntegral_panel_lower (a := (125 : ℝ) / 156) (b := 125 / 78)
    (by norm_num) (by norm_num)
  have h3 := lowPriorSeamIntegral_panel_lower (a := (125 : ℝ) / 78) (b := 125 / 52)
    (by norm_num) (by norm_num)
  have h4 := lowPriorSeamIntegral_panel_lower (a := (125 : ℝ) / 52) (b := 125 / 39)
    (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4
  have hpanels :
      (125 : ℝ) / 156 *
          (Real.log (5929 / 2185) + Real.log (2393 / 1145) +
            Real.log (8429 / 4685) + Real.log (9679 / 5935)) ≤
        lowPriorSeamIntegral (125 / 39) := by
    rw [he0] at h1
    linarith
  have hp1 : (0 : ℝ) < 5929 / 2185 := by norm_num
  have hp2 : (0 : ℝ) < 2393 / 1145 := by norm_num
  have hp3 : (0 : ℝ) < 8429 / 4685 := by norm_num
  have hp4 : (0 : ℝ) < 9679 / 5935 := by norm_num
  have hprod :
      Real.log (5929 / 2185) + Real.log (2393 / 1145) +
          Real.log (8429 / 4685) + Real.log (9679 / 5935) =
        Real.log ((1157525834384227 : ℝ) / 69564432491875) := by
    rw [← Real.log_mul hp1.ne' hp2.ne', ← Real.log_mul (mul_pos hp1 hp2).ne' hp3.ne',
      ← Real.log_mul (mul_pos (mul_pos hp1 hp2) hp3).ne' hp4.ne']
    congr 1
    norm_num
  rw [hprod] at hpanels
  have hledger := lowPriorSeamEndpointLedger
  have hP16 : (16 : ℝ) < 1157525834384227 / 69564432491875 := hledger.2.1
  have hlog16 : Real.log 16 ≤
      Real.log ((1157525834384227 : ℝ) / 69564432491875) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) hP16.le
  have hlog16eq : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hloglower : (224 : ℝ) / 81 ≤
      Real.log ((1157525834384227 : ℝ) / 69564432491875) := by
    rw [hlog16eq] at hlog16
    nlinarith [hledger.2.2.1]
  rw [ht]
  nlinarith [hpanels, hloglower]

theorem lowPriorSeamEntropyEnvelope_twoFifths_upper : lowPriorSeamEntropyEnvelope (2 / 5) ≤ (224632 : ℝ) / 40625 := by
  have hledger := lowPriorSeamEndpointLedger
  have hratio44 : (26999 : ℝ) / 624 < 44 := by norm_num
  have hlog44 : Real.log ((26999 : ℝ) / 624) < Real.log 44 := by
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) hratio44
  have hA : Real.log ((26999 : ℝ) / 624) < 19 / 5 :=
    hlog44.trans hledger.2.2.2.2.2.1
  have hratio11 : (26999 : ℝ) / 2624 < 11 := by norm_num
  have hlog11 : Real.log ((26999 : ℝ) / 2624) < Real.log 11 := by
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) hratio11
  have hB : Real.log ((26999 : ℝ) / 2624) < 12 / 5 :=
    hlog11.trans hledger.2.2.2.2.1
  unfold lowPriorSeamEntropyEnvelope contactMidpoint contactDenominator
  norm_num
  nlinarith

theorem lowPriorSeamGap_twoFifths_pos : (101924 : ℝ) / 9871875 ≤ lowPriorSeamGap (2 / 5) := by
  have hell := lowPriorSeamIntegral_twoFifths_lower
  have hU := lowPriorSeamEntropyEnvelope_twoFifths_upper
  have hid := lowPriorSeamEndpointLedger.2.2.2.2.2.2.1
  unfold lowPriorSeamGap
  nlinarith

theorem proxy_pos_at_lowPriorSeam :
    StrictProxyPositiveAtLowPriorSeam := by
  intro x hx0 hx1
  have hanti := lowPriorSeamGap_antitoneOn
  have hend := lowPriorSeamGap_twoFifths_pos
  have hxmem : x ∈ Set.Ioc (0 : ℝ) (2 / 5) := ⟨hx0, hx1⟩
  have hepmem : (2 / 5 : ℝ) ∈ Set.Ioc 0 (2 / 5) := by norm_num
  have hG : lowPriorSeamGap (2 / 5) ≤ lowPriorSeamGap x := hanti hxmem hepmem hx1
  have hcpos : 0 < (101924 : ℝ) / 9871875 := by norm_num
  have hGpos : 0 < lowPriorSeamGap x := lt_of_lt_of_le hcpos (hend.trans hG)
  have hx4pos : 0 < x ^ 4 := by positivity
  have hprod : 0 < x ^ 4 * lowPriorSeamGap x := mul_pos hx4pos hGpos
  exact lt_of_lt_of_le hprod (proxy_ge_at_lowPriorSeam hx0 hx1)

/-! ## The unconditional scalar and chart-cost bounds -/

/-- The positive scalar arm, with both seam hypotheses discharged. -/
theorem ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_phaseReward_nonneg
    (C : ScalarContactChart) (hC : C.StrictInterior) (hR : 0 ≤ C.phaseReward) :
    C.observableInfo - C.phaseReward ≤ 8 * C.mixingSum :=
  C.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_seam_pos
    proxy_pos_at_balancedSeam proxy_pos_at_lowPriorSeam hC hR

/-- The two phase arms bound the selected chart code without additional analytic hypotheses. -/
theorem ContactChart.strictFactorEight : ContactChart.StrictFactorEight :=
  ContactChart.strictFactorEight_of_seam_pos
    proxy_pos_at_balancedSeam proxy_pos_at_lowPriorSeam

end

end StochasticToDeterministicLatents.Binary
