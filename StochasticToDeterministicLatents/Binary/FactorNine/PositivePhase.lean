import StochasticToDeterministicLatents.Binary.FactorNine.NonpositivePhase

/-!
# The positive phase and its reduction to seam endpoints

The nonnegative-reward region lies below `x = 2/5` and above `pi = 3*x^4`.
There the high-arm proxy increases with the contact sum and is concave in
the prior. Its minimum is therefore bounded by the two lower-seam endpoints.
The last two theorems consume positivity at those endpoints and combine the
scalar phases into the cost bound on a supplied contact chart.

All scalar entropy expressions here use natural logarithms. The final chart
bound is in bits, with the positive factor `norm * Real.log 2` cancelled.

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

/-! ## Contact-sum derivative and logarithmic payments -/

/-- The free mixing derivative, written as a natural-log kernel. -/
def bridgeDerivative (x pi s : ℝ) : ℝ :=
  Real.log (1 + pi * (1 - pi) * (1 - x ^ 4) ^ 2 /
    ((s + x ^ 4) * (s + 1)))

theorem contactRatio_substitution_add_fourthPower {x s t : ℝ} (ht : t ≠ 1)
    (hs : s = (1 - t * x ^ 4) / (t - 1)) :
    s + x ^ 4 = (1 - x ^ 4) / (t - 1) := by
  rw [hs]
  field_simp
  ring

theorem contactRatio_substitution_add_one {x s t : ℝ} (ht : t ≠ 1)
    (hs : s = (1 - t * x ^ 4) / (t - 1)) :
    s + 1 = t * (1 - x ^ 4) / (t - 1) := by
  rw [hs]
  field_simp
  ring

theorem contactRatio_substitution_kernel {x s t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hs : s = (1 - t * x ^ 4) / (t - 1)) (hr : x ^ 4 ≠ 1) :
    (1 - x ^ 4) ^ 2 / ((s + x ^ 4) * (s + 1)) = (t - 1) ^ 2 / t := by
  rw [contactRatio_substitution_add_fourthPower ht1 hs, contactRatio_substitution_add_one ht1 hs]
  field_simp

theorem contactRatio_substitution {x s : ℝ} (hsr : s + x ^ 4 ≠ 0) (hr : x ^ 4 ≠ 1) :
    s = (1 - ((1 + s) / (x ^ 4 + s)) * x ^ 4) /
      ((1 + s) / (x ^ 4 + s) - 1) := by
  have hden : x ^ 4 + s ≠ 0 := by simpa [add_comm] using hsr
  have htm : (1 + s) / (x ^ 4 + s) - 1 ≠ 0 := by
    rw [div_sub_one hden]
    apply div_ne_zero
    · intro h
      apply hr
      linarith
    · exact hden
  apply (eq_div_iff htm).2
  field_simp
  ring

theorem inv_square_le_contactRatio {x s : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hs0 : 0 ≤ s) (hs : s ≤ x ^ 2) :
    1 / x ^ 2 ≤ (1 + s) / (x ^ 4 + s) := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hx4s : 0 < x ^ 4 + s := by positivity
  apply (div_le_div_iff₀ hx2 hx4s).2
  have hfactor : 0 ≤ (1 - x ^ 2) * (x ^ 2 - s) :=
    mul_nonneg (by nlinarith [sq_nonneg x]) (by linarith)
  nlinarith [sq_nonneg (x ^ 2)]

theorem smallLog_le_bridgeDerivative {x pi s : ℝ} (hx : 0 < x) (hxU : x < 2 / 5)
    (hpiL : 3 * x ^ 4 ≤ pi) (hpiU : pi ≤ 1 / 2)
    (hs0 : 0 ≤ s) (hsU : s ≤ x ^ 2) :
    Real.log (1 + x ^ 4 / (1 + s)) ≤ bridgeDerivative x pi s := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have hx2U : x ^ 2 ≤ 4 / 25 := by nlinarith
  have hx4U : x ^ 4 ≤ 16 / 625 := by nlinarith [sq_nonneg (x ^ 2 - 4 / 25)]
  have hpi0 : 0 ≤ pi := le_trans (by positivity : 0 ≤ 3 * x ^ 4) hpiL
  have hpip : 3 / 2 * x ^ 4 ≤ pi * (1 - pi) := by
    nlinarith [mul_nonneg hpi0 (sub_nonneg.mpr hpiU)]
  have hpoly : x ^ 2 + x ^ 4 ≤ 3 / 2 * (1 - x ^ 4) ^ 2 := by nlinarith
  have hC : x ^ 4 * (s + x ^ 4) ≤
      pi * (1 - pi) * (1 - x ^ 4) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hpoly hx4
    nlinarith [mul_le_mul_of_nonneg_right hpip (sq_nonneg (1 - x ^ 4))]
  have hs1 : 0 < s + 1 := by linarith
  have hsr : 0 < s + x ^ 4 := by positivity
  have hden : 0 < (s + x ^ 4) * (s + 1) := mul_pos hsr hs1
  have hfrac : x ^ 4 / (1 + s) ≤
      pi * (1 - pi) * (1 - x ^ 4) ^ 2 / ((s + x ^ 4) * (s + 1)) := by
    rw [add_comm 1 s]
    apply (div_le_div_iff₀ hs1 hden).2
    calc
      x ^ 4 * ((s + x ^ 4) * (s + 1)) =
          (x ^ 4 * (s + x ^ 4)) * (s + 1) := by ring
      _ ≤ (pi * (1 - pi) * (1 - x ^ 4) ^ 2) * (s + 1) :=
        mul_le_mul_of_nonneg_right hC hs1.le
  unfold bridgeDerivative
  have hnum : 0 ≤ pi * (1 - pi) * (1 - x ^ 4) ^ 2 :=
    mul_nonneg (mul_nonneg hpi0 (by linarith)) (sq_nonneg _)
  have hright : 0 < 1 + pi * (1 - pi) * (1 - x ^ 4) ^ 2 /
      ((s + x ^ 4) * (s + 1)) := by
    nlinarith [div_nonneg hnum hden.le]
  exact Real.strictMonoOn_log.monotoneOn
    (by simp only [mem_Ioi]; positivity)
    (by simpa only [mem_Ioi] using hright) (by linarith)

theorem freeMixture_shifted_product (x pi s : ℝ) :
    (s + freeLowerMixtureMass x pi) * (s + freeUpperMixtureMass x pi) - (s + x ^ 4) * (s + 1) =
      pi * (1 - pi) * (1 - x ^ 4) ^ 2 := by
  unfold freeLowerMixtureMass freeUpperMixtureMass
  ring

theorem freeMixture_product_ratio_eq_one_add {x pi s : ℝ}
    (hden : (s + x ^ 4) * (s + 1) ≠ 0) :
    ((s + freeLowerMixtureMass x pi) * (s + freeUpperMixtureMass x pi)) / ((s + x ^ 4) * (s + 1)) =
      1 + pi * (1 - pi) * (1 - x ^ 4) ^ 2 / ((s + x ^ 4) * (s + 1)) := by
  rw [one_add_div hden]
  congr 1
  linarith [freeMixture_shifted_product x pi s]

theorem hasDerivAt_pairEntropy_fourthPower_shift {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    HasDerivAt (fun z : ℝ => pairEntropy (x ^ 4) (1 + z))
      (Real.log ((x ^ 4 + (1 + s)) / (1 + s))) s := by
  have hr : 0 < x ^ 4 := pow_pos hx 4
  have hs1 : 0 < 1 + s := by linarith
  have h := (hasDerivAt_pairEntropy_right hr hs1).comp s
    ((hasDerivAt_const s 1).add (hasDerivAt_id s))
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun z : ℝ => pairEntropy (x ^ 4) (1 + z))
    (Filter.Eventually.of_forall (fun _ => rfl))
  exact h'.congr_deriv (by ring)

theorem hasDerivAt_pairEntropy_one_shift {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    HasDerivAt (fun z : ℝ => pairEntropy 1 (x ^ 4 + z))
      (Real.log ((1 + (x ^ 4 + s)) / (x ^ 4 + s))) s := by
  have hsr : 0 < x ^ 4 + s := add_pos (pow_pos hx 4) hs
  have h := (hasDerivAt_pairEntropy_right (by norm_num : (0 : ℝ) < 1) hsr).comp s
    ((hasDerivAt_const s (x ^ 4)).add (hasDerivAt_id s))
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun z : ℝ => pairEntropy 1 (x ^ 4 + z))
    (Filter.Eventually.of_forall (fun _ => rfl))
  exact h'.congr_deriv (by ring)

theorem hasDerivAt_proxy_contactSum {x pi s : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1) :
    HasDerivAt (fun z => strictProxy x pi z)
      ((5 / 2 : ℝ) * bridgeDerivative x pi s
        - pi * Real.log ((1 + s) / (x ^ 4 + s))
        - Real.log (1 + x ^ 4 / (1 + s))) s := by
  have hr : 0 < x ^ 4 := pow_pos hx 4
  have he : 0 < freeLowerMixtureMass x pi := by
    unfold freeLowerMixtureMass
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi1) hr.le]
  have hell : 0 < freeUpperMixtureMass x pi := by
    unfold freeUpperMixtureMass
    nlinarith [mul_nonneg hpi0 hr.le]
  have hs1 : 0 < 1 + s := by linarith
  have hsr : 0 < x ^ 4 + s := add_pos hr hs
  have hb : HasDerivAt (fun z => freeMixingTerm x pi z)
      (Real.log ((s + freeLowerMixtureMass x pi) / s) + Real.log ((s + freeUpperMixtureMass x pi) / s) -
        Real.log ((s + x ^ 4) / s) - Real.log ((s + 1) / s)) s := by
    unfold freeMixingTerm
    exact (((hasDerivAt_pairEntropy_left hs he).add
      (hasDerivAt_pairEntropy_left hs hell)).sub
      (hasDerivAt_pairEntropy_left hs hr)).sub
      (hasDerivAt_pairEntropy_left hs (by norm_num))
  have hAH : HasDerivAt (fun z => highArmEntropy x pi z)
      ((1 - pi) * Real.log ((x ^ 4 + (1 + s)) / (1 + s)) +
        pi * Real.log ((1 + (x ^ 4 + s)) / (x ^ 4 + s))) s := by
    unfold highArmEntropy
    exact ((hasDerivAt_pairEntropy_fourthPower_shift hx hs).const_mul (1 - pi)).add
      ((hasDerivAt_pairEntropy_one_shift hx hs).const_mul pi)
  have hbLog :
      Real.log ((s + freeLowerMixtureMass x pi) / s) + Real.log ((s + freeUpperMixtureMass x pi) / s) -
          Real.log ((s + x ^ 4) / s) - Real.log ((s + 1) / s) = bridgeDerivative x pi s := by
    have hse : s + freeLowerMixtureMass x pi ≠ 0 := (add_pos hs he).ne'
    have hsl : s + freeUpperMixtureMass x pi ≠ 0 := (add_pos hs hell).ne'
    rw [Real.log_div hse hs.ne', Real.log_div hsl hs.ne',
      Real.log_div (by simpa [add_comm] using hsr.ne') hs.ne',
      Real.log_div (by simpa [add_comm] using hs1.ne') hs.ne']
    unfold bridgeDerivative
    rw [← freeMixture_product_ratio_eq_one_add
      (mul_ne_zero (by simpa [add_comm] using hsr.ne') (by simpa [add_comm] using hs1.ne')),
      Real.log_div (mul_ne_zero hse hsl)
        (mul_ne_zero (by simpa [add_comm] using hsr.ne') (by simpa [add_comm] using hs1.ne')),
      Real.log_mul hse hsl,
      Real.log_mul (by simpa [add_comm] using hsr.ne') (by simpa [add_comm] using hs1.ne')]
    ring
  have hAHLog :
      (1 - pi) * Real.log ((x ^ 4 + (1 + s)) / (1 + s)) +
          pi * Real.log ((1 + (x ^ 4 + s)) / (x ^ 4 + s)) =
        pi * Real.log ((1 + s) / (x ^ 4 + s)) +
          Real.log (1 + x ^ 4 / (1 + s)) := by
    have hsum : 1 + (x ^ 4 + s) = x ^ 4 + (1 + s) := by ring
    have hratio : (x ^ 4 + (1 + s)) / (1 + s) = 1 + x ^ 4 / (1 + s) := by
      field_simp
      ring
    rw [hsum, hratio]
    have hfactor : (x ^ 4 + (1 + s)) / (x ^ 4 + s) =
        ((1 + s) / (x ^ 4 + s)) * (1 + x ^ 4 / (1 + s)) := by
      field_simp
      ring
    rw [hfactor, Real.log_mul]
    · ring
    · exact (div_pos hs1 hsr).ne'
    · exact (by positivity : 0 < 1 + x ^ 4 / (1 + s)).ne'
  unfold strictProxy
  have hraw := (hb.const_mul (5 / 2 : ℝ)).sub hAH
  rw [hbLog, hAHLog] at hraw
  exact hraw.congr_deriv (by ring)

/-- The remaining natural-log payment after subtracting the prior-weighted ratio. -/
def priorLogPayment (t pi : ℝ) : ℝ :=
  (3 / 2 : ℝ) * Real.log (1 + (t - 1) ^ 2 / t * pi * (1 - pi)) - pi * Real.log t

theorem hasDerivAt_priorLogPayment {t pi : ℝ} (ht : 0 < t) (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1) :
    HasDerivAt (priorLogPayment t)
      ((3 / 2 : ℝ) * ((t - 1) ^ 2 / t) * (1 - 2 * pi) /
          (1 + (t - 1) ^ 2 / t * pi * (1 - pi)) - Real.log t) pi := by
  have hk : 0 ≤ (t - 1) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have hp : 0 ≤ pi * (1 - pi) := mul_nonneg hpi0 (sub_nonneg.mpr hpi1)
  unfold priorLogPayment
  have hpder : HasDerivAt (fun z : ℝ => z * (1 - z)) (1 - 2 * pi) pi := by
    have hraw := (hasDerivAt_id pi).mul
      ((hasDerivAt_const pi 1).sub (hasDerivAt_id pi))
    have hraw' := hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z => rfl))
    change HasDerivAt (fun z : ℝ => z * (1 - z))
      (1 * (1 - pi) + pi * (0 - 1)) pi at hraw'
    exact hraw'.congr_deriv (by ring)
  have hinner : HasDerivAt
      (fun z : ℝ => 1 + (t - 1) ^ 2 / t * z * (1 - z))
      (((t - 1) ^ 2 / t) * (1 - 2 * pi)) pi := by
    have hraw := (hasDerivAt_const pi 1).add
      (hpder.const_mul ((t - 1) ^ 2 / t))
    exact (hraw.congr_of_eventuallyEq
      (f₁ := fun z : ℝ => 1 + (t - 1) ^ 2 / t * z * (1 - z))
      (Filter.Eventually.of_forall (fun z => by
        simp only [Pi.add_apply]
        ring))).congr_deriv
      (by ring)
  have hne : 1 + (t - 1) ^ 2 / t * pi * (1 - pi) ≠ 0 := by
    nlinarith [mul_nonneg hk hp]
  have hraw := ((hinner.log hne).const_mul (3 / 2 : ℝ)).sub
    ((hasDerivAt_id pi).mul_const (Real.log t))
  have hraw' := hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun z => by simp only [id_eq]; rfl))
  exact hraw'.congr_deriv (by field_simp)

theorem priorLogPayment_concave {t : ℝ} (ht : 0 < t) :
    ConcaveOn ℝ (Icc 0 (1 / 2)) (priorLogPayment t) := by
  have hk : 0 ≤ (t - 1) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc (0 : ℝ) (1 / 2))
  · intro p hp
    exact (hasDerivAt_priorLogPayment ht hp.1 (by linarith [hp.2])).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_priorLogPayment ht hp.1.le (by linarith [hp.2])).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha b hb hab
    have ha0 : 0 ≤ a := ha.1.le
    have hbU : b ≤ 1 / 2 := hb.2.le
    have hna : 0 ≤ 1 - 2 * a := by linarith
    have hnb : 0 ≤ 1 - 2 * b := by linarith
    have hqa : 0 < 1 + (t - 1) ^ 2 / t * a * (1 - a) := by
      have : 0 ≤ a * (1 - a) := mul_nonneg ha0 (by linarith [ha.2])
      nlinarith [mul_nonneg hk this]
    have hqb : 0 < 1 + (t - 1) ^ 2 / t * b * (1 - b) := by
      have : 0 ≤ b * (1 - b) := mul_nonneg hb.1.le (by linarith)
      nlinarith [mul_nonneg hk this]
    have hprod : a * (1 - a) ≤ b * (1 - b) := by
      have hgap : 0 ≤ 1 - a - b := by linarith [ha.2, hb.2]
      have hm := mul_nonneg (sub_nonneg.mpr hab) hgap
      nlinarith
    have hq : 1 + (t - 1) ^ 2 / t * a * (1 - a) ≤
        1 + (t - 1) ^ 2 / t * b * (1 - b) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod hk]
    rw [(hasDerivAt_priorLogPayment ht ha.1.le (by linarith [ha.2])).deriv,
      (hasDerivAt_priorLogPayment ht hb.1.le (by linarith [hb.2])).deriv]
    have hfrac : (1 - 2 * b) /
          (1 + (t - 1) ^ 2 / t * b * (1 - b)) ≤
        (1 - 2 * a) / (1 + (t - 1) ^ 2 / t * a * (1 - a)) := by
      exact div_le_div₀ hna (by linarith) hqa hq
    have hc : 0 ≤ (3 / 2 : ℝ) * ((t - 1) ^ 2 / t) :=
      mul_nonneg (by norm_num) hk
    have hscaled := mul_le_mul_of_nonneg_left hfrac hc
    have haeq : (3 / 2 : ℝ) * ((t - 1) ^ 2 / t) * (1 - 2 * a) /
        (1 + (t - 1) ^ 2 / t * a * (1 - a)) =
        ((3 / 2 : ℝ) * ((t - 1) ^ 2 / t)) *
          ((1 - 2 * a) / (1 + (t - 1) ^ 2 / t * a * (1 - a))) := by ring
    have hbeq : (3 / 2 : ℝ) * ((t - 1) ^ 2 / t) * (1 - 2 * b) /
        (1 + (t - 1) ^ 2 / t * b * (1 - b)) =
        ((3 / 2 : ℝ) * ((t - 1) ^ 2 / t)) *
          ((1 - 2 * b) / (1 + (t - 1) ^ 2 / t * b * (1 - b))) := by ring
    rw [haeq, hbeq]
    linarith

theorem hasDerivAt_priorLogPayment_balanced {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => priorLogPayment u (1 / 2))
      ((t - 2) / (t * (t + 1))) t := by
  have ht1 : 0 < t + 1 := by linarith
  have hform : ∀ u : ℝ, 0 < u →
      priorLogPayment u (1 / 2) =
        3 * Real.log (u + 1) - 2 * Real.log u - 3 * Real.log 2 := by
    intro u hu
    have hu1 : u + 1 ≠ 0 := (by linarith : 0 < u + 1).ne'
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    have hinner : 1 + (u - 1) ^ 2 / u * (1 / 2) * (1 - 1 / 2) =
        (u + 1) ^ 2 / (4 * u) := by
      field_simp
      ring
    rw [priorLogPayment, hinner, Real.log_div (pow_ne_zero 2 hu1)
      (mul_ne_zero h4 hu.ne'), Real.log_pow, Real.log_mul h4 hu.ne']
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    ring
  have hsimple : HasDerivAt
      (fun u : ℝ => 3 * Real.log (u + 1) - 2 * Real.log u - 3 * Real.log 2)
      ((t - 2) / (t * (t + 1))) t := by
    have hlog1 := ((hasDerivAt_id t).add_const 1).log ht1.ne'
    have hlogt := Real.hasDerivAt_log ht.ne'
    have hraw := ((hlog1.const_mul 3).sub (hlogt.const_mul 2)).sub_const
      (3 * Real.log 2)
    simp only [id_eq] at hraw
    exact hraw.congr_deriv (by field_simp [id_eq, ht.ne', ht1.ne']; ring)
  apply hsimple.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with u hu
  exact hform u hu

theorem priorLogPayment_balanced_nonneg {t : ℝ} (ht : 6 ≤ t) :
    0 ≤ priorLogPayment t (1 / 2) := by
  have hmono : MonotoneOn (fun u => priorLogPayment u (1 / 2)) (Icc 6 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (6 : ℝ) t)
    · intro u hu
      exact (hasDerivAt_priorLogPayment_balanced (by linarith [hu.1])).continuousAt.continuousWithinAt
    · intro u hu
      exact (hasDerivAt_priorLogPayment_balanced (by
        rw [interior_Icc] at hu
        linarith [hu.1])).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hasDerivAt_priorLogPayment_balanced (by linarith [hu.1])).deriv]
      exact div_nonneg (by linarith [hu.1])
        (mul_nonneg (by linarith [hu.1]) (by linarith [hu.1]))
  have hbase : 0 ≤ priorLogPayment 6 (1 / 2) := by
    have hrat : (6 : ℝ) < (49 / 24) ^ 3 := by norm_num
    have hlog : Real.log 6 ≤ Real.log ((49 / 24 : ℝ) ^ 3) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) hrat.le
    rw [Real.log_pow] at hlog
    norm_num [priorLogPayment] at hlog ⊢
    linarith
  exact le_trans hbase (hmono (by constructor <;> linarith) (by constructor <;> linarith) ht)

theorem priorLogPayment_nonneg {t pi : ℝ} (ht : 6 ≤ t)
    (hpi0 : 0 ≤ pi) (hpiU : pi ≤ 1 / 2) : 0 ≤ priorLogPayment t pi := by
  have hc := priorLogPayment_concave (lt_of_lt_of_le (by norm_num) ht)
  rcases hc with ⟨_, hc⟩
  have hcomb := hc (x := (0 : ℝ)) (by constructor <;> norm_num)
    (y := (1 / 2 : ℝ)) (by constructor <;> norm_num)
    (a := (1 : ℝ) - 2 * pi) (b := (2 : ℝ) * pi)
    (by linarith) (by linarith) (by ring)
  have hzero : priorLogPayment t 0 = 0 := by simp [priorLogPayment]
  have hend := priorLogPayment_balanced_nonneg ht
  have harg : (1 - 2 * pi) • (0 : ℝ) + (2 * pi) • (1 / 2 : ℝ) = pi := by
    simp only [smul_eq_mul]
    ring
  rw [hzero, harg] at hcomb
  have hweighted : 0 ≤ (2 * pi) • priorLogPayment t (1 / 2) := by
    simp only [smul_eq_mul]
    exact mul_nonneg (by linarith) hend
  exact le_trans (by simpa only [smul_eq_mul, mul_zero, zero_add] using hweighted) hcomb

theorem priorLog_le_three_halves_mul_bridgeDerivative {x pi s : ℝ} (hx : 0 < x) (hxU : x < 2 / 5)
    (hpi0 : 0 ≤ pi) (hpiU : pi ≤ 1 / 2)
    (hs0 : 0 ≤ s) (hsU : s ≤ x ^ 2) :
    pi * Real.log ((1 + s) / (x ^ 4 + s)) ≤ (3 / 2 : ℝ) * bridgeDerivative x pi s := by
  let t : ℝ := (1 + s) / (x ^ 4 + s)
  have hx1 : x < 1 := by linarith
  have hsr : 0 < x ^ 4 + s := by positivity
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) hsr
  have htL : 6 ≤ t := by
    have hratio := inv_square_le_contactRatio hx hx1 hs0 hsU
    have hx2U : x ^ 2 < 4 / 25 := by nlinarith
    have hinv : 25 / 4 < 1 / x ^ 2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hx)).2
      nlinarith
    dsimp [t]
    linarith
  have ht1 : t ≠ 1 := by
    intro heq
    linarith
  have hx4ne : x ^ 4 ≠ 1 := by
    have hx2 : x ^ 2 < 1 := by nlinarith
    have : x ^ 4 < 1 := by nlinarith [sq_nonneg (x ^ 2 - 1)]
    linarith
  have hsSub : s = (1 - t * x ^ 4) / (t - 1) := by
    exact contactRatio_substitution (by simpa [add_comm] using hsr.ne') hx4ne
  have hkernel := contactRatio_substitution_kernel ht.ne' ht1 hsSub hx4ne
  have hphi := priorLogPayment_nonneg htL hpi0 hpiU
  unfold priorLogPayment at hphi
  unfold bridgeDerivative
  dsimp [t] at hphi hkernel ⊢
  rw [← hkernel] at hphi
  have hphi' : 0 ≤ (3 / 2 : ℝ) *
      Real.log (1 + pi * (1 - pi) * (1 - x ^ 4) ^ 2 /
        ((s + x ^ 4) * (s + 1))) -
      pi * Real.log ((1 + s) / (x ^ 4 + s)) := by
    convert hphi using 1 <;> ring
  linarith

theorem strictProxy_monotoneInContactMass : StrictProxyMonotoneInContactMass := by
  intro x pi hx hxU hpiL hpiU
  have hx1 : x < 1 := by linarith
  have hm : 0 < contactMidpoint x := by
    unfold contactMidpoint contactDenominator
    positivity
  have hpi0 : 0 ≤ pi := le_trans (by positivity : 0 ≤ 3 * x ^ 4) hpiL
  apply monotoneOn_of_deriv_nonneg (convex_Icc (2 * contactMidpoint x) (x ^ 2))
  · intro s hs
    have hspos : 0 < s := lt_of_lt_of_le (by positivity : 0 < 2 * contactMidpoint x) hs.1
    exact (hasDerivAt_proxy_contactSum hx hspos hpi0 (by linarith)).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have hspos : 0 < s := lt_trans (by positivity : 0 < 2 * contactMidpoint x) hs.1
    exact (hasDerivAt_proxy_contactSum hx hspos hpi0 (by linarith)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have hspos : 0 < s := lt_trans (by positivity : 0 < 2 * contactMidpoint x) hs.1
    have hp1 := priorLog_le_three_halves_mul_bridgeDerivative hx hxU hpi0 hpiU hspos.le hs.2.le
    have hp2 := smallLog_le_bridgeDerivative hx hxU hpiL hpiU hspos.le hs.2.le
    rw [(hasDerivAt_proxy_contactSum hx hspos hpi0 (by linarith)).deriv]
    linarith

/-! ## Concavity in the prior -/

theorem highArmEntropy_affineInPrior (x pi s : ℝ) :
    highArmEntropy x pi s = pairEntropy (x ^ 4) (1 + s) +
      pi * (pairEntropy 1 (x ^ 4 + s) - pairEntropy (x ^ 4) (1 + s)) := by
  unfold highArmEntropy
  ring

theorem highArmEntropy_convexInPrior (x s : ℝ) {D : Set ℝ} (hD : Convex ℝ D) :
    ConvexOn ℝ D (fun pi => highArmEntropy x pi s) := by
  refine ⟨hD, ?_⟩
  intro a ha b hb u v hu hv huv
  change highArmEntropy x (u • a + v • b) s ≤ u • highArmEntropy x a s + v • highArmEntropy x b s
  rw [highArmEntropy_affineInPrior, highArmEntropy_affineInPrior, highArmEntropy_affineInPrior]
  dsimp only [smul_eq_mul]
  let H0 := pairEntropy (x ^ 4) (1 + s)
  let H1 := pairEntropy 1 (x ^ 4 + s)
  change H0 + (u * a + v * b) * (H1 - H0) ≤
    u * (H0 + a * (H1 - H0)) + v * (H0 + b * (H1 - H0))
  apply le_of_eq
  calc
    H0 + (u * a + v * b) * (H1 - H0) =
        (u + v) * H0 + (u * a + v * b) * (H1 - H0) := by rw [huv]; ring
    _ = u * (H0 + a * (H1 - H0)) + v * (H0 + b * (H1 - H0)) := by ring

theorem hasDerivAt_freeMixingTerm_prior {x pi s : ℝ}
    (hs : 0 < s) (he : 0 < freeLowerMixtureMass x pi) (hell : 0 < freeUpperMixtureMass x pi) :
    HasDerivAt (fun q : ℝ => freeMixingTerm x q s)
      ((1 - x ^ 4) *
        (Real.log ((s + freeLowerMixtureMass x pi) / freeLowerMixtureMass x pi) -
          Real.log ((s + freeUpperMixtureMass x pi) / freeUpperMixtureMass x pi))) pi := by
  have he' : HasDerivAt (fun q : ℝ => freeLowerMixtureMass x q) (1 - x ^ 4) pi := by
    unfold freeLowerMixtureMass
    have h := (hasDerivAt_id pi).add
      (((hasDerivAt_const pi (1 : ℝ)).sub (hasDerivAt_id pi)).mul_const (x ^ 4))
    have h' := h.congr_of_eventuallyEq (f₁ := fun q : ℝ => q + (1 - q) * x ^ 4)
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact h'.congr_deriv (by ring)
  have hell' : HasDerivAt (fun q : ℝ => freeUpperMixtureMass x q) (-(1 - x ^ 4)) pi := by
    unfold freeUpperMixtureMass
    have h := ((hasDerivAt_const pi (1 : ℝ)).sub (hasDerivAt_id pi)).add
      ((hasDerivAt_id pi).mul_const (x ^ 4))
    have h' := h.congr_of_eventuallyEq (f₁ := fun q : ℝ => 1 - q + q * x ^ 4)
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact h'.congr_deriv (by ring)
  have hE : HasDerivAt (fun q : ℝ => pairEntropy s (freeLowerMixtureMass x q))
      ((1 - x ^ 4) * Real.log ((s + freeLowerMixtureMass x pi) / freeLowerMixtureMass x pi)) pi := by
    have h := (hasDerivAt_pairEntropy_right hs he).comp pi he'
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun q : ℝ => pairEntropy s (freeLowerMixtureMass x q))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact h'.congr_deriv (by ring)
  have hL : HasDerivAt (fun q : ℝ => pairEntropy s (freeUpperMixtureMass x q))
      (-(1 - x ^ 4) * Real.log ((s + freeUpperMixtureMass x pi) / freeUpperMixtureMass x pi)) pi := by
    have h := (hasDerivAt_pairEntropy_right hs hell).comp pi hell'
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun q : ℝ => pairEntropy s (freeUpperMixtureMass x q))
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact h'.congr_deriv (by ring)
  have h := ((hE.add hL).sub_const (pairEntropy s (x ^ 4))).sub_const (pairEntropy s 1)
  unfold freeMixingTerm
  simpa only [Pi.add_apply, Pi.sub_apply] using h.congr_deriv (by ring)

theorem log_add_div_antitoneOn {s : ℝ} (hs : 0 < s) :
    AntitoneOn (fun z : ℝ => Real.log ((s + z) / z)) (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hdiv : s / b ≤ s / a := div_le_div_of_nonneg_left hs.le ha hab
  have harg : (s + b) / b ≤ (s + a) / a := by
    calc
      (s + b) / b = 1 + s / b := by field_simp [hb0.ne']; ring
      _ ≤ 1 + s / a := add_le_add_right hdiv 1
      _ = (s + a) / a := by field_simp [ha0.ne']; ring
  have hposa : 0 < (s + a) / a := div_pos (add_pos hs ha) ha
  have hposb : 0 < (s + b) / b := div_pos (add_pos hs hb) hb
  exact Real.strictMonoOn_log.monotoneOn hposb hposa harg

theorem freeMixingTerm_priorDerivative_antitoneOn {x s : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hs : 0 < s) :
    AntitoneOn
      (fun pi : ℝ => (1 - x ^ 4) *
        (Real.log ((s + freeLowerMixtureMass x pi) / freeLowerMixtureMass x pi) -
          Real.log ((s + freeUpperMixtureMass x pi) / freeUpperMixtureMass x pi)))
      (Icc 0 (1 / 2)) := by
  have hx4lt : x ^ 4 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hd : 0 ≤ 1 - x ^ 4 := (sub_pos.mpr hx4lt).le
  have hf := log_add_div_antitoneOn hs
  intro p hp q hq hpq
  have hp1 : p < 1 := hp.2.trans_lt (show (1 / 2 : ℝ) < 1 by norm_num)
  have hq1 : q < 1 := hq.2.trans_lt (show (1 / 2 : ℝ) < 1 by norm_num)
  have hep : 0 < freeLowerMixtureMass x p := by
    unfold freeLowerMixtureMass
    exact add_pos_of_nonneg_of_pos hp.1 (mul_pos (sub_pos.mpr hp1) (pow_pos hx0 4))
  have heq : 0 < freeLowerMixtureMass x q := by
    unfold freeLowerMixtureMass
    exact add_pos_of_nonneg_of_pos hq.1 (mul_pos (sub_pos.mpr hq1) (pow_pos hx0 4))
  have hellp : 0 < freeUpperMixtureMass x p := by
    unfold freeUpperMixtureMass
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr hp1) (mul_nonneg hp.1 (pow_pos hx0 4).le)
  have hellq : 0 < freeUpperMixtureMass x q := by
    unfold freeUpperMixtureMass
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr hq1) (mul_nonneg hq.1 (pow_pos hx0 4).le)
  have hemono : freeLowerMixtureMass x p ≤ freeLowerMixtureMass x q := by unfold freeLowerMixtureMass; nlinarith
  have hellanti : freeUpperMixtureMass x q ≤ freeUpperMixtureMass x p := by unfold freeUpperMixtureMass; nlinarith
  have hfe := hf hep heq hemono
  have hfell := hf hellq hellp hellanti
  exact mul_le_mul_of_nonneg_left (sub_le_sub hfe hfell) hd

theorem freeMixingTerm_concaveInPrior {x s : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hs : 0 < s) :
    ConcaveOn ℝ (Icc 0 (1 / 2)) (fun pi => freeMixingTerm x pi s) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
  · intro p hp
    have hp1 : p < 1 := hp.2.trans_lt (show (1 / 2 : ℝ) < 1 by norm_num)
    have he : 0 < freeLowerMixtureMass x p := by
      unfold freeLowerMixtureMass
      exact add_pos_of_nonneg_of_pos hp.1 (mul_pos (sub_pos.mpr hp1) (pow_pos hx0 4))
    have hell : 0 < freeUpperMixtureMass x p := by
      unfold freeUpperMixtureMass
      exact add_pos_of_pos_of_nonneg (sub_pos.mpr hp1) (mul_nonneg hp.1 (pow_pos hx0 4).le)
    exact (hasDerivAt_freeMixingTerm_prior hs he hell).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc, mem_Ioo] at hp
    have he : 0 < freeLowerMixtureMass x p := by unfold freeLowerMixtureMass; nlinarith [pow_pos hx0 4]
    have hell : 0 < freeUpperMixtureMass x p := by unfold freeUpperMixtureMass; nlinarith [pow_pos hx0 4]
    exact (hasDerivAt_freeMixingTerm_prior hs he hell).differentiableAt.differentiableWithinAt
  · intro p hp q hq hpq
    rw [interior_Icc, mem_Ioo] at hp hq
    have hep : 0 < freeLowerMixtureMass x p := by unfold freeLowerMixtureMass; nlinarith [pow_pos hx0 4]
    have heq : 0 < freeLowerMixtureMass x q := by unfold freeLowerMixtureMass; nlinarith [pow_pos hx0 4]
    have hellp : 0 < freeUpperMixtureMass x p := by unfold freeUpperMixtureMass; nlinarith [pow_pos hx0 4]
    have hellq : 0 < freeUpperMixtureMass x q := by unfold freeUpperMixtureMass; nlinarith [pow_pos hx0 4]
    rw [(hasDerivAt_freeMixingTerm_prior hs hep hellp).deriv,
      (hasDerivAt_freeMixingTerm_prior hs heq hellq).deriv]
    exact freeMixingTerm_priorDerivative_antitoneOn hx0 hx1 hs
      ⟨hp.1.le, hp.2.le⟩ ⟨hq.1.le, hq.2.le⟩ hpq

theorem strictProxy_concaveInPrior : StrictProxyConcaveInPrior := by
  intro x s hx0 hx1 hs0 hs1
  have hm : 0 < contactMidpoint x := by unfold contactMidpoint contactDenominator; positivity
  have hs : 0 < s := lt_of_lt_of_le (by positivity : 0 < 2 * contactMidpoint x) hs0
  have hb := freeMixingTerm_concaveInPrior hx0 hx1 hs
  have hscaled : ConcaveOn ℝ (Icc 0 (1 / 2))
      (fun pi => (5 / 2 : ℝ) * freeMixingTerm x pi s) := by
    simpa only [smul_eq_mul] using hb.smul (by norm_num : (0 : ℝ) ≤ 5 / 2)
  have ha := highArmEntropy_convexInPrior x s (convex_Icc 0 (1 / 2))
  unfold strictProxy
  change ConcaveOn ℝ (Icc 0 (1 / 2))
    ((fun pi => (5 / 2 : ℝ) * freeMixingTerm x pi s) - (fun pi => highArmEntropy x pi s))
  exact hscaled.sub ha

/-! ## Reduction to the two seam endpoints -/

theorem ScalarContactChart.two_mul_contactMidpoint_le_s (C : ScalarContactChart) :
    2 * (C.x ^ 3 / (1 + C.x + C.x ^ 2)) ≤ C.s := by
  let g : ℝ := 1 + C.x + C.x ^ 2
  let h : ℝ := 1 - C.x + C.x ^ 2
  let m : ℝ := C.x ^ 3 / g
  have hg_pos : 0 < g := by
    dsimp [g]
    nlinarith [C.x_pos, sq_nonneg C.x]
  have hh_pos : 0 < h := by
    dsimp [h]
    nlinarith [sq_nonneg (C.x - (1 / 2 : ℝ))]
  have hm_pos : 0 < m := by
    exact div_pos (pow_pos C.x_pos 3) hg_pos
  have hdisc : 4 * C.lowMass * C.highMass ≤ C.s ^ 2 := by
    dsimp only [ScalarContactChart.s]
    nlinarith [sq_nonneg (C.highMass - C.lowMass)]
  have hquad :
      0 ≤ (1 + C.y + C.r) * C.s ^ 2 + 4 * C.r * C.s - 4 * C.r * C.y := by
    have hscaled := mul_le_mul_of_nonneg_left hdisc C.denominator_pos.le
    have hcontact :
        (1 + C.y + C.r) * C.lowMass * C.highMass = C.r * (C.y - C.s) := by
      simpa only [ScalarContactChart.y, ScalarContactChart.r,
        ScalarContactChart.s] using C.contact
    nlinarith
  have hfactor : 1 + C.x ^ 2 + C.x ^ 4 = g * h := by
    dsimp [g, h]
    ring
  have hroot :
      (1 + C.y + C.r) * (2 * m) ^ 2 + 4 * C.r * (2 * m) -
          4 * C.r * C.y = 0 := by
    dsimp only [ScalarContactChart.y, ScalarContactChart.r]
    rw [hfactor]
    dsimp [m]
    field_simp [hg_pos.ne']
    dsimp [g, h]
    ring
  have hlead : 0 < 1 + C.y + C.r := C.denominator_pos
  by_contra hnot
  have hlt : C.s < 2 * m := lt_of_not_ge hnot
  have hsum_pos : 0 < (1 + C.y + C.r) * (C.s + 2 * m) + 4 * C.r := by
    have hsump : 0 < C.s + 2 * m := by nlinarith [C.s_nonneg]
    exact add_pos (mul_pos hlead hsump) (mul_pos (by norm_num) C.r_pos)
  have hdiff :
      (1 + C.y + C.r) * C.s ^ 2 + 4 * C.r * C.s - 4 * C.r * C.y -
        ((1 + C.y + C.r) * (2 * m) ^ 2 + 4 * C.r * (2 * m) -
          4 * C.r * C.y) =
        (C.s - 2 * m) * ((1 + C.y + C.r) * (C.s + 2 * m) + 4 * C.r) := by
    ring
  have hquad_neg :
      (1 + C.y + C.r) * C.s ^ 2 + 4 * C.r * C.s - 4 * C.r * C.y < 0 := by
    rw [hroot, sub_zero] at hdiff
    rw [hdiff]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hsum_pos
  linarith

theorem strictProxy_geMinAtSeamEndpoints :
    StrictProxyGeMinAtSeamEndpoints := by
  intro C hx hpi
  have hp7 : StrictProxyMonotoneInContactMass := strictProxy_monotoneInContactMass
  have hp8 : StrictProxyConcaveInPrior := strictProxy_concaveInPrior
  have hx1 : C.x < 1 := lt_trans hx (by norm_num)
  have hm : 2 * contactMidpoint C.x ≤ C.s := by
    simpa [contactMidpoint, contactDenominator] using ScalarContactChart.two_mul_contactMidpoint_le_s C
  have hsxy : C.s ≤ C.x ^ 2 := by
    simpa only [ScalarContactChart.y] using C.s_le_y
  have hlohalf : 3 * C.x ^ 4 ≤ (1 / 2 : ℝ) := hpi.trans C.pi_le_half
  have hlo0 : 0 ≤ 3 * C.x ^ 4 := by positivity
  have hconc := hp8 C.x_pos hx1 hm hsxy
  have hsub : Icc (3 * C.x ^ 4) (1 / 2) ⊆ Icc (0 : ℝ) (1 / 2) := by
    intro z hz
    exact ⟨hlo0.trans hz.1, hz.2⟩
  have hconc' := hconc.subset hsub (convex_Icc _ _)
  have hpi_mem : C.pi ∈ Icc (3 * C.x ^ 4) (1 / 2) := ⟨hpi, C.pi_le_half⟩
  have hendpoint :
      min (strictProxy C.x (3 * C.x ^ 4) C.s) (strictProxy C.x (1 / 2) C.s) ≤
        strictProxy C.x C.pi C.s := by
    exact hconc'.min_le_of_mem_Icc
      ⟨le_rfl, hlohalf⟩ ⟨hlohalf, le_rfl⟩ hpi_mem
  have hs_mem : C.s ∈ Icc (2 * contactMidpoint C.x) (C.x ^ 2) := ⟨hm, hsxy⟩
  have hp7lo := hp7 C.x_pos hx le_rfl hlohalf
  have hp7hi := hp7 C.x_pos hx hlohalf le_rfl
  have hlo_mono :
      strictProxy C.x (3 * C.x ^ 4) (2 * contactMidpoint C.x) ≤
        strictProxy C.x (3 * C.x ^ 4) C.s :=
    hp7lo ⟨le_rfl, hm.trans hsxy⟩ hs_mem hm
  have hhi_mono :
      strictProxy C.x (1 / 2) (2 * contactMidpoint C.x) ≤ strictProxy C.x (1 / 2) C.s :=
    hp7hi ⟨le_rfl, hm.trans hsxy⟩ hs_mem hm
  exact (min_le_min hlo_mono hhi_mono).trans hendpoint

/-! ## Binary stochastic data processing -/

theorem pairEntropy_scale {c u v : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    pairEntropy (c * u) (c * v) = c * pairEntropy u v := by
  by_cases hc0 : c = 0
  · subst c
    simp
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  by_cases hs0 : u + v = 0
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    subst u
    subst v
    simp
  have hspos : 0 < u + v := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm hs0)
  have hcspos : 0 < c * u + c * v := by nlinarith
  rw [pairEntropy_eq_mass_mul_binEntropy (mul_nonneg hc hu) (mul_nonneg hc hv) hcspos,
    pairEntropy_eq_mass_mul_binEntropy hu hv hspos]
  have hratio : c * u / (c * u + c * v) = u / (u + v) := by
    field_simp [hc0, hs0]
  rw [hratio]
  ring

/-- The scalar Jensen gap for binary entropy in natural-log units. -/
noncomputable def binaryEntropyJensenGap (pi u v : ℝ) : ℝ :=
  Real.binEntropy ((1 - pi) * u + pi * v) -
    ((1 - pi) * Real.binEntropy u + pi * Real.binEntropy v)

/-- Success probability after a binary stochastic channel. -/
def binaryChannel (a b t : ℝ) : ℝ := (1 - t) * a + t * b

private theorem pairEntropy_four_cells (x00 x01 x10 x11 : ℝ) :
    pairEntropy (x00 + x01) (x10 + x11) +
        pairEntropy x00 x01 + pairEntropy x10 x11 =
      pairEntropy (x00 + x10) (x01 + x11) +
        pairEntropy x00 x10 + pairEntropy x01 x11 := by
  unfold pairEntropy
  ring

theorem binaryEntropyJensenGap_eq_pairEntropy
    {pi u v : ℝ} (hpi : pi ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 1) :
    binaryEntropyJensenGap pi u v =
      Real.binEntropy pi -
        (pairEntropy ((1 - pi) * (1 - u)) (pi * (1 - v)) +
          pairEntropy ((1 - pi) * u) (pi * v)) := by
  have h1pi : 0 ≤ 1 - pi := by linarith [hpi.2]
  have h1u : 0 ≤ 1 - u := by linarith [hu.2]
  have h1v : 0 ≤ 1 - v := by linarith [hv.2]
  have hbe (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      pairEntropy (1 - t) t = Real.binEntropy t := by
    have ht0 : 0 ≤ t := ht.1
    have hct0 : 0 ≤ 1 - t := by linarith [ht.2]
    have hs : 0 < (1 - t) + t := by norm_num
    rw [pairEntropy_eq_mass_mul_binEntropy hct0 ht0 hs]
    norm_num
  have hm : (1 - pi) * u + pi * v ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg h1pi hu.1) (mul_nonneg hpi.1 hv.1)
    · nlinarith [mul_nonneg h1pi h1u, mul_nonneg hpi.1 h1v]
  have hmixcomp : 1 - ((1 - pi) * u + pi * v) =
      (1 - pi) * (1 - u) + pi * (1 - v) := by ring
  have hrow0 : pairEntropy ((1 - pi) * (1 - u)) ((1 - pi) * u) =
      (1 - pi) * Real.binEntropy u := by
    rw [pairEntropy_scale h1pi h1u hu.1, hbe u hu]
  have hrow1 : pairEntropy (pi * (1 - v)) (pi * v) =
      pi * Real.binEntropy v := by
    rw [pairEntropy_scale hpi.1 h1v hv.1, hbe v hv]
  have hrowsum0 : (1 - pi) * (1 - u) + (1 - pi) * u = 1 - pi := by ring
  have hrowsum1 : pi * (1 - v) + pi * v = pi := by ring
  have hfour := pairEntropy_four_cells
    ((1 - pi) * (1 - u)) ((1 - pi) * u) (pi * (1 - v)) (pi * v)
  rw [hrowsum0, hrowsum1, hbe pi hpi, hrow0, hrow1] at hfour
  have hcolsum1 : (1 - pi) * u + pi * v = (1 - pi) * u + pi * v := rfl
  rw [← hmixcomp, hbe _ hm] at hfour
  unfold binaryEntropyJensenGap
  linarith

theorem binaryEntropyJensenGap_binaryChannel_le
    {pi u v a b : ℝ}
    (hpi : pi ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    binaryEntropyJensenGap pi (binaryChannel a b u) (binaryChannel a b v) ≤
      binaryEntropyJensenGap pi u v := by
  have h1pi : 0 ≤ 1 - pi := by linarith [hpi.2]
  have h1u : 0 ≤ 1 - u := by linarith [hu.2]
  have h1v : 0 ≤ 1 - v := by linarith [hv.2]
  have h1a : 0 ≤ 1 - a := by linarith [ha.2]
  have h1b : 0 ≤ 1 - b := by linarith [hb.2]
  have hpost (t : ℝ) (ht : t ∈ Set.Icc 0 1) : binaryChannel a b t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · unfold binaryChannel
      exact add_nonneg (mul_nonneg (by linarith [ht.2]) ha.1) (mul_nonneg ht.1 hb.1)
    · unfold binaryChannel
      nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ 1 - t) h1a,
        mul_nonneg ht.1 h1b]
  have hpu := hpost u hu
  have hpv := hpost v hv
  let x00 := (1 - pi) * (1 - u)
  let x01 := (1 - pi) * u
  let x10 := pi * (1 - v)
  let x11 := pi * v
  have hx00 : 0 ≤ x00 := mul_nonneg h1pi h1u
  have hx01 : 0 ≤ x01 := mul_nonneg h1pi hu.1
  have hx10 : 0 ≤ x10 := mul_nonneg hpi.1 h1v
  have hx11 : 0 ≤ x11 := mul_nonneg hpi.1 hv.1
  have hzero := pairEntropy_superadditive
    (mul_nonneg h1a hx00) (mul_nonneg h1a hx10)
    (mul_nonneg h1b hx01) (mul_nonneg h1b hx11)
  have hone := pairEntropy_superadditive
    (mul_nonneg ha.1 hx00) (mul_nonneg ha.1 hx10)
    (mul_nonneg hb.1 hx01) (mul_nonneg hb.1 hx11)
  rw [pairEntropy_scale h1a hx00 hx10, pairEntropy_scale h1b hx01 hx11] at hzero
  rw [pairEntropy_scale ha.1 hx00 hx10, pairEntropy_scale hb.1 hx01 hx11] at hone
  have hcond :
      pairEntropy x00 x10 + pairEntropy x01 x11 ≤
        pairEntropy ((1 - pi) * (1 - binaryChannel a b u))
          (pi * (1 - binaryChannel a b v)) +
        pairEntropy ((1 - pi) * binaryChannel a b u)
          (pi * binaryChannel a b v) := by
    have hy00 : (1 - a) * x00 + (1 - b) * x01 =
        (1 - pi) * (1 - binaryChannel a b u) := by
      dsimp [x00, x01, binaryChannel]
      ring
    have hy10 : (1 - a) * x10 + (1 - b) * x11 =
        pi * (1 - binaryChannel a b v) := by
      dsimp [x10, x11, binaryChannel]
      ring
    have hy01 : a * x00 + b * x01 = (1 - pi) * binaryChannel a b u := by
      dsimp [x00, x01, binaryChannel]
      ring
    have hy11 : a * x10 + b * x11 = pi * binaryChannel a b v := by
      dsimp [x10, x11, binaryChannel]
      ring
    rw [hy00, hy10] at hzero
    rw [hy01, hy11] at hone
    linarith
  rw [binaryEntropyJensenGap_eq_pairEntropy hpi hpu hpv,
    binaryEntropyJensenGap_eq_pairEntropy hpi hu hv]
  dsimp [x00, x01, x10, x11] at hcond
  linarith

theorem scalarSingletonReward_binaryChannel_le
    {pi u v a b : ℝ}
    (hpi : pi ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hcond : (1 - pi) * Real.binEntropy u + pi * Real.binEntropy v ≤
      (1 - pi) * Real.binEntropy (binaryChannel a b u) +
        pi * Real.binEntropy (binaryChannel a b v)) :
    scalarSingletonReward pi (binaryChannel a b u) (binaryChannel a b v) ≤
      scalarSingletonReward pi u v := by
  have hdpi := binaryEntropyJensenGap_binaryChannel_le hpi hu hv ha hb
  unfold binaryEntropyJensenGap at hdpi
  unfold scalarSingletonReward
  linarith

/-! ## The fixed two-fifths comparison -/

theorem binEntropy_sub_mul_le_log_one_add_exp_neg
    {w lambda : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy w - lambda * w ≤ Real.log (1 + Real.exp (-lambda)) := by
  rcases eq_or_lt_of_le hw.1 with rfl | hw0
  · simp
    exact Real.log_nonneg (le_add_of_nonneg_right (Real.exp_pos _).le)
  rcases eq_or_lt_of_le (sub_nonneg.mpr hw.2) with h | hw1
  · have : w = 1 := by linarith
    subst w
    simp
    have he : Real.exp (-lambda) < 1 + Real.exp (-lambda) := by linarith
    have hsum : 0 < 1 + Real.exp (-lambda) := by positivity
    have hl := Real.strictMonoOn_log (Real.exp_pos _) hsum he
    exact (by simpa only [Real.log_exp] using hl.le)
  · have hw1' : w < 1 := by linarith
    have hpos1 : 0 < Real.exp (-lambda) / w := div_pos (Real.exp_pos _) hw0
    have hpos2 : 0 < 1 / (1 - w) := div_pos zero_lt_one (sub_pos.mpr hw1')
    have hj := strictConcaveOn_log_Ioi.concaveOn.2 hpos1 hpos2 hw.1 (sub_nonneg.mpr hw.2)
      (by ring : w + (1 - w) = 1)
    have harg : w * (Real.exp (-lambda) / w) + (1 - w) * (1 / (1 - w)) =
        1 + Real.exp (-lambda) := by field_simp [hw0.ne', sub_ne_zero.mpr (ne_of_lt hw1')]; ring
    simp only [smul_eq_mul] at hj
    rw [harg] at hj
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    unfold Real.negMulLog
    rw [Real.log_div (Real.exp_pos _).ne' hw0.ne', Real.log_exp] at hj
    rw [one_div, Real.log_inv] at hj
    linarith

/-! ## Equal-mass seam and posterior order -/

theorem exposedPhaseReward_at_equalMass_nonneg
    (C : ScalarContactChart) (hC : ScalarContactChart.StrictInterior C)
    (hreward : 0 ≤ ScalarContactChart.phaseReward C) :
    0 ≤ exposedPhaseReward C (2 * ScalarContactChart.contactMidpoint C) := by
  have hleft : 2 * ScalarContactChart.contactMidpoint C ∈ Icc (2 * ScalarContactChart.contactMidpoint C) C.y := by
    exact ⟨le_rfl, hC.2.2.1.trans (le_of_lt hC.2.2.2.1)⟩
  have hs : C.s ∈ Icc (2 * ScalarContactChart.contactMidpoint C) C.y := by
    exact ⟨hC.2.2.1, le_of_lt hC.2.2.2.1⟩
  have hanti := exposedPhaseReward_strictAntiOn C hC
  have hle : exposedPhaseReward C C.s ≤ exposedPhaseReward C (2 * ScalarContactChart.contactMidpoint C) :=
    (hanti.le_iff_ge hs hleft).2 hC.2.2.1
  rw [exposedPhaseReward_at_contact] at hle
  exact hreward.trans hle

/-- The equal-mass point of a contact fibre, retaining the original prior. -/
def ScalarContactChart.equalMassChart (C : ScalarContactChart) : ScalarContactChart where
  x := C.x
  pi := C.pi
  lowMass := ScalarContactChart.contactMidpoint C
  highMass := ScalarContactChart.contactMidpoint C
  x_pos := C.x_pos
  x_le_one := C.x_le_one
  pi_nonneg := C.pi_nonneg
  pi_le_half := C.pi_le_half
  lowMass_nonneg := (ScalarContactChart.contactMidpoint_pos C).le
  lowMass_le_highMass := le_rfl
  contact := by
    have h := ScalarContactChart.contactMidpoint_contact C
    dsimp only [ScalarContactChart.y, ScalarContactChart.r] at h ⊢
    nlinarith

theorem exposedPhaseReward_at_equalMass_eq_scaled_reward
    (C : ScalarContactChart) :
    exposedPhaseReward C (2 * ScalarContactChart.contactMidpoint C) =
      (ScalarContactChart.equalMassChart C).norm * scalarSingletonReward (ScalarContactChart.equalMassChart C).pi
        ((ScalarContactChart.equalMassChart C).r / (ScalarContactChart.equalMassChart C).norm)
        (1 / (ScalarContactChart.equalMassChart C).norm) := by
  rw [norm_mul_scalarSingletonReward_eq_splitEntropy]
  simp only [exposedPhaseReward, splitEntropy, pairEntropy, ScalarContactChart.equalMassChart,
    ScalarContactChart.norm, ScalarContactChart.r, ScalarContactChart.s,
    ScalarContactChart.e, ScalarContactChart.ell]
  ring

/-- The lower posterior at the equal-mass contact seam. -/
def seamLowerPosterior (x : ℝ) : ℝ := x ^ 4 / (1 + x ^ 4 + 2 * contactMidpoint x)

/-- The upper posterior at the equal-mass contact seam. -/
def seamUpperPosterior (x : ℝ) : ℝ := 1 / (1 + x ^ 4 + 2 * contactMidpoint x)

private def lowerPosteriorCofactor (x y : ℝ) : ℝ :=
  2*x^5*y^3+x^5*y^2+x^5*y+x^5+2*x^4*y^4+3*x^4*y^3+2*x^4*y^2+
  2*x^4*y+x^4+2*x^3*y^5+3*x^3*y^4+4*x^3*y^3+3*x^3*y^2+2*x^3*y+x^3+
  x^2*y^5+2*x^2*y^4+3*x^2*y^3+2*x^2*y^2+x^2*y+x*y^5+2*x*y^4+
  2*x*y^3+x*y^2+y^5+y^4+y^3

private def upperPosteriorCofactor (x y : ℝ) : ℝ :=
  x^5*y^2+x^5*y+x^5+x^4*y^3+2*x^4*y^2+2*x^4*y+x^4+x^3*y^4+
  2*x^3*y^3+3*x^3*y^2+2*x^3*y+x^3+x^2*y^5+2*x^2*y^4+3*x^2*y^3+
  4*x^2*y^2+3*x^2*y+2*x^2+x*y^5+2*x*y^4+2*x*y^3+3*x*y^2+2*x*y+
  y^5+y^4+y^3+2*y^2

private lemma seamNormalization_pos {x : ℝ} (hx : 0 < x) :
    0 < 1 + x ^ 4 + 2 * contactMidpoint x := by
  unfold contactMidpoint contactDenominator
  positivity

theorem seamLowerPosterior_monotoneOn : MonotoneOn seamLowerPosterior (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  have hdx := seamNormalization_pos hx
  have hdy := seamNormalization_pos hy
  rw [seamLowerPosterior, seamLowerPosterior, div_le_div_iff₀ hdx hdy]
  have hfac : 0 ≤ lowerPosteriorCofactor x y := by unfold lowerPosteriorCofactor; positivity
  have hdx' : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1)]
  have hdy' : 0 < 1 + y + y ^ 2 := by nlinarith [sq_nonneg (y + 1)]
  have hid :
      x ^ 4 * (1 + y ^ 4 + 2 * contactMidpoint y) -
        y ^ 4 * (1 + x ^ 4 + 2 * contactMidpoint x) =
          (x - y) * lowerPosteriorCofactor x y /
            ((1 + x + x ^ 2) * (1 + y + y ^ 2)) := by
    unfold contactMidpoint contactDenominator lowerPosteriorCofactor
    field_simp [hdx'.ne', hdy'.ne']
    ring
  have hden : 0 < (1 + x + x ^ 2) * (1 + y + y ^ 2) := mul_pos hdx' hdy'
  have hnonpos : (x - y) * lowerPosteriorCofactor x y /
      ((1 + x + x ^ 2) * (1 + y + y ^ 2)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hxy) hfac) hden.le
  linarith

theorem seamUpperPosterior_antitoneOn : AntitoneOn seamUpperPosterior (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  have hdx := seamNormalization_pos hx
  have hdy := seamNormalization_pos hy
  rw [seamUpperPosterior, seamUpperPosterior]
  apply one_div_le_one_div_of_le hdx
  have hfac : 0 ≤ upperPosteriorCofactor x y := by unfold upperPosteriorCofactor; positivity
  have hid :
      (1 + y ^ 4 + 2 * contactMidpoint y) - (1 + x ^ 4 + 2 * contactMidpoint x) =
        (y - x) * upperPosteriorCofactor x y /
          ((1 + x + x^2) * (1 + y + y^2)) := by
    unfold contactMidpoint contactDenominator upperPosteriorCofactor
    field_simp
    ring
  have hdx' : 0 < 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1)]
  have hdy' : 0 < 1 + y + y ^ 2 := by nlinarith [sq_nonneg (y + 1)]
  have hden : 0 < (1 + x + x^2) * (1 + y + y^2) := mul_pos hdx' hdy'
  have : 0 ≤ (y - x) * upperPosteriorCofactor x y /
      ((1 + x + x^2) * (1 + y + y^2)) := div_nonneg (mul_nonneg (sub_nonneg.mpr hxy) hfac) hden.le
  linarith

theorem seamLowerPosterior_bounds {x : ℝ} (hx : 2 / 5 ≤ x) (hx1 : x < 1) :
    (624 / 26999 : ℝ) ≤ seamLowerPosterior x ∧ seamLowerPosterior x ≤ 3 / 8 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlo := seamLowerPosterior_monotoneOn (show (2 / 5 : ℝ) ∈ Ioi 0 by norm_num) hx0 hx
  have hhi := seamLowerPosterior_monotoneOn hx0 (show (1 : ℝ) ∈ Ioi 0 by norm_num) hx1.le
  have hu0 : seamLowerPosterior (2 / 5) = (624 / 26999 : ℝ) := by
    unfold seamLowerPosterior contactMidpoint contactDenominator
    norm_num
  have hu1 : seamLowerPosterior 1 = (3 / 8 : ℝ) := by
    unfold seamLowerPosterior contactMidpoint contactDenominator
    norm_num
  simpa [hu0, hu1] using And.intro hlo hhi

theorem seamUpperPosterior_bounds {x : ℝ} (hx : 2 / 5 ≤ x) (hx1 : x < 1) :
    (3 / 8 : ℝ) ≤ seamUpperPosterior x ∧ seamUpperPosterior x ≤ 24375 / 26999 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlo := seamUpperPosterior_antitoneOn hx0 (show (1 : ℝ) ∈ Ioi 0 by norm_num) hx1.le
  have hhi := seamUpperPosterior_antitoneOn (show (2 / 5 : ℝ) ∈ Ioi 0 by norm_num) hx0 hx
  have hv0 : seamUpperPosterior (2 / 5) = (24375 / 26999 : ℝ) := by
    unfold seamUpperPosterior contactMidpoint contactDenominator
    norm_num
  have hv1 : seamUpperPosterior 1 = (3 / 8 : ℝ) := by
    unfold seamUpperPosterior contactMidpoint contactDenominator
    norm_num
  simpa [hv0, hv1] using And.intro hlo hhi

theorem seamConditionalEntropy_comparison {x pi : ℝ}
    (hx : 2 / 5 ≤ x) (hx1 : x < 1) (hpi : pi ∈ Icc 0 1) :
    (1 - pi) * Real.binEntropy (624 / 26999) +
        pi * Real.binEntropy (24375 / 26999) ≤
      (1 - pi) * Real.binEntropy (seamLowerPosterior x) +
        pi * Real.binEntropy (seamUpperPosterior x) := by
  obtain ⟨hu0, hu1⟩ := seamLowerPosterior_bounds hx hx1
  obtain ⟨hv1, hv0⟩ := seamUpperPosterior_bounds hx hx1
  have hu : Real.binEntropy (624 / 26999) ≤ Real.binEntropy (seamLowerPosterior x) := by
    apply Real.binEntropy_strictMonoOn.monotoneOn
    · constructor <;> norm_num
    · exact ⟨le_trans (by norm_num) hu0, le_trans hu1 (by norm_num)⟩
    · exact hu0
  have hv : Real.binEntropy (24375 / 26999) ≤ Real.binEntropy (seamUpperPosterior x) := by
    by_cases hhalf : 1 / 2 ≤ seamUpperPosterior x
    · apply Real.binEntropy_strictAntiOn.antitoneOn
      · exact ⟨by simpa only [one_div] using hhalf, le_trans hv0 (by norm_num)⟩
      · constructor <;> norm_num
      · exact hv0
    · have hbelow : seamUpperPosterior x ≤ 1 / 2 := le_of_not_ge hhalf
      have h38 : Real.binEntropy (3 / 8) ≤ Real.binEntropy (seamUpperPosterior x) := by
        apply Real.binEntropy_strictMonoOn.monotoneOn
        · constructor <;> norm_num
        · exact ⟨le_trans (by norm_num) hv1, by simpa only [one_div] using hbelow⟩
        · exact hv1
      have hend : Real.binEntropy (24375 / 26999) ≤ Real.binEntropy (3 / 8) := by
        rw [← Real.binEntropy_one_sub (24375 / 26999)]
        apply Real.binEntropy_strictMonoOn.monotoneOn
        · constructor <;> norm_num
        · constructor <;> norm_num
        · norm_num
      exact hend.trans h38
  exact add_le_add (mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hpi.2))
    (mul_le_mul_of_nonneg_left hv hpi.1)

/-! ## The explicit binary channel -/

/-- The equal-mass seam normalization at a chart scale. -/
def seamNormalizationAtChart (C : ScalarContactChart) : ℝ :=
  1 + C.x ^ 4 + 2 * contactMidpoint C.x

/-- The lower posterior at the moving chart scale. -/
def seamLowerPosteriorAtChart (C : ScalarContactChart) : ℝ := C.x ^ 4 / seamNormalizationAtChart C

/-- The upper posterior at the moving chart scale. -/
def seamUpperPosteriorAtChart (C : ScalarContactChart) : ℝ := 1 / seamNormalizationAtChart C

/-- The lower posterior at the two-fifths seam. -/
def twoFifthsLowerPosterior : ℝ := 624 / 26999

/-- The upper posterior at the two-fifths seam. -/
def twoFifthsUpperPosterior : ℝ := 24375 / 26999

/-- Slope of the affine channel from the fixed seam to the moving seam. -/
def seamChannelSlope (C : ScalarContactChart) : ℝ :=
  (seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C) / (twoFifthsUpperPosterior - twoFifthsLowerPosterior)

/-- Channel success probability given input zero. -/
def seamChannelZero (C : ScalarContactChart) : ℝ :=
  seamLowerPosteriorAtChart C - seamChannelSlope C * twoFifthsLowerPosterior

/-- Channel success probability given input one. -/
def seamChannelOne (C : ScalarContactChart) : ℝ :=
  seamUpperPosteriorAtChart C + seamChannelSlope C * (1 - twoFifthsUpperPosterior)

theorem seamPosterior_gap_pos (C : ScalarContactChart)
    (hC : ScalarContactChart.StrictInterior C) :
    0 < seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C := by
  have hx1 : C.x < 1 := hC.1
  have hr1 : C.x ^ 4 < 1 := pow_lt_one₀ C.x_pos.le hx1 (by norm_num)
  have hd : 0 < contactDenominator C.x := by
    unfold contactDenominator
    nlinarith [sq_nonneg C.x]
  have hm0 : 0 < contactMidpoint C.x := by
    unfold contactMidpoint
    exact div_pos (pow_pos C.x_pos 3) hd
  have hQ : 0 < seamNormalizationAtChart C := by
    unfold seamNormalizationAtChart
    nlinarith [pow_pos C.x_pos 4]
  unfold seamLowerPosteriorAtChart seamUpperPosteriorAtChart
  rw [div_sub_div_same]
  exact div_pos (sub_pos.mpr hr1) hQ

theorem twoFifthsPosterior_gap_pos : 0 < twoFifthsUpperPosterior - twoFifthsLowerPosterior := by
  norm_num [twoFifthsUpperPosterior, twoFifthsLowerPosterior]

theorem seamLowerPosterior_div_gap (C : ScalarContactChart)
    (hC : ScalarContactChart.StrictInterior C) :
    seamLowerPosteriorAtChart C / (seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C) = C.x ^ 4 / (1 - C.x ^ 4) := by
  have hd : 0 < contactDenominator C.x := by
    unfold contactDenominator
    nlinarith [sq_nonneg C.x]
  have hm0 : 0 < contactMidpoint C.x := by
    unfold contactMidpoint
    exact div_pos (pow_pos C.x_pos 3) hd
  have hQpos : 0 < seamNormalizationAtChart C := by
    unfold seamNormalizationAtChart
    nlinarith [pow_pos C.x_pos 4]
  have hQ : seamNormalizationAtChart C ≠ 0 := ne_of_gt hQpos
  have hr : 1 - C.x ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr
    (pow_lt_one₀ C.x_pos.le hC.1 (by norm_num)))
  have hdiff : seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C = (1 - C.x ^ 4) / seamNormalizationAtChart C := by
    unfold seamLowerPosteriorAtChart seamUpperPosteriorAtChart
    rw [div_sub_div_same]
  rw [hdiff]
  unfold seamLowerPosteriorAtChart
  field_simp

theorem seamUpperComplement_div_gap (C : ScalarContactChart)
    (hC : ScalarContactChart.StrictInterior C) :
    (1 - seamUpperPosteriorAtChart C) / (seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C) =
      (C.x ^ 4 + 2 * contactMidpoint C.x) / (1 - C.x ^ 4) := by
  have hd : 0 < contactDenominator C.x := by
    unfold contactDenominator
    nlinarith [sq_nonneg C.x]
  have hm0 : 0 < contactMidpoint C.x := by
    unfold contactMidpoint
    exact div_pos (pow_pos C.x_pos 3) hd
  have hQpos : 0 < seamNormalizationAtChart C := by
    unfold seamNormalizationAtChart
    nlinarith [pow_pos C.x_pos 4]
  have hQ : seamNormalizationAtChart C ≠ 0 := ne_of_gt hQpos
  have hr : 1 - C.x ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr
    (pow_lt_one₀ C.x_pos.le hC.1 (by norm_num)))
  have hone : 1 - seamUpperPosteriorAtChart C =
      (C.x ^ 4 + 2 * contactMidpoint C.x) / seamNormalizationAtChart C := by
    unfold seamUpperPosteriorAtChart
    field_simp [hQ]
    unfold seamNormalizationAtChart
    ring
  have hdiff : seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C = (1 - C.x ^ 4) / seamNormalizationAtChart C := by
    unfold seamLowerPosteriorAtChart seamUpperPosteriorAtChart
    rw [div_sub_div_same]
  rw [hone, hdiff]
  field_simp

theorem binaryChannel_mem_Icc_of_twoFifths_le (C : ScalarContactChart)
    (hC : ScalarContactChart.StrictInterior C) (hx : 2 / 5 ≤ C.x) :
    seamChannelZero C ∈ Set.Icc 0 1 ∧ seamChannelOne C ∈ Set.Icc 0 1 := by
  have hx0 : 0 < C.x := C.x_pos
  have hx1 : C.x < 1 := hC.1
  have hr0 : 0 ≤ C.x ^ 4 := by positivity
  have hr1 : C.x ^ 4 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hrge : (2 / 5 : ℝ) ^ 4 ≤ C.x ^ 4 := by
    nlinarith [sq_nonneg C.x, sq_nonneg (C.x ^ 2 - (2 / 5 : ℝ) ^ 2)]
  have hd34 : 0 < contactDenominator C.x := by
    unfold contactDenominator
    positivity
  have hm0 : 0 < contactMidpoint C.x := by
    unfold contactMidpoint
    positivity
  have hmge : (8 / 195 : ℝ) ≤ contactMidpoint C.x := by
    unfold contactMidpoint
    apply (le_div_iff₀ hd34).2
    have hfirst : 0 ≤ 5 * C.x - 2 := by norm_num at hx ⊢; linarith
    have hsecond : 0 ≤ 39 * C.x ^ 2 + 14 * C.x + 4 := by
      nlinarith [sq_nonneg C.x]
    have hfac : 0 ≤ (5 * C.x - 2) *
        (39 * C.x ^ 2 + 14 * C.x + 4) := mul_nonneg hfirst hsecond
    unfold contactDenominator
    norm_num
    nlinarith [hfac]
  have hQ : 0 < seamNormalizationAtChart C := by
    unfold seamNormalizationAtChart
    nlinarith [hm0, pow_pos hx0 4]
  have hu0 : 0 ≤ seamLowerPosteriorAtChart C := div_nonneg hr0 hQ.le
  have hu1 : seamLowerPosteriorAtChart C ≤ 1 := by
    unfold seamLowerPosteriorAtChart
    rw [div_le_iff₀ hQ]
    unfold seamNormalizationAtChart
    nlinarith [hm0]
  have hv0 : 0 ≤ seamUpperPosteriorAtChart C := div_nonneg (by norm_num) hQ.le
  have hv1 : seamUpperPosteriorAtChart C ≤ 1 := by
    unfold seamUpperPosteriorAtChart
    rw [div_le_iff₀ hQ]
    unfold seamNormalizationAtChart
    nlinarith [hm0, hr0]
  have hdelta : 0 < seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C := seamPosterior_gap_pos C hC
  have hdelta0 : 0 < twoFifthsUpperPosterior - twoFifthsLowerPosterior := twoFifthsPosterior_gap_pos
  have hk0 : 0 ≤ seamChannelSlope C := by
    unfold seamChannelSlope
    positivity
  have hsu0 : 0 ≤ twoFifthsLowerPosterior := by norm_num [twoFifthsLowerPosterior]
  have hsv1 : twoFifthsUpperPosterior ≤ 1 := by norm_num [twoFifthsUpperPosterior]
  have hlowerRatio : twoFifthsLowerPosterior / (twoFifthsUpperPosterior - twoFifthsLowerPosterior) ≤
      seamLowerPosteriorAtChart C / (seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C) := by
    rw [seamLowerPosterior_div_gap C hC]
    apply (div_le_div_iff₀ hdelta0 (sub_pos.mpr hr1)).2
    norm_num [twoFifthsLowerPosterior, twoFifthsUpperPosterior] at hrge ⊢
    nlinarith
  have hupperRatio : (1 - twoFifthsUpperPosterior) / (twoFifthsUpperPosterior - twoFifthsLowerPosterior) ≤
      (1 - seamUpperPosteriorAtChart C) / (seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C) := by
    rw [seamUpperComplement_div_gap C hC]
    apply (div_le_div_iff₀ hdelta0 (sub_pos.mpr hr1)).2
    norm_num [twoFifthsLowerPosterior, twoFifthsUpperPosterior] at hrge hmge ⊢
    nlinarith
  constructor
  · constructor
    · unfold seamChannelZero seamChannelSlope
      have hscaled := (div_le_div_iff₀ hdelta0 hdelta).1 hlowerRatio
      rw [sub_nonneg, div_mul_eq_mul_div]
      exact (div_le_iff₀ hdelta0).2 (by nlinarith [hscaled])
    · unfold seamChannelZero
      nlinarith [mul_nonneg hk0 hsu0]
  · constructor
    · unfold seamChannelOne
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hsv1)]
    · unfold seamChannelOne seamChannelSlope
      have hscaled := (div_le_div_iff₀ hdelta0 hdelta).1 hupperRatio
      have hquot : (seamUpperPosteriorAtChart C - seamLowerPosteriorAtChart C) / (twoFifthsUpperPosterior - twoFifthsLowerPosterior) * (1 - twoFifthsUpperPosterior) ≤
          1 - seamUpperPosteriorAtChart C := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hdelta0).2
        nlinarith [hscaled]
      linarith

theorem binaryChannel_twoFifthsLowerPosterior (C : ScalarContactChart) :
    binaryChannel (seamChannelZero C) (seamChannelOne C) twoFifthsLowerPosterior = seamLowerPosteriorAtChart C := by
  have hd : twoFifthsUpperPosterior - twoFifthsLowerPosterior ≠ 0 := ne_of_gt twoFifthsPosterior_gap_pos
  unfold binaryChannel seamChannelZero seamChannelOne seamChannelSlope
  field_simp
  ring

theorem binaryChannel_twoFifthsUpperPosterior (C : ScalarContactChart) :
    binaryChannel (seamChannelZero C) (seamChannelOne C) twoFifthsUpperPosterior = seamUpperPosteriorAtChart C := by
  have hd : twoFifthsUpperPosterior - twoFifthsLowerPosterior ≠ 0 := ne_of_gt twoFifthsPosterior_gap_pos
  unfold binaryChannel seamChannelZero seamChannelOne seamChannelSlope
  field_simp
  ring

/-! ## Excluding contact scales at or above two fifths -/

theorem binEntropy_twoFifthsLowerPosterior_gt :
    (1 : ℝ) / 10 < Real.binEntropy ((624 : ℝ) / 26999) := by
  have hl := oddLogPartialSum_le_logRatio 10
    (t := (26375 : ℝ) / 27623) (by norm_num) (by norm_num)
  have hlog : (7 / 2 : ℝ) < Real.log (1 / ((624 : ℝ) / 26999)) := by
    norm_num [oddLogPartialSum] at hl ⊢
    linarith
  have hb := pairEntropy_unit_lower (z := (624 : ℝ) / 26999) (by norm_num) (by norm_num)
  rw [pairEntropy_eq_mass_mul_binEntropy
    (by norm_num) (by norm_num) (by norm_num)] at hb
  norm_num at hb ⊢
  nlinarith

theorem binEntropy_twoFifthsUpperPosterior_gt :
    (3 : ℝ) / 10 < Real.binEntropy ((24375 : ℝ) / 26999) := by
  rw [show ((24375 : ℝ) / 26999) = 1 - (2624 : ℝ) / 26999 by norm_num,
    Real.binEntropy_one_sub]
  have hl := oddLogPartialSum_le_logRatio 8
    (t := (24375 : ℝ) / 29623) (by norm_num) (by norm_num)
  have hlog : (9 / 4 : ℝ) < Real.log (1 / ((2624 : ℝ) / 26999)) := by
    norm_num [oddLogPartialSum] at hl ⊢
    linarith
  have hb := pairEntropy_unit_lower (z := (2624 : ℝ) / 26999) (by norm_num) (by norm_num)
  rw [pairEntropy_eq_mass_mul_binEntropy
    (by norm_num) (by norm_num) (by norm_num)] at hb
  norm_num at hb ⊢
  nlinarith

theorem singletonReward_twoFifthsSeam_neg
    {pi : ℝ} (hpi : pi ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    scalarSingletonReward pi ((624 : ℝ) / 26999) ((24375 : ℝ) / 26999) < 0 := by
  rcases positivePhaseTwoFifthsGateLedger with
    ⟨hu0, huv, hlambda0, hlambda1, hexp, hlog, hlambdau⟩
  let u : ℝ := (624 : ℝ) / 26999
  let v : ℝ := (24375 : ℝ) / 26999
  let lambda : ℝ := (107996 : ℝ) / 118755
  have hu_mem : u ∈ Icc (0 : ℝ) 1 := by dsimp [u]; norm_num
  have hv_mem : v ∈ Icc (0 : ℝ) 1 := by dsimp [v]; norm_num
  have hpi01 : pi ∈ Icc (0 : ℝ) 1 := ⟨hpi.1, hpi.2.trans (by norm_num)⟩
  have hw : (1 - pi) * u + pi * v ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (by linarith [hpi.2]) hu_mem.1)
        (mul_nonneg hpi.1 hv_mem.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hpi01.2) (sub_nonneg.mpr hu_mem.2),
        mul_nonneg hpi01.1 (sub_nonneg.mpr hv_mem.2)]
  have hexplambda : (12 : ℝ) / 5 < Real.exp lambda := by
    have hmono : Real.exp (9 / 10 : ℝ) < Real.exp lambda :=
      Real.exp_lt_exp.mpr (by simpa [lambda] using hlambda0)
    exact lt_trans hexp hmono
  have hexpneg : Real.exp (-lambda) < (5 : ℝ) / 12 := by
    rw [Real.exp_neg]
    rw [show (5 : ℝ) / 12 = 1 / ((12 : ℝ) / 5) by norm_num]
    simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 12 / 5) hexplambda
  have hlogsum : Real.log (1 + Real.exp (-lambda)) < (3 : ℝ) / 8 := by
    have harg : 1 + Real.exp (-lambda) < (17 : ℝ) / 12 := by linarith
    have hpos : 0 < 1 + Real.exp (-lambda) := by positivity
    have hlogmono := Real.strictMonoOn_log hpos (by norm_num) harg
    exact lt_trans hlogmono (by simpa using hlog)
  have hmix := binEntropy_sub_mul_le_log_one_add_exp_neg (w := (1 - pi) * u + pi * v)
    (lambda := lambda) hw
  have hmix_upper :
      Real.binEntropy ((1 - pi) * u + pi * v) < (2 / 5 : ℝ) + (4 / 5) * pi := by
    have hgap : lambda * (v - u) = (4 : ℝ) / 5 := by
      dsimp [lambda, u, v]
      norm_num
    have hlu : lambda * u < (1 : ℝ) / 40 := by simpa [lambda, u] using hlambdau
    have hrewrite : lambda * ((1 - pi) * u + pi * v) =
        lambda * u + pi * (lambda * (v - u)) := by ring
    rw [hrewrite, hgap] at hmix
    linarith
  have hcond_lower :
      (2 / 5 : ℝ) + (4 / 5) * pi <
        4 * ((1 - pi) * Real.binEntropy u + pi * Real.binEntropy v) := by
    have hu := binEntropy_twoFifthsLowerPosterior_gt
    have hv := binEntropy_twoFifthsUpperPosterior_gt
    dsimp [u, v] at hu hv ⊢
    have hleft := mul_lt_mul_of_pos_left hu (show 0 < 4 * (1 - pi) by
      nlinarith [hpi.2])
    have hright := mul_le_mul_of_nonneg_left hv.le (show 0 ≤ 4 * pi by
      nlinarith [hpi.1])
    nlinarith
  unfold scalarSingletonReward
  dsimp [u, v] at hmix_upper hcond_lower ⊢
  linarith

theorem seamReward_neg :
    ∀ pi : ℝ, pi ∈ Set.Icc 0 (1 / 2) →
      scalarSingletonReward pi (624 / 26999 : ℝ) (24375 / 26999 : ℝ) < 0 :=
  fun pi hpi => singletonReward_twoFifthsSeam_neg hpi

theorem ScalarContactChart.x_lt_two_fifths_of_phaseReward_nonneg :
    ∀ C : ScalarContactChart,
      ScalarContactChart.StrictInterior C → 0 ≤ ScalarContactChart.phaseReward C → C.x < 2 / 5 := by
  intro C hC hreward
  have hF5 := seamReward_neg
  by_contra hnot
  have hx : (2 / 5 : ℝ) ≤ C.x := le_of_not_gt hnot
  have hbalanced : 0 ≤ exposedPhaseReward C (2 * ScalarContactChart.contactMidpoint C) :=
    exposedPhaseReward_at_equalMass_nonneg C hC hreward
  rw [exposedPhaseReward_at_equalMass_eq_scaled_reward] at hbalanced
  have hQ : 0 < (ScalarContactChart.equalMassChart C).norm := (ScalarContactChart.equalMassChart C).norm_pos
  have hlow : (ScalarContactChart.equalMassChart C).r / (ScalarContactChart.equalMassChart C).norm =
      seamLowerPosterior C.x := by
    simp [ScalarContactChart.equalMassChart, ScalarContactChart.r, ScalarContactChart.norm,
      ScalarContactChart.s, seamLowerPosterior,
      contactMidpoint, contactDenominator,
      ScalarContactChart.contactMidpoint]
    ring
  have hhigh : 1 / (ScalarContactChart.equalMassChart C).norm =
      seamUpperPosterior C.x := by
    simp [ScalarContactChart.equalMassChart, ScalarContactChart.r, ScalarContactChart.norm,
      ScalarContactChart.s, seamUpperPosterior,
      contactMidpoint, contactDenominator,
      ScalarContactChart.contactMidpoint]
    ring
  rw [hlow, hhigh] at hbalanced
  have hmoving : 0 ≤ scalarSingletonReward C.pi
      (seamLowerPosterior C.x) (seamUpperPosterior C.x) :=
    (mul_nonneg_iff_of_pos_left hQ).mp hbalanced
  have hpi1 : C.pi ∈ Set.Icc (0 : ℝ) 1 := ⟨C.pi_nonneg, C.pi_le_half.trans (by norm_num)⟩
  have hpiHalf : C.pi ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨C.pi_nonneg, C.pi_le_half⟩
  have hchannel := binaryChannel_mem_Icc_of_twoFifths_le C hC hx
  have hcond := seamConditionalEntropy_comparison
    hx hC.1 hpi1
  have hpostU := binaryChannel_twoFifthsLowerPosterior C
  have hpostV := binaryChannel_twoFifthsUpperPosterior C
  have hcond' :
      (1 - C.pi) * Real.binEntropy twoFifthsLowerPosterior +
          C.pi * Real.binEntropy twoFifthsUpperPosterior ≤
        (1 - C.pi) * Real.binEntropy
            (binaryChannel (seamChannelZero C)
              (seamChannelOne C) twoFifthsLowerPosterior) +
          C.pi * Real.binEntropy
            (binaryChannel (seamChannelZero C)
              (seamChannelOne C) twoFifthsUpperPosterior) := by
    rw [hpostU, hpostV]
    simpa [twoFifthsLowerPosterior, twoFifthsUpperPosterior,
      seamLowerPosteriorAtChart, seamUpperPosteriorAtChart,
      seamNormalizationAtChart, seamLowerPosterior,
      seamUpperPosterior] using hcond
  have hdp := scalarSingletonReward_binaryChannel_le
    hpi1 (show twoFifthsLowerPosterior ∈ Set.Icc (0 : ℝ) 1 by
      constructor <;> norm_num [twoFifthsLowerPosterior])
    (show twoFifthsUpperPosterior ∈ Set.Icc (0 : ℝ) 1 by
      constructor <;> norm_num [twoFifthsUpperPosterior])
    hchannel.1 hchannel.2 hcond'
  rw [hpostU, hpostV] at hdp
  have hmoving' : 0 ≤ scalarSingletonReward C.pi
      (seamLowerPosteriorAtChart C) (seamUpperPosteriorAtChart C) := by
    simpa [seamLowerPosteriorAtChart, seamUpperPosteriorAtChart,
      seamNormalizationAtChart, seamLowerPosterior,
      seamUpperPosterior] using hmoving
  have hfixed : scalarSingletonReward C.pi twoFifthsLowerPosterior
      twoFifthsUpperPosterior < 0 := by
    simpa [twoFifthsLowerPosterior, twoFifthsUpperPosterior] using hF5 C.pi hpiHalf
  linarith

/-! ## The lower-prior gate -/

/-- Natural-log reward with free contact sum and prior. -/
noncomputable def freePriorPhaseReward (C : ScalarContactChart) (s pi : ℝ) : ℝ :=
  let r := C.r
  let e := r + pi * (1 - r)
  let ell := 1 - pi + pi * r
  pairEntropy e (ell + s) -
    4 * ((1 - pi) * pairEntropy r (1 + s) + pi * pairEntropy 1 (r + s))

/-- The tangent at zero prior to the natural-log phase reward. -/
noncomputable def phaseRewardPriorTangent (C : ScalarContactChart) (s pi : ℝ) : ℝ :=
  let H0 := pairEntropy C.r (1 + s)
  let H1 := pairEntropy 1 (C.r + s)
  let L := Real.log ((1 + s) / C.r)
  (-3 * H0 + pi * ((1 - C.r) * L + 4 * H0 - 4 * H1))

theorem freePriorPhaseReward_at_chart (C : ScalarContactChart) :
    freePriorPhaseReward C C.s C.pi = ScalarContactChart.phaseReward C := by
  unfold freePriorPhaseReward ScalarContactChart.phaseReward
  dsimp only
  rw [show C.r + C.pi * (1 - C.r) = C.e by unfold ScalarContactChart.e; ring]
  rw [show 1 - C.pi + C.pi * C.r = C.ell by rfl]

theorem freePriorPhaseReward_strictConcaveOn (C : ScalarContactChart) {s : ℝ}
    (hs : 0 ≤ s) (hx : C.x < 1) :
    StrictConcaveOn ℝ (Icc 0 (1 / 2)) (freePriorPhaseReward C s) := by
  let Q : ℝ := 1 + C.r + s
  let p : ℝ → ℝ := fun pi => (C.r + pi * (1 - C.r)) / Q
  have hr0 : 0 < C.r := C.r_pos
  have hr1 : C.r < 1 := by
    dsimp only [ScalarContactChart.r]
    exact pow_lt_one₀ C.x_pos.le hx (by norm_num)
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hnormalize : ∀ pi ∈ Icc (0 : ℝ) (1 / 2),
      freePriorPhaseReward C s pi =
        Q * Real.binEntropy (p pi) -
          4 * ((1 - pi) * pairEntropy C.r (1 + s) +
            pi * pairEntropy 1 (C.r + s)) := by
    intro pi hpi
    have he0 : 0 ≤ C.r + pi * (1 - C.r) :=
      add_nonneg hr0.le (mul_nonneg hpi.1 (sub_nonneg.mpr hr1.le))
    have hell0 : 0 ≤ 1 - pi + pi * C.r + s := by nlinarith [hpi.2, hs, hr0]
    have hsum : 0 <
        (C.r + pi * (1 - C.r)) + (1 - pi + pi * C.r + s) := by
      rw [show (C.r + pi * (1 - C.r)) + (1 - pi + pi * C.r + s) = Q by
        dsimp [Q]; ring]
      exact hQ
    unfold freePriorPhaseReward
    dsimp only
    rw [pairEntropy_eq_mass_mul_binEntropy he0 hell0 hsum]
    change
      ((C.r + pi * (1 - C.r)) + (1 - pi + pi * C.r + s)) *
          Real.binEntropy
            ((C.r + pi * (1 - C.r)) /
              ((C.r + pi * (1 - C.r)) + (1 - pi + pi * C.r + s))) - _ = _
    rw [show (C.r + pi * (1 - C.r)) + (1 - pi + pi * C.r + s) = Q by
      dsimp [Q]; ring]
  refine ⟨convex_Icc 0 (1 / 2), ?_⟩
  intro x hxmem y hymem hxy a b ha hb hab
  have hmix : a * x + b * y ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor <;> nlinarith [hxmem.1, hxmem.2, hymem.1, hymem.2]
  have hp_mem : ∀ t ∈ Icc (0 : ℝ) (1 / 2), p t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    dsimp [p]
    constructor
    · exact div_nonneg
        (add_nonneg hr0.le (mul_nonneg ht.1 (sub_nonneg.mpr hr1.le))) hQ.le
    · apply (div_le_one hQ).2
      dsimp [Q]
      nlinarith [ht.2, hs]
  have hp_ne : p x ≠ p y := by
    intro heq
    dsimp [p] at heq
    field_simp [hQ.ne'] at heq
    apply hxy
    nlinarith
  have hstrict := Real.strictConcave_binEntropy.2
    (hp_mem x hxmem) (hp_mem y hymem) hp_ne ha hb hab
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
    a * freePriorPhaseReward C s x + b * freePriorPhaseReward C s y =
        Q * (a * Real.binEntropy (p x) + b * Real.binEntropy (p y)) -
          4 * ((1 - (a * x + b * y)) * pairEntropy C.r (1 + s) +
            (a * x + b * y) * pairEntropy 1 (C.r + s)) := by
      rw [hnormalize x hxmem, hnormalize y hymem, hone_mix]
      ring
    _ < Q * Real.binEntropy (p (a * x + b * y)) -
          4 * ((1 - (a * x + b * y)) * pairEntropy C.r (1 + s) +
            (a * x + b * y) * pairEntropy 1 (C.r + s)) := by linarith
    _ = freePriorPhaseReward C s (a * x + b * y) := by
      rw [hnormalize (a * x + b * y) hmix]

theorem hasDerivAt_freePriorPhaseReward_zero (C : ScalarContactChart) {s : ℝ}
    (hs : 0 ≤ s) :
    HasDerivAt (fun pi : ℝ => freePriorPhaseReward C s pi)
      ((1 - C.r) * Real.log ((1 + s) / C.r) +
        4 * pairEntropy C.r (1 + s) - 4 * pairEntropy 1 (C.r + s)) 0 := by
  have hr : C.r ≠ 0 := C.r_pos.ne'
  have h1s : 1 + s ≠ 0 := by linarith
  have hQ : 1 + C.r + s ≠ 0 := by linarith [C.r_pos]
  have he : HasDerivAt (fun pi : ℝ => C.r + pi * (1 - C.r)) (1 - C.r) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) C.r).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (1 - C.r))
    apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with pi
    rfl
  have hell : HasDerivAt (fun pi : ℝ => 1 - pi + pi * C.r + s) (-(1 - C.r)) 0 := by
    have h := ((((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id (𝕜 := ℝ) 0)).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const C.r)).add_const s)
    have h' : HasDerivAt (fun pi : ℝ => 1 - pi + pi * C.r + s) (-1 + C.r) 0 := by
      apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
      filter_upwards [] with pi
      rfl
    have heq : -1 + C.r = -(1 - C.r) := by ring
    rw [← heq]
    exact h'
  have hphiE : HasDerivAt
      (fun pi : ℝ => xLogX (C.r + pi * (1 - C.r)))
      ((Real.log C.r + 1) * (1 - C.r)) 0 := by
    have hout : HasDerivAt xLogX (Real.log C.r + 1)
        (C.r + 0 * (1 - C.r)) := by
      simpa using hasDerivAt_xLogX hr
    exact hout.comp 0 he
  have hphiEll : HasDerivAt
      (fun pi : ℝ => xLogX (1 - pi + pi * C.r + s))
      ((Real.log (1 + s) + 1) * (-(1 - C.r))) 0 := by
    have hout : HasDerivAt xLogX (Real.log (1 + s) + 1)
        (1 - 0 + 0 * C.r + s) := by
      simpa using hasDerivAt_xLogX h1s
    exact hout.comp 0 hell
  have hfirst : HasDerivAt
      (fun pi : ℝ => pairEntropy (C.r + pi * (1 - C.r)) (1 - pi + pi * C.r + s))
      ((1 - C.r) * Real.log ((1 + s) / C.r)) 0 := by
    unfold pairEntropy
    have hconst : HasDerivAt
        (fun _ : ℝ => xLogX (1 + C.r + s)) 0 0 := hasDerivAt_const 0 _
    have hraw := (hconst.sub hphiE).sub hphiEll
    have hfun : (fun pi : ℝ =>
        pairEntropy (C.r + pi * (1 - C.r)) (1 - pi + pi * C.r + s)) =ᶠ[nhds 0]
        (((fun _ : ℝ => xLogX (1 + C.r + s)) -
          fun pi => xLogX (C.r + pi * (1 - C.r))) -
          fun pi => xLogX (1 - pi + pi * C.r + s)) := by
      filter_upwards [] with pi
      unfold pairEntropy
      congr 3
      ring
    have hder : 0 - (Real.log C.r + 1) * (1 - C.r) -
        (Real.log (1 + s) + 1) * (-(1 - C.r)) =
          (1 - C.r) * Real.log ((1 + s) / C.r) := by
      rw [Real.log_div h1s hr]
      ring
    rw [← hder]
    exact hraw.congr_of_eventuallyEq hfun
  have hbase := ((((hasDerivAt_const (0 : ℝ) 1).sub
    (hasDerivAt_id (𝕜 := ℝ) 0)).mul_const (pairEntropy C.r (1 + s))).add
    ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (pairEntropy 1 (C.r + s))))
  have haff := hbase.const_mul 4
  have hsub := hfirst.sub haff
  have hfun : (fun pi : ℝ => freePriorPhaseReward C s pi) =ᶠ[nhds 0]
      ((fun pi : ℝ => pairEntropy (C.r + pi * (1 - C.r)) (1 - pi + pi * C.r + s)) -
        fun pi : ℝ => 4 * ((1 - pi) * pairEntropy C.r (1 + s) +
          pi * pairEntropy 1 (C.r + s))) := by
    filter_upwards [] with pi
    rfl
  have hder :
      (1 - C.r) * Real.log ((1 + s) / C.r) -
          4 * ((0 - 1) * pairEntropy C.r (1 + s) + 1 * pairEntropy 1 (C.r + s)) =
        (1 - C.r) * Real.log ((1 + s) / C.r) +
          4 * pairEntropy C.r (1 + s) - 4 * pairEntropy 1 (C.r + s) := by ring
  rw [← hder]
  exact hsub.congr_of_eventuallyEq hfun

theorem freePriorPhaseReward_le_tangent (C : ScalarContactChart) {s pi : ℝ}
    (hs : 0 ≤ s) (hx : C.x < 1) (hpi : pi ∈ Icc (0 : ℝ) (1 / 2)) :
    freePriorPhaseReward C s pi ≤ phaseRewardPriorTangent C s pi := by
  by_cases hpi0 : pi = 0
  · subst pi
    simp [freePriorPhaseReward, phaseRewardPriorTangent]
    nlinarith
  have hpos : 0 < pi := lt_of_le_of_ne hpi.1 (Ne.symm hpi0)
  have hslope := (freePriorPhaseReward_strictConcaveOn C hs hx).concaveOn.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 (1 / 2) by norm_num) hpi hpos
    (hasDerivAt_freePriorPhaseReward_zero C hs)
  unfold slope at hslope
  have hzero : freePriorPhaseReward C s 0 = -3 * pairEntropy C.r (1 + s) := by
    unfold freePriorPhaseReward
    dsimp only
    ring
  unfold phaseRewardPriorTangent
  dsimp only
  rw [hzero] at hslope
  have hpine : pi ≠ 0 := hpi0
  dsimp only [vsub_eq_sub, smul_eq_mul, sub_zero] at hslope
  have hmul := (div_le_iff₀ hpos).mp (by simpa [div_eq_inv_mul] using hslope)
  have hmul' : freePriorPhaseReward C s pi + 3 * pairEntropy C.r (1 + s) ≤
      ((1 - C.r) * Real.log ((1 + s) / C.r) + 4 * pairEntropy C.r (1 + s) -
        4 * pairEntropy 1 (C.r + s)) * pi := by
    simpa [div_eq_mul_inv, mul_comm] using hmul
  nlinarith

theorem r_mul_log_le_pairEntropy_low (C : ScalarContactChart) {s : ℝ} (hs : 0 ≤ s) :
    C.r * Real.log ((1 + s) / C.r) ≤ pairEntropy C.r (1 + s) := by
  have h1s : 0 < 1 + s := by linarith
  have hsum : 0 < C.r + (1 + s) := add_pos C.r_pos h1s
  rw [pairEntropy_eq_sum_logs C.r_pos h1s]
  have hratio : 1 ≤ (C.r + (1 + s)) / (1 + s) :=
    (le_div_iff₀ h1s).2 (by linarith [C.r_pos])
  have hlog : 0 ≤ Real.log ((C.r + (1 + s)) / (1 + s)) := Real.log_nonneg hratio
  have harg : (1 + s) / C.r ≤ (C.r + (1 + s)) / C.r := by
    exact (div_le_div_iff_of_pos_right C.r_pos).2 (by linarith [C.r_pos])
  have hlogFirst := Real.strictMonoOn_log.monotoneOn
    (show (1 + s) / C.r ∈ Set.Ioi 0 by exact div_pos h1s C.r_pos)
    (show (C.r + (1 + s)) / C.r ∈ Set.Ioi 0 by exact div_pos hsum C.r_pos) harg
  nlinarith [mul_le_mul_of_nonneg_left hlogFirst C.r_pos.le]

theorem r_mul_log_le_pairEntropy_high (C : ScalarContactChart) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    C.r * Real.log ((1 + s) / C.r) ≤ pairEntropy 1 (C.r + s) := by
  have hsuper := pairEntropy_superadditive
    (show (0 : ℝ) ≤ 1 by norm_num) C.r_pos.le (show (0 : ℝ) ≤ 0 by norm_num) hs
  have hzero : pairEntropy 0 s = 0 := by simp [pairEntropy, xLogX]
  simp only [hzero, add_zero, zero_add] at hsuper
  have hr1 : 0 < 1 + C.r := by linarith [C.r_pos]
  have hlogLower : C.r ≤ (1 + C.r) * Real.log (1 + C.r) := by
    have h := Real.one_sub_inv_le_log_of_pos hr1
    have hmul := mul_le_mul_of_nonneg_left h hr1.le
    field_simp [hr1.ne'] at hmul
    nlinarith [C.r_pos]
  have hlogUpper : C.r * Real.log (1 + s) ≤ C.r * s := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + s by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h C.r_pos.le]
  have hrs : C.r * s ≤ C.r := mul_le_of_le_one_right C.r_pos.le hs1
  have hE : C.r * Real.log ((1 + s) / C.r) ≤ pairEntropy 1 C.r := by
    rw [pairEntropy_eq_sum_logs (show (0 : ℝ) < 1 by norm_num) C.r_pos]
    rw [Real.log_div (show (0 : ℝ) < 1 + s by linarith).ne' C.r_pos.ne',
      Real.log_div hr1.ne' C.r_pos.ne']
    simp only [div_one, one_mul]
    nlinarith
  exact hE.trans hsuper

theorem phaseRewardPriorTangent_neg_of_prior_le_three_mul_r (C : ScalarContactChart)
    (hdom : ScalarContactChart.StrictInterior C) (hx : C.x < 2 / 5)
    (hpi : C.pi ≤ 3 * C.r) : phaseRewardPriorTangent C C.s C.pi < 0 := by
  rcases hdom with ⟨hx1, hpi0, hsLower, hsUpper, hcontact⟩
  have hs0 : 0 ≤ C.s := C.s_nonneg
  have hs1 : C.s ≤ 1 := by
    have hy1 : C.y < 1 := by
      dsimp only [ScalarContactChart.y]
      nlinarith [C.x_pos, hx1]
    exact (le_of_lt hsUpper).trans hy1.le
  have hrQuarter : C.r < 1 / 4 := by
    have hx2 : C.x ^ 2 < (2 / 5 : ℝ) ^ 2 := by nlinarith [C.x_pos]
    have hx4 : C.x ^ 4 < (2 / 5 : ℝ) ^ 4 := by nlinarith
    dsimp only [ScalarContactChart.r]
    norm_num at hx4 ⊢
    linarith
  let L : ℝ := Real.log ((1 + C.s) / C.r)
  let H0 : ℝ := pairEntropy C.r (1 + C.s)
  let H1 : ℝ := pairEntropy 1 (C.r + C.s)
  have hratio : 1 < (1 + C.s) / C.r := by
    apply (lt_div_iff₀ C.r_pos).2
    linarith [C.r_pos, hrQuarter]
  have hL : 0 < L := Real.log_pos hratio
  have hH0 : C.r * L ≤ H0 := by
    exact r_mul_log_le_pairEntropy_low C hs0
  have hH1 : C.r * L ≤ H1 := by
    exact r_mul_log_le_pairEntropy_high C hs0 hs1
  have hH0pos : 0 < H0 := lt_of_lt_of_le (mul_pos C.r_pos hL) hH0
  have hT0 : (-3 : ℝ) * H0 < 0 := mul_neg_of_neg_of_pos (by norm_num) hH0pos
  have hcoef : -3 + 12 * C.r < 0 := by linarith
  have hcoefH0 : (-3 + 12 * C.r) * H0 ≤ (-3 + 12 * C.r) * (C.r * L) :=
    mul_le_mul_of_nonpos_left hH0 hcoef.le
  have hminusH1 : -12 * C.r * H1 ≤ -12 * C.r * (C.r * L) :=
    mul_le_mul_of_nonpos_left hH1 (by nlinarith [C.r_pos])
  have hT3 :
      (-3 + 12 * C.r) * H0 + 3 * C.r * (1 - C.r) * L - 12 * C.r * H1 < 0 := by
    have hr2L : 0 < C.r ^ 2 * L := mul_pos (sq_pos_of_pos C.r_pos) hL
    nlinarith
  let D : ℝ := (1 - C.r) * L + 4 * H0 - 4 * H1
  have hpiNonneg : 0 ≤ C.pi := C.pi_nonneg
  have hTpi : -3 * H0 + C.pi * D < 0 := by
    by_cases hD : D ≤ 0
    · have hprod : C.pi * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpiNonneg hD
      linarith
    · have hDpos : 0 < D := lt_of_not_ge hD
      have hprod : C.pi * D ≤ (3 * C.r) * D :=
        mul_le_mul_of_nonneg_right hpi hDpos.le
      have hT3' : -3 * H0 + (3 * C.r) * D < 0 := by
        dsimp only [D]
        nlinarith
      linarith
  unfold phaseRewardPriorTangent
  dsimp only
  dsimp only [L, H0, H1, D] at hTpi
  exact hTpi

theorem phaseReward_neg_of_prior_le_three_mul_r (C : ScalarContactChart)
    (hdom : ScalarContactChart.StrictInterior C) (hx : C.x < 2 / 5)
    (hpi : C.pi ≤ 3 * C.r) : ScalarContactChart.phaseReward C < 0 := by
  have htangent := phaseRewardPriorTangent_neg_of_prior_le_three_mul_r C hdom hx hpi
  have hbound := freePriorPhaseReward_le_tangent C C.s_nonneg hdom.1
    ⟨C.pi_nonneg, C.pi_le_half⟩
  rw [freePriorPhaseReward_at_chart] at hbound
  exact hbound.trans_lt htangent

theorem ScalarContactChart.three_mul_r_lt_pi_of_phaseReward_nonneg (C : ScalarContactChart)
    (hdom : ScalarContactChart.StrictInterior C)
    (hphase : 0 ≤ ScalarContactChart.phaseReward C) : 3 * C.r < C.pi := by
  have hx := C.x_lt_two_fifths_of_phaseReward_nonneg hdom hphase
  by_contra h
  have hpi : C.pi ≤ 3 * C.r := le_of_not_gt h
  exact (not_lt_of_ge hphase) (phaseReward_neg_of_prior_le_three_mul_r C hdom hx hpi)

/-! ## Slack identity and chart cost -/

theorem positivePhaseSlack_eq_three_mul_proxy_add_remainders (C : ScalarContactChart) :
    8 * ScalarContactChart.mixingSum C - (ScalarContactChart.observableInfo C - ScalarContactChart.phaseReward C) =
      3 * strictProxy C.x C.pi C.s
        + 8 * (ScalarContactChart.mixingSum C - ScalarContactChart.offDiagonalLoss C)
        + ((1 / 2 : ℝ) * ScalarContactChart.offDiagonalLoss C - ScalarContactChart.highInformationLoss C) := by
  have hreward := ScalarContactChart.phaseReward_eq_highInformation_sub_three_mul_highConditionalEntropy C
  have hn : ScalarContactChart.highInformationLoss C = ScalarContactChart.observableInfo C - ScalarContactChart.highInformation C := rfl
  have hb := freeMixingTerm_eq_offDiagonalLoss C
  have ha := highArmEntropy_eq_highConditionalEntropy C
  rw [hreward, hn]
  unfold strictProxy
  rw [hb, ha]
  ring

theorem three_mul_proxy_le_positivePhaseSlack (C : ScalarContactChart) :
    3 * strictProxy C.x C.pi C.s ≤ 8 * ScalarContactChart.mixingSum C - (ScalarContactChart.observableInfo C - ScalarContactChart.phaseReward C) := by
  rw [positivePhaseSlack_eq_three_mul_proxy_add_remainders]
  have horient : 2 * ScalarContactChart.highInformationLoss C ≤ ScalarContactChart.offDiagonalLoss C := ScalarContactChart.two_mul_highInformationLoss_le_offDiagonalLoss C
  have hbridge : ScalarContactChart.offDiagonalLoss C ≤ ScalarContactChart.mixingSum C := offDiagonalLoss_le_mixingSum C
  nlinarith

/-- The positive scalar arm follows once the two seam endpoints are positive. -/
theorem ScalarContactChart.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_seam_pos
    (hbal : StrictProxyPositiveAtBalancedSeam)
    (hlow : StrictProxyPositiveAtLowPriorSeam)
    (C : ScalarContactChart) (hC : C.StrictInterior) (hR : 0 ≤ C.phaseReward) :
    C.observableInfo - C.phaseReward ≤ 8 * C.mixingSum := by
  have hx := C.x_lt_two_fifths_of_phaseReward_nonneg hC hR
  have hpi := C.three_mul_r_lt_pi_of_phaseReward_nonneg hC hR
  have hmin : 0 < min
      (strictProxy C.x (3 * C.x ^ 4) (2 * Binary.contactMidpoint C.x))
      (strictProxy C.x (1 / 2) (2 * Binary.contactMidpoint C.x)) :=
    lt_min (hlow C.x_pos hx.le) (hbal C.x_pos hx.le)
  have hproxy := hmin.trans_le (strictProxy_geMinAtSeamEndpoints C hx hpi.le)
  have hslack := three_mul_proxy_le_positivePhaseSlack C
  linarith

/-- The two scalar arms give the factor-eight cost bound at a supplied chart,
conditional only on the two seam-positivity statements. -/
theorem ContactChart.strictFactorEight_of_seam_pos
    (hbal : StrictProxyPositiveAtBalancedSeam)
    (hlow : StrictProxyPositiveAtLowPriorSeam) : ContactChart.StrictFactorEight := by
  intro C x hx0 hx1 hratio hmass heq
  let S := C.toScalarChart x hx0 hx1 hmass heq
  have hdomain : S.StrictInterior :=
    C.toScalarChart_strictInterior x hx0 hx1 hratio hmass heq
  have hscaledInfo := ScalarContactChart.norm_mul_log_two_mul_observableInfo_eq
    C x hx0 hx1 hratio hmass heq
  have hscaledCost := norm_mul_log_two_mul_w3Cost_phaseSelector_eq_of_observableInfo
    C x hx0 hx1 hratio hmass heq hscaledInfo
  have hscaledScore := ScalarContactChart.norm_mul_log_two_mul_score_eq_contactEntropyGap_add_mixingSum
    C x hx0 hx1 hratio hmass heq
  have hm := contactEntropyGap_nonneg S
  have hscalar : S.observableInfo - max 0 S.phaseReward ≤
      8 * (S.contactEntropyGap + S.mixingSum) := by
    by_cases hphase : 0 ≤ S.phaseReward
    · rw [max_eq_right hphase]
      have h := S.observableInfo_sub_phaseReward_le_eight_mul_mixingSum_of_seam_pos
        hbal hlow hdomain hphase
      linarith
    · have hnonpos := le_of_not_ge hphase
      rw [max_eq_left hnonpos]
      have h := S.observableInfo_le_eight_mul_mixingSum_of_phaseReward_nonpos hdomain hnonpos
      linarith
  have hscale : 0 < S.norm * Real.log 2 :=
    mul_pos S.norm_pos (Real.log_pos (by norm_num))
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  calc
    S.norm * Real.log 2 * w3Cost C.toTransposeChart.latent (phaseSelector C.toTransposeChart) =
        S.observableInfo - max 0 S.phaseReward := hscaledCost
    _ ≤ 8 * (S.contactEntropyGap + S.mixingSum) := hscalar
    _ = S.norm * Real.log 2 * (8 * C.toTransposeChart.latent.score) := by
      rw [← hscaledScore]
      ring


end

end StochasticToDeterministicLatents.Binary
