import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Bernoulli divergence bounds

Two lower bounds on the Bernoulli divergence `klBer q r`, which is `D(Ber q ‖ Ber r)`, for
`q ∈ [0, 1]` and `r ∈ (0, 1)`:

* Pinsker's inequality `2 (q - r)² ≤ klBer q r` (`klBer_ge_two_sq`), hence `0 ≤ klBer q r`
  (`klBer_nonneg`);
* the Ordentlich–Weinberger refinement `owL r * (q - r)² ≤ klBer q r` (`klBer_ge_owL_mul_sq`),
  where `owL r = log ((1 - r)/r) / (1 - 2r)` and `owL (1/2) = 2`.

The coefficient `owL` is symmetric about `1/2` (`owL_symm`), at least `2` (`two_le_owL`), and
decreasing on `(0, 1/2]` (`owL_antitoneOn`).

Everything here is in nats, through `Real.log`; the library's information quantities are in
bits. This module imports only Mathlib.

For `r < 1/2` the refinement is proved from the sign of the derivative of
`G q = klBer q r - owL r * (q - r)²`: the derivative is concave on `(0, 1/2]`, vanishes at `r`
and at `1/2`, and is odd about `1/2`, so `G` decreases, increases, decreases and increases
between the points `0, r, 1/2, 1 - r, 1`, and `G r = G (1 - r) = 0`. The case `r > 1/2` follows
by complementing `q` and `r`. The endpoints `q = 0` and `q = 1` are covered on closed intervals,
through the continuity of `x log x`.

## Attribution

Original to this repository. The refinement is due to E. Ordentlich and M. J. Weinberger, "A
distribution dependent refinement of Pinsker's inequality", IEEE Transactions on Information
Theory 51 (2005).
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

/-- The Bernoulli divergence `D(Ber q ‖ Ber r)` in nats. `Real.log 0 = 0` gives
`0 log 0 = 0`. -/
def klBer (q r : ℝ) : ℝ :=
  q * Real.log (q / r) + (1 - q) * Real.log ((1 - q) / (1 - r))

/-- The Ordentlich–Weinberger coefficient `log((1 - r)/r)/(1 - 2r)`, with value `2` at `r = 1/2`. -/
def owL (r : ℝ) : ℝ :=
  if r = 1 / 2 then 2 else Real.log ((1 - r) / r) / (1 - 2 * r)

/-! ## Helper lemmas -/

/-- For `r ≠ 0` and `1 - r ≠ 0`, `klBer q r` expanded into `x log x` terms, for every `q`. -/
theorem klBer_eq_mul_log {q r : ℝ} (hr0 : r ≠ 0) (hr1 : 1 - r ≠ 0) :
    klBer q r = q * Real.log q - q * Real.log r +
      ((1 - q) * Real.log (1 - q) - (1 - q) * Real.log (1 - r)) := by
  unfold klBer
  have h1 : q * Real.log (q / r) = q * Real.log q - q * Real.log r := by
    rcases eq_or_ne q 0 with h | h
    · simp [h]
    · rw [Real.log_div h hr0]; ring
  have h2 : (1 - q) * Real.log ((1 - q) / (1 - r)) =
      (1 - q) * Real.log (1 - q) - (1 - q) * Real.log (1 - r) := by
    rcases eq_or_ne (1 - q) 0 with h | h
    · simp [h]
    · rw [Real.log_div h hr1]; ring
  rw [h1, h2]

/-- For `r ≠ 0` and `1 - r ≠ 0`, `klBer q r` is continuous in `q` on all of `ℝ`. -/
theorem continuous_klBer_left {r : ℝ} (hr0 : r ≠ 0) (hr1 : 1 - r ≠ 0) :
    Continuous fun q => klBer q r := by
  have e : (fun q => klBer q r) = fun q => q * Real.log q - q * Real.log r +
      ((1 - q) * Real.log (1 - q) - (1 - q) * Real.log (1 - r)) :=
    funext fun q => klBer_eq_mul_log (q := q) hr0 hr1
  rw [e]
  have h1 : Continuous fun q : ℝ => q * Real.log q := Real.continuous_mul_log
  have h2 : Continuous fun q : ℝ => (1 - q) * Real.log (1 - q) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact (h1.sub (continuous_id.mul continuous_const)).add
    (h2.sub ((continuous_const.sub continuous_id).mul continuous_const))

private theorem hasDerivAt_klBer {q r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hr0 : r ≠ 0)
    (hr1 : 1 - r ≠ 0) :
    HasDerivAt (fun x => klBer x r)
      (Real.log q - Real.log (1 - q) - (Real.log r - Real.log (1 - r))) q := by
  have e : (fun x => klBer x r) = fun x => x * Real.log x - x * Real.log r +
      ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - r)) :=
    funext fun x => klBer_eq_mul_log (q := x) hr0 hr1
  rw [e]
  have hq1' : (1 : ℝ) - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log q + 1) q :=
    Real.hasDerivAt_mul_log hq0.ne'
  have hl : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id' q).const_sub (1 : ℝ)
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      ((Real.log (1 - q) + 1) * (-1)) q :=
    (Real.hasDerivAt_mul_log hq1').comp q hl
  have h3 : HasDerivAt (fun x : ℝ => x * Real.log r) (1 * Real.log r) q :=
    (hasDerivAt_id' q).mul_const (Real.log r)
  have h4 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - r)) ((-1) * Real.log (1 - r)) q :=
    hl.mul_const (Real.log (1 - r))
  exact ((h1.sub h3).add (h2.sub h4)).congr_deriv (by ring)

/-- Derivative of `klBer · r - c (· - r)²`. -/
private theorem hasDerivAt_G {q r c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hr0 : r ≠ 0)
    (hr1 : 1 - r ≠ 0) :
    HasDerivAt (fun x => klBer x r - c * (x - r) ^ 2)
      (Real.log q - Real.log (1 - q) - (Real.log r - Real.log (1 - r)) - c * (2 * (q - r))) q := by
  have h := hasDerivAt_klBer hq0 hq1 hr0 hr1
  have hs : HasDerivAt (fun x : ℝ => x - r) 1 q := by
    simpa using (hasDerivAt_id' q).sub_const r
  have h2 : HasDerivAt (fun x : ℝ => c * (x - r) ^ 2) (c * (2 * (q - r))) q := by
    exact ((hs.pow 2).const_mul c).congr_deriv (by norm_num)
  exact h.sub h2

/-- Generic tool: a sign condition on the derivative of `klBer · r - c (· - r)²` on the open
interval gives antitonicity on the closed interval. -/
private theorem G_antitoneOn {r c u v : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hu : 0 ≤ u) (hv : v ≤ 1)
    (hs : ∀ x, u < x → x < v →
      Real.log x - Real.log (1 - x) - (Real.log r - Real.log (1 - r)) - c * (2 * (x - r)) ≤ 0) :
    AntitoneOn (fun x => klBer x r - c * (x - r) ^ 2) (Set.Icc u v) := by
  have hr0' : r ≠ 0 := hr0.ne'
  have hr1' : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc u v)
  · exact ((continuous_klBer_left hr0' hr1').sub (by fun_prop)).continuousOn
  · rw [interior_Icc]
    intro x hx
    exact (hasDerivAt_G (c := c) (by linarith [hx.1]) (by linarith [hx.2]) hr0'
      hr1').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(hasDerivAt_G (c := c) (by linarith [hx.1]) (by linarith [hx.2]) hr0' hr1').deriv]
    exact hs x hx.1 hx.2

private theorem G_monotoneOn {r c u v : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hu : 0 ≤ u) (hv : v ≤ 1)
    (hs : ∀ x, u < x → x < v →
      0 ≤ Real.log x - Real.log (1 - x) - (Real.log r - Real.log (1 - r)) - c * (2 * (x - r))) :
    MonotoneOn (fun x => klBer x r - c * (x - r) ^ 2) (Set.Icc u v) := by
  have hr0' : r ≠ 0 := hr0.ne'
  have hr1' : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
  · exact ((continuous_klBer_left hr0' hr1').sub (by fun_prop)).continuousOn
  · rw [interior_Icc]
    intro x hx
    exact (hasDerivAt_G (c := c) (by linarith [hx.1]) (by linarith [hx.2]) hr0'
      hr1').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(hasDerivAt_G (c := c) (by linarith [hx.1]) (by linarith [hx.2]) hr0' hr1').deriv]
    exact hs x hx.1 hx.2

private theorem recip_eq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    1 / t + 1 / (1 - t) = 1 / (t * (1 - t)) := by
  rw [div_add_div _ _ ht0.ne' (sub_pos.mpr ht1).ne']
  congr 1
  ring

private theorem four_le_recip {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    4 ≤ 1 / t + 1 / (1 - t) := by
  rw [recip_eq ht0 ht1, le_div_iff₀ (mul_pos ht0 (sub_pos.mpr ht1))]
  nlinarith [sq_nonneg (t - 1 / 2)]

private theorem recip_anti {x y : ℝ} (hx0 : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    1 / y + 1 / (1 - y) ≤ 1 / x + 1 / (1 - x) := by
  rw [recip_eq (by linarith) (by linarith), recip_eq hx0 (by linarith)]
  apply one_div_le_one_div_of_le (mul_pos hx0 (by linarith))
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : (0 : ℝ) ≤ 1 - x - y)]

/-- Derivative of the logit plus an affine function. -/
private theorem hasDerivAt_logit {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a b : ℝ) :
    HasDerivAt (fun x => Real.log x - Real.log (1 - x) + a * x + b)
      (1 / q + 1 / (1 - q) + a) q := by
  have h1 : HasDerivAt Real.log q⁻¹ q := Real.hasDerivAt_log hq0.ne'
  have hl : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id' q).const_sub (1 : ℝ)
  have h2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1) / (1 - q)) q :=
    hl.log (sub_pos.mpr hq1).ne'
  have h3 : HasDerivAt (fun x : ℝ => a * x) (a * 1) q := (hasDerivAt_id' q).const_mul a
  exact (((h1.sub h2).add h3).add_const b).congr_deriv (by ring)

private theorem logit_mono (a b : ℝ) (ha : -4 ≤ a) :
    MonotoneOn (fun q => Real.log q - Real.log (1 - q) + a * q + b) (Set.Ioo 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · intro x hx
    exact (hasDerivAt_logit hx.1 hx.2 a b).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro x hx
    exact (hasDerivAt_logit hx.1 hx.2 a b).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro x hx
    rw [(hasDerivAt_logit hx.1 hx.2 a b).deriv]
    have := four_le_recip hx.1 hx.2
    linarith

private theorem logit_concave (a b : ℝ) :
    ConcaveOn ℝ (Set.Ioc 0 (1 / 2)) (fun q => Real.log q - Real.log (1 - q) + a * q + b) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioc 0 (1 / 2))
  · intro x hx
    exact (hasDerivAt_logit hx.1 (by linarith [hx.2]) a b).continuousAt.continuousWithinAt
  · rw [interior_Ioc]
    intro x hx
    exact (hasDerivAt_logit hx.1 (by linarith [hx.2]) a b).differentiableAt.differentiableWithinAt
  · rw [interior_Ioc]
    intro x hx y hy hxy
    rw [(hasDerivAt_logit hx.1 (by linarith [hx.2]) a b).deriv,
      (hasDerivAt_logit hy.1 (by linarith [hy.2]) a b).deriv]
    have := recip_anti hx.1 hxy hy.2.le
    linarith

/-- Concavity at a point between two others, in weighted form. -/
private theorem concave_pt {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {x y z : ℝ}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x ≤ y) (hyz : y ≤ z) (hxz : x < z) :
    (z - y) / (z - x) * f x + (y - x) / (z - x) * f z ≤ f y := by
  have hne : z - x ≠ 0 := (sub_pos.mpr hxz).ne'
  have ha : 0 ≤ (z - y) / (z - x) := div_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ (y - x) / (z - x) := div_nonneg (by linarith) (by linarith)
  have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hne]
    ring
  have h := hf.2 hx hz ha hb hab
  have hy : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]
    ring
  simp only [smul_eq_mul] at h
  rwa [hy] at h

/-- Sign pattern of a concave function on `(0, 1/2]` vanishing at `r` and at `1/2`. -/
private theorem concave_sign {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ioc 0 (1 / 2)) f) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1 / 2) (hfr : f r = 0) (hfh : f (1 / 2) = 0) {x : ℝ}
    (hx0 : 0 < x) : (x ≤ r → f x ≤ 0) ∧ (r ≤ x → x ≤ 1 / 2 → 0 ≤ f x) := by
  have hh : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_rfl⟩
  constructor
  · intro hxr
    rcases eq_or_lt_of_le hxr with h | h
    · rw [h, hfr]
    · have hc := concave_pt hf ⟨hx0, by linarith⟩ hh hxr hr.le (by linarith)
      rw [hfr, hfh, mul_zero, add_zero] at hc
      have hA : 0 < (1 / 2 - r) / (1 / 2 - x) := div_pos (by linarith) (by linarith)
      rcases le_or_gt (f x) 0 with h1 | h1
      · exact h1
      · have := mul_pos hA h1
        linarith
  · intro hrx hxh
    have hc := concave_pt hf ⟨hr0, hr.le⟩ hh hrx hxh hr
    rw [hfr, hfh, mul_zero, mul_zero, add_zero] at hc
    exact hc

/-- For `r ∈ (0, 1)` other than `1/2`, `owL r * (1 - 2r) = log (1 - r) - log r`. -/
theorem owL_mul_one_sub_two_mul {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : r ≠ 1 / 2) :
    owL r * (1 - 2 * r) = Real.log (1 - r) - Real.log r := by
  have h2 : 1 - 2 * r ≠ 0 := by
    intro h
    apply hr
    linarith
  rw [owL, if_neg hr, Real.log_div (sub_pos.mpr hr1).ne' hr0.ne', div_mul_cancel₀ _ h2]

/-- The coefficient at the centre: `owL (1/2) = 2`. -/
theorem owL_half : owL (1 / 2) = 2 := by
  simp [owL]

/-- Complementing both arguments preserves the divergence: `klBer (1 - q) (1 - r) = klBer q r`. -/
theorem klBer_one_sub_one_sub (q r : ℝ) : klBer (1 - q) (1 - r) = klBer q r := by
  unfold klBer
  simp only [sub_sub_cancel]
  ring

private theorem klBer_self_of_mem {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : klBer r r = 0 := by
  unfold klBer
  rw [div_self hr0.ne', div_self (sub_pos.mpr hr1).ne']
  simp

/-- Pinsker's inequality, the form the public statements below use. -/
private theorem pinsker {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    2 * (q - r) ^ 2 ≤ klBer q r := by
  have hmono := logit_mono (-4) 0 le_rfl
  have g1 := G_antitoneOn (c := 2) (u := 0) (v := r) hr0 hr1 le_rfl hr1.le
    (fun x hx0 hx1 => by
      have := hmono ⟨hx0, by linarith⟩ ⟨hr0, hr1⟩ hx1.le
      dsimp only at this
      linarith)
  have g2 := G_monotoneOn (c := 2) (u := r) (v := 1) hr0 hr1 hr0.le le_rfl
    (fun x hx0 hx1 => by
      have := hmono ⟨hr0, hr1⟩ ⟨by linarith, hx1⟩ hx0.le
      dsimp only at this
      linarith)
  have hGr := klBer_self_of_mem hr0 hr1
  rcases le_total q r with h | h
  · have := g1 ⟨hq0, h⟩ ⟨hr0.le, le_rfl⟩ h
    dsimp only at this
    nlinarith
  · have := g2 ⟨le_rfl, hr1.le⟩ ⟨h, hq1⟩ h
    dsimp only at this
    nlinarith

private theorem two_le_owL_lt {r : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2) : 2 ≤ owL r := by
  have hmono := logit_mono (-4) 0 le_rfl
  have h := hmono ⟨hr0, by linarith⟩ ⟨by norm_num, by norm_num⟩ hr.le
  dsimp only at h
  have h12 : Real.log (1 / 2) - Real.log (1 - 1 / 2) = 0 := by norm_num
  have hL := owL_mul_one_sub_two_mul hr0 (by linarith) hr.ne
  have key : 2 * (1 - 2 * r) ≤ owL r * (1 - 2 * r) := by linarith
  exact le_of_mul_le_mul_right key (by linarith)

/-- Ordentlich–Weinberger for `r < 1/2`. -/
private theorem ow_lt {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r) (hr : r < 1 / 2) :
    owL r * (q - r) ^ 2 ≤ klBer q r := by
  have hr1 : r < 1 := by linarith
  have hL := owL_mul_one_sub_two_mul hr0 hr1 hr.ne
  have hconc := logit_concave (-2 * owL r) (owL r)
  have hsign := fun x (hx : 0 < x) => concave_sign hconc hr0 hr
    (by linear_combination hL)
    (by
      have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [this]
      ring) hx
  have hDH : ∀ x : ℝ, Real.log x - Real.log (1 - x) - (Real.log r - Real.log (1 - r)) -
      owL r * (2 * (x - r)) = Real.log x - Real.log (1 - x) + -2 * owL r * x + owL r := by
    intro x
    linear_combination (-1 : ℝ) * hL
  have hodd : ∀ x : ℝ, Real.log (1 - x) - Real.log (1 - (1 - x)) + -2 * owL r * (1 - x) + owL r =
      -(Real.log x - Real.log (1 - x) + -2 * owL r * x + owL r) := by
    intro x
    rw [sub_sub_cancel]
    ring
  have g1 := G_antitoneOn (c := owL r) (u := 0) (v := r) hr0 hr1 le_rfl hr1.le
    (fun x hx0 hx1 => by
      rw [hDH]
      exact (hsign x hx0).1 hx1.le)
  have g2 := G_monotoneOn (c := owL r) (u := r) (v := 1 / 2) hr0 hr1 hr0.le (by norm_num)
    (fun x hx0 hx1 => by
      rw [hDH]
      exact (hsign x (by linarith)).2 hx0.le hx1.le)
  have g3 := G_antitoneOn (c := owL r) (u := 1 / 2) (v := 1 - r) hr0 hr1 (by norm_num)
    (by linarith)
    (fun x hx0 hx1 => by
      rw [hDH]
      have := (hsign (1 - x) (by linarith)).2 (by linarith) (by linarith)
      have := hodd x
      linarith)
  have g4 := G_monotoneOn (c := owL r) (u := 1 - r) (v := 1) hr0 hr1 (by linarith) le_rfl
    (fun x hx0 hx1 => by
      rw [hDH]
      have := (hsign (1 - x) (by linarith)).1 (by linarith)
      have := hodd x
      linarith)
  have hGr : klBer r r - owL r * (r - r) ^ 2 = 0 := by
    rw [klBer_self_of_mem hr0 hr1]
    ring
  have hG1r : klBer (1 - r) r - owL r * (1 - r - r) ^ 2 = 0 := by
    rw [klBer_eq_mul_log hr0.ne' (sub_pos.mpr hr1).ne', sub_sub_cancel]
    linear_combination (2 * r - 1) * hL
  have hr12 : r ≤ 1 / 2 := hr.le
  rcases le_total q r with h | h
  · have := g1 ⟨hq0, h⟩ ⟨hr0.le, le_rfl⟩ h
    dsimp only at this
    linarith
  rcases le_total q (1 / 2) with h' | h'
  · have := g2 ⟨le_rfl, hr12⟩ ⟨h, h'⟩ h
    dsimp only at this
    linarith
  rcases le_total q (1 - r) with h'' | h''
  · have := g3 ⟨h', h''⟩ ⟨by linarith, le_rfl⟩ h''
    dsimp only at this
    linarith
  · have := g4 ⟨le_rfl, by linarith⟩ ⟨h'', hq1⟩ h''
    dsimp only at this
    linarith

/-! ## Pinsker and Ordentlich–Weinberger -/

/-- For `q ∈ [0, 1]` and `r ∈ (0, 1)`, the Bernoulli divergence is nonnegative. -/
theorem klBer_nonneg {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ klBer q r := by
  have := pinsker hq0 hq1 hr0 hr1
  nlinarith [sq_nonneg (q - r)]

/-- Pinsker's inequality: for `q ∈ [0, 1]` and `r ∈ (0, 1)`, `2 (q - r)² ≤ klBer q r`. -/
theorem klBer_ge_two_sq {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    2 * (q - r) ^ 2 ≤ klBer q r := by
  exact pinsker hq0 hq1 hr0 hr1

/-- For `r ∈ (0, 1)`, the coefficient is symmetric about `1/2`: `owL (1 - r) = owL r`. -/
theorem owL_symm {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : owL (1 - r) = owL r := by
  by_cases h : r = 1 / 2
  · subst h
    norm_num
  · have h' : 1 - r ≠ 1 / 2 := by
      intro h'
      apply h
      linarith
    have hne : 1 - 2 * r ≠ 0 := by
      intro h''
      apply h
      linarith
    have e1 := owL_mul_one_sub_two_mul (r := 1 - r) (by linarith) (by linarith) h'
    have e2 := owL_mul_one_sub_two_mul hr0 hr1 h
    rw [sub_sub_cancel] at e1
    apply mul_right_cancel₀ hne
    linear_combination -e1 - e2

/-- For `r ∈ (0, 1)`, the coefficient is at least `2`, its value at `1/2`. -/
theorem two_le_owL {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 2 ≤ owL r := by
  rcases lt_trichotomy r (1 / 2) with h | h | h
  · exact two_le_owL_lt hr0 h
  · rw [h, owL_half]
  · rw [← owL_symm hr0 hr1]
    exact two_le_owL_lt (by linarith) (by linarith)

/-- The coefficient is antitone on `(0, 1/2]`. -/
theorem owL_antitoneOn : AntitoneOn owL (Set.Ioc 0 (1 / 2)) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hy.2 with h | h
  · rw [h, owL_half]
    exact two_le_owL hx.1 (by linarith [hx.2])
  · have hx1 : x < 1 / 2 := lt_of_le_of_lt hxy h
    have hc := concave_pt (logit_concave 0 0) (y := y) hx
      (⟨by norm_num, le_rfl⟩ : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2)) hxy h.le (by linarith)
    have h12 : Real.log (1 / 2) - Real.log (1 - 1 / 2) + 0 * (1 / 2) + 0 = 0 := by norm_num
    rw [h12, mul_zero, add_zero] at hc
    have hLx := owL_mul_one_sub_two_mul hx.1 (by linarith) hx1.ne
    have hLy := owL_mul_one_sub_two_mul hy.1 (by linarith) h.ne
    have hne : (1 : ℝ) / 2 - x ≠ 0 := (sub_pos.mpr hx1).ne'
    have e : (1 / 2 - y) / (1 / 2 - x) * (1 - 2 * x) = 1 - 2 * y := by
      rw [div_mul_eq_mul_div, div_eq_iff hne]
      ring
    have hA : (1 / 2 - y) / (1 / 2 - x) * (Real.log x - Real.log (1 - x) + 0 * x + 0) =
        -(owL x * (1 - 2 * y)) := by
      linear_combination (1 / 2 - y) / (1 / 2 - x) * hLx - owL x * e
    have key : owL y * (1 - 2 * y) ≤ owL x * (1 - 2 * y) := by linarith
    exact le_of_mul_le_mul_right key (by linarith)

/-- The Ordentlich–Weinberger refinement of Pinsker's inequality: for `q ∈ [0, 1]` and
`r ∈ (0, 1)`, `owL r * (q - r)² ≤ klBer q r`. -/
theorem klBer_ge_owL_mul_sq {q r : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    owL r * (q - r) ^ 2 ≤ klBer q r := by
  rcases lt_trichotomy r (1 / 2) with h | h | h
  · exact ow_lt hq0 hq1 hr0 h
  · rw [h, owL_half]
    rw [h] at hr0 hr1
    exact pinsker hq0 hq1 hr0 hr1
  · have := ow_lt (q := 1 - q) (r := 1 - r) (by linarith) (by linarith) (by linarith)
      (by linarith)
    rw [owL_symm hr0 hr1, klBer_one_sub_one_sub] at this
    have e : (1 - q - (1 - r)) ^ 2 = (q - r) ^ 2 := by ring
    rw [e] at this
    exact this

/-- The divergence of a Bernoulli law from itself is zero, for every `r`: at `r = 0` and `r = 1`
through `Real.log 0 = 0`. -/
theorem klBer_self (r : ℝ) : klBer r r = 0 := by
  have h : ∀ x : ℝ, Real.log (x / x) = 0 := fun x => by
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · rw [div_self hx, Real.log_one]
  simp only [klBer, h, mul_zero, add_zero]

end

end BinaryRow

end StochasticToDeterministicLatents
