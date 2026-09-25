import StochasticToDeterministicLatents.BinaryRow.Bernoulli

/-!
# The Jensen gap of binary entropy on a band

For `0 < ε < q < 1 - ε`, row means `r₀ ∈ [ε, q]` and `r₁ ∈ [1 - q, 1 - ε]` and a weight
`w ∈ [0, 1]`,

  `h((1 - w) r₀ + w r₁) - (1 - w) h(r₀) - w h(r₁) ≤ P · w (1 - w) (r₁ - r₀)²`,
  `P = klBer (1 - q) ε / (1 - q - ε)²`

(`binEntropy_jensenGap_le`). The row means need not be ordered. Everything is in nats, through
`Real.log`.

The proof has two steps.

* Along a segment from `a` to `b` in `(0, 1)`, the gap is at most `M w (1 - w) (b - a)²` as soon as
  `klBer b a ≤ M (b - a)²` and `klBer a b ≤ M (b - a)²` (`binEntropy_gap_le_of_klBer_le`). The
  difference `φ` of the two sides vanishes at both ends, the endpoint conditions fix the signs of
  `φ'` there, and `φ''` has the sign of `1/(π(1 - π)) - 2M`, which cannot be negative, positive,
  negative in turn because `π(1 - π)` is concave along the segment. Five mean value steps give
  `φ ≥ 0`.
* The two endpoint conditions hold with `M = P` on the whole rectangle. The ratio
  `klBer p s / (p - s)²` is antitone in `p` below `1 - s` and monotone above it, by the divergence
  asymmetry `klBer s p ≤ klBer p s` for `s ≤ p ≤ 1 - s` (`klBer_div_sq_antitoneOn` is the first
  half at `s = ε`), and its sign in `s` is read off a function that increases on `(0, 1/2]`. On the
  strip `[1 - q, q]` a curvature comparison is used instead.

This is not the divided-difference argument, which writes the normalized gap as an integral of
`1/(x(1 - x))` and uses joint convexity of the divergence ratio to reduce to four corners.

## Attribution

Original to this repository.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Set

/-! ### Generic calculus helpers -/

private theorem aux_le_of_deriv_nonneg {f f' : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hd : ∀ x ∈ Icc u v, HasDerivAt f (f' x) x) (hs : ∀ x ∈ Ioo u v, 0 ≤ f' x) :
    f u ≤ f v := by
  rcases eq_or_lt_of_le huv with h | h
  · rw [h]
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    have h1 := hs c hc
    rw [hcd, le_div_iff₀ (sub_pos.2 h), zero_mul] at h1
    linarith

private theorem aux_le_of_deriv_nonpos {f f' : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hd : ∀ x ∈ Icc u v, HasDerivAt f (f' x) x) (hs : ∀ x ∈ Ioo u v, f' x ≤ 0) :
    f v ≤ f u := by
  have h : -f u ≤ -f v := aux_le_of_deriv_nonneg (f := fun x => -f x) (f' := fun x => -f' x) huv
    (fun x hx => (hd x hx).neg) (fun x hx => by linarith [hs x hx])
  linarith

private theorem aux_lt_of_deriv_pos {f f' : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hd : ∀ x ∈ Icc u v, HasDerivAt f (f' x) x) (hs : ∀ x ∈ Ioo u v, 0 < f' x) :
    f u < f v := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f f' huv
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Ioo_subset_Icc_self hx))
  have h1 := hs c hc
  rw [hcd, lt_div_iff₀ (sub_pos.2 huv), zero_mul] at h1
  linarith

private theorem aux_recip_mul {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (1 / x + 1 / (1 - x)) * (x * (1 - x)) = 1 := by
  have h1 : (1 : ℝ) - x ≠ 0 := (sub_pos.2 hx1).ne'
  have e1 : 1 / x * x = 1 := one_div_mul_cancel hx0.ne'
  have e2 : 1 / (1 - x) * (1 - x) = 1 := one_div_mul_cancel h1
  calc (1 / x + 1 / (1 - x)) * (x * (1 - x))
      = (1 / x * x) * (1 - x) + (1 / (1 - x) * (1 - x)) * x := by ring
    _ = 1 := by rw [e1, e2]; ring

private theorem aux_G_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 / x + 1 / (1 - x) = 1 / (x * (1 - x)) := by
  have hp : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.2 hx1)
  rw [eq_div_iff hp.ne']
  exact aux_recip_mul hx0 hx1

private theorem aux_inv_sq_nonneg {z : ℝ} (hz0 : 0 < z) (hz : z ≤ 1 / 2) :
    0 ≤ 1 / z ^ 2 - 1 / (1 - z) ^ 2 := by
  have h : 1 / (1 - z) ^ 2 ≤ 1 / z ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hz0 2) (by nlinarith)
  linarith

private theorem aux_inv_sq_nonpos {z : ℝ} (hz : 1 / 2 ≤ z) (hz1 : z < 1) :
    1 / z ^ 2 - 1 / (1 - z) ^ 2 ≤ 0 := by
  have h : 1 / z ^ 2 ≤ 1 / (1 - z) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos (sub_pos.2 hz1) 2) (by nlinarith)
  linarith

private theorem aux_hasDerivAt_sq_left (a x : ℝ) :
    HasDerivAt (fun p : ℝ => (p - a) ^ 2) (2 * (x - a)) x :=
  (((hasDerivAt_id' x).sub_const a).pow 2).congr_deriv (by norm_num)

private theorem aux_hasDerivAt_sq_right (p s : ℝ) :
    HasDerivAt (fun z : ℝ => (p - z) ^ 2) (-(2 * (p - s))) s :=
  (((hasDerivAt_id' s).const_sub p).pow 2).congr_deriv (by norm_num)

/-! ### Derivatives of the divergence and of binary entropy -/

private theorem aux_hasDerivAt_klBer_left {q r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hr0 : r ≠ 0)
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

private theorem aux_hasDerivAt_klBer_right (x : ℝ) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun z => klBer x z) ((y - x) * (1 / y + 1 / (1 - y))) y := by
  have hy0' : y ≠ 0 := hy0.ne'
  have hy1' : (1 : ℝ) - y ≠ 0 := (sub_pos.2 hy1).ne'
  have hev : (fun z => klBer x z) =ᶠ[nhds y] fun z => x * Real.log x - x * Real.log z +
      ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - z)) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hy0, hy1⟩) fun z hz =>
      klBer_eq_mul_log hz.1.ne' (sub_pos.2 hz.2).ne'
  have hl : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
    simpa using (hasDerivAt_id' y).const_sub (1 : ℝ)
  have h1 : HasDerivAt (fun z => Real.log z) y⁻¹ y := Real.hasDerivAt_log hy0'
  have h2 : HasDerivAt (fun z => Real.log (1 - z)) ((-1) / (1 - y)) y := hl.log hy1'
  have h := ((h1.const_mul x).const_sub (x * Real.log x)).add
    ((h2.const_mul (1 - x)).const_sub ((1 - x) * Real.log (1 - x)))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq hev
  field_simp
  ring

private theorem aux_binEntropy_eq (x : ℝ) :
    Real.binEntropy x = -(x * Real.log x) - (1 - x) * Real.log (1 - x) := by
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  ring

/-- For `s ∈ (0, 1)`, the Bregman form `klBer p s = h(s) + h'(s)(p - s) - h(p)` with
`h'(s) = log (1 - s) - log s`, in nats. -/
theorem klBer_eq_bregman {p s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    klBer p s = Real.binEntropy s + (Real.log (1 - s) - Real.log s) * (p - s) -
      Real.binEntropy p := by
  rw [klBer_eq_mul_log hs0.ne' (sub_pos.2 hs1).ne', aux_binEntropy_eq, aux_binEntropy_eq]
  ring

private theorem aux_klBer_add {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    klBer a b + klBer b a =
      (b - a) * (Real.log b - Real.log (1 - b) - (Real.log a - Real.log (1 - a))) := by
  rw [klBer_eq_mul_log hb0.ne' (sub_pos.2 hb1).ne', klBer_eq_mul_log ha0.ne' (sub_pos.2 ha1).ne']
  ring

/-! ### The gap along a segment -/

private theorem aux_hasDerivAt_phi (a Δ M c₀ c₁ : ℝ) {z : ℝ} (hp0 : 0 < a + z * Δ)
    (hp1 : a + z * Δ < 1) :
    HasDerivAt (fun y => M * (y * (1 - y) * Δ ^ 2) -
        (Real.binEntropy (a + y * Δ) - (1 - y) * c₀ - y * c₁))
      (M * ((1 - 2 * z) * Δ ^ 2) -
        ((Real.log (1 - (a + z * Δ)) - Real.log (a + z * Δ)) * Δ + (c₀ - c₁))) z := by
  have hi : HasDerivAt (fun y => a + y * Δ) Δ z :=
    (((hasDerivAt_id' z).mul_const Δ).const_add a).congr_deriv (one_mul Δ)
  have hH0 := (Real.hasDerivAt_binEntropy hp0.ne' hp1.ne).comp z hi
  have hH : HasDerivAt (fun y => Real.binEntropy (a + y * Δ))
      ((Real.log (1 - (a + z * Δ)) - Real.log (a + z * Δ)) * Δ) z := hH0
  have hq : HasDerivAt (fun y : ℝ => y * (1 - y) * Δ ^ 2) ((1 - 2 * z) * Δ ^ 2) z :=
    (((hasDerivAt_id' z).mul ((hasDerivAt_id' z).const_sub 1)).mul_const (Δ ^ 2)).congr_deriv
      (by ring)
  have h0 : HasDerivAt (fun y : ℝ => (1 - y) * c₀) (-1 * c₀) z :=
    ((hasDerivAt_id' z).const_sub 1).mul_const c₀
  have h1 : HasDerivAt (fun y : ℝ => y * c₁) (1 * c₁) z := (hasDerivAt_id' z).mul_const c₁
  exact ((hq.const_mul M).sub ((hH.sub h0).sub h1)).congr_deriv (by ring)

private theorem aux_hasDerivAt_psi (a Δ M c : ℝ) {z : ℝ} (hp0 : 0 < a + z * Δ)
    (hp1 : a + z * Δ < 1) :
    HasDerivAt (fun y => M * ((1 - 2 * y) * Δ ^ 2) -
        ((Real.log (1 - (a + y * Δ)) - Real.log (a + y * Δ)) * Δ + c))
      (Δ ^ 2 * (1 / (a + z * Δ) + 1 / (1 - (a + z * Δ)) - 2 * M)) z := by
  have hi : HasDerivAt (fun y => a + y * Δ) Δ z :=
    (((hasDerivAt_id' z).mul_const Δ).const_add a).congr_deriv (one_mul Δ)
  have hj : HasDerivAt (fun y => 1 - (a + y * Δ)) (-Δ) z := hi.const_sub 1
  have hl1 : HasDerivAt (fun y => Real.log (1 - (a + y * Δ))) (-Δ / (1 - (a + z * Δ))) z :=
    hj.log (sub_pos.2 hp1).ne'
  have hl0 : HasDerivAt (fun y => Real.log (a + y * Δ)) (Δ / (a + z * Δ)) z := hi.log hp0.ne'
  have hlin : HasDerivAt (fun y : ℝ => (1 - 2 * y) * Δ ^ 2) (-(2 * 1) * Δ ^ 2) z :=
    (((hasDerivAt_id' z).const_mul 2).const_sub 1).mul_const (Δ ^ 2)
  exact ((hlin.const_mul M).sub (((hl1.sub hl0).mul_const Δ).add_const c)).congr_deriv (by ring)

/-- The sign argument: a function vanishing at `0` and `1`, whose derivative is `≥ 0` at `0` and
`≤ 0` at `1`, and whose second derivative is never negative, positive, negative in that order,
is nonnegative on `(0, 1)`. -/
private theorem aux_shape {φ ψ ψ' : ℝ → ℝ} {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (hφ : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt φ (ψ z) z)
    (hψ : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (ψ' z) z)
    (h0 : φ 0 = 0) (h1 : φ 1 = 0) (hψ0 : 0 ≤ ψ 0) (hψ1 : ψ 1 ≤ 0)
    (hq : ∀ s t u : ℝ, 0 < s → s < t → t < u → u < 1 → ψ' s < 0 → ψ' u < 0 → ψ' t ≤ 0) :
    0 ≤ φ w := by
  by_contra hneg
  push Not at hneg
  have mvt : ∀ (f f' : ℝ → ℝ) (x y : ℝ), 0 ≤ x → x < y → y ≤ 1 →
      (∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' z) z) →
      ∃ c ∈ Ioo x y, f' c = (f y - f x) / (y - x) := by
    intro f f' x y hx hxy hy hd
    exact exists_hasDerivAt_eq_slope f f' hxy
      (fun z hz => (hd z ⟨le_trans hx hz.1, le_trans hz.2 hy⟩).continuousAt.continuousWithinAt)
      (fun z hz => hd z ⟨le_trans hx hz.1.le, le_trans hz.2.le hy⟩)
  obtain ⟨x, hx, hxd⟩ := mvt φ ψ 0 w le_rfl hw0 hw1.le hφ
  obtain ⟨y, hy, hyd⟩ := mvt φ ψ w 1 hw0.le hw1 le_rfl hφ
  have hψx : ψ x < 0 := by
    rw [hxd, h0]
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hψy : 0 < ψ y := by
    rw [hyd, h1]
    exact div_pos (by linarith) (by linarith)
  obtain ⟨s, hs, hsd⟩ := mvt ψ ψ' 0 x le_rfl hx.1 (by linarith [hx.2]) hψ
  obtain ⟨t, ht, htd⟩ := mvt ψ ψ' x y hx.1.le (by linarith [hx.2, hy.1]) (by linarith [hy.2]) hψ
  obtain ⟨u, hu, hud⟩ := mvt ψ ψ' y 1 (by linarith [hy.1]) hy.2 le_rfl hψ
  have hs' : ψ' s < 0 := by
    rw [hsd]
    exact div_neg_of_neg_of_pos (by linarith) (by linarith [hx.1])
  have ht' : 0 < ψ' t := by
    rw [htd]
    exact div_pos (by linarith) (by linarith [hx.2, hy.1])
  have hu' : ψ' u < 0 := by
    rw [hud]
    exact div_neg_of_neg_of_pos (by linarith) (by linarith [hy.2])
  have := hq s t u hs.1 (by linarith [hs.2, ht.1]) (by linarith [ht.2, hu.1]) hu.2 hs' hu'
  linarith

/-- `π(1 - π)` is concave along the segment, so the curvature `1/π + 1/(1 - π)` cannot exceed
`2M` strictly between two points where it is below `2M`. -/
private theorem aux_quasi {a Δ M s t u : ℝ} (hst : s < t) (htu : t < u)
    (hps : 0 < a + s * Δ ∧ a + s * Δ < 1) (hpt : 0 < a + t * Δ ∧ a + t * Δ < 1)
    (hpu : 0 < a + u * Δ ∧ a + u * Δ < 1)
    (hs : Δ ^ 2 * (1 / (a + s * Δ) + 1 / (1 - (a + s * Δ)) - 2 * M) < 0)
    (hu : Δ ^ 2 * (1 / (a + u * Δ) + 1 / (1 - (a + u * Δ)) - 2 * M) < 0) :
    Δ ^ 2 * (1 / (a + t * Δ) + 1 / (1 - (a + t * Δ)) - 2 * M) ≤ 0 := by
  have key : ∀ p : ℝ, 0 < p → p < 1 →
      (1 / p + 1 / (1 - p) - 2 * M < 0 ↔ 1 < 2 * M * (p * (1 - p))) := by
    intro p hp0 hp1
    have hm := aux_recip_mul hp0 hp1
    have hQ : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.2 hp1)
    constructor
    · intro h
      have := mul_lt_mul_of_pos_right h hQ
      linarith
    · intro h
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hQ.le
      linarith
  have pos_of : ∀ X : ℝ, Δ ^ 2 * X < 0 → X < 0 := by
    intro X hX
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sq_nonneg Δ) hc]
  have h1 := (key _ hps.1 hps.2).1 (pos_of _ hs)
  have h2 := (key _ hpu.1 hpu.2).1 (pos_of _ hu)
  have e : (u - s) * ((a + t * Δ) * (1 - (a + t * Δ))) =
      (u - t) * ((a + s * Δ) * (1 - (a + s * Δ))) + (t - s) * ((a + u * Δ) * (1 - (a + u * Δ))) +
        Δ ^ 2 * ((u - t) * (t - s) * (u - s)) := by ring
  have hQs0 : 0 < (a + s * Δ) * (1 - (a + s * Δ)) := mul_pos hps.1 (sub_pos.2 hps.2)
  have hM : 0 < M := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -M) hQs0.le]
  have h3 : 0 ≤ Δ ^ 2 * ((u - t) * (t - s) * (u - s)) :=
    mul_nonneg (sq_nonneg Δ)
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have h4 : 1 < 2 * M * ((a + t * Δ) * (1 - (a + t * Δ))) := by
    have h5 := mul_lt_mul_of_pos_left h1 (by linarith : (0 : ℝ) < u - t)
    have h6 := mul_lt_mul_of_pos_left h2 (by linarith : (0 : ℝ) < t - s)
    have h7 : 0 ≤ 2 * M * (Δ ^ 2 * ((u - t) * (t - s) * (u - s))) := mul_nonneg (by linarith) h3
    have h8 : (u - s) * 1 < (u - s) * (2 * M * ((a + t * Δ) * (1 - (a + t * Δ)))) := by
      have e2 : (u - s) * (2 * M * ((a + t * Δ) * (1 - (a + t * Δ)))) =
          (u - t) * (2 * M * ((a + s * Δ) * (1 - (a + s * Δ)))) +
            (t - s) * (2 * M * ((a + u * Δ) * (1 - (a + u * Δ)))) +
            2 * M * (Δ ^ 2 * ((u - t) * (t - s) * (u - s))) := by
        linear_combination 2 * M * e
      rw [e2]
      linarith
    exact lt_of_mul_lt_mul_left h8 (by linarith)
  have h9 := (key _ hpt.1 hpt.2).2 h4
  nlinarith [mul_nonneg (sq_nonneg Δ) (neg_nonneg.2 h9.le)]

/-- For `a, b ∈ (0, 1)` and `w ∈ [0, 1]`, if both divergences `klBer b a` and `klBer a b` are
at most `M (b - a)²`, then the Jensen gap of binary entropy at `a + w (b - a)` is at most
`M w (1 - w) (b - a)²`, in nats. -/
theorem binEntropy_gap_le_of_klBer_le {a b M w : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b)
    (hb1 : b < 1)
    (hA : klBer b a ≤ M * (b - a) ^ 2) (hB : klBer a b ≤ M * (b - a) ^ 2)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Real.binEntropy (a + w * (b - a)) - (1 - w) * Real.binEntropy a - w * Real.binEntropy b ≤
      M * (w * (1 - w) * (b - a) ^ 2) := by
  have hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < a + z * (b - a) ∧ a + z * (b - a) < 1 := by
    intro z hz
    have hm : 0 < min a b := lt_min ha0 hb0
    have hM : max a b < 1 := max_lt ha1 hb1
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hz.2) (sub_nonneg.2 (min_le_left a b)),
        mul_nonneg hz.1 (sub_nonneg.2 (min_le_right a b))]
    · nlinarith [mul_nonneg (sub_nonneg.2 hz.2) (sub_nonneg.2 (le_max_left a b)),
        mul_nonneg hz.1 (sub_nonneg.2 (le_max_right a b))]
  rcases eq_or_lt_of_le hw0 with h | hw0'
  · subst h
    simp
  rcases eq_or_lt_of_le hw1 with h | hw1'
  · subst h
    rw [show a + 1 * (b - a) = b by ring]
    simp
  have key : 0 ≤ M * (w * (1 - w) * (b - a) ^ 2) - (Real.binEntropy (a + w * (b - a)) -
      (1 - w) * Real.binEntropy a - w * Real.binEntropy b) := aux_shape (w := w)
    (φ := fun z => M * (z * (1 - z) * (b - a) ^ 2) -
      (Real.binEntropy (a + z * (b - a)) - (1 - z) * Real.binEntropy a - z * Real.binEntropy b))
    (ψ := fun z => M * ((1 - 2 * z) * (b - a) ^ 2) -
      ((Real.log (1 - (a + z * (b - a))) - Real.log (a + z * (b - a))) * (b - a) +
        (Real.binEntropy a - Real.binEntropy b)))
    (ψ' := fun z => (b - a) ^ 2 * (1 / (a + z * (b - a)) + 1 / (1 - (a + z * (b - a))) - 2 * M))
    hw0' hw1'
    (fun z hz => aux_hasDerivAt_phi a (b - a) M (Real.binEntropy a) (Real.binEntropy b)
      (hpos z hz).1 (hpos z hz).2)
    (fun z hz => aux_hasDerivAt_psi a (b - a) M (Real.binEntropy a - Real.binEntropy b)
      (hpos z hz).1 (hpos z hz).2)
    (by simp)
    (by
      show M * (1 * (1 - 1) * (b - a) ^ 2) - (Real.binEntropy (a + 1 * (b - a)) -
        (1 - 1) * Real.binEntropy a - 1 * Real.binEntropy b) = 0
      rw [show a + 1 * (b - a) = b by ring]
      ring)
    (by
      show 0 ≤ M * ((1 - 2 * 0) * (b - a) ^ 2) - ((Real.log (1 - (a + 0 * (b - a))) -
        Real.log (a + 0 * (b - a))) * (b - a) + (Real.binEntropy a - Real.binEntropy b))
      rw [show a + 0 * (b - a) = a by ring]
      have e := klBer_eq_bregman (p := b) ha0 ha1
      linarith)
    (by
      show M * ((1 - 2 * 1) * (b - a) ^ 2) - ((Real.log (1 - (a + 1 * (b - a))) -
        Real.log (a + 1 * (b - a))) * (b - a) + (Real.binEntropy a - Real.binEntropy b)) ≤ 0
      rw [show a + 1 * (b - a) = b by ring]
      have e := klBer_eq_bregman (p := a) hb0 hb1
      linarith)
    (fun s t u hs hst htu hu hs' hu' => aux_quasi hst htu (hpos s ⟨hs.le, by linarith⟩)
      (hpos t ⟨by linarith, by linarith⟩) (hpos u ⟨by linarith, hu.le⟩) hs' hu')
  linarith

/-! ### The divergence ratio -/

/-- The divergence ratio `klBer p s / (p - s)²`. -/
private def aux_K (p s : ℝ) : ℝ := klBer p s / (p - s) ^ 2

/-- The divergence asymmetry `klBer x a - klBer a x`. -/
private def aux_d (a x : ℝ) : ℝ := klBer x a - klBer a x

/-- The derivative of `aux_d a`. -/
private def aux_g (a x : ℝ) : ℝ :=
  Real.log x - Real.log (1 - x) - (Real.log a - Real.log (1 - a)) - (x - a) * (1 / x + 1 / (1 - x))

/-- The sign function of the second-argument derivative of the ratio. -/
private def aux_E (p s : ℝ) : ℝ := 2 * klBer p s - (p - s) ^ 2 * (1 / s + 1 / (1 - s))

private theorem aux_hasDerivAt_Kleft {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx0 : 0 < x)
    (hx1 : x < 1)
    (hxa : x ≠ a) :
    HasDerivAt (fun p => aux_K p a)
      ((x - a) * (klBer a x - klBer x a) / ((x - a) ^ 2) ^ 2) x := by
  have h1 := aux_hasDerivAt_klBer_left hx0 hx1 ha0.ne' (sub_pos.2 ha1).ne'
  have h2 := aux_hasDerivAt_sq_left a x
  have hne : (x - a) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hxa)
  have e := aux_klBer_add ha0 ha1 hx0 hx1
  refine (h1.div h2 hne).congr_deriv ?_
  congr 1
  linear_combination (a - x) * e

private theorem aux_hasDerivAt_Kright {p s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsp : s ≠ p) :
    HasDerivAt (aux_K p) ((p - s) * aux_E p s / ((p - s) ^ 2) ^ 2) s := by
  have h1 := aux_hasDerivAt_klBer_right p hs0 hs1
  have h2 := aux_hasDerivAt_sq_right p s
  have hne : (p - s) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hsp.symm)
  have h := h1.div h2 hne
  unfold aux_E
  exact h.congr_deriv (by ring)

private theorem aux_K_anti {a u v : ℝ} (ha0 : 0 < a) (hau : a < u) (huv : u ≤ v) (hv1 : v < 1)
    (hd : ∀ x ∈ Ioo u v, 0 ≤ aux_d a x) : aux_K v a ≤ aux_K u a := by
  have ha1 : a < 1 := by linarith
  refine aux_le_of_deriv_nonpos (f := fun p => aux_K p a) huv
    (fun x hx => aux_hasDerivAt_Kleft ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.1] : a < x).ne') (fun x hx => ?_)
  have h1 : 0 < x - a := by linarith [hx.1]
  have hp : 0 < ((x - a) ^ 2) ^ 2 := pow_pos (pow_pos h1 2) 2
  have h2 := hd x hx
  unfold aux_d at h2
  rw [div_le_iff₀ hp, zero_mul]
  nlinarith [mul_nonneg h1.le h2]

private theorem aux_K_mono {a u v : ℝ} (ha0 : 0 < a) (hau : a < u) (huv : u ≤ v) (hv1 : v < 1)
    (hd : ∀ x ∈ Ioo u v, aux_d a x ≤ 0) : aux_K u a ≤ aux_K v a := by
  have ha1 : a < 1 := by linarith
  refine aux_le_of_deriv_nonneg (f := fun p => aux_K p a) huv
    (fun x hx => aux_hasDerivAt_Kleft ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.1] : a < x).ne') (fun x hx => ?_)
  have h1 : 0 < x - a := by linarith [hx.1]
  have hp : 0 < ((x - a) ^ 2) ^ 2 := pow_pos (pow_pos h1 2) 2
  have h2 := hd x hx
  unfold aux_d at h2
  rw [le_div_iff₀ hp, zero_mul]
  nlinarith [mul_nonneg h1.le (by linarith : (0 : ℝ) ≤ klBer a x - klBer x a)]

private theorem aux_Kright_anti {p u v : ℝ} (hu0 : 0 < u) (huv : u ≤ v) (hvp : v < p) (hp1 : p < 1)
    (he : ∀ x ∈ Ioo u v, aux_E p x ≤ 0) : aux_K p v ≤ aux_K p u := by
  refine aux_le_of_deriv_nonpos (f := aux_K p) huv
    (fun x hx => aux_hasDerivAt_Kright (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.2] : x < p).ne) (fun x hx => ?_)
  have h1 : 0 < p - x := by linarith [hx.2]
  have hp : 0 < ((p - x) ^ 2) ^ 2 := pow_pos (pow_pos h1 2) 2
  rw [div_le_iff₀ hp, zero_mul]
  nlinarith [mul_nonneg h1.le (neg_nonneg.2 (he x hx))]

private theorem aux_Kright_mono {p u v : ℝ} (hu0 : 0 < u) (huv : u ≤ v) (hvp : v < p) (hp1 : p < 1)
    (he : ∀ x ∈ Ioo u v, 0 ≤ aux_E p x) : aux_K p u ≤ aux_K p v := by
  refine aux_le_of_deriv_nonneg (f := aux_K p) huv
    (fun x hx => aux_hasDerivAt_Kright (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.2] : x < p).ne) (fun x hx => ?_)
  have h1 : 0 < p - x := by linarith [hx.2]
  have hp : 0 < ((p - x) ^ 2) ^ 2 := pow_pos (pow_pos h1 2) 2
  rw [le_div_iff₀ hp, zero_mul]
  exact mul_nonneg h1.le (he x hx)

/-! ### The asymmetry `klBer x a - klBer a x` -/

private theorem aux_hasDerivAt_d {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (aux_d a) (aux_g a x) x :=
  (aux_hasDerivAt_klBer_left hx0 hx1 ha0.ne' (sub_pos.2 ha1).ne').sub
    (aux_hasDerivAt_klBer_right a hx0 hx1)

private theorem aux_hasDerivAt_g {a x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (aux_g a) ((x - a) * (1 / x ^ 2 - 1 / (1 - x) ^ 2)) x := by
  have hx1' : (1 : ℝ) - x ≠ 0 := (sub_pos.2 hx1).ne'
  have hl : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub (1 : ℝ)
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have h2 : HasDerivAt (fun z => Real.log (1 - z)) ((-1) / (1 - x)) x := hl.log hx1'
  have hG : HasDerivAt (fun z : ℝ => 1 / z + 1 / (1 - z))
      ((0 * x - 1 * 1) / x ^ 2 + (0 * (1 - x) - 1 * (-1)) / (1 - x) ^ 2) x :=
    ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id' x) hx0.ne').add
      ((hasDerivAt_const x (1 : ℝ)).div hl hx1')
  have hm := ((hasDerivAt_id' x).sub_const a).mul hG
  have h := ((h1.sub h2).sub_const (Real.log a - Real.log (1 - a))).sub hm
  exact h.congr_deriv (by ring)

private theorem aux_hasDerivAt_E (p : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (aux_E p) ((p - s) ^ 2 * (1 / s ^ 2 - 1 / (1 - s) ^ 2)) s := by
  have hs1' : (1 : ℝ) - s ≠ 0 := (sub_pos.2 hs1).ne'
  have hl : HasDerivAt (fun z : ℝ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id' s).const_sub (1 : ℝ)
  have hG : HasDerivAt (fun z : ℝ => 1 / z + 1 / (1 - z))
      ((0 * s - 1 * 1) / s ^ 2 + (0 * (1 - s) - 1 * (-1)) / (1 - s) ^ 2) s :=
    ((hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id' s) hs0.ne').add
      ((hasDerivAt_const s (1 : ℝ)).div hl hs1')
  have h := ((aux_hasDerivAt_klBer_right p hs0 hs1).const_mul 2).sub
    ((aux_hasDerivAt_sq_right p s).mul hG)
  exact h.congr_deriv (by ring)

private theorem aux_g_self (a : ℝ) : aux_g a a = 0 := by
  unfold aux_g
  ring

private theorem aux_d_self (a : ℝ) : aux_d a a = 0 := by
  unfold aux_d
  ring

private theorem aux_d_one_sub (a : ℝ) : aux_d a (1 - a) = 0 := by
  unfold aux_d
  have h := klBer_one_sub_one_sub a (1 - a)
  rw [sub_sub_cancel] at h
  linarith

private theorem aux_E_self (p : ℝ) : aux_E p p = 0 := by
  unfold aux_E
  rw [klBer_self]
  ring

private theorem aux_g_nonneg {a x : ℝ} (ha0 : 0 < a) (hax : a ≤ x) (hx : x ≤ 1 / 2) :
    0 ≤ aux_g a x := by
  have h := aux_le_of_deriv_nonneg (f := aux_g a) hax
    (fun z hz => aux_hasDerivAt_g (a := a) (by linarith [hz.1]) (by linarith [hz.2]))
    (fun z hz => mul_nonneg (by linarith [hz.1])
      (aux_inv_sq_nonneg (by linarith [hz.1]) (by linarith [hz.2])))
  rwa [aux_g_self] at h

private theorem aux_g_anti {a x y : ℝ} (hx : 1 / 2 ≤ x) (hxy : x ≤ y) (hy : y < 1) (hax : a ≤ x) :
    aux_g a y ≤ aux_g a x :=
  aux_le_of_deriv_nonpos (f := aux_g a) hxy
    (fun z hz => aux_hasDerivAt_g (a := a) (by linarith [hz.1]) (by linarith [hz.2]))
    (fun z hz => by
      nlinarith [mul_nonneg (by linarith [hz.1] : (0 : ℝ) ≤ z - a)
        (neg_nonneg.2 (aux_inv_sq_nonpos (z := z) (by linarith [hz.1]) (by linarith [hz.2])))])

private theorem aux_d_nonneg_left {a x : ℝ} (ha0 : 0 < a) (hax : a ≤ x) (hx : x ≤ 1 / 2) :
    0 ≤ aux_d a x := by
  have h := aux_le_of_deriv_nonneg (f := aux_d a) (f' := aux_g a) hax
    (fun z hz => aux_hasDerivAt_d ha0 (by linarith) (by linarith [hz.1]) (by linarith [hz.2]))
    (fun z hz => aux_g_nonneg ha0 hz.1.le (by linarith [hz.2]))
  rwa [aux_d_self] at h

/-- For `a < 1/2` and `a ≤ x ≤ 1 - a`: `klBer a x ≤ klBer x a`. -/
private theorem aux_d_nonneg {a x : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hax : a ≤ x)
    (hx : x ≤ 1 - a) :
    0 ≤ aux_d a x := by
  have ha1 : a < 1 := by linarith
  have hder : ∀ z ∈ Icc (1 / 2 : ℝ) (1 - a), HasDerivAt (aux_d a) (aux_g a z) z :=
    fun z hz => aux_hasDerivAt_d ha0 ha1 (by linarith [hz.1]) (by linarith [hz.2])
  rcases le_total x (1 / 2) with h | h
  · exact aux_d_nonneg_left ha0 hax h
  · have hx1 : x < 1 := by linarith
    rcases le_total 0 (aux_g a x) with hg | hg
    · have h2 := aux_le_of_deriv_nonneg (f := aux_d a) (f' := aux_g a) h
        (fun z hz => hder z ⟨hz.1, by linarith [hz.2]⟩)
        (fun z hz => le_trans hg (aux_g_anti hz.1.le hz.2.le hx1 (by linarith [hz.1])))
      linarith [aux_d_nonneg_left ha0 ha.le (le_refl (1 / 2 : ℝ))]
    · have h2 := aux_le_of_deriv_nonpos (f := aux_d a) (f' := aux_g a) hx
        (fun z hz => hder z ⟨by linarith [hz.1], hz.2⟩)
        (fun z hz => le_trans (aux_g_anti h hz.1.le (by linarith [hz.2]) (by linarith)) hg)
      rw [aux_d_one_sub] at h2
      exact h2

/-- For `a < x < 1` with `1 - a ≤ x`: `klBer x a ≤ klBer a x`. -/
private theorem aux_d_nonpos {a x : ℝ} (ha0 : 0 < a) (hax : a < x) (hx1 : x < 1) (hx : 1 - a ≤ x) :
    aux_d a x ≤ 0 := by
  have ha1 : a < 1 := by linarith
  rcases le_or_gt (1 / 2) a with ha | ha
  · have h2 := aux_le_of_deriv_nonpos (f := aux_d a) (f' := aux_g a) hax.le
      (fun z hz => aux_hasDerivAt_d ha0 ha1 (by linarith [hz.1]) (by linarith [hz.2]))
      (fun z hz => by
        have := aux_g_anti (a := a) ha hz.1.le (by linarith [hz.2]) le_rfl
        rw [aux_g_self] at this
        exact this)
    rwa [aux_d_self] at h2
  · rcases le_or_gt (aux_g a (1 - a)) 0 with hg | hg
    · have h2 := aux_le_of_deriv_nonpos (f := aux_d a) (f' := aux_g a) hx
        (fun z hz => aux_hasDerivAt_d ha0 ha1 (by linarith [hz.1]) (by linarith [hz.2]))
        (fun z hz => le_trans (aux_g_anti (by linarith) hz.1.le (by linarith [hz.2])
          (by linarith)) hg)
      rwa [aux_d_one_sub] at h2
    · exfalso
      have h2 := aux_lt_of_deriv_pos (f := aux_d a) (f' := aux_g a) (u := 1 / 2) (v := 1 - a)
        (by linarith)
        (fun z hz => aux_hasDerivAt_d ha0 ha1 (by linarith [hz.1]) (by linarith [hz.2]))
        (fun z hz => lt_of_lt_of_le hg
          (aux_g_anti hz.1.le hz.2.le (by linarith) (by linarith [hz.1])))
      rw [aux_d_one_sub] at h2
      linarith [aux_d_nonneg_left ha0 ha.le (le_refl (1 / 2 : ℝ))]

private theorem aux_E_mono (p : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1 / 2) :
    aux_E p u ≤ aux_E p v :=
  aux_le_of_deriv_nonneg (f := aux_E p) huv
    (fun x hx => aux_hasDerivAt_E p (by linarith [hx.1]) (by linarith [hx.2]))
    (fun x hx => mul_nonneg (sq_nonneg _)
      (aux_inv_sq_nonneg (by linarith [hx.1]) (by linarith [hx.2])))

private theorem aux_K_one_sub_self {r : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2) :
    aux_K (1 - r) r = owL r := by
  have hr1 : r < 1 := by linarith
  have hL := owL_mul_one_sub_two_mul hr0 hr1 hr.ne
  have hne : (1 : ℝ) - 2 * r ≠ 0 := by
    intro h
    linarith
  have e : klBer (1 - r) r = owL r * (1 - 2 * r) ^ 2 := by
    rw [klBer_eq_mul_log hr0.ne' (sub_pos.2 hr1).ne', sub_sub_cancel]
    linear_combination (2 * r - 1) * hL
  unfold aux_K
  rw [e, show (1 : ℝ) - r - r = 1 - 2 * r by ring, mul_div_assoc,
    div_self (pow_ne_zero 2 hne), mul_one]

/-! ### Curvature comparison -/

private theorem aux_hasDerivAt_j (x C : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (fun z => C * (x - z) ^ 2 - 2 * klBer x z)
      (2 * (x - s) * (1 / s + 1 / (1 - s) - C)) s :=
  (((aux_hasDerivAt_sq_right x s).const_mul C).sub
    ((aux_hasDerivAt_klBer_right x hs0 hs1).const_mul 2)).congr_deriv (by ring)

private theorem aux_two_klBer_le_of_ge {x y C : ℝ} (hy0 : 0 < y) (hyx : y ≤ x) (hx1 : x < 1)
    (hC : ∀ σ ∈ Icc y x, 1 / σ + 1 / (1 - σ) ≤ C) :
    2 * klBer x y ≤ C * (x - y) ^ 2 := by
  have h2 : C * (x - x) ^ 2 - 2 * klBer x x ≤ C * (x - y) ^ 2 - 2 * klBer x y :=
    aux_le_of_deriv_nonpos (f := fun z => C * (x - z) ^ 2 - 2 * klBer x z) hyx
      (fun z hz => aux_hasDerivAt_j x C (by linarith [hz.1]) (by linarith [hz.2]))
      (fun z hz => by
        have hG := hC z ⟨hz.1.le, hz.2.le⟩
        nlinarith [mul_nonneg (by linarith [hz.2] : (0 : ℝ) ≤ x - z)
          (by linarith : (0 : ℝ) ≤ C - (1 / z + 1 / (1 - z)))])
  have h3 : C * (x - x) ^ 2 - 2 * klBer x x = 0 := by
    rw [klBer_self]
    ring
  linarith

private theorem aux_two_klBer_le_of_le {x y C : ℝ} (hx0 : 0 < x) (hxy : x ≤ y) (hy1 : y < 1)
    (hC : ∀ σ ∈ Icc x y, 1 / σ + 1 / (1 - σ) ≤ C) :
    2 * klBer x y ≤ C * (x - y) ^ 2 := by
  have h2 : C * (x - x) ^ 2 - 2 * klBer x x ≤ C * (x - y) ^ 2 - 2 * klBer x y :=
    aux_le_of_deriv_nonneg (f := fun z => C * (x - z) ^ 2 - 2 * klBer x z) hxy
      (fun z hz => aux_hasDerivAt_j x C (by linarith [hz.1]) (by linarith [hz.2]))
      (fun z hz => by
        have hG := hC z ⟨hz.1.le, hz.2.le⟩
        nlinarith [mul_nonneg (by linarith [hz.1] : (0 : ℝ) ≤ z - x)
          (by linarith : (0 : ℝ) ≤ C - (1 / z + 1 / (1 - z)))])
  have h3 : C * (x - x) ^ 2 - 2 * klBer x x = 0 := by
    rw [klBer_self]
    ring
  linarith

private theorem aux_two_klBer_ge_of_ge {x y c : ℝ} (hy0 : 0 < y) (hyx : y ≤ x) (hx1 : x < 1)
    (hc : ∀ σ ∈ Icc y x, c ≤ 1 / σ + 1 / (1 - σ)) :
    c * (x - y) ^ 2 ≤ 2 * klBer x y := by
  have h2 : c * (x - y) ^ 2 - 2 * klBer x y ≤ c * (x - x) ^ 2 - 2 * klBer x x :=
    aux_le_of_deriv_nonneg (f := fun z => c * (x - z) ^ 2 - 2 * klBer x z) hyx
      (fun z hz => aux_hasDerivAt_j x c (by linarith [hz.1]) (by linarith [hz.2]))
      (fun z hz => by
        have hG := hc z ⟨hz.1.le, hz.2.le⟩
        nlinarith [mul_nonneg (by linarith [hz.2] : (0 : ℝ) ≤ x - z)
          (by linarith : (0 : ℝ) ≤ 1 / z + 1 / (1 - z) - c)])
  have h3 : c * (x - x) ^ 2 - 2 * klBer x x = 0 := by
    rw [klBer_self]
    ring
  linarith

/-- On the middle strip `[1 - q, q]` (for `q ≥ 1/2`) the curvature is at most its value at `q`,
which the corner ratio dominates. -/
private theorem aux_middle {ε q x y : ℝ} (hε : 0 < ε) (hq : q < 1 - ε) (hq2 : 1 / 2 ≤ q)
    (hx : x ∈ Icc (1 - q) q) (hy : y ∈ Icc (1 - q) q) :
    klBer x y ≤ klBer (1 - q) ε / (1 - q - ε) ^ 2 * (x - y) ^ 2 := by
  have hq1 : q < 1 := by linarith
  have hQ : 0 < q * (1 - q) := mul_pos (by linarith) (by linarith)
  have hCq : 1 / q + 1 / (1 - q) = 1 / (q * (1 - q)) := aux_G_eq (by linarith) hq1
  have hup : ∀ σ ∈ Icc (1 - q) q, 1 / σ + 1 / (1 - σ) ≤ 1 / q + 1 / (1 - q) := by
    intro σ hσ
    have hσ0 : 0 < σ := by linarith [hσ.1]
    have hσ1 : σ < 1 := by linarith [hσ.2]
    rw [aux_G_eq hσ0 hσ1, hCq]
    apply one_div_le_one_div_of_le hQ
    nlinarith [mul_nonneg (sub_nonneg.2 hσ.2) (sub_nonneg.2 hσ.1)]
  have hlow : ∀ σ ∈ Icc ε (1 - q), 1 / q + 1 / (1 - q) ≤ 1 / σ + 1 / (1 - σ) := by
    intro σ hσ
    have hσ0 : 0 < σ := by linarith [hσ.1]
    have hσ1 : σ < 1 := by linarith [hσ.2]
    rw [aux_G_eq hσ0 hσ1, hCq]
    apply one_div_le_one_div_of_le (mul_pos hσ0 (by linarith))
    nlinarith [mul_nonneg (by linarith [hσ.2] : (0 : ℝ) ≤ q - σ)
      (by linarith [hσ.2] : (0 : ℝ) ≤ 1 - q - σ)]
  have hP : (1 / q + 1 / (1 - q)) * (1 - q - ε) ^ 2 ≤ 2 * klBer (1 - q) ε :=
    aux_two_klBer_ge_of_ge hε (by linarith) (by linarith) hlow
  have hxy : 2 * klBer x y ≤ (1 / q + 1 / (1 - q)) * (x - y) ^ 2 := by
    rcases le_total y x with h | h
    · exact aux_two_klBer_le_of_ge (by linarith [hy.1]) h (by linarith [hx.2])
        (fun σ hσ => hup σ ⟨le_trans hy.1 hσ.1, le_trans hσ.2 hx.2⟩)
    · exact aux_two_klBer_le_of_le (by linarith [hx.1]) h (by linarith [hy.2])
        (fun σ hσ => hup σ ⟨le_trans hx.1 hσ.1, le_trans hσ.2 hy.2⟩)
  have hd : 0 < (1 - q - ε) ^ 2 := pow_pos (by linarith) 2
  have hPC : (1 / q + 1 / (1 - q)) / 2 ≤ klBer (1 - q) ε / (1 - q - ε) ^ 2 := by
    rw [le_div_iff₀ hd]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hPC (sq_nonneg (x - y))]

/-- The corner monotonicity: for `0 < ε < 1/2`, `p ↦ klBer p ε / (p - ε)²` is antitone on
`(ε, 1 - ε]`. -/
theorem klBer_div_sq_antitoneOn {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    AntitoneOn (fun p : ℝ => klBer p ε / (p - ε) ^ 2) (Set.Ioc ε (1 - ε)) := by
  intro x hx y hy hxy
  exact aux_K_anti (a := ε) (u := x) (v := y) hε0 hx.1 hxy (by linarith [hy.2])
    (fun z hz => aux_d_nonneg hε0 hε (by linarith [hx.1, hz.1]) (by linarith [hy.2, hz.2]))

/-- The endpoint condition on the rectangle. -/
private theorem aux_rect {ε q a b : ℝ} (hε : 0 < ε) (hεq : ε < q) (hq : q < 1 - ε)
    (ha : a ∈ Icc ε q) (hb : b ∈ Icc (1 - q) (1 - ε)) :
    klBer b a ≤ klBer (1 - q) ε / (1 - q - ε) ^ 2 * (b - a) ^ 2 := by
  have hε2 : ε < 1 / 2 := by linarith
  have ha0 : 0 < a := by linarith [ha.1]
  have hb1 : b < 1 := by linarith [hb.2]
  have ofK : ∀ x y : ℝ, x ≠ y → aux_K x y ≤ aux_K (1 - q) ε →
      klBer x y ≤ klBer (1 - q) ε / (1 - q - ε) ^ 2 * (x - y) ^ 2 := by
    intro x y hxy h
    have hp : 0 < (x - y) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (sub_ne_zero.2 hxy)).symm
    unfold aux_K at h
    rwa [div_le_iff₀ hp] at h
  have thm1 := klBer_div_sq_antitoneOn hε hε2
  rcases lt_trichotomy a b with hab | hab | hab
  · rcases le_or_gt (1 - a) b with h3 | h3
    · apply ofK b a hab.ne'
      have s1 : aux_K b a ≤ aux_K (1 - ε) a :=
        aux_K_mono ha0 hab hb.2 (by linarith)
          (fun z hz => aux_d_nonpos ha0 (by linarith [hz.1]) (by linarith [hz.2])
            (by linarith [hz.1]))
      have s2 : aux_K (1 - ε) a ≤ aux_K (1 - a) ε := by
        have hd := aux_d_nonneg (a := ε) (x := 1 - a) hε hε2 (by linarith [ha.2])
          (by linarith [ha.1])
        unfold aux_d at hd
        have e1 : klBer (1 - ε) a = klBer ε (1 - a) := by
          have h := klBer_one_sub_one_sub ε (1 - a)
          rwa [sub_sub_cancel] at h
        have e2 : (1 - ε - a) ^ 2 = (1 - a - ε) ^ 2 := by ring
        unfold aux_K
        rw [e1, e2]
        exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      have s3 : aux_K (1 - a) ε ≤ aux_K (1 - q) ε :=
        thm1 ⟨by linarith, by linarith⟩ ⟨by linarith [ha.2], by linarith [ha.1]⟩
          (by linarith [ha.2])
      linarith
    · rcases le_or_gt (1 - q) a with h1q | h1q
      · exact aux_middle hε hq (by linarith) ⟨by linarith [hb.1], by linarith⟩ ⟨h1q, ha.2⟩
      · apply ofK b a hab.ne'
        have ha2 : a < 1 / 2 := by linarith
        have s1 : aux_K b a ≤ aux_K (1 - q) a :=
          aux_K_anti ha0 h1q hb.1 hb1
            (fun z hz => aux_d_nonneg ha0 ha2 (by linarith [hz.1]) (by linarith [hz.2]))
        have s2 : aux_K (1 - q) a ≤ aux_K (1 - q) ε := by
          rcases le_or_gt (aux_E (1 - q) a) 0 with he | he
          · exact aux_Kright_anti hε ha.1 h1q (by linarith)
              (fun x hx => le_trans (aux_E_mono (1 - q) (by linarith [hx.1]) hx.2.le ha2.le) he)
          · have hq2 : q < 1 / 2 := by
              by_contra hq2
              push Not at hq2
              have h := aux_E_mono (1 - q) ha0 h1q.le (by linarith)
              rw [aux_E_self] at h
              linarith
            have s2a : aux_K (1 - q) a ≤ aux_K (1 - q) q :=
              aux_Kright_mono ha0 ha.2 (by linarith) (by linarith)
                (fun x hx => le_trans he.le
                  (aux_E_mono (1 - q) ha0 hx.1.le (by linarith [hx.2])))
            have s2b : aux_K (1 - q) q = owL q := aux_K_one_sub_self (by linarith) hq2
            have s2c : owL q ≤ owL ε :=
              owL_antitoneOn ⟨hε, hε2.le⟩ ⟨by linarith, hq2.le⟩ hεq.le
            have s2d : aux_K (1 - ε) ε = owL ε := aux_K_one_sub_self hε hε2
            have s2e : aux_K (1 - ε) ε ≤ aux_K (1 - q) ε :=
              thm1 ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
            linarith
        linarith
  · subst hab
    simp [klBer_self]
  · exact aux_middle hε hq (by linarith [ha.2, hb.1]) ⟨hb.1, by linarith [ha.2]⟩
      ⟨by linarith [hb.1], ha.2⟩

/-- The normalized Jensen gap of binary entropy on a band rectangle: for `0 < ε < q < 1 - ε`,
`r₀ ∈ [ε, q]`, `r₁ ∈ [1 - q, 1 - ε]` and `w ∈ [0, 1]`,
`h((1-w) r₀ + w r₁) - (1-w) h(r₀) - w h(r₁) ≤ P · w(1-w)(r₁ - r₀)²` with
`P = klBer (1 - q) ε / (1 - q - ε)²`, in nats. -/
theorem binEntropy_jensenGap_le {ε q r₀ r₁ w : ℝ} (hε : 0 < ε) (hεq : ε < q) (hq : q < 1 - ε)
    (hr₀ : r₀ ∈ Set.Icc ε q) (hr₁ : r₁ ∈ Set.Icc (1 - q) (1 - ε)) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Real.binEntropy ((1 - w) * r₀ + w * r₁) - (1 - w) * Real.binEntropy r₀
        - w * Real.binEntropy r₁ ≤
      klBer (1 - q) ε / (1 - q - ε) ^ 2 * (w * (1 - w) * (r₁ - r₀) ^ 2) := by
  have hr₀0 : 0 < r₀ := by linarith [hr₀.1]
  have hr₀1 : r₀ < 1 := by linarith [hr₀.2]
  have hr₁0 : 0 < r₁ := by linarith [hr₁.1]
  have hr₁1 : r₁ < 1 := by linarith [hr₁.2]
  have hA := aux_rect hε hεq hq hr₀ hr₁
  have hB : klBer r₀ r₁ ≤ klBer (1 - q) ε / (1 - q - ε) ^ 2 * (r₁ - r₀) ^ 2 := by
    have h := aux_rect hε hεq hq (a := 1 - r₁) (b := 1 - r₀)
      ⟨by linarith [hr₁.2], by linarith [hr₁.1]⟩ ⟨by linarith [hr₀.2], by linarith [hr₀.1]⟩
    rw [klBer_one_sub_one_sub] at h
    have e : (1 - r₀ - (1 - r₁)) ^ 2 = (r₁ - r₀) ^ 2 := by ring
    rwa [e] at h
  have key := binEntropy_gap_le_of_klBer_le hr₀0 hr₀1 hr₁0 hr₁1 hA hB hw0 hw1
  have e : (1 - w) * r₀ + w * r₁ = r₀ + w * (r₁ - r₀) := by ring
  rw [e]
  exact key

end

end BinaryRow

end StochasticToDeterministicLatents
