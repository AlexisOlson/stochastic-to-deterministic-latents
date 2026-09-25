import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Homogeneous binary entropy

`homBinEntropy x y = negMulLog x + negMulLog y - negMulLog (x + y)`, in nats. For positive
arguments it equals `x log (1 + y / x) + y log (1 + x / y)`, which is `x + y` times the binary
entropy of `x / (x + y)`. It is symmetric, homogeneous of degree one (for every real scale, with
Mathlib's `log` conventions), nonnegative on `[0, ∞)²`, and monotone in each argument there.

The main result is a separation inequality (`homBinEntropy_separation`): for `x, y > 0`,
`L, R ≥ 15` and `L R ≥ 4096`, `(13/2) Hh(x, y) ≤ Hh(L x, y) + Hh(x, R y)`.

Homogeneity and symmetry reduce it to `x = 1`, `y = t ≥ 1`. For `t ≤ 8`, the bounds
`Hh(L, t) ≥ t log (L / t) + t`, `Hh(1, R t) ≥ log (R t) + 1` and `log L + log R ≥ 12 log 2`
leave a function `G` of `t`. `G` is convex on `[1, 4]`, and its tangent at 2 gives `G ≥ 1/2`.
On `[4, 8]`, `G'' ≥ -1/16` because `t³ - 15t² + 72t - 16 = (t - 6)²(t - 3) + 92`, and the tangent
at 4 with a quadratic correction gives `G ≥ 0`; this step has no slack at `t = 8`. For `t ≥ 8`,
monotonicity lowers `L` and `R` to 15. The resulting difference has nonnegative derivative by
`2x / (2 + x) ≤ log (1 + x) ≤ x`, and is nonnegative at 8. The numerical inputs are enclosures
of `log 2`, `log (3/2)`, `log (5/4)`, `log (11/10)` and `log (23/22)` from the `artanh` series.

## Attribution

Original to this repository.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Set

/-- Homogeneous binary entropy `Hh(x, y) = negMulLog x + negMulLog y - negMulLog (x + y)`, in nats:
`x + y` times the binary entropy of `x/(x + y)`. -/
def homBinEntropy (x y : ℝ) : ℝ :=
  Real.negMulLog x + Real.negMulLog y - Real.negMulLog (x + y)

/-- For positive arguments, `Hh(x, y) = x log (1 + y/x) + y log (1 + x/y)`. -/
theorem homBinEntropy_eq_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    homBinEntropy x y = x * Real.log (1 + y / x) + y * Real.log (1 + x / y) := by
  have h1 : Real.log (1 + y / x) = Real.log (x + y) - Real.log x := by
    rw [← Real.log_div (by positivity) hx.ne']
    congr 1
    field_simp
  have h2 : Real.log (1 + x / y) = Real.log (x + y) - Real.log y := by
    rw [← Real.log_div (by positivity) hy.ne']
    congr 1
    field_simp
    ring
  rw [h1, h2]
  unfold homBinEntropy Real.negMulLog
  ring

/-- `Hh` is symmetric. -/
theorem homBinEntropy_comm (x y : ℝ) : homBinEntropy x y = homBinEntropy y x := by
  unfold homBinEntropy
  rw [add_comm y x]
  ring

/-- `Hh` is homogeneous of degree one: `Hh(c x, c y) = c Hh(x, y)` for every real `c`. For
`c < 0` this holds through Mathlib's conventions `log x = log |x|` and `log 0 = 0`. -/
theorem homBinEntropy_mul (c x y : ℝ) : homBinEntropy (c * x) (c * y) = c * homBinEntropy x y := by
  unfold homBinEntropy
  rw [← mul_add, Real.negMulLog_mul, Real.negMulLog_mul, Real.negMulLog_mul]
  ring

/-- `Hh` is nonnegative on `[0, ∞)²`. -/
theorem homBinEntropy_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ homBinEntropy x y := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp [homBinEntropy]
  rcases hy.eq_or_lt with rfl | hy0
  · simp [homBinEntropy]
  rw [homBinEntropy_eq_log hx0 hy0]
  have h1 : 0 ≤ Real.log (1 + y / x) := Real.log_nonneg (by linarith [div_pos hy0 hx0])
  have h2 : 0 ≤ Real.log (1 + x / y) := Real.log_nonneg (by linarith [div_pos hx0 hy0])
  exact add_nonneg (mul_nonneg hx0.le h1) (mul_nonneg hy0.le h2)

/-! ### Calculus helpers -/

/-- A function with nonnegative derivative on the interior of `[a, b]` is monotone there. -/
private lemma aux_monotoneOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hnn : ∀ x ∈ Ioo a b, 0 ≤ f' x) :
    MonotoneOn f (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc a b) hc ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx ⊢
    exact (hd x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hnn x hx

/-- A function with nonpositive derivative on the interior of `[a, b]` is antitone there. -/
private lemma aux_antitoneOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hnp : ∀ x ∈ Ioo a b, f' x ≤ 0) :
    AntitoneOn f (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc a b) hc ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx ⊢
    exact (hd x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hnp x hx

/-- Tangent line with a quadratic correction: if `f'' ≥ -c` on `[lo, hi]`, then for `a, t` in
`[lo, hi]`, `f a + f' a (t - a) - (c/2) (t - a)² ≤ f t`. -/
private lemma aux_tangent {f f' f'' : ℝ → ℝ} {lo hi c a t : ℝ}
    (h1 : ∀ x ∈ Icc lo hi, HasDerivAt f (f' x) x)
    (h2 : ∀ x ∈ Icc lo hi, HasDerivAt f' (f'' x) x)
    (h2c : ∀ x ∈ Icc lo hi, -c ≤ f'' x) (ha : a ∈ Icc lo hi) (ht : t ∈ Icc lo hi) :
    f a + f' a * (t - a) - c / 2 * (t - a) ^ 2 ≤ f t := by
  let g : ℝ → ℝ := fun x => f x + c / 2 * ((x - a) * (x - a)) - f' a * x
  let g' : ℝ → ℝ := fun x => f' x + c * (x - a) - f' a
  have hgd : ∀ x ∈ Icc lo hi, HasDerivAt g (g' x) x := by
    intro x hx
    have e : HasDerivAt (fun x => f x + c / 2 * ((x - a) * (x - a)) - f' a * x)
        (f' x + c / 2 * (1 * (x - a) + (x - a) * 1) - f' a * 1) x :=
      ((h1 x hx).add ((((hasDerivAt_id' x).sub_const a).mul
        ((hasDerivAt_id' x).sub_const a)).const_mul (c / 2))).sub
        ((hasDerivAt_id' x).const_mul (f' a))
    exact e.congr_deriv (by ring)
  have hg'd : ∀ x ∈ Icc lo hi, HasDerivAt g' (f'' x + c) x := by
    intro x hx
    have e : HasDerivAt (fun x => f' x + c * (x - a) - f' a) (f'' x + c * 1) x :=
      ((h2 x hx).add (((hasDerivAt_id' x).sub_const a).const_mul c)).sub_const (f' a)
    exact e.congr_deriv (by ring)
  have hg'mono : MonotoneOn g' (Icc lo hi) :=
    aux_monotoneOn_Icc (fun x hx => (hg'd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hg'd x (Ioo_subset_Icc_self hx))
      (fun x hx => by linarith [h2c x (Ioo_subset_Icc_self hx)])
  have hg'a : g' a = 0 := by simp only [g']; ring
  have key : g a ≤ g t := by
    rcases le_total a t with hat | hta
    · have hsub : Icc a t ⊆ Icc lo hi := Icc_subset_Icc ha.1 ht.2
      have hm : MonotoneOn g (Icc a t) :=
        aux_monotoneOn_Icc (fun x hx => (hgd x (hsub hx)).continuousAt.continuousWithinAt)
          (fun x hx => hgd x (hsub (Ioo_subset_Icc_self hx)))
          (fun x hx => by
            rw [← hg'a]
            exact hg'mono ha (hsub (Ioo_subset_Icc_self hx)) hx.1.le)
      exact hm ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat
    · have hsub : Icc t a ⊆ Icc lo hi := Icc_subset_Icc ht.1 ha.2
      have hm : AntitoneOn g (Icc t a) :=
        aux_antitoneOn_Icc (fun x hx => (hgd x (hsub hx)).continuousAt.continuousWithinAt)
          (fun x hx => hgd x (hsub (Ioo_subset_Icc_self hx)))
          (fun x hx => by
            rw [← hg'a]
            exact hg'mono (hsub (Ioo_subset_Icc_self hx)) ha hx.2.le)
      exact hm ⟨le_rfl, hta⟩ ⟨hta, le_rfl⟩ hta
  simp only [g] at key
  nlinarith [key]

/-! ### Monotonicity and nonnegativity -/

/-- `Hh` is monotone in its first argument on `[0, ∞)`. -/
theorem homBinEntropy_mono_left {x x' y : ℝ} (hx : 0 ≤ x) (hxx' : x ≤ x') (hy : 0 ≤ y) :
    homBinEntropy x y ≤ homBinEntropy x' y := by
  have hc : ContinuousOn (fun u => homBinEntropy u y) (Icc x x') := by
    have : Continuous (fun u => homBinEntropy u y) := by
      unfold homBinEntropy
      fun_prop
    exact this.continuousOn
  have hm : MonotoneOn (fun u => homBinEntropy u y) (Icc x x') := by
    refine aux_monotoneOn_Icc (f' := fun u => Real.log (u + y) - Real.log u) hc ?_ ?_
    · intro u hu
      have hu0 : 0 < u := lt_of_le_of_lt hx hu.1
      have huy : u + y ≠ 0 := by positivity
      have e1 := Real.hasDerivAt_negMulLog hu0.ne'
      have e2 := (Real.hasDerivAt_negMulLog huy).comp u ((hasDerivAt_id' u).add_const y)
      have e : HasDerivAt (fun u => Real.negMulLog u + Real.negMulLog y - Real.negMulLog (u + y))
          ((-Real.log u - 1) - (-Real.log (u + y) - 1) * 1) u :=
        (e1.add_const (Real.negMulLog y)).sub e2
      exact e.congr_deriv (by ring)
    · intro u hu
      have hu0 : 0 < u := lt_of_le_of_lt hx hu.1
      have := Real.log_le_log hu0 (by linarith : u ≤ u + y)
      linarith
  exact hm ⟨le_rfl, hxx'⟩ ⟨hxx', le_rfl⟩ hxx'

/-- `Hh` is monotone in its second argument on `[0, ∞)`. -/
theorem homBinEntropy_mono_right {x y y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyy' : y ≤ y') :
    homBinEntropy x y ≤ homBinEntropy x y' := by
  rw [homBinEntropy_comm x y, homBinEntropy_comm x y']
  exact homBinEntropy_mono_left hy hyy' hx

/-! ### Logarithm helpers -/

/-- Partial sums of the `artanh` series bound `log p - log q` from below. -/
private lemma aux_log_lower {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, ((p - q) / (p + q)) ^ (2 * i + 1) / (2 * i + 1) ≤
      Real.log p - Real.log q := by
  have hpq : 0 < p + q := by linarith
  have hx0 : 0 ≤ (p - q) / (p + q) := div_nonneg (by linarith) hpq.le
  have hx1 : (p - q) / (p + q) < 1 := by rw [div_lt_one hpq]; linarith
  have h := Real.sum_range_le_log_div hx0 hx1 n
  have hq' : q ≠ 0 := hq.ne'
  have hpq' : p + q ≠ 0 := hpq.ne'
  have e : (1 + (p - q) / (p + q)) / (1 - (p - q) / (p + q)) = p / q := by
    rw [div_eq_div_iff (sub_pos.2 hx1).ne' hq']
    field_simp
    ring
  rw [e, Real.log_div (by linarith) hq.ne'] at h
  linarith

/-- Partial sums of the `artanh` series plus a geometric tail bound `log p - log q` from above. -/
private lemma aux_log_upper {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) (n : ℕ) :
    Real.log p - Real.log q ≤
      2 * (∑ i ∈ Finset.range n, ((p - q) / (p + q)) ^ (2 * i + 1) / (2 * i + 1) +
        ((p - q) / (p + q)) ^ (2 * n + 1) / (1 - ((p - q) / (p + q)) ^ 2)) := by
  have hpq : 0 < p + q := by linarith
  have hx0 : 0 ≤ (p - q) / (p + q) := div_nonneg (by linarith) hpq.le
  have hx1 : (p - q) / (p + q) < 1 := by rw [div_lt_one hpq]; linarith
  have h := Real.log_div_le_sum_range_add hx0 hx1 n
  have hq' : q ≠ 0 := hq.ne'
  have hpq' : p + q ≠ 0 := hpq.ne'
  have e : (1 + (p - q) / (p + q)) / (1 - (p - q) / (p + q)) = p / q := by
    rw [div_eq_div_iff (sub_pos.2 hx1).ne' hq']
    field_simp
    ring
  rw [e, Real.log_div (by linarith) hq.ne'] at h
  linarith

/-- First-order lower bound: `2 (p - q) / (p + q) ≤ log p - log q` for `0 < q ≤ p`. -/
private lemma aux_log_sub_ge {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) :
    2 * (p - q) / (p + q) ≤ Real.log p - Real.log q := by
  have h := aux_log_lower hq hqp 1
  simp only [Finset.sum_range_one] at h
  have e : 2 * (((p - q) / (p + q)) ^ (2 * 0 + 1) / (2 * ((0 : ℕ) : ℝ) + 1)) =
      2 * (p - q) / (p + q) := by
    push_cast
    ring
  linarith

/-- Upper bound: `log p - log q ≤ (p - q) / q` for positive `p, q`. -/
private lemma aux_log_sub_le {p q : ℝ} (hq : 0 < q) (hp : 0 < p) :
    Real.log p - Real.log q ≤ (p - q) / q := by
  have h := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div hp.ne' hq.ne'] at h
  have e : p / q - 1 = (p - q) / q := by field_simp
  linarith

/-- Enclosures of `log 2`, `log (3/2)` and `log (5/4)`, and lower bounds for `log (11/10)` and
`log (23/22)`. -/
private lemma aux_log_consts :
    0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 ∧
    (0.405465 : ℝ) ≤ Real.log 3 - Real.log 2 ∧ Real.log 3 - Real.log 2 ≤ 0.4054652 ∧
    (0.2231435 : ℝ) ≤ Real.log 5 - 2 * Real.log 2 ∧ Real.log 5 - 2 * Real.log 2 ≤ 0.2231436 ∧
    (0.09531 : ℝ) ≤ Real.log 11 - Real.log 2 - Real.log 5 ∧
    (0.04445 : ℝ) ≤ Real.log 23 - Real.log 2 - Real.log 11 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h22 : Real.log 22 = Real.log 2 + Real.log 11 := by
    rw [show (22 : ℝ) = 2 * 11 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have a3 := aux_log_lower (p := 3) (q := 2) (by norm_num) (by norm_num) 5
  have b3 := aux_log_upper (p := 3) (q := 2) (by norm_num) (by norm_num) 5
  have a5 := aux_log_lower (p := 5) (q := 4) (by norm_num) (by norm_num) 4
  have b5 := aux_log_upper (p := 5) (q := 4) (by norm_num) (by norm_num) 4
  have a11 := aux_log_lower (p := 11) (q := 10) (by norm_num) (by norm_num) 3
  have a23 := aux_log_lower (p := 23) (q := 22) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at a3 b3 a5 b5 a11 a23
  refine ⟨Real.log_two_gt_d9, Real.log_two_lt_d9, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### The comparison function on `[1, 8]` -/

/-- The slack lower bound on `[1, 8]`. -/
private def aux_G (t : ℝ) : ℝ :=
  12 * Real.log 2 + (t - 1) * Real.log 15 + (11 / 2 * t + 1) * Real.log t + 1 + t -
    13 / 2 * ((1 + t) * Real.log (1 + t))

/-- Its derivative. -/
private def aux_G1 (t : ℝ) : ℝ :=
  Real.log 15 + 11 / 2 * Real.log t + t⁻¹ - 13 / 2 * Real.log (1 + t)

/-- Its second derivative. -/
private def aux_G2 (t : ℝ) : ℝ :=
  11 / 2 * t⁻¹ - (t ^ 2)⁻¹ - 13 / 2 * (1 + t)⁻¹

private lemma aux_G_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt aux_G (aux_G1 t) t := by
  have h1t : (1 : ℝ) + t ≠ 0 := by positivity
  have e1 := ((hasDerivAt_id' t).sub_const 1).mul_const (Real.log 15)
  have e2 := (((hasDerivAt_id' t).const_mul (11 / 2 : ℝ)).add_const 1).mul
    (Real.hasDerivAt_log ht.ne')
  have e3 := ((hasDerivAt_id' t).const_add 1).mul
    (((hasDerivAt_id' t).const_add 1).log h1t)
  have e := ((((e1.const_add (12 * Real.log 2)).add e2).add_const 1).add
    (hasDerivAt_id' t)).sub (e3.const_mul (13 / 2 : ℝ))
  refine e.congr_deriv ?_
  unfold aux_G1
  field_simp
  ring

private lemma aux_G1_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt aux_G1 (aux_G2 t) t := by
  have h1t : (1 : ℝ) + t ≠ 0 := by positivity
  have e := ((((Real.hasDerivAt_log ht.ne').const_mul (11 / 2 : ℝ)).const_add
    (Real.log 15)).add (hasDerivAt_inv ht.ne')).sub
    ((((hasDerivAt_id' t).const_add 1).log h1t).const_mul (13 / 2 : ℝ))
  refine e.congr_deriv ?_
  unfold aux_G2
  field_simp
  ring

private lemma aux_G2_eq {t : ℝ} (ht : 0 < t) :
    aux_G2 t = (-2 * t ^ 2 + 9 * t - 2) / (2 * t ^ 2 * (1 + t)) := by
  unfold aux_G2
  field_simp
  ring

private lemma aux_G_ge_14 {t : ℝ} (h1 : 1 ≤ t) (h4 : t ≤ 4) : 1 / 2 ≤ aux_G t := by
  have hmem : ∀ x ∈ Icc (1 : ℝ) 4, 0 < x := fun x hx => by linarith [hx.1]
  have htan := aux_tangent (f := aux_G) (f' := aux_G1) (f'' := aux_G2) (lo := 1) (hi := 4)
    (c := 0) (a := 2) (t := t)
    (fun x hx => aux_G_hasDerivAt (hmem x hx))
    (fun x hx => aux_G1_hasDerivAt (hmem x hx))
    (fun x hx => by
      rw [aux_G2_eq (hmem x hx)]
      have hx0 := hmem x hx
      have : 0 ≤ -2 * x ^ 2 + 9 * x - 2 := by nlinarith [hx.1, hx.2]
      have := div_nonneg this (by positivity : (0 : ℝ) ≤ 2 * x ^ 2 * (1 + x))
      linarith)
    ⟨by norm_num, by norm_num⟩ ⟨h1, h4⟩
  obtain ⟨l2a, l2b, l3a, l3b, l5a, l5b, -, -⟩ := aux_log_consts
  have h15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hG1 : aux_G1 2 ≤ 0 := by
    unfold aux_G1
    norm_num
    linarith
  have hG2 : 1 / 2 ≤ aux_G 2 + 2 * aux_G1 2 := by
    unfold aux_G aux_G1
    norm_num
    linarith
  have := mul_nonneg_of_nonpos_of_nonpos hG1 (by linarith : t - 4 ≤ 0)
  nlinarith [htan]

-- The tangent bound at 4 is exactly `0` at `t = 8`; any change of constants breaks this step
-- first.
private lemma aux_G_ge_48 {t : ℝ} (h4 : 4 ≤ t) (h8 : t ≤ 8) : 0 ≤ aux_G t := by
  have hmem : ∀ x ∈ Icc (4 : ℝ) 8, 0 < x := fun x hx => by linarith [hx.1]
  have htan := aux_tangent (f := aux_G) (f' := aux_G1) (f'' := aux_G2) (lo := 4) (hi := 8)
    (c := 1 / 16) (a := 4) (t := t)
    (fun x hx => aux_G_hasDerivAt (hmem x hx))
    (fun x hx => aux_G1_hasDerivAt (hmem x hx))
    (fun x hx => by
      have hx0 := hmem x hx
      have e : aux_G2 x + 1 / 16 = (x ^ 3 - 15 * x ^ 2 + 72 * x - 16) / (16 * x ^ 2 * (1 + x)) := by
        rw [aux_G2_eq hx0]
        field_simp
        ring
      have : 0 ≤ x ^ 3 - 15 * x ^ 2 + 72 * x - 16 := by
        nlinarith [mul_nonneg (sq_nonneg (x - 6)) (by linarith [hx.1] : (0 : ℝ) ≤ x - 3)]
      have := div_nonneg this (by positivity : (0 : ℝ) ≤ 16 * x ^ 2 * (1 + x))
      linarith)
    ⟨by norm_num, by norm_num⟩ ⟨h4, h8⟩
  have hG4 : 1 / 2 ≤ aux_G 4 := aux_G_ge_14 (by norm_num) le_rfl
  obtain ⟨l2a, l2b, l3a, l3b, l5a, l5b, -, -⟩ := aux_log_consts
  have h15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h4' : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hG1 : 0 ≤ aux_G1 4 := by
    unfold aux_G1
    norm_num
    linarith
  have := mul_nonneg hG1 (by linarith : (0 : ℝ) ≤ t - 4)
  nlinarith [htan]

/-! ### The comparison function on `[8, ∞)` -/

/-- `Hh a b ≥ b log a - b log b + b` for positive `a, b`. -/
private lemma aux_Hh_ge {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b * Real.log a - b * Real.log b + b ≤ homBinEntropy a b := by
  have hab : 0 < a + b := by linarith
  have h' : b ≤ (a + b) * (Real.log (a + b) - Real.log a) := by
    -- `log (1 + b/a) ≥ b / (a + b)`, from `log x ≤ x - 1` at `x = a / (a + b)`
    have h2 := aux_log_sub_le (p := a) (q := a + b) hab ha
    have e2 : (a - (a + b)) / (a + b) = -(b / (a + b)) := by ring
    rw [e2] at h2
    have : b / (a + b) ≤ Real.log (a + b) - Real.log a := by linarith
    calc b = (a + b) * (b / (a + b)) := by field_simp
      _ ≤ (a + b) * (Real.log (a + b) - Real.log a) := by gcongr
  unfold homBinEntropy Real.negMulLog
  nlinarith [h']

private lemma aux_hasDerivAt_Hh {a k s : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (hs : 0 < s) :
    HasDerivAt (fun u => homBinEntropy a (k * u))
      (k * (Real.log (a + k * s) - Real.log (k * s))) s := by
  have hks : k * s ≠ 0 := by positivity
  have haks : a + k * s ≠ 0 := by positivity
  have e1 := (Real.hasDerivAt_negMulLog hks).comp s ((hasDerivAt_id' s).const_mul k)
  have e2 := (Real.hasDerivAt_negMulLog haks).comp s (((hasDerivAt_id' s).const_mul k).const_add a)
  have e : HasDerivAt
      (fun u => Real.negMulLog a + Real.negMulLog (k * u) - Real.negMulLog (a + k * u)) _ s :=
    (e1.const_add (Real.negMulLog a)).sub e2
  exact e.congr_deriv (by ring)

/-- The large-ratio case: `(13/2) Hh(1, t) ≤ Hh(15, t) + Hh(1, 15 t)` for `t ≥ 8`. -/
private lemma aux_D_nonneg {t : ℝ} (ht : 8 ≤ t) :
    13 / 2 * homBinEntropy 1 t ≤ homBinEntropy 15 t + homBinEntropy 1 (15 * t) := by
  set D : ℝ → ℝ := fun s =>
    homBinEntropy 15 (1 * s) + homBinEntropy 1 (15 * s) - 13 / 2 * homBinEntropy 1 (1 * s) with hD
  have hc : ContinuousOn D (Icc 8 t) := by
    have : Continuous D := by
      rw [hD]
      unfold homBinEntropy
      fun_prop
    exact this.continuousOn
  have hm : MonotoneOn D (Icc 8 t) := by
    refine aux_monotoneOn_Icc (f' := fun s =>
      1 * (Real.log (15 + 1 * s) - Real.log (1 * s)) +
        15 * (Real.log (1 + 15 * s) - Real.log (15 * s)) -
        13 / 2 * (1 * (Real.log (1 + 1 * s) - Real.log (1 * s)))) hc ?_ ?_
    · intro s hs
      have hs0 : 0 < s := by linarith [hs.1]
      have e := ((aux_hasDerivAt_Hh (a := 15) (k := 1) (by norm_num) one_pos hs0).add
        (aux_hasDerivAt_Hh (a := 1) (k := 15) (by norm_num) (by norm_num) hs0)).sub
        ((aux_hasDerivAt_Hh (a := 1) (k := 1) (by norm_num) one_pos hs0).const_mul (13 / 2 : ℝ))
      exact e
    · intro s hs
      have hs0 : 0 < s := by linarith [hs.1]
      have hA := aux_log_sub_ge (p := 15 + s) (q := s) hs0 (by linarith)
      have hB := aux_log_sub_ge (p := 1 + 15 * s) (q := 15 * s) (by positivity) (by linarith)
      have hC := aux_log_sub_le (p := 1 + s) (q := s) hs0 (by positivity)
      have eA : 2 * (15 + s - s) / (15 + s + s) = 30 / (2 * s + 15) := by ring
      have eB : 2 * (1 + 15 * s - 15 * s) / (1 + 15 * s + 15 * s) = 2 / (30 * s + 1) := by ring
      have eC : (1 + s - s) / s = 1 / s := by ring
      rw [eA] at hA
      rw [eB] at hB
      rw [eC] at hC
      have key : 13 / 2 * (1 / s) ≤ 30 / (2 * s + 15) + 15 * (2 / (30 * s + 1)) := by
        have e : 30 / (2 * s + 15) + 15 * (2 / (30 * s + 1)) - 13 / 2 * (1 / s) =
            (1140 * s ^ 2 - 4916 * s - 195) / (2 * s * (2 * s + 15) * (30 * s + 1)) := by
          field_simp
          ring
        have hnum : 0 ≤ 1140 * s ^ 2 - 4916 * s - 195 := by nlinarith [hs.1]
        have := div_nonneg hnum (by positivity : (0 : ℝ) ≤ 2 * s * (2 * s + 15) * (30 * s + 1))
        linarith
      simp only [one_mul]
      nlinarith [hA, hB, hC, key]
  have hD8 : 0 ≤ D 8 := by
    obtain ⟨l2a, l2b, l3a, l3b, l5a, l5b, l11a, l23a⟩ := aux_log_consts
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have h9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h121 : Real.log 121 = 2 * Real.log 11 := by
      rw [show (121 : ℝ) = 11 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h15 : Real.log 15 = Real.log 3 + Real.log 5 := by
      rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have h120 : Real.log 120 = Real.log 8 + Real.log 15 := by
      rw [show (120 : ℝ) = 8 * 15 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    simp only [hD, homBinEntropy, Real.negMulLog]
    norm_num
    linarith
  have := hm ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [hD, one_mul] at this hD8
  linarith

/-! ### The core inequality -/

/-- The separation lemma at `x = 1`, `y = t ≥ 1`. -/
private lemma aux_core {t L R : ℝ} (ht : 1 ≤ t) (hL : 15 ≤ L) (hR : 15 ≤ R) (hLR : 4096 ≤ L * R) :
    13 / 2 * homBinEntropy 1 t ≤ homBinEntropy L t + homBinEntropy 1 (R * t) := by
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := by linarith
  rcases le_total t 8 with h8 | h8
  · have hG : 0 ≤ aux_G t := by
      rcases le_total t 4 with h4 | h4
      · linarith [aux_G_ge_14 ht h4]
      · exact aux_G_ge_48 h4 h8
    have hA := aux_Hh_ge hL0 ht0
    have hB := aux_Hh_ge (a := R * t) (b := 1) (by positivity) one_pos
    rw [← homBinEntropy_comm] at hB
    have hf : homBinEntropy 1 t = (1 + t) * Real.log (1 + t) - t * Real.log t := by
      unfold homBinEntropy Real.negMulLog
      simp
      ring
    have hRt : Real.log (R * t) = Real.log R + Real.log t :=
      Real.log_mul hR0.ne' ht0.ne'
    have hLRlog : 12 * Real.log 2 ≤ Real.log L + Real.log R := by
      rw [← Real.log_mul hL0.ne' hR0.ne']
      have : Real.log 4096 = 12 * Real.log 2 := by
        rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
        norm_num
      rw [← this]
      exact Real.log_le_log (by norm_num) hLR
    have hL15 : (t - 1) * Real.log 15 ≤ (t - 1) * Real.log L :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hL) (by linarith)
    rw [hf]
    rw [hRt, Real.log_one] at hB
    unfold aux_G at hG
    nlinarith [hA, hB, hG, hLRlog, hL15]
  · have h1 := homBinEntropy_mono_left (by norm_num : (0 : ℝ) ≤ 15) hL ht0.le
    have h2 := homBinEntropy_mono_right (x := 1) (by norm_num) (by positivity : (0 : ℝ) ≤ 15 * t)
      (mul_le_mul_of_nonneg_right hR ht0.le)
    have := aux_D_nonneg h8
    linarith

/-- The separation lemma: two well-separated pairs dominate the crossed pair. For `x, y > 0`,
`L, R ≥ 15` and `L R ≥ 4096`, `(13/2) Hh(x, y) ≤ Hh(L x, y) + Hh(x, R y)`. -/
theorem homBinEntropy_separation {x y L R : ℝ} (hx : 0 < x) (hy : 0 < y) (hL : 15 ≤ L)
    (hR : 15 ≤ R) (hLR : 4096 ≤ L * R) :
    13 / 2 * homBinEntropy x y ≤ homBinEntropy (L * x) y + homBinEntropy x (R * y) := by
  rcases le_total x y with hxy | hxy
  · have ht : 1 ≤ y / x := by rw [le_div_iff₀ hx]; linarith
    have core := aux_core ht hL hR hLR
    have e1 : homBinEntropy x y = x * homBinEntropy 1 (y / x) := by
      rw [← homBinEntropy_mul]
      congr 1 <;> field_simp
    have e2 : homBinEntropy (L * x) y = x * homBinEntropy L (y / x) := by
      rw [← homBinEntropy_mul]
      congr 1
      · ring
      · field_simp
    have e3 : homBinEntropy x (R * y) = x * homBinEntropy 1 (R * (y / x)) := by
      rw [← homBinEntropy_mul]
      congr 1
      · ring
      · field_simp
    rw [e1, e2, e3]
    have := mul_le_mul_of_nonneg_left core hx.le
    linarith
  · have ht : 1 ≤ x / y := by rw [le_div_iff₀ hy]; linarith
    have core := aux_core ht hR hL (by linarith [mul_comm L R])
    have e1 : homBinEntropy x y = y * homBinEntropy 1 (x / y) := by
      rw [homBinEntropy_comm, ← homBinEntropy_mul]
      congr 1 <;> field_simp
    have e2 : homBinEntropy (L * x) y = y * homBinEntropy 1 (L * (x / y)) := by
      rw [homBinEntropy_comm, ← homBinEntropy_mul]
      congr 1
      · field_simp
      · field_simp
    have e3 : homBinEntropy x (R * y) = y * homBinEntropy R (x / y) := by
      rw [homBinEntropy_comm R, ← homBinEntropy_mul]
      congr 1
      · field_simp
      · ring
    rw [e1, e2, e3]
    have := mul_le_mul_of_nonneg_left core hy.le
    linarith

end

end BinaryRow

end StochasticToDeterministicLatents
