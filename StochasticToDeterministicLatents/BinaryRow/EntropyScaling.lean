import StochasticToDeterministicLatents.BinaryRow.HomEntropy
import StochasticToDeterministicLatents.BinaryRow.BandConstants

/-!
# Scaling of homogeneous binary entropy

With `δ = 4/25` and `η₀ = 33/289`, for `0 < η ≤ η₀` and `x, y > 0`,
`Hh(η x, y) ≤ δ Hh(x, y) + (η/η₀) · (149/1000) · x`, in nats (`homBinEntropy_scale_le`).

The core case is `g(t) = Hh(η₀, t) - δ Hh(1, t) < 149/1000` for `t > 0`. Its derivative
`D(t) = log (1 + η₀/t) - δ log (1 + 1/t)` has `D'(t) = (331 t - 693)/(25 t (1 + t)(289 t + 33))`,
so `D` is antitone on `(0, 693/331]`. The rational comparisons
`(189/89)^4 ≤ (29021/25721)^25` and `(977/867)^25 ≤ (19/9)^4` give `D(89/100) ≥ 0` and
`D(9/10) ≤ 0`; for `t ≥ 3/2`, `log (1 + a) ≤ a` and `log (1 + a) ≥ 2a/(a + 2)` give `D(t) ≤ 0`.
So `g` is monotone on `(0, 89/100]` and antitone on `[9/10, ∞)`, and monotonicity of `Hh` in its
second argument gives `g(t) ≤ Hh(η₀, 9/10) - δ Hh(1, 89/100)`. `artanh`-series enclosures, with
`log (977/110) = 3 log 2 + log (1 + 97/880)`, put this below `149/1000`. For general `η`, with
`c = η x/η₀`, homogeneity gives `Hh(η x, y) = c Hh(η₀, y/c)` and `Hh(x, y) = c Hh(η₀/η, y/c)`,
and `η₀/η ≥ 1` with monotonicity in the first argument finishes.

## Attribution

Original to this repository.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Set

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

/-- The derivative of `Hh(a, ·)` at `s > 0` is `log (a + s) - log s`. -/
private lemma aux_hasDerivAt_Hh {a s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    HasDerivAt (fun u => homBinEntropy a u) (Real.log (a + s) - Real.log s) s := by
  have has : a + s ≠ 0 := (by linarith : (0 : ℝ) < a + s).ne'
  have e1 := Real.hasDerivAt_negMulLog hs.ne'
  have e2 := (Real.hasDerivAt_negMulLog has).comp s ((hasDerivAt_id' s).const_add a)
  have e : HasDerivAt (fun u => Real.negMulLog a + Real.negMulLog u - Real.negMulLog (a + u))
      ((-Real.log s - 1) - (-Real.log (a + s) - 1) * 1) s :=
    (e1.const_add (Real.negMulLog a)).sub e2
  exact e.congr_deriv (by ring)

/-! ### The comparison function and its derivative -/

/-- `g(t) = Hh(η₀, t) - δ Hh(1, t)`. -/
private def aux_g (t : ℝ) : ℝ := homBinEntropy (33 / 289) t - 4 / 25 * homBinEntropy 1 t

/-- The derivative of `g`. -/
private def aux_D (t : ℝ) : ℝ :=
  Real.log (33 / 289 + t) - Real.log t - 4 / 25 * (Real.log (1 + t) - Real.log t)

/-- The derivative of `D`. -/
private def aux_D1 (t : ℝ) : ℝ :=
  1 / (33 / 289 + t) - t⁻¹ - 4 / 25 * (1 / (1 + t) - t⁻¹)

private lemma aux_g_continuous : Continuous aux_g := by
  unfold aux_g homBinEntropy
  fun_prop

private lemma aux_hasDerivAt_g {t : ℝ} (ht : 0 < t) : HasDerivAt aux_g (aux_D t) t := by
  have e := (aux_hasDerivAt_Hh (a := 33 / 289) (by norm_num) ht).sub
    ((aux_hasDerivAt_Hh (a := 1) (by norm_num) ht).const_mul (4 / 25 : ℝ))
  exact e

private lemma aux_hasDerivAt_D {t : ℝ} (ht : 0 < t) : HasDerivAt aux_D (aux_D1 t) t := by
  have h1 : (33 / 289 : ℝ) + t ≠ 0 := by positivity
  have h2 : (1 : ℝ) + t ≠ 0 := by positivity
  have eA := ((hasDerivAt_id' t).const_add (33 / 289 : ℝ)).log h1
  have eB := Real.hasDerivAt_log ht.ne'
  have eC := ((hasDerivAt_id' t).const_add (1 : ℝ)).log h2
  have e := (eA.sub eB).sub ((eC.sub eB).const_mul (4 / 25 : ℝ))
  refine e.congr_deriv ?_
  unfold aux_D1
  ring

private lemma aux_D1_nonpos {t : ℝ} (ht : 0 < t) (h : t ≤ 693 / 331) : aux_D1 t ≤ 0 := by
  have hden : 0 < 7225 * (t * (33 / 289 + t) * (1 + t)) := by positivity
  have e : aux_D1 t = (331 * t - 693) / (7225 * (t * (33 / 289 + t) * (1 + t))) := by
    unfold aux_D1
    field_simp
    ring
  rw [e, div_le_iff₀ hden, zero_mul]
  linarith

private lemma aux_D_antitone {a b : ℝ} (ha : 0 < a) (hb : b ≤ 693 / 331) :
    AntitoneOn aux_D (Icc a b) := by
  refine aux_antitoneOn_Icc (f' := aux_D1) ?_ ?_ ?_
  · intro x hx
    exact (aux_hasDerivAt_D (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    exact aux_hasDerivAt_D (by linarith [hx.1])
  · intro x hx
    exact aux_D1_nonpos (by linarith [hx.1]) (by linarith [hx.2])

/-! ### Signs of `D` -/

private lemma aux_pow_lo : ((189 : ℝ) / 89) ^ 4 ≤ (29021 / 25721) ^ 25 := by norm_num

private lemma aux_pow_hi : ((977 : ℝ) / 867) ^ 25 ≤ (19 / 9) ^ 4 := by norm_num

private lemma aux_D_lo : 0 ≤ aux_D (89 / 100) := by
  have h := Real.log_le_log (by norm_num) aux_pow_lo
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  have e1 : Real.log (33 / 289 + 89 / 100) - Real.log (89 / 100) = Real.log (29021 / 25721) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have e2 : Real.log (1 + 89 / 100) - Real.log (89 / 100) = Real.log (189 / 89) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  unfold aux_D
  rw [e1, e2]
  linarith

private lemma aux_D_hi : aux_D (9 / 10) ≤ 0 := by
  have h := Real.log_le_log (by norm_num) aux_pow_hi
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  have e1 : Real.log (33 / 289 + 9 / 10) - Real.log (9 / 10) = Real.log (977 / 867) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have e2 : Real.log (1 + 9 / 10) - Real.log (9 / 10) = Real.log (19 / 9) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  unfold aux_D
  rw [e1, e2]
  linarith

private lemma aux_D_tail {t : ℝ} (ht : 3 / 2 ≤ t) : aux_D t ≤ 0 := by
  have ht0 : 0 < t := by linarith
  have h1 : Real.log (33 / 289 + t) - Real.log t ≤ 33 / 289 / t := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < 33 / 289 + t) ht0)
    rw [Real.log_div (by positivity) ht0.ne'] at h
    have e : (33 / 289 + t) / t - 1 = 33 / 289 / t := by
      field_simp
      ring
    linarith
  have h2 : 2 / (2 * t + 1) ≤ Real.log (1 + t) - Real.log t := by
    have h := sum_le_log_one_add (a := 1 / t) (by positivity) 1
    have e1 : Real.log (1 + 1 / t) = Real.log (1 + t) - Real.log t := by
      rw [← Real.log_div (by positivity) ht0.ne']
      congr 1
      field_simp
      ring
    have e2 : 2 * ∑ k ∈ Finset.range 1, 1 / (2 * (k : ℝ) + 1) *
        (1 / t / (1 / t + 2)) ^ (2 * k + 1) =
        2 / (2 * t + 1) := by
      simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, pow_one]
      field_simp
      ring
    linarith
  have h3 : 33 / 289 / t ≤ 4 / 25 * (2 / (2 * t + 1)) := by
    have e : 4 / 25 * (2 / (2 * t + 1)) - 33 / 289 / t =
        (662 * t - 825) / (7225 * (t * (2 * t + 1))) := by
      field_simp
      ring
    have := div_nonneg (by linarith : (0 : ℝ) ≤ 662 * t - 825)
      (by positivity : (0 : ℝ) ≤ 7225 * (t * (2 * t + 1)))
    linarith
  unfold aux_D
  linarith

private lemma aux_D_nonneg_small {s : ℝ} (hs : 0 < s) (h : s ≤ 89 / 100) : 0 ≤ aux_D s := by
  have := aux_D_antitone (a := s) (b := 89 / 100) hs (by norm_num) ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
  linarith [aux_D_lo]

private lemma aux_D_nonpos_mid {s : ℝ} (hs : 9 / 10 ≤ s) (h : s ≤ 3 / 2) : aux_D s ≤ 0 := by
  have := aux_D_antitone (a := 9 / 10) (b := 3 / 2) (by norm_num) (by norm_num)
    ⟨le_rfl, by norm_num⟩ ⟨hs, h⟩ hs
  linarith [aux_D_hi]

/-! ### The bound on `g` -/

private lemma aux_g_mono {a b : ℝ} (ha : 0 < a) (hD : ∀ s ∈ Ioo a b, 0 ≤ aux_D s) :
    MonotoneOn aux_g (Icc a b) :=
  aux_monotoneOn_Icc aux_g_continuous.continuousOn
    (fun s hs => aux_hasDerivAt_g (by linarith [hs.1])) hD

private lemma aux_g_anti {a b : ℝ} (ha : 0 < a) (hD : ∀ s ∈ Ioo a b, aux_D s ≤ 0) :
    AntitoneOn aux_g (Icc a b) :=
  aux_antitoneOn_Icc aux_g_continuous.continuousOn
    (fun s hs => aux_hasDerivAt_g (by linarith [hs.1])) hD

private lemma aux_g_le_nine {t : ℝ} (ht : 9 / 10 ≤ t) : aux_g t ≤ aux_g (9 / 10) := by
  have hmid : ∀ b, 9 / 10 ≤ b → b ≤ 3 / 2 → aux_g b ≤ aux_g (9 / 10) := by
    intro b hb1 hb2
    have hm := aux_g_anti (a := 9 / 10) (b := b) (by norm_num)
      (fun s hs => aux_D_nonpos_mid hs.1.le (by linarith [hs.2]))
    exact hm ⟨le_rfl, hb1⟩ ⟨hb1, le_rfl⟩ hb1
  rcases le_total t (3 / 2) with h | h
  · exact hmid t ht h
  · have hm := aux_g_anti (a := 3 / 2) (b := t) (by norm_num)
      (fun s hs => aux_D_tail hs.1.le)
    have := hm ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
    have := hmid (3 / 2) (by norm_num) le_rfl
    linarith

private lemma aux_g_le {t : ℝ} (ht : 0 < t) :
    aux_g t ≤ homBinEntropy (33 / 289) (9 / 10) - 4 / 25 * homBinEntropy 1 (89 / 100) := by
  have hη : (0 : ℝ) ≤ 33 / 289 := by norm_num
  rcases le_total t (89 / 100) with h1 | h1
  · have hm := aux_g_mono (a := t) (b := 89 / 100) ht
      (fun s hs => aux_D_nonneg_small (by linarith [hs.1]) hs.2.le)
    have a1 := hm ⟨le_rfl, h1⟩ ⟨h1, le_rfl⟩ h1
    have a2 := homBinEntropy_mono_right (x := 33 / 289) hη (by norm_num : (0 : ℝ) ≤ 89 / 100)
      (by norm_num : (89 / 100 : ℝ) ≤ 9 / 10)
    unfold aux_g at a1 ⊢
    linarith
  rcases le_total t (9 / 10) with h2 | h2
  · have a1 := homBinEntropy_mono_right (x := 33 / 289) hη ht.le h2
    have a2 := homBinEntropy_mono_right (x := 1) zero_le_one (by norm_num : (0 : ℝ) ≤ 89 / 100) h1
    unfold aux_g
    linarith
  · have a1 := aux_g_le_nine h2
    have a2 := homBinEntropy_mono_right (x := 1) zero_le_one (by norm_num : (0 : ℝ) ≤ 89 / 100)
      (by norm_num : (89 / 100 : ℝ) ≤ 9 / 10)
    unfold aux_g at a1 ⊢
    linarith

/-! ### The constant -/

private lemma aux_log_a : Real.log (1 + 9 / 10 / (33 / 289)) ≤ 3 * (6931471808 / 10000000000) +
    (2 * ∑ k ∈ Finset.range 2, 1 / (2 * (k : ℝ) + 1) *
        ((97 / 880) / ((97 / 880) + 2)) ^ (2 * k + 1) +
      2 * ((97 / 880) / ((97 / 880) + 2)) ^ (2 * 2 + 1) /
        ((2 * ((2 : ℕ) : ℝ) + 1) * (1 - ((97 / 880) / ((97 / 880) + 2)) ^ 2))) := by
  have h := log_one_add_le_sum_add (a := 97 / 880) (by norm_num) 2
  have h2 : Real.log 2 < 6931471808 / 10000000000 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  rw [show (1 : ℝ) + 9 / 10 / (33 / 289) = 2 ^ 3 * (1 + 97 / 880) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith

private lemma aux_const :
    homBinEntropy (33 / 289) (9 / 10) - 4 / 25 * homBinEntropy 1 (89 / 100) < 149 / 1000 := by
  rw [homBinEntropy_eq_log (by norm_num) (by norm_num),
    homBinEntropy_eq_log (by norm_num) (by norm_num)]
  have hA := aux_log_a
  have hB := log_one_add_le_sum_add (a := 33 / 289 / (9 / 10)) (by norm_num) 2
  have hC := sum_le_log_one_add (a := 89 / 100 / 1) (by norm_num) 4
  have hD := sum_le_log_one_add (a := 1 / (89 / 100)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hA hB hC hD ⊢
  linarith

/-! ### The scaling lemma -/

/-- The scaling lemma: for `0 < η ≤ 33/289` and `x, y > 0`,
`Hh(η x, y) ≤ (4/25) Hh(x, y) + (η/(33/289)) · (149/1000) · x`, in nats. -/
theorem homBinEntropy_scale_le {η x y : ℝ} (hη : 0 < η) (hη0 : η ≤ 33 / 289) (hx : 0 < x)
    (hy : 0 < y) :
    homBinEntropy (η * x) y ≤
      4 / 25 * homBinEntropy x y + η / (33 / 289) * (149 / 1000) * x := by
  have hK : ∀ u, 0 < u → homBinEntropy (33 / 289) u ≤ 4 / 25 * homBinEntropy 1 u + 149 / 1000 := by
    intro u hu
    have a1 := aux_g_le hu
    have a2 := aux_const
    unfold aux_g at a1
    linarith
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = η / (33 / 289) * x := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  have hc0 : c ≠ 0 := hc.ne'
  have hη' : η ≠ 0 := hη.ne'
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = y / c := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; positivity
  have e1 : homBinEntropy (η * x) y = c * homBinEntropy (33 / 289) u := by
    rw [← homBinEntropy_mul]
    congr 1
    · rw [hc_def]
      field_simp
    · rw [hu_def]
      field_simp
  have e2 : homBinEntropy x y = c * homBinEntropy (33 / 289 / η) u := by
    rw [← homBinEntropy_mul]
    congr 1
    · rw [hc_def]
      field_simp
    · rw [hu_def]
      field_simp
  have hm : homBinEntropy 1 u ≤ homBinEntropy (33 / 289 / η) u :=
    homBinEntropy_mono_left zero_le_one (by rw [le_div_iff₀ hη]; linarith) hu.le
  have e3 : η / (33 / 289) * (149 / 1000) * x = c * (149 / 1000) := by
    rw [hc_def]
    ring
  rw [e1, e2, e3]
  calc c * homBinEntropy (33 / 289) u ≤ c * (4 / 25 * homBinEntropy 1 u + 149 / 1000) :=
        mul_le_mul_of_nonneg_left (hK u hu) hc.le
    _ ≤ c * (4 / 25 * homBinEntropy (33 / 289 / η) u + 149 / 1000) :=
        mul_le_mul_of_nonneg_left (by linarith) hc.le
    _ = 4 / 25 * (c * homBinEntropy (33 / 289 / η) u) + c * (149 / 1000) := by ring

end

end BinaryRow

end StochasticToDeterministicLatents
