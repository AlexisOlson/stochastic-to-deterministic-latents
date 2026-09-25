import StochasticToDeterministicLatents.BinaryRow.Bernoulli
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Constants of the separation bands

For a separation band `[A, B]` put `ε = 1/(B² + B + 1)`, `q = (A + 1)/(A² + A + 1)` and
`κ(x) = x/(1 + x)²`. The band has three constants, in nats:
`P = klBer (1 - q) ε/(1 - q - ε)²`, `Q = h(ε)/(ε(1 - ε))` and `r = κ(B) · owL (min q (1/2))`.
For the six bands `[1, 4]`, `[4, 8]`, `[8, 12]`, `[12, 14]`, `[14, 76/5]` and `[76/5, 16]`,
the theorems `constants_band_*` bound `P` and `Q` above and `r` below by the rationals that
`balanceCoeff_bands_le` uses, with `ε` and `q` written as reduced fractions. For the band
`[1, 4]`, `q = 2/3 ≥ 1/2`, so `r = 2κ(4) = 8/25` exactly and its clause holds with equality.

The tool is a pair of enclosures of `log (1 + a)` for `a ≥ 0` by partial sums of the series
`log (1 + a) = 2 Σ y^(2k+1)/(2k+1)` with `y = a/(a + 2)`: the partial sums bound it below
(`sum_le_log_one_add`), and a partial sum plus a geometric tail bounds it above
(`log_one_add_le_sum_add`). Each logarithm is reduced to `m log 2 ± log (1 + a)` with the
Mathlib bounds on `log 2`, and every endpoint is rational.

## Attribution

Original to this repository.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset

/-- Partial sums of the `atanh` series bound `log (1 + a)` below: with `y = a/(a + 2)`,
`2 Σ_{k<n} y^(2k+1)/(2k+1) ≤ log (1 + a)`. -/
theorem sum_le_log_one_add {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    2 * ∑ k ∈ range n, 1 / (2 * (k : ℝ) + 1) * (a / (a + 2)) ^ (2 * k + 1) ≤
      Real.log (1 + a) := by
  have hy : 0 ≤ a / (a + 2) := div_nonneg ha (by linarith)
  have h := Real.hasSum_log_one_add ha
  rw [Finset.mul_sum]
  refine le_of_eq_of_le ?_ (sum_le_hasSum (range n)
    (fun i _ => mul_nonneg (by positivity) (pow_nonneg hy _)) h)
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The geometric tail bound: with `y = a/(a + 2)`,
`log (1 + a) ≤ 2 Σ_{k<n} y^(2k+1)/(2k+1) + 2 y^(2n+1)/((2n + 1)(1 - y²))`. -/
theorem log_one_add_le_sum_add {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.log (1 + a) ≤
      2 * ∑ k ∈ range n, 1 / (2 * (k : ℝ) + 1) * (a / (a + 2)) ^ (2 * k + 1) +
        2 * (a / (a + 2)) ^ (2 * n + 1) / ((2 * (n : ℝ) + 1) * (1 - (a / (a + 2)) ^ 2)) := by
  have h := Real.hasSum_log_one_add ha
  set y := a / (a + 2) with hydef
  have hy0 : 0 ≤ y := div_nonneg ha (by linarith)
  have hy1 : y < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hy20 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy21 : y ^ 2 < 1 := by nlinarith
  have ht := (hasSum_nat_add_iff' n).mpr h
  have hg := (hasSum_geometric_of_lt_one hy20 hy21).mul_left
    (2 * (1 / (2 * (n : ℝ) + 1)) * y ^ (2 * n + 1))
  have hle := hasSum_le (fun k => by
    show 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * y ^ (2 * (k + n) + 1) ≤
      2 * (1 / (2 * (n : ℝ) + 1)) * y ^ (2 * n + 1) * (y ^ 2) ^ k
    have hp : y ^ (2 * (k + n) + 1) = y ^ (2 * n + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    have hk : 1 / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 / (2 * (n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [hp, mul_assoc (2 * (1 / (2 * (n : ℝ) + 1)))]
    have hpos : 0 ≤ y ^ (2 * n + 1) * (y ^ 2) ^ k := by positivity
    have := mul_le_mul_of_nonneg_right hk hpos
    linarith) ht hg
  have hs : ∑ i ∈ range n, 2 * (1 / (2 * (i : ℝ) + 1)) * y ^ (2 * i + 1) =
      2 * ∑ k ∈ range n, 1 / (2 * (k : ℝ) + 1) * y ^ (2 * k + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hne : (1 : ℝ) - y ^ 2 ≠ 0 := by linarith
  have hn : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hc : 2 * (1 / (2 * (n : ℝ) + 1)) * y ^ (2 * n + 1) * (1 - y ^ 2)⁻¹ =
      2 * y ^ (2 * n + 1) / ((2 * (n : ℝ) + 1) * (1 - y ^ 2)) := by
    field_simp
  rw [hs, hc] at hle
  linarith

/-! ## Helpers: rational enclosures of logarithms and the three constants -/

/-- The lower bound on `log 2` as a fraction. -/
private theorem aux_log_two_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 :=
  calc (6931471803 / 10000000000 : ℝ) = 0.6931471803 := by norm_num
    _ < Real.log 2 := Real.log_two_gt_d9

/-- The upper bound on `log 2` as a fraction. -/
private theorem aux_log_two_hi : Real.log 2 < 6931471808 / 10000000000 :=
  calc Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    _ = 6931471808 / 10000000000 := by norm_num

/-- Upper bound on `log x` for `x = 2^m (1 + a)`, by the series with `n` terms and its tail. -/
private theorem aux_up_mul {x a c : ℝ} (m n : ℕ) (ha : 0 ≤ a) (hx : x = 2 ^ m * (1 + a))
    (hc : (m : ℝ) * (6931471808 / 10000000000) +
      (2 * ∑ k ∈ range n, 1 / (2 * (k : ℝ) + 1) * (a / (a + 2)) ^ (2 * k + 1) +
        2 * (a / (a + 2)) ^ (2 * n + 1) / ((2 * (n : ℝ) + 1) * (1 - (a / (a + 2)) ^ 2))) ≤ c) :
    Real.log x ≤ c := by
  have h1 := log_one_add_le_sum_add ha n
  have h3 : (m : ℝ) * Real.log 2 ≤ m * (6931471808 / 10000000000) :=
    mul_le_mul_of_nonneg_left aux_log_two_hi.le (Nat.cast_nonneg m)
  rw [hx, Real.log_mul (by positivity) (by linarith : (0 : ℝ) < 1 + a).ne', Real.log_pow]
  linarith

/-- Lower bound on `log x` for `x = 2^m (1 + a)`, by the series with `n` terms. -/
private theorem aux_lo_mul {x a c : ℝ} (m n : ℕ) (ha : 0 ≤ a) (hx : x = 2 ^ m * (1 + a))
    (hc : c ≤ (m : ℝ) * (6931471803 / 10000000000) +
      2 * ∑ k ∈ range n, 1 / (2 * (k : ℝ) + 1) * (a / (a + 2)) ^ (2 * k + 1)) :
    c ≤ Real.log x := by
  have h1 := sum_le_log_one_add ha n
  have h3 : (m : ℝ) * (6931471803 / 10000000000) ≤ m * Real.log 2 :=
    mul_le_mul_of_nonneg_left aux_log_two_lo.le (Nat.cast_nonneg m)
  rw [hx, Real.log_mul (by positivity) (by linarith : (0 : ℝ) < 1 + a).ne', Real.log_pow]
  linarith

/-- Upper bound on `log x` for `x = 2^m / (1 + a)`, by the series with `n` terms. -/
private theorem aux_up_div {x a c : ℝ} (m n : ℕ) (ha : 0 ≤ a) (hx : x = 2 ^ m / (1 + a))
    (hc : (m : ℝ) * (6931471808 / 10000000000) -
      2 * ∑ k ∈ range n, 1 / (2 * (k : ℝ) + 1) * (a / (a + 2)) ^ (2 * k + 1) ≤ c) :
    Real.log x ≤ c := by
  have h1 := sum_le_log_one_add ha n
  have h3 : (m : ℝ) * Real.log 2 ≤ m * (6931471808 / 10000000000) :=
    mul_le_mul_of_nonneg_left aux_log_two_hi.le (Nat.cast_nonneg m)
  rw [hx, Real.log_div (by positivity) (by linarith : (0 : ℝ) < 1 + a).ne', Real.log_pow]
  linarith

/-- Lower bound on `log x` for `x = 2^m / (1 + a)`, by the series with `n` terms and its tail. -/
private theorem aux_lo_div {x a c : ℝ} (m n : ℕ) (ha : 0 ≤ a) (hx : x = 2 ^ m / (1 + a))
    (hc : c ≤ (m : ℝ) * (6931471803 / 10000000000) -
      (2 * ∑ k ∈ range n, 1 / (2 * (k : ℝ) + 1) * (a / (a + 2)) ^ (2 * k + 1) +
        2 * (a / (a + 2)) ^ (2 * n + 1) / ((2 * (n : ℝ) + 1) * (1 - (a / (a + 2)) ^ 2)))) :
    c ≤ Real.log x := by
  have h1 := log_one_add_le_sum_add ha n
  have h3 : (m : ℝ) * (6931471803 / 10000000000) ≤ m * Real.log 2 :=
    mul_le_mul_of_nonneg_left aux_log_two_lo.le (Nat.cast_nonneg m)
  rw [hx, Real.log_div (by positivity) (by linarith : (0 : ℝ) < 1 + a).ne', Real.log_pow]
  linarith

/-- The constant `P` from an upper bound on `log ((1 - q)/ε)` and a lower bound on
`log ((1 - ε)/q)`. -/
private theorem aux_bandP_le_of_log {q e cX cY u : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hd : 0 < (1 - q - e) ^ 2)
    (hX : Real.log ((1 - q) / e) ≤ cX) (hY : cY ≤ Real.log ((1 - e) / q))
    (h : (1 - q) * cX - q * cY ≤ u * (1 - q - e) ^ 2) :
    klBer (1 - q) e / (1 - q - e) ^ 2 ≤ u := by
  rw [div_le_iff₀ hd]
  have hYi : Real.log (q / (1 - e)) = -Real.log ((1 - e) / q) := by
    rw [← Real.log_inv, inv_div]
  unfold klBer
  rw [sub_sub_cancel, hYi]
  have h1 := mul_le_mul_of_nonneg_left hX (sub_nonneg.mpr hq1)
  have h2 := mul_le_mul_of_nonneg_left hY hq0
  linarith

/-- The constant `Q` from upper bounds on `log ε⁻¹` and `log (1 - ε)⁻¹`. -/
private theorem aux_bandQ_le_of_log {e cN cZ u : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (hN : Real.log e⁻¹ ≤ cN) (hZ : Real.log (1 - e)⁻¹ ≤ cZ)
    (h : e * cN + (1 - e) * cZ ≤ u * (e * (1 - e))) :
    Real.binEntropy e / (e * (1 - e)) ≤ u := by
  rw [div_le_iff₀ (mul_pos he0 (sub_pos.mpr he1))]
  unfold Real.binEntropy
  have h1 := mul_le_mul_of_nonneg_left hN he0.le
  have h2 := mul_le_mul_of_nonneg_left hZ (sub_pos.mpr he1).le
  linarith

/-- The constant `r` for `q < 1/2` from a lower bound on `log ((1 - q)/q)`. -/
private theorem aux_le_bandR_of_log {q B cW u : ℝ} (hq : q < 1 / 2) (hB : 0 ≤ B / (1 + B) ^ 2)
    (hW : cW ≤ Real.log ((1 - q) / q)) (h : u ≤ B / (1 + B) ^ 2 * (cW / (1 - 2 * q))) :
    u ≤ B / (1 + B) ^ 2 * owL (min q (1 / 2)) := by
  rw [min_eq_left hq.le, owL, if_neg hq.ne]
  exact h.trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hW (by linarith)) hB)

/-! ## The six bands -/

/-- The band `[1, 4]`: `ε = 1/21`, `q = 2/3`. -/
theorem constants_band_1_4 :
    klBer (1 - 2 / 3) (1 / 21) / (1 - 2 / 3 - 1 / 21) ^ 2 ≤ (503296 / 100000 : ℝ) ∧
    Real.binEntropy (1 / 21) / (1 / 21 * (1 - 1 / 21)) ≤ (422135 / 100000 : ℝ) ∧
    (32000 / 100000 : ℝ) ≤ 4 / (1 + 4) ^ 2 * owL (min (2 / 3) (1 / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact aux_bandP_le_of_log (cX := 19459101497755 / 10000000000000)
      (cY := 3566749436787 / 10000000000000) (by norm_num) (by norm_num) (by norm_num)
      (aux_up_div 3 5 (a := 1 / 7) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_lo_div 1 7 (a := 2 / 5) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_bandQ_le_of_log (cN := 30445224386837 / 10000000000000)
      (cZ := 487901641695 / 10000000000000) (by norm_num) (by norm_num)
      (aux_up_mul 4 6 (a := 5 / 16) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_up_mul 0 4 (a := 1 / 20) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · rw [min_eq_right (by norm_num), owL_half]
    norm_num

/-- The band `[4, 8]`: `ε = 1/73`, `q = 5/21`. -/
theorem constants_band_4_8 :
    klBer (1 - 5 / 21) (1 / 73) / (1 - 5 / 21 - 1 / 73) ^ 2 ≤ (486473 / 100000 : ℝ) ∧
    Real.binEntropy (1 / 73) / (1 / 73 * (1 - 1 / 73)) ≤ (535697 / 100000 : ℝ) ∧
    (21931 / 100000 : ℝ) ≤ 8 / (1 + 8) ^ 2 * owL (min (5 / 21) (1 / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact aux_bandP_le_of_log (cX := 40185257271052 / 10000000000000)
      (cY := 14212912026369 / 10000000000000) (by norm_num) (by norm_num) (by norm_num)
      (aux_up_div 6 5 (a := 11 / 73) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_lo_mul 2 3 (a := 13 / 365) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_bandQ_le_of_log (cN := 42904594425888 / 10000000000000)
      (cZ := 137933221324 / 10000000000000) (by norm_num) (by norm_num)
      (aux_up_mul 6 5 (a := 9 / 64) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_up_mul 0 3 (a := 1 / 72) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_le_bandR_of_log (cW := 11631508092857 / 10000000000000) (by norm_num) (by norm_num)
      (aux_lo_div 2 6 (a := 1 / 4) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)

/-- The band `[8, 12]`: `ε = 1/157`, `q = 9/73`. -/
theorem constants_band_8_12 :
    klBer (1 - 9 / 73) (1 / 157) / (1 - 9 / 73 - 1 / 157) ^ 2 ≤ (536008 / 100000 : ℝ) ∧
    Real.binEntropy (1 / 157) / (1 / 157 * (1 - 1 / 157)) ≤ (609186 / 100000 : ℝ) ∧
    (18487 / 100000 : ℝ) ≤ 12 / (1 + 12) ^ 2 * owL (min (9 / 73) (1 / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact aux_bandP_le_of_log (cX := 49246694492400 / 10000000000000)
      (cY := 20868450649332 / 10000000000000) (by norm_num) (by norm_num) (by norm_num)
      (aux_up_mul 7 4 (a := 11 / 146) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_lo_mul 3 2 (a := 7 / 942) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_bandQ_le_of_log (cN := 50562458070287 / 10000000000000)
      (cZ := 63897980988 / 10000000000000) (by norm_num) (by norm_num)
      (aux_up_mul 7 6 (a := 29 / 128) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_up_mul 0 2 (a := 1 / 156) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_le_bandR_of_log (cW := 19616585052436 / 10000000000000) (by norm_num) (by norm_num)
      (aux_lo_div 3 5 (a := 1 / 8) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)

/-- The band `[12, 14]`: `ε = 1/211`, `q = 13/157`. -/
theorem constants_band_12_14 :
    klBer (1 - 13 / 157) (1 / 211) / (1 - 13 / 157 - 1 / 211) ^ 2 ≤ (555328 / 100000 : ℝ) ∧
    Real.binEntropy (1 / 211) / (1 / 211 * (1 - 1 / 211)) ≤ (637973 / 100000 : ℝ) ∧
    (17933 / 100000 : ℝ) ≤ 14 / (1 + 14) ^ 2 * owL (min (13 / 157) (1 / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact aux_bandP_le_of_log (cX := 52654256296243 / 10000000000000)
      (cY := 24865458440883 / 10000000000000) (by norm_num) (by norm_num) (by norm_num)
      (aux_up_div 8 7 (a := 613 / 1899) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_lo_div 4 7 (a := 5459 / 16485) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_bandQ_le_of_log (cN := 53518581353966 / 10000000000000)
      (cZ := 47506027586 / 10000000000000) (by norm_num) (by norm_num)
      (aux_up_div 8 6 (a := 45 / 211) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_up_mul 0 2 (a := 1 / 210) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_le_bandR_of_log (cW := 24048639413344 / 10000000000000) (by norm_num) (by norm_num)
      (aux_lo_mul 3 7 (a := 5 / 13) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)

/-- The band `[14, 76/5]`: `ε = 25/6181`, `q = 15/211`. -/
theorem constants_band_14_76_5 :
    klBer (1 - 15 / 211) (25 / 6181) / (1 - 15 / 211 - 25 / 6181) ^ 2 ≤ (568460 / 100000 : ℝ) ∧
    Real.binEntropy (25 / 6181) / (25 / 6181 * (1 - 25 / 6181)) ≤ (653477 / 100000 : ℝ) ∧
    (17352 / 100000 : ℝ) ≤ 76 / 5 / (1 + 76 / 5) ^ 2 * owL (min (15 / 211) (1 / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact aux_bandP_le_of_log (cX := 54366160524669 / 10000000000000)
      (cY := 26397550766335 / 10000000000000) (by norm_num) (by norm_num) (by norm_num)
      (aux_up_div 8 4 (a := 34731 / 302869) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_lo_div 4 5 (a := 15377 / 108243) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_bandQ_le_of_log (cN := 55103595267117 / 10000000000000)
      (cZ := 40528547006 / 10000000000000) (by norm_num) (by norm_num)
      (aux_up_div 8 3 (a := 219 / 6181) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_up_mul 0 2 (a := 25 / 6156) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_le_bandR_of_log (cW := 25700644570885 / 10000000000000) (by norm_num) (by norm_num)
      (aux_lo_div 4 6 (a := 11 / 49) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)

/-- The band `[76/5, 16]`: `ε = 1/273`, `q = 405/6181`. -/
theorem constants_band_76_5_16 :
    klBer (1 - 405 / 6181) (1 / 273) / (1 - 405 / 6181 - 1 / 273) ^ 2 ≤ (577122 / 100000 : ℝ) ∧
    Real.binEntropy (1 / 273) / (1 / 273 * (1 - 1 / 273)) ≤ (663194 / 100000 : ℝ) ∧
    (16932 / 100000 : ℝ) ≤ 16 / (1 + 16) ^ 2 * owL (min (405 / 6181) (1 / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact aux_bandP_le_of_log (cX := 55417031280188 / 10000000000000)
      (cY := 27216785526239 / 10000000000000) (by norm_num) (by norm_num) (by norm_num)
      (aux_up_div 8 2 (a := 49 / 14079) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_lo_div 4 4 (a := 784 / 15011) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_bandQ_le_of_log (cN := 56094717971054 / 10000000000000)
      (cZ := 36697288890 / 10000000000000) (by norm_num) (by norm_num)
      (aux_up_mul 8 4 (a := 17 / 256) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (aux_up_mul 0 2 (a := 1 / 272) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)
  · exact aux_le_bandR_of_log (cW := 26575796124263 / 10000000000000) (by norm_num) (by norm_num)
      (aux_lo_div 4 5 (a := 44 / 361) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
      (by norm_num)

end

end BinaryRow

end StochasticToDeterministicLatents
