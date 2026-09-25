import StochasticToDeterministicLatents.BinaryRow.EntropyScaling
import StochasticToDeterministicLatents.BinaryRow.ReplicaCells
import StochasticToDeterministicLatents.BinaryRow.EntropySums
import StochasticToDeterministicLatents.BinaryRow.ComponentInfo

/-!
# Large separation

Let `V` be a `Bit`-labelled latent on `Bit × Y` whose two components are contacts of one
feasible kernel, with row parameters `0 < s < t`, positive priors and `t/s ≥ 16`. Then
`(173/325) · H(W | X) ≤ V.score` (`twoContact_condEntropy_label_le_score`). Combined with
`T_le_score_add_three_condEntropy` and `condEntropy_label_le`, this gives `T ≤ (1148/173) · score`.

The statement is in bits. The proof multiplies by `log 2` and works in nats, where
`homBinEntropy` (`Hh`) and `owL` live. Write `k = t/s`, `κ = st/(s+t)² = k/(k+1)²`,
`η = (2k+1)/(k+1)²`, `a = s³/(1+s³)`, `b = 1/(1+t³)`, priors `π₀, π₁`, and `A0 = π₀(1-a)`,
`B0 = π₀a`, `A1 = π₁b`, `B1 = π₁(1-b)`.

* `log 2 · H(W|X) = Hh(A0,A1) + Hh(B0,B1)`; `log 2 · H(W|X',X)` is `Hh` summed over the four
  replica cells.
* `(st)² < s+t` and `1 < st(s+t)` give `k²s³ < k+1` and `k(k+1)s³ > 1`. Hence
  `a + κ(1-a) ≤ η`, `b + κ(1-b) ≤ η`, both odds `(1-a)/a` and `(1-b)/b` are at least 15,
  their product is `k³ ≥ 4096`, and `η ≤ 33/289`.
* Monotonicity of `Hh` bounds the diagonal cells by `Hh(A0,ηA1)` and `Hh(ηB0,B1)`, and each
  off-diagonal cell by `Hh(B0,A1)`.
* `homBinEntropy_separation` gives `2 Hh(B0,A1) ≤ (4/13)(Hh(A0,A1) + Hh(B0,B1))`.
* `homBinEntropy_scale_le` bounds the diagonal cells by `4/25` of the same sum plus
  `(43061/16000) κ (B0 + A1)`.
* `log 15 > 27/10` and `twoContact_condMutualInfo_ge_owL` give
  `log 2 · I(X;Y|W) ≥ (27/10) κ (B0 + A1)`, which pays that error.
* `latent_replica_bound` with `replicaLaw_B2_eq` gives
  `score ≥ I(X;Y|W) + H(W|X) - H(W|X',X)`, and `1 - 4/25 - 4/13 = 173/325`.

## Attribution

Original to this repository, on the latent interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-! ### Scalar helpers -/

/-- `log 15 > 27/10`, from `log 16 = 4 log 2` and `log (16/15) ≤ 1/15`. -/
private theorem aux_log15 : (27 : ℝ) / 10 < Real.log 15 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  norm_num at h2
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hq := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 / 15 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at hq
  linarith

/-- For `0 < r` with odds `(1 - r)/r ≥ 15`, `owL r · r(1 - r) ≥ (27/10) r`. -/
private theorem aux_owL {r : ℝ} (h0 : 0 < r) (h15 : 15 ≤ (1 - r) / r) :
    27 / 10 * r ≤ owL r * (r * (1 - r)) := by
  have hr : 15 * r ≤ 1 - r := by rwa [le_div_iff₀ h0] at h15
  have hhalf : r ≠ 1 / 2 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have hlog : 27 / 10 < Real.log ((1 - r) / r) :=
    lt_of_lt_of_le aux_log15 (Real.log_le_log (by norm_num) h15)
  have hd : 0 < 1 - 2 * r := by linarith
  have hrr : 0 ≤ r * (1 - r) := mul_nonneg h0.le (by linarith)
  have e : Real.log ((1 - r) / r) / (1 - 2 * r) * (r * (1 - r)) =
      Real.log ((1 - r) / r) * (r * (1 - r)) / (1 - 2 * r) := div_mul_eq_mul_div _ _ _
  rw [owL, if_neg hhalf, e, le_div_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_right hlog.le hrr, mul_pos h0 h0]

/-- The complementary form: for `m < 1` with odds `m/(1 - m) ≥ 15`,
`owL m · m(1 - m) ≥ (27/10)(1 - m)`. -/
private theorem aux_owL_one_sub {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (h15 : 15 ≤ m / (1 - m)) :
    27 / 10 * (1 - m) ≤ owL m * (m * (1 - m)) := by
  have h := aux_owL (r := 1 - m) (by linarith) (by rwa [sub_sub_cancel])
  rw [owL_symm hm0 hm1, sub_sub_cancel] at h
  linarith

/-- Combining the two component bounds with the prior weights. -/
private theorem aux_J {κ p0 p1 x0 x1 y0 y1 J : ℝ} (hκ : 0 ≤ κ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (h0 : 27 / 10 * x0 ≤ y0) (h1 : 27 / 10 * x1 ≤ y1) (hJ : κ * (p0 * y0 + p1 * y1) ≤ J) :
    27 / 10 * (κ * (p0 * x0 + p1 * x1)) ≤ J := by
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left h0 hp0) (mul_le_mul_of_nonneg_left h1 hp1)) hκ
  linarith

/-- Monotonicity of `Hh` in both arguments on `[0, ∞)²`. -/
private theorem aux_mono {x y X Z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxX : x ≤ X) (hyZ : y ≤ Z) :
    homBinEntropy x y ≤ homBinEntropy X Z :=
  (homBinEntropy_mono_left hx hxX hy).trans (homBinEntropy_mono_right (hx.trans hxX) hy hyZ)

/-- The band facts for `t = k s`, `k ≥ 16`, from the determinant inequalities. -/
private theorem aux_params {s t k a m : ℝ} (hs : 0 < s) (htk : t = k * s) (hk : 16 ≤ k)
    (h1 : (s * t) ^ 2 < s + t) (h2 : 1 < s * t * (s + t))
    (ha : a = s ^ 3 / (1 + s ^ 3)) (hm : m = t ^ 3 / (1 + t ^ 3)) :
    0 < a ∧ a < 1 ∧ 0 < m ∧ m < 1 ∧
    0 ≤ s * t / (s + t) ^ 2 ∧ s * t / (s + t) ^ 2 ≤ 1 ∧
    0 < (2 * k + 1) / (k + 1) ^ 2 ∧ (2 * k + 1) / (k + 1) ^ 2 ≤ 33 / 289 ∧
    a + s * t / (s + t) ^ 2 * (1 - a) ≤ (2 * k + 1) / (k + 1) ^ 2 ∧
    (1 - m) + s * t / (s + t) ^ 2 * m ≤ (2 * k + 1) / (k + 1) ^ 2 ∧
    15 ≤ (1 - a) / a ∧ 15 ≤ m / (1 - m) ∧ 4096 ≤ (1 - a) / a * (m / (1 - m)) ∧
    (2 * k + 1) / (k + 1) ^ 2 / (33 / 289) * (149 / 1000) ≤
      43061 / 16000 * (s * t / (s + t) ^ 2) := by
  subst htk ha hm
  have hk0 : 0 < k := by linarith
  have hs' : s ≠ 0 := hs.ne'
  have hu : 0 < s ^ 3 := by positivity
  have hu' : s ^ 3 ≠ 0 := hu.ne'
  have hU : (1 + s ^ 3) ≠ 0 := by positivity
  have hT : (1 + (k * s) ^ 3) ≠ 0 := by positivity
  have hk1 : k + 1 ≠ 0 := by positivity
  have hsk : s + k * s ≠ 0 := by positivity
  have hκ : s * (k * s) / (s + k * s) ^ 2 = k / (k + 1) ^ 2 := by
    field_simp
    ring
  have hu1 : k ^ 2 * s ^ 3 < k + 1 := by
    have e1 : (s * (k * s)) ^ 2 = s * (k ^ 2 * s ^ 3) := by ring
    have e2 : s + k * s = s * (k + 1) := by ring
    rw [e1, e2] at h1
    exact lt_of_mul_lt_mul_left h1 hs.le
  have hu2 : 1 < k * (k + 1) * s ^ 3 := by
    have e : s * (k * s) * (s + k * s) = k * (k + 1) * s ^ 3 := by ring
    rwa [e] at h2
  have hq : 15 * (k + 1) ≤ k ^ 2 := by nlinarith
  rw [hκ]
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_, by positivity, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    linarith
  · rw [div_lt_one (by positivity)]
    linarith
  · rw [div_le_one (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hk) (by linarith : (0 : ℝ) ≤ 33 * k + 16)]
  · have e : (2 * k + 1) / (k + 1) ^ 2 -
        (s ^ 3 / (1 + s ^ 3) + k / (k + 1) ^ 2 * (1 - s ^ 3 / (1 + s ^ 3))) =
        (k + 1 - k ^ 2 * s ^ 3) / ((1 + s ^ 3) * (k + 1) ^ 2) := by
      field_simp
      ring
    have : 0 ≤ (k + 1 - k ^ 2 * s ^ 3) / ((1 + s ^ 3) * (k + 1) ^ 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  · have e : (2 * k + 1) / (k + 1) ^ 2 -
        ((1 - (k * s) ^ 3 / (1 + (k * s) ^ 3)) +
          k / (k + 1) ^ 2 * ((k * s) ^ 3 / (1 + (k * s) ^ 3))) =
        k ^ 2 * (k * (k + 1) * s ^ 3 - 1) / ((k + 1) ^ 2 * (1 + (k * s) ^ 3)) := by
      field_simp
      ring
    have : 0 ≤ k ^ 2 * (k * (k + 1) * s ^ 3 - 1) / ((k + 1) ^ 2 * (1 + (k * s) ^ 3)) :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    linarith
  · have e : (1 - s ^ 3 / (1 + s ^ 3)) / (s ^ 3 / (1 + s ^ 3)) = 1 / s ^ 3 := by
      field_simp
      ring
    rw [e, le_div_iff₀ hu]
    have h3 : k ^ 2 * (15 * s ^ 3) < k ^ 2 * 1 := by nlinarith
    have := lt_of_mul_lt_mul_left h3 (by positivity)
    linarith
  · have e : (k * s) ^ 3 / (1 + (k * s) ^ 3) / (1 - (k * s) ^ 3 / (1 + (k * s) ^ 3)) =
        k ^ 3 * s ^ 3 := by
      field_simp
      ring
    rw [e]
    have h3 : (k + 1) * 15 < (k + 1) * (k ^ 3 * s ^ 3) := by
      nlinarith [mul_lt_mul_of_pos_left hu2 (by positivity : (0 : ℝ) < k ^ 2)]
    linarith [lt_of_mul_lt_mul_left h3 (by linarith : (0 : ℝ) ≤ k + 1)]
  · have e : (1 - s ^ 3 / (1 + s ^ 3)) / (s ^ 3 / (1 + s ^ 3)) *
        ((k * s) ^ 3 / (1 + (k * s) ^ 3) / (1 - (k * s) ^ 3 / (1 + (k * s) ^ 3))) = k ^ 3 := by
      field_simp
      ring
    rw [e]
    have : (16 : ℝ) ^ 3 ≤ k ^ 3 := pow_le_pow_left₀ (by norm_num) hk 3
    norm_num at this
    linarith
  · have e : 43061 / 16000 * (k / (k + 1) ^ 2) - (2 * k + 1) / (k + 1) ^ 2 / (33 / 289) *
        (149 / 1000) = 43061 * (k - 16) / (528000 * (k + 1) ^ 2) := by
      field_simp
      ring
    have : 0 ≤ 43061 * (k - 16) / (528000 * (k + 1) ^ 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith

/-- The cell domination, separation and scaling chain, on plain reals. -/
private theorem aux_cells {p0 p1 a m κ η : ℝ} (hp0 : 0 < p0) (hp1 : 0 < p1) (ha0 : 0 < a)
    (ha1 : a < 1)
    (hm0 : 0 < m) (hm1 : m < 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hη0 : 0 < η) (hη : η ≤ 33 / 289)
    (hηa : a + κ * (1 - a) ≤ η) (hηm : (1 - m) + κ * m ≤ η) (hL : 15 ≤ (1 - a) / a)
    (hR : 15 ≤ m / (1 - m)) (hLR : 4096 ≤ (1 - a) / a * (m / (1 - m)))
    (hηκ : η / (33 / 289) * (149 / 1000) ≤ 43061 / 16000 * κ) :
    homBinEntropy (p0 * ((1 - a) ^ 2 + κ * a * (1 - a))) (p1 * ((1 - m) ^ 2 + κ * m * (1 - m)))
      + homBinEntropy (p0 * ((1 - κ) * a * (1 - a))) (p1 * ((1 - κ) * m * (1 - m)))
      + (homBinEntropy (p0 * ((1 - κ) * a * (1 - a))) (p1 * ((1 - κ) * m * (1 - m)))
        + homBinEntropy (p0 * (a ^ 2 + κ * a * (1 - a))) (p1 * (m ^ 2 + κ * m * (1 - m)))) ≤
      (4 / 25 + 4 / 13) * (homBinEntropy (p0 * (1 - a)) (p1 * (1 - m))
        + homBinEntropy (p0 * a) (p1 * m))
      + 43061 / 16000 * (κ * (p0 * a + p1 * (1 - m))) := by
  have h1a : 0 < 1 - a := by linarith
  have h1m : 0 < 1 - m := by linarith
  have h1κ : 0 ≤ 1 - κ := by linarith
  have hA0 : 0 < p0 * (1 - a) := mul_pos hp0 h1a
  have hA1 : 0 < p1 * (1 - m) := mul_pos hp1 h1m
  have hB0 : 0 < p0 * a := mul_pos hp0 ha0
  have hB1 : 0 < p1 * m := mul_pos hp1 hm0
  have c00 : homBinEntropy (p0 * ((1 - a) ^ 2 + κ * a * (1 - a)))
      (p1 * ((1 - m) ^ 2 + κ * m * (1 - m))) ≤
      homBinEntropy (p0 * (1 - a)) (η * (p1 * (1 - m))) := by
    refine aux_mono (mul_nonneg hp0.le ?_) (mul_nonneg hp1.le ?_) ?_ ?_
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hκ0 ha0.le) h1a.le)
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hκ0 hm0.le) h1m.le)
    · exact mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg (mul_nonneg h1a.le ha0.le) h1κ]) hp0.le
    · have h := mul_le_mul_of_nonneg_left hηm h1m.le
      nlinarith [mul_le_mul_of_nonneg_left h hp1.le]
  have c01 : homBinEntropy (p0 * ((1 - κ) * a * (1 - a))) (p1 * ((1 - κ) * m * (1 - m))) ≤
      homBinEntropy (p0 * a) (p1 * (1 - m)) := by
    refine aux_mono (mul_nonneg hp0.le (mul_nonneg (mul_nonneg h1κ ha0.le) h1a.le))
      (mul_nonneg hp1.le (mul_nonneg (mul_nonneg h1κ hm0.le) h1m.le)) ?_ ?_
    · exact mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg ha0.le hκ0, mul_nonneg (mul_nonneg ha0.le ha0.le) h1κ]) hp0.le
    · exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (1 - m), mul_nonneg (mul_nonneg hκ0 hm0.le) h1m.le]) hp1.le
  have c11 : homBinEntropy (p0 * (a ^ 2 + κ * a * (1 - a))) (p1 * (m ^ 2 + κ * m * (1 - m))) ≤
      homBinEntropy (η * (p0 * a)) (p1 * m) := by
    refine aux_mono
      (mul_nonneg hp0.le (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hκ0 ha0.le) h1a.le)))
      (mul_nonneg hp1.le (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hκ0 hm0.le) h1m.le)))
      ?_ ?_
    · have h := mul_le_mul_of_nonneg_left hηa ha0.le
      nlinarith [mul_le_mul_of_nonneg_left h hp0.le]
    · exact mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg (mul_nonneg hm0.le h1m.le) h1κ]) hp1.le
  have hsep := homBinEntropy_separation hB0 hA1 hL hR hLR
  have e1 : (1 - a) / a * (p0 * a) = p0 * (1 - a) := by
    rw [div_mul_eq_mul_div, div_eq_iff ha0.ne']
    ring
  have e2 : m / (1 - m) * (p1 * (1 - m)) = p1 * m := by
    rw [div_mul_eq_mul_div, div_eq_iff h1m.ne']
    ring
  rw [e1, e2] at hsep
  have hs1 := homBinEntropy_scale_le hη0 hη hA1 hA0
  rw [homBinEntropy_comm (η * (p1 * (1 - m))) (p0 * (1 - a)),
    homBinEntropy_comm (p1 * (1 - m)) (p0 * (1 - a))] at hs1
  have hs2 := homBinEntropy_scale_le hη0 hη hB0 hB1
  have hc := mul_le_mul_of_nonneg_right hηκ (add_pos hA1 hB0).le
  linarith

/-- The final combination, on plain reals. -/
private theorem aux_final {l HWX HWXX Jb B2 S Vn V2n κe : ℝ} (hl : 0 < l) (hB : B2 = HWX - HWXX)
    (hS : Jb + B2 ≤ S) (hV : l * HWX = Vn) (hV2 : l * HWXX = V2n) (hJ : 27 / 10 * κe ≤ l * Jb)
    (hC : V2n ≤ (4 / 25 + 4 / 13) * Vn + 43061 / 16000 * κe) (hκe : 0 ≤ κe) :
    173 / 325 * HWX ≤ S := by
  have h1 : l * (Jb + B2) ≤ l * S := mul_le_mul_of_nonneg_left hS hl.le
  have h2 : l * (Jb + B2) = l * Jb + Vn - V2n := by
    rw [hB, ← hV, ← hV2]
    ring
  have h3 : l * (173 / 325 * HWX) = 173 / 325 * Vn := by
    rw [← hV]
    ring
  exact le_of_mul_le_mul_left (by linarith) hl

/-! ### Replica cells and row masses -/

private theorem aux_cell_00 (κ r : ℝ) : replicaCell κ r 0 0 = (1 - r) ^ 2 + κ * r * (1 - r) := by
  have h01 : (0 : Bit) ≠ 1 := by decide
  simp only [replicaCell, h01, ↓reduceIte]

private theorem aux_cell_01 (κ r : ℝ) : replicaCell κ r 0 1 = (1 - κ) * r * (1 - r) := by
  have h01 : (0 : Bit) ≠ 1 := by decide
  simp only [replicaCell, h01, ↓reduceIte]

private theorem aux_cell_10 (κ r : ℝ) : replicaCell κ r 1 0 = (1 - κ) * r * (1 - r) := by
  have h01 : (0 : Bit) ≠ 1 := by decide
  simp only [replicaCell, h01, ↓reduceIte]

private theorem aux_cell_11 (κ r : ℝ) : replicaCell κ r 1 1 = r ^ 2 + κ * r * (1 - r) := by
  simp only [replicaCell, ↓reduceIte]

omit [DecidableEq Y] in
private theorem aux_rowMass_zero {q : Bit × Y → ℝ} {x : ℝ} (h : RowCubeParam q x) :
    rowMass q 0 = 1 - rowMass q 1 := by
  obtain ⟨hx, h0, h1⟩ := h
  have hU : (1 + x ^ 3) ≠ 0 := by positivity
  rw [h0, h1, one_sub_div hU]
  ring

/-- Large separation: for a two-contact latent with row parameters `0 < s < t`, positive priors and
`t/s ≥ 16`, `(173/325) · H(W | X) ≤ score`. -/
theorem twoContact_condEntropy_label_le_score {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s < t) (hpos : ∀ v, 0 < V.prior v) (hk : 16 ≤ t / s) :
    173 / 325 * condEntropy (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1) V.joint ≤
      V.score := by
  have hp0 := hpos (e.symm 0)
  have hp1 := hpos (e.symm 1)
  have hs0 : 0 < s := hs.1
  obtain ⟨hA, hB⟩ :=
    rowTwoContact_param_ineq hw h0 h1 (ne_of_rowCubeParam_ne hs ht hst.ne) hs ht
  obtain ⟨ha0, ha1, hm0, hm1, hκ0, hκ1, hη0, hη, hηa, hηm, hL, hR, hLR, hηκ⟩ :=
    aux_params (k := t / s) hs0 (by field_simp) hk hA hB hs.2.2 ht.2.2
  have hV : Real.log 2 *
      condEntropy (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1) V.joint =
      homBinEntropy (V.prior (e.symm 0) * (1 - rowMass (V.comp (e.symm 0)) 1))
          (V.prior (e.symm 1) * (1 - rowMass (V.comp (e.symm 1)) 1))
        + homBinEntropy (V.prior (e.symm 0) * rowMass (V.comp (e.symm 0)) 1)
          (V.prior (e.symm 1) * rowMass (V.comp (e.symm 1)) 1) := by
    rw [bitLatent_log_two_mul_condEntropy_label V e, Fin.sum_univ_two, aux_rowMass_zero hs,
      aux_rowMass_zero ht]
    rfl
  have hV2 : Real.log 2 *
      condEntropy (fun a : V.ι × (Bit × (Bit × Y)) => a.1) (fun a => (a.2.2.1, a.2.1))
        (replicaLaw V.joint) =
      homBinEntropy (V.prior (e.symm 0) * ((1 - rowMass (V.comp (e.symm 0)) 1) ^ 2 +
            s * t / (s + t) ^ 2 * rowMass (V.comp (e.symm 0)) 1 *
              (1 - rowMass (V.comp (e.symm 0)) 1)))
          (V.prior (e.symm 1) * ((1 - rowMass (V.comp (e.symm 1)) 1) ^ 2 +
            s * t / (s + t) ^ 2 * rowMass (V.comp (e.symm 1)) 1 *
              (1 - rowMass (V.comp (e.symm 1)) 1)))
        + homBinEntropy (V.prior (e.symm 0) * ((1 - s * t / (s + t) ^ 2) *
            rowMass (V.comp (e.symm 0)) 1 * (1 - rowMass (V.comp (e.symm 0)) 1)))
          (V.prior (e.symm 1) * ((1 - s * t / (s + t) ^ 2) *
            rowMass (V.comp (e.symm 1)) 1 * (1 - rowMass (V.comp (e.symm 1)) 1)))
        + (homBinEntropy (V.prior (e.symm 0) * ((1 - s * t / (s + t) ^ 2) *
            rowMass (V.comp (e.symm 0)) 1 * (1 - rowMass (V.comp (e.symm 0)) 1)))
          (V.prior (e.symm 1) * ((1 - s * t / (s + t) ^ 2) *
            rowMass (V.comp (e.symm 1)) 1 * (1 - rowMass (V.comp (e.symm 1)) 1)))
        + homBinEntropy (V.prior (e.symm 0) * (rowMass (V.comp (e.symm 0)) 1 ^ 2 +
            s * t / (s + t) ^ 2 * rowMass (V.comp (e.symm 0)) 1 *
              (1 - rowMass (V.comp (e.symm 0)) 1)))
          (V.prior (e.symm 1) * (rowMass (V.comp (e.symm 1)) 1 ^ 2 +
            s * t / (s + t) ^ 2 * rowMass (V.comp (e.symm 1)) 1 *
              (1 - rowMass (V.comp (e.symm 1)) 1)))) := by
    rw [twoContact_log_two_mul_condEntropy_label_rows V e hw h0 h1 hs ht hst.ne]
    simp only [Fin.sum_univ_two, aux_cell_00, aux_cell_01, aux_cell_10, aux_cell_11]
    rfl
  have hC := aux_cells hp0 hp1 ha0 ha1 hm0 hm1 hκ0 hκ1 hη0 hη hηa hηm hL hR hLR hηκ
  have hJ0 := twoContact_condMutualInfo_ge_owL V e hw h0 h1 hs ht hst.ne
  simp only [Fin.sum_univ_two] at hJ0
  have hJ := aux_J hκ0 hp0.le hp1.le (aux_owL ha0 hL) (aux_owL_one_sub hm0 hm1 hR) hJ0
  have hκe : 0 ≤ s * t / (s + t) ^ 2 * (V.prior (e.symm 0) * rowMass (V.comp (e.symm 0)) 1 +
      V.prior (e.symm 1) * (1 - rowMass (V.comp (e.symm 1)) 1)) :=
    mul_nonneg hκ0 (add_nonneg (mul_nonneg hp0.le ha0.le) (mul_nonneg hp1.le (by linarith)))
  exact aux_final (Real.log_pos one_lt_two) (replicaLaw_B2_eq V.joint_isPMF)
    (latent_replica_bound V) hV hV2 hJ hC hκe

end

end BinaryRow

end StochasticToDeterministicLatents
