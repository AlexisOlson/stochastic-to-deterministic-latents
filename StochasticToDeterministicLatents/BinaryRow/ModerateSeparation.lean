import StochasticToDeterministicLatents.BinaryRow.ReplicaInfo
import StochasticToDeterministicLatents.BinaryRow.SeparationBand
import StochasticToDeterministicLatents.BinaryRow.JensenGap
import StochasticToDeterministicLatents.BinaryRow.EntropyVariance
import StochasticToDeterministicLatents.BinaryRow.EntropySums
import StochasticToDeterministicLatents.BinaryRow.Interfaces

/-!
# Moderate separation: the balance bound on one band

For a two-contact latent `V` on `Bit × Y` with row parameters `0 < s < t`, positive priors and
ratio `k = t/s` in a separation band `1 ≤ A ≤ k ≤ B`, put `ε = 1/(B² + B + 1)`,
`q = (A + 1)/(A² + A + 1)`, `κ(x) = x/(1 + x)²` and `σ = 2 (1 - κ(A))²`. If `P`, `Q` and `r`
bound the band constants, `P ≥ klBer (1 - q) ε/(1 - q - ε)²`, `Q ≥ h(ε)/(ε (1 - ε))` and
`0 < r ≤ κ(B) · owL (min q (1/2))`, with `2r < Q`, then
`min (I(X; Y), H(X | Y)) ≤ balanceCoeff P Q r σ · score(V)` (`twoContact_min_le_balanceCoeff`).

The proof applies `twoCode_balance` to the quantities multiplied by `log 2`, with
`a = P(X = 1 | W = 0)`, `b = P(X = 0 | W = 1)`, `w = P(W = 1)` and the between- and
within-component variances `u`, `v`: the replica bound `I(X; Y | W) + I(W; X' | X) ≤ score`; the
two code interfaces; the Jensen-gap bound `log 2 · I(W; X) ≤ P u` on the band rectangle
`a ∈ [ε, q]`, `1 - b ∈ [1 - q, 1 - ε]`; the entropy bound `log 2 · H(X | W) ≤ Q v`; the band
bound `r v ≤ log 2 · I(X; Y | W)`; and the replica bound `σ u v/(u + v) ≤ log 2 · I(W; X' | X)`,
using `κ(t/s) ≤ κ(A)`.

Both sides of the conclusion are in bits. The band constants are in nats; they meet the
bit-valued quantities through the factor `log 2`, which cancels because the bound is homogeneous.

## Attribution

Original to this repository, on the latent interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- The band constants: for `1 ≤ A ≤ t/s ≤ B` with `0 < s < t`, `ε = 1/(B² + B + 1)` and
`q = (A + 1)/(A² + A + 1)` satisfy `0 < ε ≤ 1/2` and `ε < q < 1 - ε`. -/
private theorem aux_band {A B s t : ℝ} (hA : 1 ≤ A) (hs0 : 0 < s) (hst : s < t) (hAk : A ≤ t / s)
    (hkB : t / s ≤ B) :
    0 < 1 / (B ^ 2 + B + 1) ∧ 1 / (B ^ 2 + B + 1) ≤ 1 / 2 ∧
      1 / (B ^ 2 + B + 1) < (A + 1) / (A ^ 2 + A + 1) ∧
      (A + 1) / (A ^ 2 + A + 1) < 1 - 1 / (B ^ 2 + B + 1) := by
  have hks : 1 < t / s := (one_lt_div hs0).2 hst
  have hB1 : 1 < B := lt_of_lt_of_le hks hkB
  have hAB : A ≤ B := hAk.trans hkB
  have hDB : 0 < B ^ 2 + B + 1 := by nlinarith
  have hDA : 0 < A ^ 2 + A + 1 := by nlinarith
  have hε : 0 < 1 / (B ^ 2 + B + 1) := div_pos one_pos hDB
  have hε2 : 1 / (B ^ 2 + B + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hDB (by norm_num)]
    nlinarith
  have hεq : 1 / (B ^ 2 + B + 1) < (A + 1) / (A ^ 2 + A + 1) := by
    rw [div_lt_div_iff₀ hDB hDA]
    nlinarith [mul_le_mul hAB hAB (by linarith) (by linarith)]
  have hq23 : (A + 1) / (A ^ 2 + A + 1) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ hDA (by norm_num)]
    nlinarith
  have hε3 : 1 / (B ^ 2 + B + 1) < 1 / 3 := by
    rw [div_lt_div_iff₀ hDB (by norm_num)]
    nlinarith
  exact ⟨hε, hε2, hεq, by linarith⟩

omit [DecidableEq Y] in
/-- A row cube parameter makes the two row masses sum to one. -/
private theorem aux_rowMass_one {q : Bit × Y → ℝ} {x : ℝ} (h : RowCubeParam q x) :
    rowMass q 1 = 1 - rowMass q 0 := by
  have hx : 0 < x := h.1
  rw [h.2.2, h.2.1]
  have : (0 : ℝ) < 1 + x ^ 3 := by positivity
  field_simp
  ring

/-- The scalar assembly: the balance applied to the `log 2`-scaled quantities, then divided by
`log 2`. Here `L` stands for `log 2`, `mI`, `cH`, `S`, `J`, `B2`, `M`, `U` for the bit-valued
quantities, `a`, `b`, `wt` for the row means and the weight, and `K`, `κ` for the band and
replica constants. -/
private theorem aux_balance_assembly {L mI cH S J B2 M U a b wt ε q P Q r K κ A : ℝ} (hL : 0 < L)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hεq : ε < q) (hq1 : q < 1 - ε)
    (ha1 : ε ≤ a) (ha2 : a ≤ q) (hb1 : ε ≤ b) (hb2 : b ≤ q)
    (hw0 : 0 < wt) (hw1 : wt < 1)
    (hP : klBer (1 - q) ε / (1 - q - ε) ^ 2 ≤ P)
    (hQ : Real.binEntropy ε / (ε * (1 - ε)) ≤ Q)
    (hr : r ≤ K) (hr0 : 0 < r) (hE : 0 < Q - 2 * r)
    (hA : 1 ≤ A) (hκ : κ ≤ A / (1 + A) ^ 2)
    (hRep : J + B2 ≤ S) (hI : mI ≤ S + M) (hH : cH ≤ S + U - 2 * J)
    (hMeq : L * M = Real.binEntropy ((1 - wt) * a + wt * (1 - b)) -
      ((1 - wt) * Real.binEntropy a + wt * Real.binEntropy (1 - b)))
    (hUeq : L * U = (1 - wt) * Real.binEntropy a + wt * Real.binEntropy (1 - b))
    (hJ : K * withinVariance a b wt ≤ L * J)
    (hB : 2 * (1 - κ) ^ 2 * (betweenVariance a b wt * withinVariance a b wt /
        (betweenVariance a b wt + withinVariance a b wt)) ≤ L * B2) :
    min mI cH ≤ balanceCoeff P Q r (2 * (1 - A / (1 + A) ^ 2) ^ 2) * S := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have ha1' : a < 1 := by linarith
  have hb1' : b < 1 := by linarith
  have hv : 0 < withinVariance a b wt := by
    unfold withinVariance
    exact add_pos (mul_pos (mul_pos (by linarith) ha0) (by linarith))
      (mul_pos (mul_pos hw0 hb0) (by linarith))
  have hu : 0 ≤ betweenVariance a b wt := by
    unfold betweenVariance
    exact mul_nonneg (mul_nonneg hw0.le (by linarith)) (sq_nonneg _)
  have hP0 : 0 < P := by
    have hd : 0 < 1 - q - ε := by linarith
    have h2 := klBer_ge_two_sq (q := 1 - q) (r := ε) (by linarith) (by linarith) hε (by linarith)
    have h3 : 2 ≤ klBer (1 - q) ε / (1 - q - ε) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hd 2)]
      linarith
    linarith
  have hσ : 0 ≤ 2 * (1 - A / (1 + A) ^ 2) ^ 2 := by positivity
  have hκA : A / (1 + A) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (A - 1)]
  -- The seven hypotheses of the balance, on the `L`-scaled quantities.
  have hS' : L * J + L * B2 ≤ L * S := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hRep hL.le
  have hI' : L * mI ≤ L * S + L * M := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hI hL.le
  have hH' : L * cH ≤ L * S + L * U - 2 * (L * J) := by
    refine (mul_le_mul_of_nonneg_left hH hL.le).trans (le_of_eq ?_)
    ring
  have hM' : L * M ≤ P * betweenVariance a b wt := by
    have hJen := binEntropy_jensenGap_le (r₀ := a) (r₁ := 1 - b) (w := wt) hε hεq hq1
      ⟨ha1, ha2⟩ ⟨by linarith, by linarith⟩ hw0.le hw1.le
    have hu_eq : wt * (1 - wt) * (1 - b - a) ^ 2 = betweenVariance a b wt := by
      unfold betweenVariance
      ring
    rw [hu_eq] at hJen
    have := mul_le_mul_of_nonneg_right hP hu
    rw [hMeq]
    linarith
  have hU' : L * U ≤ Q * withinVariance a b wt := by
    have hEa := binEntropy_le_mul_of_mem hε hε2 ha1 (by linarith : a ≤ 1 - ε)
    have hEb := binEntropy_le_mul_of_mem hε hε2 (by linarith : ε ≤ 1 - b)
      (by linarith : 1 - b ≤ 1 - ε)
    have hva : 0 ≤ a * (1 - a) := mul_nonneg ha0.le (by linarith)
    have hvb : 0 ≤ (1 - b) * (1 - (1 - b)) := mul_nonneg (by linarith) (by linarith)
    have hEa' := hEa.trans (mul_le_mul_of_nonneg_right hQ hva)
    have hEb' := hEb.trans (mul_le_mul_of_nonneg_right hQ hvb)
    have e1 := mul_le_mul_of_nonneg_left hEa' (by linarith : (0 : ℝ) ≤ 1 - wt)
    have e2 := mul_le_mul_of_nonneg_left hEb' hw0.le
    have hvb_eq : (1 - b) * (1 - (1 - b)) = b * (1 - b) := by ring
    rw [hvb_eq] at e2
    rw [hUeq]
    unfold withinVariance
    calc (1 - wt) * Real.binEntropy a + wt * Real.binEntropy (1 - b)
        ≤ (1 - wt) * (Q * (a * (1 - a))) + wt * (Q * (b * (1 - b))) := add_le_add e1 e2
      _ = Q * ((1 - wt) * a * (1 - a) + wt * b * (1 - b)) := by ring
  have hJ' : r * withinVariance a b wt ≤ L * J :=
    (mul_le_mul_of_nonneg_right hr hv.le).trans hJ
  have hB' : 2 * (1 - A / (1 + A) ^ 2) ^ 2 *
      (betweenVariance a b wt * withinVariance a b wt /
        (betweenVariance a b wt + withinVariance a b wt)) ≤ L * B2 := by
    have hX : 0 ≤ betweenVariance a b wt * withinVariance a b wt /
        (betweenVariance a b wt + withinVariance a b wt) :=
      div_nonneg (mul_nonneg hu hv.le) (by linarith)
    have hsq : (1 - A / (1 + A) ^ 2) ^ 2 ≤ (1 - κ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    refine le_trans ?_ hB
    exact mul_le_mul_of_nonneg_right (by linarith) hX
  have key := twoCode_balance hv hu hP0 hr0 hσ hE hS' hI' hH' hM' hU' hJ' hB'
  rcases le_total mI cH with h | h
  · rw [min_eq_left h]
    rw [min_eq_left (mul_le_mul_of_nonneg_left h hL.le)] at key
    have k2 : L * mI ≤ L * (balanceCoeff P Q r (2 * (1 - A / (1 + A) ^ 2) ^ 2) * S) :=
      key.trans (le_of_eq (by ring))
    exact le_of_mul_le_mul_left k2 hL
  · rw [min_eq_right h]
    rw [min_eq_right (mul_le_mul_of_nonneg_left h hL.le)] at key
    have k2 : L * cH ≤ L * (balanceCoeff P Q r (2 * (1 - A / (1 + A) ^ 2) ^ 2) * S) :=
      key.trans (le_of_eq (by ring))
    exact le_of_mul_le_mul_left k2 hL

/-- The moderate-separation bound for one band: for a two-contact latent with row parameters
`0 < s < t`, positive priors and `1 ≤ A ≤ t/s ≤ B`, and band constants `P`, `Q`, `r` bounding
`klBer (1 - q) ε/(1 - q - ε)²`, `h(ε)/(ε(1 - ε))` and `κ(B) · owL (min q (1/2))` with
`0 < r` and `2r < Q`, `min (I(X; Y), H(X | Y)) ≤ balanceCoeff P Q r (2 (1 - κ(A))²) · score`,
in bits. -/
theorem twoContact_min_le_balanceCoeff {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s < t) (hpos : ∀ v, 0 < V.prior v) {A B P Q r : ℝ} (hA : 1 ≤ A) (hAk : A ≤ t / s)
    (hkB : t / s ≤ B)
    (hP : klBer (1 - (A + 1) / (A ^ 2 + A + 1)) (1 / (B ^ 2 + B + 1)) /
        (1 - (A + 1) / (A ^ 2 + A + 1) - 1 / (B ^ 2 + B + 1)) ^ 2 ≤ P)
    (hQ : Real.binEntropy (1 / (B ^ 2 + B + 1)) /
        (1 / (B ^ 2 + B + 1) * (1 - 1 / (B ^ 2 + B + 1))) ≤ Q)
    (hr : r ≤ B / (1 + B) ^ 2 * owL (min ((A + 1) / (A ^ 2 + A + 1)) (1 / 2)))
    (hr0 : 0 < r) (hE : 0 < Q - 2 * r) :
    min (mutualInfo Prod.fst Prod.snd p) (condEntropy Prod.fst Prod.snd p) ≤
      balanceCoeff P Q r (2 * (1 - A / (1 + A) ^ 2) ^ 2) * V.score := by
  have hs0 : 0 < s := hs.1
  have ht0 : 0 < t := hs0.trans hst
  have hk1 : 1 ≤ t / s := hA.trans hAk
  obtain ⟨hε, hε2, hεq, hq1⟩ := aux_band hA hs0 hst hAk hkB
  have hw0 := hpos (e.symm 1)
  have hw1 := bitLatent_prior_lt_one V e hpos 1
  have hp0 : V.prior (e.symm 0) = 1 - V.prior (e.symm 1) := by
    linarith [bitLatent_prior_sum V e]
  have hm1 := aux_rowMass_one ht
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ :=
    twoContact_rowMass_mem_band V e hw h0 h1 hs ht hst hA hAk hkB
  have hMeq := bitLatent_log_two_mul_mutualInfo_label_row V e
  have hUeq := bitLatent_log_two_mul_condEntropy_row V e
  simp only [Fin.sum_univ_two] at hMeq hUeq
  rw [hm1, hp0] at hMeq
  rw [hm1, hp0] at hUeq
  have hBrep := twoContact_replica_info_ge V e hw h0 h1 hs ht hs0 hst hpos
  have hκ : s * t / (s + t) ^ 2 ≤ A / (1 + A) ^ 2 := by
    rw [mul_div_add_sq_eq hs0 ht0]
    exact kappa_antitoneOn hA hk1 hAk
  exact aux_balance_assembly (Real.log_pos one_lt_two) hε hε2 hεq hq1 ha1 ha2 hb1 hb2 hw0 hw1
    hP hQ hr hr0
    hE hA hκ (latent_replica_bound V) (mutualInfo_le_score_add V) (condEntropy_le_score_add V)
    hMeq hUeq
    (twoContact_condMutualInfo_ge_band V e hw h0 h1 hs ht hst hpos hA hAk hkB) hBrep

end

end BinaryRow

end StochasticToDeterministicLatents
