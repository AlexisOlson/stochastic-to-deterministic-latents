import StochasticToDeterministicLatents.BinaryRow.ModerateSeparation
import StochasticToDeterministicLatents.BinaryRow.BandConstants

/-!
# Moderate separation: six bands reach 27/4

For a two-contact latent `V` on `Bit × Y` with row parameters `0 < s < t`, positive
priors and `t/s ≤ 16`,
`min (I(X; Y), H(X | Y)) ≤ (27/4) · score(V)` (`twoContact_min_le_twentySevenQuarters`).
Both sides are in bits.

Since `1 ≤ t/s`, the ratio lies in one of the closed bands `[1, 4]`, `[4, 8]`, `[8, 12]`,
`[12, 14]`, `[14, 76/5]` and `[76/5, 16]`. On each, `twoContact_min_le_balanceCoeff` applies
with the rational constants of `constants_band_*`, where `ε = 1/(B² + B + 1)` and
`q = (A + 1)/(A² + A + 1)` are rewritten to reduced fractions and
`σ = 2 (1 - A/(1 + A)²)²` is evaluated exactly; `balanceCoeff_bands_le` bounds each
coefficient by `27/4`, and `Latent.score_nonneg` closes the step. The coefficient `27/4`
comes from these coarse rational constants and is not the band relaxation's exact maximum.

## Attribution

Original to this repository, on the latent interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- Scalar closing step: `m ≤ c S`, `c ≤ 27/4` and `0 ≤ S` give `m ≤ (27/4) S`. -/
private theorem aux_finish {m c S : ℝ} (h : m ≤ c * S) (hc : c ≤ 27 / 4) (hS : 0 ≤ S) :
    m ≤ 27 / 4 * S :=
  h.trans (mul_le_mul_of_nonneg_right hc hS)

/-- One band: `twoContact_min_le_balanceCoeff` with the band's σ rewritten to a rational and its
coefficient bounded by `27/4`. -/
private theorem aux_band_bound {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s < t) (hpos : ∀ v, 0 < V.prior v) {A B P Q r σ : ℝ} (hA : 1 ≤ A) (hAk : A ≤ t / s)
    (hkB : t / s ≤ B)
    (hP : klBer (1 - (A + 1) / (A ^ 2 + A + 1)) (1 / (B ^ 2 + B + 1)) /
        (1 - (A + 1) / (A ^ 2 + A + 1) - 1 / (B ^ 2 + B + 1)) ^ 2 ≤ P)
    (hQ : Real.binEntropy (1 / (B ^ 2 + B + 1)) /
        (1 / (B ^ 2 + B + 1) * (1 - 1 / (B ^ 2 + B + 1))) ≤ Q)
    (hr : r ≤ B / (1 + B) ^ 2 * owL (min ((A + 1) / (A ^ 2 + A + 1)) (1 / 2)))
    (hr0 : 0 < r) (hE : 0 < Q - 2 * r) (hσ : 2 * (1 - A / (1 + A) ^ 2) ^ 2 = σ)
    (hc : balanceCoeff P Q r σ ≤ 27 / 4) :
    min (mutualInfo Prod.fst Prod.snd p) (condEntropy Prod.fst Prod.snd p) ≤ 27 / 4 * V.score := by
  have hb := twoContact_min_le_balanceCoeff V e hw h0 h1 hs ht hst hpos hA hAk hkB hP hQ hr hr0 hE
  rw [hσ] at hb
  exact aux_finish hb hc V.score_nonneg

/-- Moderate separation: for a two-contact latent with row parameters `0 < s < t`, positive priors
and `t/s ≤ 16`, `min (I(X; Y), H(X | Y)) ≤ (27/4) · score`. -/
theorem twoContact_min_le_twentySevenQuarters {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s < t) (hpos : ∀ v, 0 < V.prior v) (hk : t / s ≤ 16) :
    min (mutualInfo Prod.fst Prod.snd p) (condEntropy Prod.fst Prod.snd p) ≤ 27 / 4 * V.score := by
  have hs0 : 0 < s := hs.1
  have hk1 : (1 : ℝ) ≤ t / s := ((one_lt_div hs0).mpr hst).le
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := balanceCoeff_bands_le
  rcases le_total (t / s) 4 with h4 | h4
  · exact aux_band_bound V e hw h0 h1 hs ht hst hpos (A := 1) (B := 4) (by norm_num) hk1 h4
      (by
        rw [show ((1 : ℝ) + 1) / (1 ^ 2 + 1 + 1) = 2 / 3 by norm_num,
          show (1 : ℝ) / (4 ^ 2 + 4 + 1) = 1 / 21 by norm_num]
        exact constants_band_1_4.1)
      (by
        rw [show (1 : ℝ) / (4 ^ 2 + 4 + 1) = 1 / 21 by norm_num]
        exact constants_band_1_4.2.1)
      (by
        rw [show ((1 : ℝ) + 1) / (1 ^ 2 + 1 + 1) = 2 / 3 by norm_num]
        exact constants_band_1_4.2.2)
      (by norm_num) (by norm_num) (by norm_num) c1
  rcases le_total (t / s) 8 with h8 | h8
  · exact aux_band_bound V e hw h0 h1 hs ht hst hpos (A := 4) (B := 8) (by norm_num) h4 h8
      (by
        rw [show ((4 : ℝ) + 1) / (4 ^ 2 + 4 + 1) = 5 / 21 by norm_num,
          show (1 : ℝ) / (8 ^ 2 + 8 + 1) = 1 / 73 by norm_num]
        exact constants_band_4_8.1)
      (by
        rw [show (1 : ℝ) / (8 ^ 2 + 8 + 1) = 1 / 73 by norm_num]
        exact constants_band_4_8.2.1)
      (by
        rw [show ((4 : ℝ) + 1) / (4 ^ 2 + 4 + 1) = 5 / 21 by norm_num]
        exact constants_band_4_8.2.2)
      (by norm_num) (by norm_num) (by norm_num) c2
  rcases le_total (t / s) 12 with h12 | h12
  · exact aux_band_bound V e hw h0 h1 hs ht hst hpos (A := 8) (B := 12) (by norm_num) h8 h12
      (by
        rw [show ((8 : ℝ) + 1) / (8 ^ 2 + 8 + 1) = 9 / 73 by norm_num,
          show (1 : ℝ) / (12 ^ 2 + 12 + 1) = 1 / 157 by norm_num]
        exact constants_band_8_12.1)
      (by
        rw [show (1 : ℝ) / (12 ^ 2 + 12 + 1) = 1 / 157 by norm_num]
        exact constants_band_8_12.2.1)
      (by
        rw [show ((8 : ℝ) + 1) / (8 ^ 2 + 8 + 1) = 9 / 73 by norm_num]
        exact constants_band_8_12.2.2)
      (by norm_num) (by norm_num) (by norm_num) c3
  rcases le_total (t / s) 14 with h14 | h14
  · exact aux_band_bound V e hw h0 h1 hs ht hst hpos (A := 12) (B := 14) (by norm_num) h12 h14
      (by
        rw [show ((12 : ℝ) + 1) / (12 ^ 2 + 12 + 1) = 13 / 157 by norm_num,
          show (1 : ℝ) / (14 ^ 2 + 14 + 1) = 1 / 211 by norm_num]
        exact constants_band_12_14.1)
      (by
        rw [show (1 : ℝ) / (14 ^ 2 + 14 + 1) = 1 / 211 by norm_num]
        exact constants_band_12_14.2.1)
      (by
        rw [show ((12 : ℝ) + 1) / (12 ^ 2 + 12 + 1) = 13 / 157 by norm_num]
        exact constants_band_12_14.2.2)
      (by norm_num) (by norm_num) (by norm_num) c4
  rcases le_total (t / s) (76 / 5) with h765 | h765
  · exact aux_band_bound V e hw h0 h1 hs ht hst hpos (A := 14) (B := 76 / 5) (by norm_num) h14 h765
      (by
        rw [show ((14 : ℝ) + 1) / (14 ^ 2 + 14 + 1) = 15 / 211 by norm_num,
          show (1 : ℝ) / ((76 / 5) ^ 2 + 76 / 5 + 1) = 25 / 6181 by norm_num]
        exact constants_band_14_76_5.1)
      (by
        rw [show (1 : ℝ) / ((76 / 5) ^ 2 + 76 / 5 + 1) = 25 / 6181 by norm_num]
        exact constants_band_14_76_5.2.1)
      (by
        rw [show ((14 : ℝ) + 1) / (14 ^ 2 + 14 + 1) = 15 / 211 by norm_num]
        exact constants_band_14_76_5.2.2)
      (by norm_num) (by norm_num) (by norm_num) c5
  · exact aux_band_bound V e hw h0 h1 hs ht hst hpos (A := 76 / 5) (B := 16) (by norm_num) h765 hk
      (by
        rw [show ((76 / 5 : ℝ) + 1) / ((76 / 5) ^ 2 + 76 / 5 + 1) = 405 / 6181 by norm_num,
          show (1 : ℝ) / (16 ^ 2 + 16 + 1) = 1 / 273 by norm_num]
        exact constants_band_76_5_16.1)
      (by
        rw [show (1 : ℝ) / (16 ^ 2 + 16 + 1) = 1 / 273 by norm_num]
        exact constants_band_76_5_16.2.1)
      (by
        rw [show ((76 / 5 : ℝ) + 1) / ((76 / 5) ^ 2 + 76 / 5 + 1) = 405 / 6181 by norm_num]
        exact constants_band_76_5_16.2.2)
      (by norm_num) (by norm_num) (by norm_num) c6

end

end BinaryRow

end StochasticToDeterministicLatents
