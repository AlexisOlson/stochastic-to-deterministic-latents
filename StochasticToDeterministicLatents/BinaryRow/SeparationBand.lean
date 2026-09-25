import StochasticToDeterministicLatents.BinaryRow.ComponentInfo
import StochasticToDeterministicLatents.BinaryRow.Balance

/-!
# Separation bands for a two-contact row

A separation band is `1 ≤ A ≤ k ≤ B` for the ratio `k = t/s` of the two row parameters
`0 < s < t`. Its constants are `ε = 1/(B² + B + 1)`, `q = (A + 1)/(A² + A + 1)` and
`κ(x) = x/(1 + x)²`.

Scalar facts: `st/(s + t)² = κ(t/s)`; `κ` is antitone on `[1, ∞)`; `x ↦ (x + 1)/(x² + x + 1)`
is antitone on `[0, ∞)`; and on `(0, q]` with `q < 1`, `owL` is at least `owL (min q (1/2))`.

For a two-contact latent whose component parameters `s < t` lie in a band, the row means
`a = P(X = 1 | W = 0)` and `b = P(X = 0 | W = 1)` lie in `[ε, q]`
(`twoContact_rowMass_mem_band`). With `w = P(W = 1)`, positive priors and
`v = (1 - w) a (1 - a) + w b (1 - b)`,
`κ(B) · owL (min q (1/2)) · v ≤ log 2 · I(X; Y | W)` (`twoContact_condMutualInfo_ge_band`).
The left side is in nats; the right side is `log 2` times the conditional mutual information
in bits.

## Attribution

Original to this repository, on the latent interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

/-- `st/(s+t)² = κ(t/s)` with `κ(x) = x/(1 + x)²`. -/
theorem mul_div_add_sq_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    s * t / (s + t) ^ 2 = t / s / (1 + t / s) ^ 2 := by
  have hst : 0 < s + t := by linarith
  field_simp

/-- `κ(x) = x/(1 + x)²` is antitone on `[1, ∞)`. -/
theorem kappa_antitoneOn : AntitoneOn (fun x : ℝ => x / (1 + x) ^ 2) (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  show y / (1 + y) ^ 2 ≤ x / (1 + x) ^ 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hxy1 : 0 ≤ x * y - 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) hxy1]

/-- `x ↦ (x + 1)/(x² + x + 1)` is antitone on `[0, ∞)`. -/
theorem bandUpper_antitoneOn :
    AntitoneOn (fun x : ℝ => (x + 1) / (x ^ 2 + x + 1)) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  show (y + 1) / (y ^ 2 + y + 1) ≤ (x + 1) / (x ^ 2 + x + 1)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hp : 0 ≤ x * y + x + y := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) hp]

/-- On `(0, q]` with `q < 1`, the Ordentlich–Weinberger coefficient is at least its value at
`min q (1/2)`. -/
theorem owL_min_le {q x : ℝ} (hx0 : 0 < x) (hxq : x ≤ q) (hq1 : q < 1) :
    owL (min q (1 / 2)) ≤ owL x := by
  rcases le_or_gt x (1 / 2) with hx | hx
  · have hm0 : 0 < min q (1 / 2) := lt_min (by linarith) (by norm_num)
    exact owL_antitoneOn ⟨hx0, hx⟩ ⟨hm0, min_le_right _ _⟩ (le_min hxq hx)
  · rw [min_eq_right (by linarith), owL_half]
    exact two_le_owL hx0 (by linarith)

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- In a separation band `1 ≤ A ≤ t/s ≤ B`, the two-contact row means
`a = rowMass (comp 0) 1` and `b = rowMass (comp 1) 0` lie in
`[1/(B² + B + 1), (A + 1)/(A² + A + 1)]`. -/
theorem twoContact_rowMass_mem_band {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s < t) {A B : ℝ} (hA : 1 ≤ A) (hAk : A ≤ t / s) (hkB : t / s ≤ B) :
    (1 / (B ^ 2 + B + 1) ≤ rowMass (V.comp (e.symm 0)) 1 ∧
      rowMass (V.comp (e.symm 0)) 1 ≤ (A + 1) / (A ^ 2 + A + 1)) ∧
    (1 / (B ^ 2 + B + 1) ≤ rowMass (V.comp (e.symm 1)) 0 ∧
      rowMass (V.comp (e.symm 1)) 0 ≤ (A + 1) / (A ^ 2 + A + 1)) := by
  have hs0 : 0 < s := hs.1
  have ht0 : 0 < t := ht.1
  have hne : V.comp (e.symm 0) ≠ V.comp (e.symm 1) := ne_of_rowCubeParam_ne hs ht hst.ne
  obtain ⟨hi1, hi2⟩ := rowTwoContact_param_ineq hw h0 h1 hne hs ht
  obtain ⟨ha1, ha2⟩ := twoContact_a_mem hs0 ht0 hi1 hi2
  obtain ⟨hb1, hb2⟩ := twoContact_b_mem hs0 ht0 hi1 hi2
  have hk1 : 1 ≤ t / s := le_trans hA hAk
  have hlow : 1 / (B ^ 2 + B + 1) ≤ 1 / ((t / s) ^ 2 + t / s + 1) :=
    one_div_le_one_div_of_le (by positivity)
      (by nlinarith [mul_le_mul hkB hkB (by linarith) (by linarith)])
  have hup : (t / s + 1) / ((t / s) ^ 2 + t / s + 1) ≤ (A + 1) / (A ^ 2 + A + 1) :=
    bandUpper_antitoneOn (show A ∈ Set.Ici (0 : ℝ) from le_trans zero_le_one hA)
      (show t / s ∈ Set.Ici (0 : ℝ) from le_trans zero_le_one hk1) hAk
  rw [hs.2.2, ht.2.1]
  exact ⟨⟨hlow.trans ha1.le, ha2.le.trans hup⟩, ⟨hlow.trans hb1.le, hb2.le.trans hup⟩⟩

/-- The band lower bound on the component information: in a separation band,
`κ(B) · owL (min q (1/2)) · v ≤ log 2 · I(X; Y | W)`, with `q = (A + 1)/(A² + A + 1)` and
`v = withinVariance a b w` for `a = rowMass (comp 0) 1`, `b = rowMass (comp 1) 0`, `w = prior 1`;
nats on the left, `log 2` times bits on the right. -/
theorem twoContact_condMutualInfo_ge_band {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s < t) (hpos : ∀ v, 0 < V.prior v) {A B : ℝ} (hA : 1 ≤ A) (hAk : A ≤ t / s)
    (hkB : t / s ≤ B) :
    B / (1 + B) ^ 2 * owL (min ((A + 1) / (A ^ 2 + A + 1)) (1 / 2)) *
        withinVariance (rowMass (V.comp (e.symm 0)) 1) (rowMass (V.comp (e.symm 1)) 0)
          (V.prior (e.symm 1)) ≤
      Real.log 2 *
        condMutualInfo (fun a : V.ι × (Bit × Y) => a.2.1) (fun a => a.2.2) (fun a => a.1)
          V.joint := by
  have hs0 : 0 < s := hs.1
  have ht0 : 0 < t := ht.1
  have base := twoContact_condMutualInfo_ge_owL V e hw h0 h1 hs ht hst.ne
  simp only [Fin.sum_univ_two] at base
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ :=
    twoContact_rowMass_mem_band V e hw h0 h1 hs ht hst hA hAk hkB
  have hm1 : rowMass (V.comp (e.symm 1)) 1 = 1 - rowMass (V.comp (e.symm 1)) 0 := by
    rw [ht.2.2, ht.2.1]
    have : (0 : ℝ) < 1 + t ^ 3 := by positivity
    field_simp
    ring
  have hp0 : V.prior (e.symm 0) = 1 - V.prior (e.symm 1) := by
    linarith [bitLatent_prior_sum V e]
  have hw1 := bitLatent_prior_lt_one V e hpos 1
  have hw0 := hpos (e.symm 1)
  rw [hm1, hp0] at base
  have hk1 : 1 ≤ t / s := le_trans hA hAk
  have hκ : B / (1 + B) ^ 2 ≤ s * t / (s + t) ^ 2 := by
    rw [mul_div_add_sq_eq hs0 ht0]
    exact kappa_antitoneOn (show t / s ∈ Set.Ici (1 : ℝ) from hk1)
      (show B ∈ Set.Ici (1 : ℝ) from le_trans hk1 hkB) hkB
  set a := rowMass (V.comp (e.symm 0)) 1 with ha_def
  set b := rowMass (V.comp (e.symm 1)) 0 with hb_def
  set v := V.prior (e.symm 1) with hv_def
  set q := (A + 1) / (A ^ 2 + A + 1) with hq_def
  have hB1 : 1 ≤ B := le_trans hk1 hkB
  have hε : 0 < 1 / (B ^ 2 + B + 1) := div_pos one_pos (by nlinarith)
  have ha0 : 0 < a := lt_of_lt_of_le hε ha1
  have hb0 : 0 < b := lt_of_lt_of_le hε hb1
  have hq0 : 0 < q := div_pos (by linarith) (by nlinarith)
  have hq1 : q < 1 := by
    rw [hq_def, div_lt_one (by nlinarith)]
    nlinarith
  have hb1' : b < 1 := lt_of_le_of_lt hb2 hq1
  rw [owL_symm hb0 hb1'] at base
  have hLa := owL_min_le ha0 ha2 hq1
  have hLb := owL_min_le hb0 hb2 hq1
  have hm0 : 0 < min q (1 / 2) := lt_min hq0 (by norm_num)
  have hL2 : 2 ≤ owL (min q (1 / 2)) :=
    two_le_owL hm0 (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  have hva : 0 ≤ a * (1 - a) := mul_nonneg ha0.le (by linarith)
  have hvb : 0 ≤ (1 - b) * (1 - (1 - b)) := mul_nonneg (by linarith) (by linarith)
  have hS : owL (min q (1 / 2)) * withinVariance a b v ≤
      (1 - v) * (owL a * (a * (1 - a))) + v * (owL b * ((1 - b) * (1 - (1 - b)))) := by
    have e1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLa hva)
      (show (0 : ℝ) ≤ 1 - v by linarith)
    have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLb hvb) hw0.le
    calc
      owL (min q (1 / 2)) * withinVariance a b v =
          (1 - v) * (owL (min q (1 / 2)) * (a * (1 - a))) +
            v * (owL (min q (1 / 2)) * ((1 - b) * (1 - (1 - b)))) := by
        unfold withinVariance
        ring
      _ ≤ _ := add_le_add e1 e2
  have hW : 0 ≤ owL (min q (1 / 2)) * withinVariance a b v := by
    unfold withinVariance
    have hv1 : (0 : ℝ) ≤ 1 - v := by linarith
    have hb1'' : (0 : ℝ) ≤ 1 - b := by linarith
    have ha1'' : (0 : ℝ) ≤ 1 - a := by linarith
    exact mul_nonneg (by linarith)
      (add_nonneg (mul_nonneg (mul_nonneg hv1 ha0.le) ha1'')
        (mul_nonneg (mul_nonneg hw0.le hb0.le) hb1''))
  have hκ0 : 0 ≤ s * t / (s + t) ^ 2 := by positivity
  calc
    B / (1 + B) ^ 2 * owL (min q (1 / 2)) * withinVariance a b v =
        B / (1 + B) ^ 2 * (owL (min q (1 / 2)) * withinVariance a b v) := by ring
    _ ≤ s * t / (s + t) ^ 2 *
        ((1 - v) * (owL a * (a * (1 - a))) + v * (owL b * ((1 - b) * (1 - (1 - b))))) :=
      mul_le_mul hκ hS hW hκ0
    _ ≤ _ := base

end

end BinaryRow

end StochasticToDeterministicLatents
