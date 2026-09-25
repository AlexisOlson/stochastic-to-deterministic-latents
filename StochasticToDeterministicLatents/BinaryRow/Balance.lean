import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The variance split and the balance coefficient

For a two-component mixture on a binary row, where the component `W = 1` has weight `w`,
`P(X = 1 | W = 0) = a` and `P(X = 0 | W = 1) = b`, this module defines the row-one mass `π`
(`mixtureMean`), the between-component variance `u = w (1 - w) (1 - a - b)²`
(`betweenVariance`) and the within-component variance `v = (1 - w) a (1 - a) + w b (1 - b)`
(`withinVariance`). It proves the law of total variance `π (1 - π) = u + v`
(`mixture_variance_split`) and the Bayes identity `E[α_X (1 - α_X)] = w (1 - w) v / (u + v)` for
`α_x = P(W = 1 | X = x)` (`posterior_label_variance`).

It then gives a scalar maximization (`scalar_balance`) and, from it, a bound on the smaller of two
code costs by the balance coefficient `c = 1 + E (P + E) / (r (P + E) + σ E)`, where
`E = Q - 2r`, times the score (`twoCode_balance`). Last, `balanceCoeff_bands_le` checks
`c ≤ 27/4` for six rational constant sets.

Everything here is real algebra with no information quantity and no units. `twoCode_balance` is
linear in its information-valued arguments, so natural-log constants meet bit-valued quantities by
applying it to the quantities multiplied by `Real.log 2`.

## Attribution

Original to this repository.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

/-- `P(X = 1) = (1 - w) a + w (1 - b)` for a mixture with `P(X = 1 | W = 0) = a`,
`P(X = 0 | W = 1) = b` and `P(W = 1) = w`. -/
def mixtureMean (a b w : ℝ) : ℝ := (1 - w) * a + w * (1 - b)

/-- The between-component variance `u = w (1 - w) (1 - a - b)²`. -/
def betweenVariance (a b w : ℝ) : ℝ := w * (1 - w) * (1 - a - b) ^ 2

/-- The within-component variance `v = (1 - w) a (1 - a) + w b (1 - b)`. -/
def withinVariance (a b w : ℝ) : ℝ := (1 - w) * a * (1 - a) + w * b * (1 - b)

/-- The balance coefficient `1 + E (P + E) / (r (P + E) + σ E)` with `E = Q - 2r`. -/
def balanceCoeff (P Q r σ : ℝ) : ℝ :=
  1 + (Q - 2 * r) * (P + (Q - 2 * r)) / (r * (P + (Q - 2 * r)) + σ * (Q - 2 * r))

/-- The law of total variance for the mixture: `π (1 - π) = u + v`. -/
theorem mixture_variance_split (a b w : ℝ) :
    mixtureMean a b w * (1 - mixtureMean a b w) = betweenVariance a b w + withinVariance a b w := by
  unfold mixtureMean betweenVariance withinVariance
  ring

/-- With `α₁ = w (1 - b) / π` and `α₀ = w b / (1 - π)`, the posteriors `P(W = 1 | X = 1)` and
`P(W = 1 | X = 0)`, the expected posterior variance `E[α_X (1 - α_X)]` equals
`w (1 - w) v / (u + v)`. -/
theorem posterior_label_variance {a b w : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1)
    (hw0 : 0 < w) (hw1 : w < 1) :
    mixtureMean a b w * (w * (1 - b) / mixtureMean a b w * (1 - w * (1 - b) / mixtureMean a b w))
        + (1 - mixtureMean a b w) *
          (w * b / (1 - mixtureMean a b w) * (1 - w * b / (1 - mixtureMean a b w))) =
      w * (1 - w) * withinVariance a b w / (betweenVariance a b w + withinVariance a b w) := by
  have hp : 0 < mixtureMean a b w := by
    unfold mixtureMean
    nlinarith [mul_pos (sub_pos.2 hw1) ha, mul_pos hw0 (show (0 : ℝ) < 1 - b by linarith)]
  have hq : 0 < 1 - mixtureMean a b w := by
    unfold mixtureMean
    nlinarith [mul_pos (sub_pos.2 hw1) (show (0 : ℝ) < 1 - a by linarith), mul_pos hw0 hb]
  rw [← mixture_variance_split]
  field_simp
  unfold mixtureMean withinVariance
  ring

/-- The scalar balance: for `x ≥ 0`,
`min (P x) E ≤ E (P + E) / (r (P + E) + σ E) · (r + σ x / (1 + x))`. -/
theorem scalar_balance {P E r σ x : ℝ} (hP : 0 < P) (hE : 0 < E) (hr : 0 < r) (hσ : 0 ≤ σ)
    (hx : 0 ≤ x) :
    min (P * x) E ≤ E * (P + E) / (r * (P + E) + σ * E) * (r + σ * x / (1 + x)) := by
  have hD : 0 < r * (P + E) + σ * E := by positivity
  have h1x : 0 < 1 + x := by linarith
  have key : E * (P + E) / (r * (P + E) + σ * E) * (r + σ * x / (1 + x)) =
      E * (P + E) * (r * (1 + x) + σ * x) / ((r * (P + E) + σ * E) * (1 + x)) := by
    field_simp
  rw [key, le_div_iff₀ (by positivity)]
  rcases le_total (P * x) E with h | h
  · refine (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans ?_
    have h0 : 0 ≤ E - P * x := by linarith
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hr.le (by linarith : (0 : ℝ) ≤ P + E))
      h1x.le) h0, mul_nonneg (mul_nonneg (mul_nonneg hσ hx) hE.le) h0]
  · refine (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans ?_
    have h0 : 0 ≤ P * x - E := by linarith
    nlinarith [mul_nonneg (mul_nonneg hE.le hσ) h0]

/-- The two-code balance: from the replica bound `J + B2 ≤ S`, the two code interfaces
`I ≤ S + M` and `H ≤ S + U - 2J`, and the four uniform bounds `M ≤ P u`, `U ≤ Q v`, `r v ≤ J` and
`σ u v / (u + v) ≤ B2`, the smaller of the two code costs is at most `balanceCoeff P Q r σ · S`. -/
theorem twoCode_balance {I H S J B2 M U u v P Q r σ : ℝ} (hv : 0 < v) (hu : 0 ≤ u)
    (hP : 0 < P) (hr : 0 < r) (hσ : 0 ≤ σ) (hE : 0 < Q - 2 * r)
    (hS : J + B2 ≤ S) (hI : I ≤ S + M) (hH : H ≤ S + U - 2 * J)
    (hM : M ≤ P * u) (hU : U ≤ Q * v) (hJ : r * v ≤ J) (hB : σ * (u * v / (u + v)) ≤ B2) :
    min I H ≤ balanceCoeff P Q r σ * S := by
  have hx := scalar_balance hP hE hr hσ (div_nonneg hu hv.le)
  unfold balanceCoeff
  set c := (Q - 2 * r) * (P + (Q - 2 * r)) / (r * (P + (Q - 2 * r)) + σ * (Q - 2 * r)) with hc
  have hc0 : 0 ≤ c :=
    div_nonneg (mul_nonneg hE.le (by linarith))
      (add_nonneg (mul_nonneg hr.le (by linarith)) (mul_nonneg hσ hE.le))
  have huv : 0 < u + v := by linarith
  have e1 : min (P * u) ((Q - 2 * r) * v) ≤ v * min (P * (u / v)) (Q - 2 * r) := by
    rcases le_total (P * (u / v)) (Q - 2 * r) with h | h
    · rw [min_eq_left h]
      have : P * u = v * (P * (u / v)) := by field_simp
      exact (min_le_left _ _).trans this.le
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (le_of_eq (mul_comm _ _))
  have e2 : v * (c * (r + σ * (u / v) / (1 + u / v))) = c * (r * v + σ * (u * v / (u + v))) := by
    field_simp
    ring
  have key : min (P * u) ((Q - 2 * r) * v) ≤ c * (r * v + σ * (u * v / (u + v))) := by
    rw [← e2]
    exact e1.trans (mul_le_mul_of_nonneg_left hx hv.le)
  have hcS : c * (r * v + σ * (u * v / (u + v))) ≤ c * S :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have hmin : min I H ≤ S + min (P * u) ((Q - 2 * r) * v) := by
    rcases le_total (P * u) ((Q - 2 * r) * v) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith)
  linarith

/-- For the six rational constant sets used on the separation bands `[1, 4]`, `[4, 8]`, `[8, 12]`,
`[12, 14]`, `[14, 76/5]` and `[76/5, 16]`, in that order, the balance coefficient is at most
`27/4`. -/
theorem balanceCoeff_bands_le :
    balanceCoeff (503296 / 100000) (422135 / 100000) (32000 / 100000) (9 / 8) ≤ 27 / 4 ∧
    balanceCoeff (486473 / 100000) (535697 / 100000) (21931 / 100000) (882 / 625) ≤ 27 / 4 ∧
    balanceCoeff (536008 / 100000) (609186 / 100000) (18487 / 100000) (10658 / 6561) ≤ 27 / 4 ∧
    balanceCoeff (555328 / 100000) (637973 / 100000) (17933 / 100000) (49298 / 28561) ≤ 27 / 4 ∧
    balanceCoeff (568460 / 100000) (653477 / 100000) (17352 / 100000) (89042 / 50625) ≤ 27 / 4 ∧
    balanceCoeff (577122 / 100000) (663194 / 100000) (16932 / 100000) (76409522 / 43046721) ≤
      27 / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold balanceCoeff; norm_num)

end

end BinaryRow

end StochasticToDeterministicLatents
