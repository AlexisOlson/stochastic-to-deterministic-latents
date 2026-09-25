import StochasticToDeterministicLatents.BinaryRow.ReplicaCells
import StochasticToDeterministicLatents.BinaryRow.ComponentInfo
import StochasticToDeterministicLatents.BinaryRow.Balance

/-!
# The replica information is at least a variance ratio

On `Bit × Y`, let the two components of a `Bit`-labelled latent be contacts of one feasible
kernel with row parameters `0 < s < t` and positive priors. Write `a = P(X = 1 | W = 0)`,
`b = P(X = 0 | W = 1)`, `w = P(W = 1)`, `κ = st/(s + t)²`, `u = w (1 - w) (1 - a - b)²` and
`v = (1 - w) a (1 - a) + w b (1 - b)`. With `X'` the row replica,

  `2 (1 - κ)² · u v / (u + v) ≤ log 2 · I(W; X' | X)` (`twoContact_replica_info_ge`).

The right side is the replica term of `latent_replica_bound`.

The proof writes `log 2 · I(W; X' | X)` as the sum over `x` and `w` of `P(W = w, X = x)` times
the Bernoulli divergence of `P(X' = 1 | w, x)` from `P(X' = 1 | x)`, and applies Pinsker's
inequality in each fibre. Given `X = x`, the two labels' conditional means of `X'` are `(1 - κ) r`
for `x = 0` and `r + κ (1 - r)` for `x = 1`, with `r` the label's row-one mass, so they differ by
`(1 - κ)(1 - a - b)` for either `x`. The weighted spread of two means is `S₀S₁/(S₀ + S₁)` times
their squared difference, and the law of total variance `π (1 - π) = u + v`
(`mixture_variance_split`) turns the sum over `x` into the left side exactly; Pinsker is the only
inequality. All eight replica cells are positive (`replicaCell_pos`), so no logarithm meets zero.

The left side and `klBer` are in nats; `I(W; X' | X)` is in bits, so `Real.log 2 · I` is its value
in nats.

## Attribution

Original to this repository, on the entropy interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

/-! ## Generic helpers: conditional mutual information in nats -/

/-- `log 2 · I(f; g | h)` as a signed sum of `negMulLog`s of the four pushforwards; the mass
terms cancel, so this holds for every nonnegative finite measure. -/
private theorem aux_log_two_mul_condMI {Ω A B C : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    Real.log 2 * stoch_to_det.condMI f g h m =
      ∑ p, Real.negMulLog (stoch_to_det.push (fun ω => (f ω, h ω)) m p)
        + ∑ p, Real.negMulLog (stoch_to_det.push (fun ω => (g ω, h ω)) m p)
        - ∑ p, Real.negMulLog (stoch_to_det.push (fun ω => (f ω, g ω, h ω)) m p)
        - ∑ p, Real.negMulLog (stoch_to_det.push h m p) := by
  have e1 := stoch_to_det.H_eq_negMulLog
    (stoch_to_det.isFinMeas_push (f := fun ω => (f ω, h ω)) (m := m) hm)
  have e2 := stoch_to_det.H_eq_negMulLog
    (stoch_to_det.isFinMeas_push (f := fun ω => (g ω, h ω)) (m := m) hm)
  have e3 := stoch_to_det.H_eq_negMulLog
    (stoch_to_det.isFinMeas_push (f := fun ω => (f ω, g ω, h ω)) (m := m) hm)
  have e4 := stoch_to_det.H_eq_negMulLog (stoch_to_det.isFinMeas_push (f := h) (m := m) hm)
  rw [stoch_to_det.mass_push] at e1 e2 e3 e4
  unfold stoch_to_det.condMI stoch_to_det.Hvar
  linear_combination e1 + e2 - e3 - e4

/-- Conditional mutual information of variables factoring through `φ` is conditional mutual
information under the pushforward along `φ`. -/
private theorem aux_condMI_push {Ω Ω' A B C : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (m : Ω → ℝ) (φ : Ω → Ω') (f : Ω' → A) (g : Ω' → B) (h : Ω' → C) :
    stoch_to_det.condMI (fun ω => f (φ ω)) (fun ω => g (φ ω)) (fun ω => h (φ ω)) m =
      stoch_to_det.condMI f g h (stoch_to_det.push φ m) := by
  unfold stoch_to_det.condMI stoch_to_det.Hvar
  rw [stoch_to_det.push_push, stoch_to_det.push_push, stoch_to_det.push_push,
    stoch_to_det.push_push]
  rfl

/-- The law of the first coordinate of an equivalence `e : Ω ≃ A × K` at `a` is the sum over the
second coordinate. -/
private theorem aux_push_fst_equiv {Ω A K : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype K] (e : Ω ≃ A × K) (m : Ω → ℝ) (a : A) :
    stoch_to_det.push (fun ω => (e ω).1) m a = ∑ k, m (e.symm (a, k)) := by
  unfold stoch_to_det.push
  rw [Finset.sum_filter, ← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- The pushforward along an equivalence is the measure composed with the inverse. -/
private theorem aux_push_equiv {Ω A : Type*} [Fintype Ω] [DecidableEq A] (e : Ω ≃ A) (m : Ω → ℝ)
    (a : A) : stoch_to_det.push (fun ω => e ω) m a = m (e.symm a) := by
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Finset.sum_eq_single (e.symm a)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (by rw [← h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Regroup `(W, (X, X'))` as `((W, X), X')`. -/
private def aux_E1 {I : Type*} : I × (Bit × Bit) ≃ (I × Bit) × Bit where
  toFun z := ((z.1, z.2.1), z.2.2)
  invFun p := (p.1.1, (p.1.2, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup `(W, (X, X'))` as `((X', X), W)`. -/
private def aux_E2 {I : Type*} : I × (Bit × Bit) ≃ (Bit × Bit) × I where
  toFun z := ((z.2.2, z.2.1), z.1)
  invFun p := (p.2, (p.1.2, p.1.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reorder `(W, (X, X'))` as `(W, (X', X))`. -/
private def aux_E3 {I : Type*} : I × (Bit × Bit) ≃ I × (Bit × Bit) where
  toFun z := (z.1, (z.2.2, z.2.1))
  invFun p := (p.1, (p.2.2, p.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup `(W, (X, X'))` as `(X, (W, X'))`. -/
private def aux_E4 {I : Type*} : I × (Bit × Bit) ≃ Bit × (I × Bit) where
  toFun z := (z.2.1, (z.1, z.2.2))
  invFun p := (p.2.1, (p.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- One column of the Bernoulli-average identity with positive cells `A`, `B` and `R ∈ (0, 1)`. -/
private theorem aux_col {A B R : ℝ} (hA : 0 < A) (hB : 0 < B) (hR0 : 0 < R) (hR1 : R < 1) :
    (A + B) * klBer (B / (A + B)) R =
      Real.negMulLog (A + B) - Real.negMulLog A - Real.negMulLog B - B * Real.log R
        - A * Real.log (1 - R) := by
  have hS : 0 < A + B := add_pos hA hB
  have h1R : 0 < 1 - R := by linarith
  have e1 : 1 - B / (A + B) = A / (A + B) := by
    rw [eq_div_iff hS.ne', sub_mul, div_mul_cancel₀ _ hS.ne']
    ring
  have lB : Real.log (B / (A + B) / R) = Real.log B - Real.log (A + B) - Real.log R := by
    rw [Real.log_div (div_pos hB hS).ne' hR0.ne', Real.log_div hB.ne' hS.ne']
  have lA : Real.log (A / (A + B) / (1 - R)) =
      Real.log A - Real.log (A + B) - Real.log (1 - R) := by
    rw [Real.log_div (div_pos hA hS).ne' h1R.ne', Real.log_div hA.ne' hS.ne']
  have hb' : (A + B) * (B / (A + B)) = B := by field_simp
  have ha' : (A + B) * (A / (A + B)) = A := by field_simp
  unfold klBer
  rw [e1, lB, lA]
  calc
    (A + B) * (B / (A + B) * (Real.log B - Real.log (A + B) - Real.log R) +
        A / (A + B) * (Real.log A - Real.log (A + B) - Real.log (1 - R))) =
        ((A + B) * (B / (A + B))) * (Real.log B - Real.log (A + B) - Real.log R) +
          ((A + B) * (A / (A + B))) * (Real.log A - Real.log (A + B) - Real.log (1 - R)) := by
      ring
    _ = _ := by
      rw [hb', ha']
      simp only [Real.negMulLog]
      ring

/-- One fibre of the conditioner: with positive cells `A i`, `B i`, the weighted Bernoulli
divergences from the pooled row-one mass are a signed sum of `negMulLog`s. -/
private theorem aux_fibre {I : Type*} [Fintype I] (A B : I → ℝ) (hA : ∀ i, 0 < A i)
    (hB : ∀ i, 0 < B i) :
    ∑ i, (A i + B i) * klBer (B i / (A i + B i)) ((∑ j, B j) / ∑ j, (A j + B j)) =
      ∑ i, Real.negMulLog (A i + B i) - ∑ i, Real.negMulLog (A i) - ∑ i, Real.negMulLog (B i)
        + Real.negMulLog (∑ i, B i) + Real.negMulLog (∑ i, A i)
        - Real.negMulLog (∑ i, (A i + B i)) := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i0⟩⟩
  · simp
  have hSA : 0 < ∑ i, A i := Finset.sum_pos (fun i _ => hA i) ⟨i0, Finset.mem_univ _⟩
  have hSB : 0 < ∑ i, B i := Finset.sum_pos (fun i _ => hB i) ⟨i0, Finset.mem_univ _⟩
  have hT : ∑ j, (A j + B j) = ∑ j, A j + ∑ j, B j := Finset.sum_add_distrib
  have hS : 0 < ∑ j, A j + ∑ j, B j := add_pos hSA hSB
  rw [hT]
  have hR0 : 0 < (∑ j, B j) / (∑ j, A j + ∑ j, B j) := div_pos hSB hS
  have hR1 : (∑ j, B j) / (∑ j, A j + ∑ j, B j) < 1 := by
    rw [div_lt_one hS]
    linarith
  rw [Finset.sum_congr rfl fun i _ => aux_col (hA i) (hB i) hR0 hR1]
  have h1R : 1 - (∑ j, B j) / (∑ j, A j + ∑ j, B j) = (∑ j, A j) / (∑ j, A j + ∑ j, B j) := by
    rw [eq_div_iff hS.ne', sub_mul, div_mul_cancel₀ _ hS.ne']
    ring
  rw [h1R, Real.log_div hSB.ne' hS.ne', Real.log_div hSA.ne' hS.ne']
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [Real.negMulLog]
  ring

/-- For a positive law `c` of `(W, (X, X'))` with `X, X'` bits, `log 2 · I(W; X' | X)` is the sum
over `x` and `w` of `P(W = w, X = x)` times the Bernoulli divergence of `P(X' = 1 | w, x)` from
`P(X' = 1 | x)`. -/
private theorem aux_log_two_condMI_eq {I : Type*} [Fintype I] [DecidableEq I]
    (c : I × (Bit × Bit) → ℝ)
    (hc : ∀ z, 0 < c z) :
    Real.log 2 *
        stoch_to_det.condMI (fun z : I × (Bit × Bit) => z.1) (fun z => z.2.2) (fun z => z.2.1) c =
      ∑ x : Bit, ∑ i, (c (i, (x, 0)) + c (i, (x, 1))) *
        klBer (c (i, (x, 1)) / (c (i, (x, 0)) + c (i, (x, 1))))
          ((∑ j, c (j, (x, 1))) / ∑ j, (c (j, (x, 0)) + c (j, (x, 1)))) := by
  rw [aux_log_two_mul_condMI (fun z => (hc z).le)]
  have e1 : ∀ p : I × Bit, stoch_to_det.push (fun a : I × (Bit × Bit) => (a.1, a.2.1)) c p =
      c (p.1, (p.2, 0)) + c (p.1, (p.2, 1)) := by
    intro p
    refine (aux_push_fst_equiv aux_E1 c p).trans ?_
    rw [Fin.sum_univ_two]
    rfl
  have e2 : ∀ p : Bit × Bit, stoch_to_det.push (fun a : I × (Bit × Bit) => (a.2.2, a.2.1)) c p =
      ∑ i, c (i, (p.2, p.1)) := by
    intro p
    exact (aux_push_fst_equiv aux_E2 c p).trans rfl
  have e3 : ∀ p : I × (Bit × Bit),
      stoch_to_det.push (fun a : I × (Bit × Bit) => (a.1, a.2.2, a.2.1)) c p =
        c (p.1, (p.2.2, p.2.1)) := by
    intro p
    exact (aux_push_equiv aux_E3 c p).trans rfl
  have e4 : ∀ x : Bit, stoch_to_det.push (fun a : I × (Bit × Bit) => a.2.1) c x =
      ∑ i, (c (i, (x, 0)) + c (i, (x, 1))) := by
    intro x
    refine (aux_push_fst_equiv aux_E4 c x).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_two]
    rfl
  have hF : ∀ x : Bit, ∑ i, (c (i, (x, 0)) + c (i, (x, 1))) *
        klBer (c (i, (x, 1)) / (c (i, (x, 0)) + c (i, (x, 1))))
          ((∑ j, c (j, (x, 1))) / ∑ j, (c (j, (x, 0)) + c (j, (x, 1)))) =
      ∑ i, Real.negMulLog (c (i, (x, 0)) + c (i, (x, 1)))
        - ∑ i, Real.negMulLog (c (i, (x, 0))) - ∑ i, Real.negMulLog (c (i, (x, 1)))
        + Real.negMulLog (∑ i, c (i, (x, 1))) + Real.negMulLog (∑ i, c (i, (x, 0)))
        - Real.negMulLog (∑ i, (c (i, (x, 0)) + c (i, (x, 1)))) :=
    fun x => aux_fibre (fun i => c (i, (x, 0))) (fun i => c (i, (x, 1))) (fun _ => hc _)
      (fun _ => hc _)
  simp only [e1, e2, e3, e4, hF]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- Pinsker in each fibre: `log 2 · I(W; X' | X)` is at least the `P(W, X)`-weighted squared
spread of `P(X' = 1 | w, x)` about `P(X' = 1 | x)`, times two. -/
private theorem aux_bound {I : Type*} [Fintype I] [DecidableEq I] (c : I × (Bit × Bit) → ℝ)
    (hc : ∀ z, 0 < c z) :
    ∑ x : Bit, ∑ i, (c (i, (x, 0)) + c (i, (x, 1))) *
        (2 * (c (i, (x, 1)) / (c (i, (x, 0)) + c (i, (x, 1))) -
          (∑ j, c (j, (x, 1))) / ∑ j, (c (j, (x, 0)) + c (j, (x, 1)))) ^ 2) ≤
      Real.log 2 *
        stoch_to_det.condMI (fun z : I × (Bit × Bit) => z.1) (fun z => z.2.2) (fun z => z.2.1)
          c := by
  rw [aux_log_two_condMI_eq c hc]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
  have hA := hc (i, (x, 0))
  have hB := hc (i, (x, 1))
  have hAB : 0 < c (i, (x, 0)) + c (i, (x, 1)) := add_pos hA hB
  have hSA : 0 < ∑ j, c (j, (x, 0)) :=
    Finset.sum_pos (fun j _ => hc _) ⟨i, Finset.mem_univ _⟩
  have hSB : 0 < ∑ j, c (j, (x, 1)) :=
    Finset.sum_pos (fun j _ => hc _) ⟨i, Finset.mem_univ _⟩
  have hT : ∑ j, (c (j, (x, 0)) + c (j, (x, 1))) = ∑ j, c (j, (x, 0)) + ∑ j, c (j, (x, 1)) :=
    Finset.sum_add_distrib
  refine mul_le_mul_of_nonneg_left (klBer_ge_two_sq ?_ ?_ ?_ ?_) hAB.le
  · exact div_nonneg hB.le hAB.le
  · rw [div_le_one hAB]
    linarith
  · rw [hT]
    exact div_pos hSB (add_pos hSA hSB)
  · rw [hT, div_lt_one (add_pos hSA hSB)]
    linarith

/-! ## Scalar helpers -/

/-- The weighted squared spread of two means about their pooled mean. -/
private def aux_Q (S0 B0 S1 B1 : ℝ) : ℝ :=
  S0 * (2 * (B0 / S0 - (B0 + B1) / (S0 + S1)) ^ 2) +
    S1 * (2 * (B1 / S1 - (B0 + B1) / (S0 + S1)) ^ 2)

/-- Two-point spread: `S₀ (m₀ - m̄)² + S₁ (m₁ - m̄)² = S₀ S₁ / (S₀ + S₁) · (m₁ - m₀)²`. -/
private theorem aux_two {S0 B0 S1 B1 : ℝ} (h0 : 0 < S0) (h1 : 0 < S1) :
    aux_Q S0 B0 S1 B1 = 2 * (S0 * S1 / (S0 + S1)) * (B1 / S1 - B0 / S0) ^ 2 := by
  have h01 : 0 < S0 + S1 := add_pos h0 h1
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h01' := h01.ne'
  unfold aux_Q
  field_simp
  ring

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

/-- The replica cells are positive for `0 ≤ κ < 1` and `0 < r < 1`. -/
theorem replicaCell_pos {κ r : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (x x' : Bit) : 0 < replicaCell κ r x x' := by
  have h1 : 0 < 1 - κ := by linarith
  have h2 : 0 < 1 - r := by linarith
  unfold replicaCell
  split_ifs
  · exact add_pos_of_pos_of_nonneg (pow_pos hr0 2) (mul_nonneg (mul_nonneg hκ0 hr0.le) h2.le)
  · exact mul_pos (mul_pos h1 hr0) h2
  · exact mul_pos (mul_pos h1 hr0) h2
  · exact add_pos_of_pos_of_nonneg (pow_pos h2 2) (mul_nonneg (mul_nonneg hκ0 hr0.le) h2.le)

/-- The closing identity: the Pinsker bound evaluated on the two-contact cells is exactly
`2 (1 - κ)² u v / (u + v)`. -/
private theorem aux_final {κ a r w0 w1 : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hw0 : 0 < w0) (hw1 : 0 < w1) (hw : w0 + w1 = 1) :
    2 * (1 - κ) ^ 2 * (betweenVariance a (1 - r) w1 * withinVariance a (1 - r) w1 /
        (betweenVariance a (1 - r) w1 + withinVariance a (1 - r) w1)) =
      aux_Q (w0 * replicaCell κ a 0 0 + w0 * replicaCell κ a 0 1) (w0 * replicaCell κ a 0 1)
          (w1 * replicaCell κ r 0 0 + w1 * replicaCell κ r 0 1) (w1 * replicaCell κ r 0 1) +
        aux_Q (w0 * replicaCell κ a 1 0 + w0 * replicaCell κ a 1 1) (w0 * replicaCell κ a 1 1)
          (w1 * replicaCell κ r 1 0 + w1 * replicaCell κ r 1 1) (w1 * replicaCell κ r 1 1) := by
  have pa := replicaCell_pos hκ0 hκ1 ha0 ha1
  have pr := replicaCell_pos hκ0 hκ1 hr0 hr1
  rw [aux_two (add_pos (mul_pos hw0 (pa 0 0)) (mul_pos hw0 (pa 0 1)))
      (add_pos (mul_pos hw1 (pr 0 0)) (mul_pos hw1 (pr 0 1))),
    aux_two (add_pos (mul_pos hw0 (pa 1 0)) (mul_pos hw0 (pa 1 1)))
      (add_pos (mul_pos hw1 (pr 1 0)) (mul_pos hw1 (pr 1 1)))]
  simp only [aux_cell_00, aux_cell_01, aux_cell_10, aux_cell_11]
  have h1a : 0 < 1 - a := by linarith
  have h1r : 0 < 1 - r := by linarith
  have s0a : w0 * ((1 - a) ^ 2 + κ * a * (1 - a)) + w0 * ((1 - κ) * a * (1 - a)) =
      w0 * (1 - a) := by ring
  have s0r : w1 * ((1 - r) ^ 2 + κ * r * (1 - r)) + w1 * ((1 - κ) * r * (1 - r)) =
      w1 * (1 - r) := by ring
  have s1a : w0 * ((1 - κ) * a * (1 - a)) + w0 * (a ^ 2 + κ * a * (1 - a)) = w0 * a := by ring
  have s1r : w1 * ((1 - κ) * r * (1 - r)) + w1 * (r ^ 2 + κ * r * (1 - r)) = w1 * r := by ring
  rw [s0a, s0r, s1a, s1r]
  have m0a : w0 * ((1 - κ) * a * (1 - a)) / (w0 * (1 - a)) = (1 - κ) * a := by
    rw [div_eq_iff (mul_pos hw0 h1a).ne']
    ring
  have m0r : w1 * ((1 - κ) * r * (1 - r)) / (w1 * (1 - r)) = (1 - κ) * r := by
    rw [div_eq_iff (mul_pos hw1 h1r).ne']
    ring
  have m1a : w0 * (a ^ 2 + κ * a * (1 - a)) / (w0 * a) = a + κ * (1 - a) := by
    rw [div_eq_iff (mul_pos hw0 ha0).ne']
    ring
  have m1r : w1 * (r ^ 2 + κ * r * (1 - r)) / (w1 * r) = r + κ * (1 - r) := by
    rw [div_eq_iff (mul_pos hw1 hr0).ne']
    ring
  rw [m0a, m0r, m1a, m1r]
  obtain rfl : w0 = 1 - w1 := by linarith
  have hπ : 0 < mixtureMean a (1 - r) w1 := by
    unfold mixtureMean
    nlinarith [mul_pos hw0 ha0, mul_pos hw1 hr0]
  have hπ1 : 0 < 1 - mixtureMean a (1 - r) w1 := by
    unfold mixtureMean
    nlinarith [mul_pos hw0 h1a, mul_pos hw1 h1r]
  rw [← mixture_variance_split]
  have ep1 : (1 - w1) * a + w1 * r = mixtureMean a (1 - r) w1 := by
    unfold mixtureMean
    ring
  have ep0 : (1 - w1) * (1 - a) + w1 * (1 - r) = 1 - mixtureMean a (1 - r) w1 := by
    unfold mixtureMean
    ring
  rw [ep1, ep0]
  have hπne := hπ.ne'
  have hπ1ne := hπ1.ne'
  field_simp
  unfold mixtureMean betweenVariance withinVariance
  ring

/-- A row cube parameter puts the row-one mass strictly inside `(0, 1)`. -/
theorem rowCubeParam_rowMass_mem {Y : Type} [Fintype Y] {q : Bit × Y → ℝ} {x : ℝ}
    (h : RowCubeParam q x) :
    0 < rowMass q 1 ∧ rowMass q 1 < 1 := by
  obtain ⟨hx, -, h1⟩ := h
  have hU : 0 < 1 + x ^ 3 := by positivity
  rw [h1]
  exact ⟨by positivity, by rw [div_lt_one hU]; linarith⟩

/-- A row cube parameter makes the two row masses sum to one. -/
private theorem aux_row_zero {Y : Type} [Fintype Y] {q : Bit × Y → ℝ} {x : ℝ}
    (h : RowCubeParam q x) :
    rowMass q 0 = 1 - rowMass q 1 := by
  obtain ⟨hx, h0, h1⟩ := h
  have hU : 0 < 1 + x ^ 3 := by positivity
  rw [h0, h1, eq_sub_iff_add_eq, ← add_div, div_self hU.ne']

/-- The replica lower bound: `2 (1 - κ)² u v / (u + v) ≤ log 2 · I(W; X' | X)` for a two-contact
latent with row parameters `0 < s < t` and positive priors; nats on the left, `log 2` times bits
on the right. -/
theorem twoContact_replica_info_ge {Y : Type} [Fintype Y] [DecidableEq Y]
    {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit) {w : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hs0 : 0 < s) (hst : s < t) (hpos : ∀ v, 0 < V.prior v) :
    2 * (1 - s * t / (s + t) ^ 2) ^ 2 *
        (betweenVariance (rowMass (V.comp (e.symm 0)) 1) (rowMass (V.comp (e.symm 1)) 0)
            (V.prior (e.symm 1)) *
          withinVariance (rowMass (V.comp (e.symm 0)) 1) (rowMass (V.comp (e.symm 1)) 0)
            (V.prior (e.symm 1)) /
          (betweenVariance (rowMass (V.comp (e.symm 0)) 1) (rowMass (V.comp (e.symm 1)) 0)
              (V.prior (e.symm 1)) +
            withinVariance (rowMass (V.comp (e.symm 0)) 1) (rowMass (V.comp (e.symm 1)) 0)
              (V.prior (e.symm 1)))) ≤
      Real.log 2 *
        condMutualInfo (fun a : V.ι × (Bit × (Bit × Y)) => a.1) (fun a => a.2.2.1) (fun a => a.2.1)
          (replicaLaw V.joint) := by
  have ht0 : 0 < t := hs0.trans hst
  have hκ0 : 0 ≤ s * t / (s + t) ^ 2 := div_nonneg (mul_pos hs0 ht0).le (sq_nonneg _)
  have hκ1 : s * t / (s + t) ^ 2 < 1 := by
    rw [div_lt_one (pow_pos (add_pos hs0 ht0) 2)]
    nlinarith [mul_pos hs0 ht0, sq_nonneg s, sq_nonneg t]
  have hrow : ∀ i : Bit,
      0 < rowMass (V.comp (e.symm i)) 1 ∧ rowMass (V.comp (e.symm i)) 1 < 1 := by
    intro i
    fin_cases i
    · exact rowCubeParam_rowMass_mem hs
    · exact rowCubeParam_rowMass_mem ht
  have hb : rowMass (V.comp (e.symm 1)) 0 = 1 - rowMass (V.comp (e.symm 1)) 1 := aux_row_zero ht
  have hcell := twoContact_replica_rows V e hw h0 h1 hs ht hst.ne
  have hcpos : ∀ z, 0 < pushforward (fun a : V.ι × (Bit × (Bit × Y)) => (a.1, (a.2.1, a.2.2.1)))
      (replicaLaw V.joint) z := by
    rintro ⟨v, x, x'⟩
    obtain ⟨i, rfl⟩ := e.symm.surjective v
    rw [hcell i x x']
    exact mul_pos (hpos _) (replicaCell_pos hκ0 hκ1 (hrow i).1 (hrow i).2 x x')
  have hred : condMutualInfo (fun a : V.ι × (Bit × (Bit × Y)) => a.1) (fun a => a.2.2.1)
        (fun a => a.2.1) (replicaLaw V.joint) =
      stoch_to_det.condMI (fun z : V.ι × (Bit × Bit) => z.1) (fun z => z.2.2) (fun z => z.2.1)
        (pushforward (fun a : V.ι × (Bit × (Bit × Y)) => (a.1, (a.2.1, a.2.2.1)))
          (replicaLaw V.joint)) :=
    aux_condMI_push (replicaLaw V.joint)
      (fun a : V.ι × (Bit × (Bit × Y)) => (a.1, (a.2.1, a.2.2.1)))
      (fun z : V.ι × (Bit × Bit) => z.1) (fun z => z.2.2) (fun z => z.2.1)
  have hsumV : ∀ g : V.ι → ℝ, ∑ v, g v = g (e.symm 0) + g (e.symm 1) := fun g => by
    rw [← Equiv.sum_comp e.symm g, Fin.sum_univ_two]
  have key := aux_bound _ hcpos
  simp only [hsumV, Fin.sum_univ_two, hcell] at key
  rw [hred, hb]
  calc
    _ = _ := aux_final hκ0 hκ1 (hrow 0).1 (hrow 0).2 (hrow 1).1 (hrow 1).2 (hpos (e.symm 0))
        (hpos (e.symm 1)) (bitLatent_prior_sum V e)
    _ ≤ _ := key

end

end BinaryRow

end StochasticToDeterministicLatents
