import StochasticToDeterministicLatents.BinaryRow.Replica
import StochasticToDeterministicLatents.BinaryRow.Posterior

/-!
# The replica's row law and the two-contact cells

For a finite label `W` and the observed pair `(X, Y)` on any finite `α × β`: the row replica's
mass in division form (`replicaLaw_apply`), the law of `(W, X, X')` as a sum over columns
(`replicaLaw_pushforward_rows`), `I(f; g | h) = H(f | h) - H(f | (g, h))`
(`condMutualInfo_eq_condEntropy_sub`), and `I(W; X' | X) = H(W | X) - H(W | X', X)` with
`H(W | X)` taken under the original law (`replicaLaw_B2_eq`).

On `Bit × Y`, for a `Bit`-labelled latent whose two components are contacts of one feasible
kernel with different row parameters `s` and `t`, the law of `(W, X, X')` at each label is the
prior times `replicaCell κ r`, with `r` the component's row-one mass and `κ = st/(s+t)²`
(`twoContact_replica_rows`). The cells are `(1-r)² + κ r(1-r)` and `r² + κ r(1-r)` on the
diagonal and `(1-κ) r(1-r)` off it.

All information quantities are in bits.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose entropy
functionals and latent structure these proofs use. The replica cell table and its proof are
original to this repository.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

/-! ## Helpers: fibre sums through an equivalence -/

/-- The law of the first coordinate of an equivalence `e : Ω ≃ A × K` at `a` is the
sum over the second coordinate. -/
private theorem aux_push_fst_equiv {Ω A K : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype K] (e : Ω ≃ A × K) (m : Ω → ℝ) (a : A) :
    pushforward (fun ω => (e ω).1) m a = ∑ k, m (e.symm (a, k)) := by
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, ← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- Regroup the replica coordinates as `((W, (X, X')), Y)`. -/
private def aux_eRows {I A B : Type*} : I × (A × (A × B)) ≃ (I × (A × A)) × B where
  toFun a := ((a.1, (a.2.1, a.2.2.1)), a.2.2.2)
  invFun b := (b.1.1, (b.1.2.1, (b.1.2.2, b.2)))
  left_inv _ := rfl
  right_inv _ := rfl

section Generic

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype β] [DecidableEq α] [DecidableEq β] [Fintype ι] [DecidableEq ι] in
/-- The replica in division form: `Real` division by zero gives the zero-mass convention. -/
theorem replicaLaw_apply (r : ι × (α × β) → ℝ) (a : ι × (α × (α × β))) :
    replicaLaw r a =
      r (a.1, (a.2.1, a.2.2.2)) * r (a.1, (a.2.2.1, a.2.2.2)) / labelColMass r a.1 a.2.2.2 := by
  unfold replicaLaw
  split_ifs with h
  · simp [h]
  · rfl

omit [DecidableEq β] in
/-- The law of `(W, (X, X'))` under the replica, as a sum over columns. -/
theorem replicaLaw_pushforward_rows (r : ι × (α × β) → ℝ) (i : ι) (x x' : α) :
    pushforward (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.1))) (replicaLaw r) (i, (x, x')) =
      ∑ y, r (i, (x, y)) * r (i, (x', y)) / labelColMass r i y := by
  refine (aux_push_fst_equiv aux_eRows (replicaLaw r) (i, (x, x'))).trans ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  exact replicaLaw_apply r (i, (x, (x', y)))

/-- Conditional mutual information as a drop in conditional entropy:
`I(f; g | h) = H(f | h) - H(f | (g, h))`. -/
theorem condMutualInfo_eq_condEntropy_sub {Ω A B C : Type*} [Fintype Ω] [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (m : Ω → ℝ) (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    condMutualInfo f g h m = condEntropy f h m - condEntropy f (fun ω => (g ω, h ω)) m := by
  simp only [condMutualInfo, condEntropy, stoch_to_det.condMI, stoch_to_det.condH]
  ring

/-- `I(W; X' | X)` under the replica equals `H(W | X)` under `r` minus `H(W | (X', X))` under the
replica. -/
theorem replicaLaw_B2_eq {r : ι × (α × β) → ℝ} (hr : IsPMF r) :
    condMutualInfo (fun a : ι × (α × (α × β)) => a.1) (fun a => a.2.2.1) (fun a => a.2.1)
        (replicaLaw r) =
      condEntropy (fun a : ι × (α × β) => a.1) (fun a => a.2.1) r
        - condEntropy (fun a : ι × (α × (α × β)) => a.1) (fun a => (a.2.2.1, a.2.1))
          (replicaLaw r) := by
  rw [condMutualInfo_eq_condEntropy_sub (replicaLaw r)]
  have h1 : entropyOf (fun b : ι × (α × β) => (b.1, b.2.1)) r =
      entropyOf (fun a : ι × (α × (α × β)) => (a.1, a.2.1)) (replicaLaw r) := by
    have h := entropyOf_pushforward_comp (replicaLaw r)
      (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.2)))
      (fun b : ι × (α × β) => (b.1, b.2.1))
    rw [replicaLaw_pushforward_original hr] at h
    exact h
  have h2 : entropyOf (fun b : ι × (α × β) => b.2.1) r =
      entropyOf (fun a : ι × (α × (α × β)) => a.2.1) (replicaLaw r) := by
    have h := entropyOf_pushforward_comp (replicaLaw r)
      (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.2)))
      (fun b : ι × (α × β) => b.2.1)
    rw [replicaLaw_pushforward_original hr] at h
    exact h
  simp only [entropyOf] at h1 h2
  simp only [condEntropy, stoch_to_det.condH]
  rw [h1, h2]

end Generic

/-- The law of the two rows `(X, X')` of a component's replica when the component has row-one
mass `r` and its row-one posterior has variance `κ r (1 - r)`: diagonal cells
`(1-r)² + κ r(1-r)` and `r² + κ r(1-r)`, off-diagonal cells `(1-κ) r(1-r)`. -/
def replicaCell (κ r : ℝ) (x x' : Bit) : ℝ :=
  if x = 1 then
    (if x' = 1 then r ^ 2 + κ * r * (1 - r) else (1 - κ) * r * (1 - r))
  else
    (if x' = 1 then (1 - κ) * r * (1 - r) else (1 - r) ^ 2 + κ * r * (1 - r))

/-! ## Helpers: the two-contact cells -/

/-- The label-column mass of a latent's joint law is the prior times the component's column
mass. -/
theorem labelColMass_latent_joint {Y : Type} [Fintype Y] [DecidableEq Y] {p : Bit × Y → ℝ}
    (V : Latent p) (v : V.ι) (y : Y) :
    labelColMass V.joint v y = V.prior v * colMass (V.comp v) y := by
  show ∑ x, V.prior v * V.comp v (x, y) = V.prior v * (V.comp v (0, y) + V.comp v (1, y))
  rw [Fin.sum_univ_two]
  ring

/-- The row sum of the replica of a latent's joint law factors through the prior. -/
private theorem aux_joint_rows {Y : Type} [Fintype Y] [DecidableEq Y] {p : Bit × Y → ℝ}
    (V : Latent p) (v : V.ι) (x x' : Bit) :
    ∑ y, V.joint (v, (x, y)) * V.joint (v, (x', y)) / labelColMass V.joint v y =
      V.prior v * ∑ y, V.comp v (x, y) * V.comp v (x', y) / colMass (V.comp v) y := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [labelColMass_latent_joint]
  show V.prior v * V.comp v (x, y) * (V.prior v * V.comp v (x', y)) /
      (V.prior v * colMass (V.comp v) y) = _
  rcases eq_or_ne (V.prior v) 0 with h | h
  · simp [h]
  · rw [show V.prior v * V.comp v (x, y) * (V.prior v * V.comp v (x', y)) =
        V.prior v * (V.prior v * (V.comp v (x, y) * V.comp v (x', y))) by ring,
      mul_div_mul_left _ _ h, mul_div_assoc]

/-- For a contact `q` whose row-one posterior has variance `κ r (1 - r)` over the columns, with
`r = rowMass q 1`, the column-weighted row products `∑ y, q(x,y) q(x',y) / colMass q y` are
`replicaCell κ r x x'`. -/
theorem rowContact_replicaCell {Y : Type} [Fintype Y] [DecidableEq Y] {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) (hq : IsContact (univ : Finset (Bit × Y)) w q)
    {κ : ℝ}
    (hvar : ∑ y, colMass q y * (q (1, y) / colMass q y) ^ 2 - rowMass q 1 ^ 2 =
      κ * rowMass q 1 * (1 - rowMass q 1))
    (x x' : Bit) :
    ∑ y, q (x, y) * q (x', y) / colMass q y = replicaCell κ (rowMass q 1) x x' := by
  have hc : ∀ y, 0 < colMass q y := rowContact_colMass_pos hw hq
  have hS0 : ∑ y, colMass q y = 1 := by
    simpa [stoch_to_det.mass] using (colMass_isPMF hq.1).total
  have hS1 := rowContact_posterior_mean hw hq
  have t11 : ∀ y, q (1, y) * q (1, y) / colMass q y =
      colMass q y * (q (1, y) / colMass q y) ^ 2 := by
    intro y
    have hne := (hc y).ne'
    field_simp
  have t10 : ∀ y, q (1, y) * q (0, y) / colMass q y =
      colMass q y * (q (1, y) / colMass q y) - colMass q y * (q (1, y) / colMass q y) ^ 2 := by
    intro y
    have hne := (hc y).ne'
    simp only [colMass] at hne ⊢
    field_simp
    ring
  have t01 : ∀ y, q (0, y) * q (1, y) / colMass q y =
      colMass q y * (q (1, y) / colMass q y) - colMass q y * (q (1, y) / colMass q y) ^ 2 := by
    intro y
    rw [mul_comm]
    exact t10 y
  have t00 : ∀ y, q (0, y) * q (0, y) / colMass q y =
      colMass q y - 2 * (colMass q y * (q (1, y) / colMass q y)) +
        colMass q y * (q (1, y) / colMass q y) ^ 2 := by
    intro y
    have hne := (hc y).ne'
    simp only [colMass] at hne ⊢
    field_simp
    ring
  have h01 : (0 : Bit) ≠ 1 := by decide
  have hx : ∀ z : Bit, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx x with rfl | rfl <;> rcases hx x' with rfl | rfl
  · simp only [replicaCell, h01, ↓reduceIte]
    rw [Finset.sum_congr rfl fun y _ => t00 y, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    linear_combination hS0 - 2 * hS1 + hvar
  · simp only [replicaCell, h01, ↓reduceIte]
    rw [Finset.sum_congr rfl fun y _ => t01 y, Finset.sum_sub_distrib]
    linear_combination hS1 - hvar
  · simp only [replicaCell, h01, ↓reduceIte]
    rw [Finset.sum_congr rfl fun y _ => t10 y, Finset.sum_sub_distrib]
    linear_combination hS1 - hvar
  · simp only [replicaCell, ↓reduceIte]
    rw [Finset.sum_congr rfl fun y _ => t11 y]
    linear_combination hvar

/-- The two-contact replica: the `(W, X, X')` marginal at label `e.symm i` is the prior times
`replicaCell κ r`, with `r` the component's row-one mass and `κ = st/(s+t)²`. -/
theorem twoContact_replica_rows {Y : Type} [Fintype Y] [DecidableEq Y]
    {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit) {w : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s ≠ t) (i x x' : Bit) :
    pushforward (fun a : V.ι × (Bit × (Bit × Y)) => (a.1, (a.2.1, a.2.2.1))) (replicaLaw V.joint)
        (e.symm i, (x, x')) =
      V.prior (e.symm i) *
        replicaCell (s * t / (s + t) ^ 2) (rowMass (V.comp (e.symm i)) 1) x x' := by
  rw [replicaLaw_pushforward_rows, aux_joint_rows]
  congr 1
  have hv0 := rowTwoContact_variance hw h0 h1 (ne_of_rowCubeParam_ne hs ht hst) hs ht
  have hv1 := rowTwoContact_variance hw h1 h0 (ne_of_rowCubeParam_ne ht hs hst.symm) ht hs
  rw [show t * s / (t + s) ^ 2 = s * t / (s + t) ^ 2 by ring] at hv1
  have hx : i = 0 ∨ i = 1 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with rfl | rfl
  · exact rowContact_replicaCell hw h0 hv0 x x'
  · exact rowContact_replicaCell hw h1 hv1 x x'

end

end BinaryRow

end StochasticToDeterministicLatents
