import StochasticToDeterministicLatents.BinaryRow.Foundation

/-!
# Code interfaces of a latent

For a latent `L` of a law `p` on a finite `α × β`, with label `W` and observed pair `(X, Y)`
under `L.joint`, the chain rule gives `I(X;Y) = I(X;Y|W) + I(W;X) - I(W;X|Y)`
(`mutualInfo_eq_latent`) and `H(X|Y) = H(X|W) - I(X;Y|W) + I(W;X|Y)` (`condEntropy_eq_latent`),
the left sides under `p`. Since `L.score = I(X;Y|W) + I(W;X|Y) + I(W;Y|X)`, the constant-code and
row-code scores satisfy `I(X;Y) ≤ L.score + I(W;X)` (`mutualInfo_le_score_add`) and
`H(X|Y) ≤ L.score + H(X|W) - 2 I(X;Y|W)` (`condEntropy_le_score_add`), and
`H(W|X,Y) ≤ H(W|X)` (`condEntropy_label_le`).

All quantities are in bits; each statement is homogeneous and holds in any base.
`condMutualInfo f g h m` is `I(f; g | h)` and `condEntropy f g m` is `H(f | g)` under `m`.

## Attribution

Original to this repository, on the entropy interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ## Helpers -/

/-- Mutual information of variables on a law pushed forward along any map is that of the
composed variables on the original law. -/
private theorem aux_mutualInfo_pushforward_comp {Ω Ω' A B : Type*} [Fintype Ω] [Fintype Ω']
    [DecidableEq Ω'] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (m : Ω → ℝ) (φ : Ω → Ω') (f : Ω' → A) (g : Ω' → B) :
    mutualInfo f g (pushforward φ m) =
      mutualInfo (fun ω => f (φ ω)) (fun ω => g (φ ω)) m := by
  have h1 := entropyOf_pushforward_comp m φ f
  have h2 := entropyOf_pushforward_comp m φ g
  have h3 := entropyOf_pushforward_comp m φ (fun z => (f z, g z))
  simp only [entropyOf] at h1 h2 h3
  unfold mutualInfo stoch_to_det.MI
  rw [h1, h2, h3]

/-- Conditional entropy of variables on a law pushed forward along any map is that of the
composed variables on the original law. -/
private theorem aux_condEntropy_pushforward_comp {Ω Ω' A B : Type*} [Fintype Ω] [Fintype Ω']
    [DecidableEq Ω'] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (m : Ω → ℝ) (φ : Ω → Ω') (f : Ω' → A) (g : Ω' → B) :
    condEntropy f g (pushforward φ m) =
      condEntropy (fun ω => f (φ ω)) (fun ω => g (φ ω)) m := by
  have h2 := entropyOf_pushforward_comp m φ g
  have h3 := entropyOf_pushforward_comp m φ (fun z => (f z, g z))
  simp only [entropyOf] at h2 h3
  unfold condEntropy stoch_to_det.condH
  rw [h2, h3]

/-- Swapping a pair does not change its entropy. -/
private theorem aux_entropyOf_pair_comm {Ω A B : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) :
    entropyOf (fun ω => (f ω, g ω)) m = entropyOf (fun ω => (g ω, f ω)) m := by
  symm
  simpa using entropyOf_equiv hm (fun ω => (f ω, g ω)) (Equiv.prodComm A B)

/-- Rotating a triple does not change its entropy: `H(f, g, h) = H(h, f, g)`. -/
private theorem aux_entropyOf_triple_rotate {Ω A B C : Type*} [Fintype Ω] [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    entropyOf (fun ω => (f ω, (g ω, h ω))) m =
      entropyOf (fun ω => (h ω, (f ω, g ω))) m := by
  let e : A × (B × C) ≃ C × (A × B) :=
    { toFun := fun a => (a.2.2, (a.1, a.2.1))
      invFun := fun a => (a.2.1, (a.2.2, a.1))
      left_inv := by intro a; rcases a with ⟨a, b, c⟩; rfl
      right_inv := by intro a; rcases a with ⟨c, a, b⟩; rfl }
  symm
  simpa [e] using entropyOf_equiv hm (fun ω => (f ω, (g ω, h ω))) e

/-- Swapping the inner pair of a triple does not change its entropy. -/
private theorem aux_entropyOf_triple_swap_inner {Ω A B C : Type*} [Fintype Ω] [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    entropyOf (fun ω => (f ω, (g ω, h ω))) m =
      entropyOf (fun ω => (f ω, (h ω, g ω))) m := by
  let e : A × (B × C) ≃ A × (C × B) :=
    { toFun := fun a => (a.1, (a.2.2, a.2.1))
      invFun := fun a => (a.1, (a.2.2, a.2.1))
      left_inv := by intro a; rcases a with ⟨a, b, c⟩; rfl
      right_inv := by intro a; rcases a with ⟨a, c, b⟩; rfl }
  symm
  simpa [e] using entropyOf_equiv hm (fun ω => (f ω, (g ω, h ω))) e

/-- The observed marginal of a latent's joint law is the observed law. -/
private theorem aux_pushforward_snd_joint {p : α × β → ℝ} (L : Latent p) :
    pushforward (Prod.snd : L.ι × (α × β) → α × β) L.joint = p := by
  funext z
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact L.mixture z

/-- The score of a latent, written with the public information quantities. -/
private theorem aux_score_eq {p : α × β → ℝ} (L : Latent p) :
    L.score =
      condMutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) L.joint
        + condMutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2)
          L.joint
        + condMutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1)
          L.joint :=
  rfl

/-- `I(X;Y)` under `p` is `I(X;Y)` under the latent's joint law. -/
private theorem aux_mutualInfo_joint {p : α × β → ℝ} (L : Latent p) :
    mutualInfo Prod.fst Prod.snd p =
      mutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) L.joint := by
  have h := aux_mutualInfo_pushforward_comp L.joint (Prod.snd : L.ι × (α × β) → α × β)
    (Prod.fst : α × β → α) (Prod.snd : α × β → β)
  rw [aux_pushforward_snd_joint L] at h
  exact h

/-- `H(X|Y)` under `p` is `H(X|Y)` under the latent's joint law. -/
private theorem aux_condEntropy_joint {p : α × β → ℝ} (L : Latent p) :
    condEntropy Prod.fst Prod.snd p =
      condEntropy (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) L.joint := by
  have h := aux_condEntropy_pushforward_comp L.joint (Prod.snd : L.ι × (α × β) → α × β)
    (Prod.fst : α × β → α) (Prod.snd : α × β → β)
  rw [aux_pushforward_snd_joint L] at h
  exact h

/-- For every latent, `I(X;Y)` under `p` equals `I(X;Y|W) + I(W;X) - I(W;X|Y)` under its
joint law. -/
theorem mutualInfo_eq_latent {p : α × β → ℝ} (L : Latent p) :
    mutualInfo Prod.fst Prod.snd p =
      condMutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) L.joint
        + mutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1) L.joint
        - condMutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2)
          L.joint := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  rw [aux_mutualInfo_joint L]
  have e1 := aux_entropyOf_pair_comm hJ (fun a : L.ι × (α × β) => a.2.1) (fun a => a.1)
  have e2 := aux_entropyOf_pair_comm hJ (fun a : L.ι × (α × β) => a.2.2) (fun a => a.1)
  have e3 := aux_entropyOf_triple_rotate hJ (fun a : L.ι × (α × β) => a.2.1)
    (fun a => a.2.2) (fun a => a.1)
  simp only [entropyOf] at e1 e2 e3
  simp only [mutualInfo, condMutualInfo, stoch_to_det.MI, stoch_to_det.condMI]
  rw [e1, e2, e3]
  ring

/-- For every latent, `H(X|Y)` under `p` equals `H(X|W) - I(X;Y|W) + I(W;X|Y)` under its
joint law. -/
theorem condEntropy_eq_latent {p : α × β → ℝ} (L : Latent p) :
    condEntropy Prod.fst Prod.snd p =
      condEntropy (fun a : L.ι × (α × β) => a.2.1) (fun a => a.1) L.joint
        - condMutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) L.joint
        + condMutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2)
          L.joint := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  rw [aux_condEntropy_joint L]
  have e2 := aux_entropyOf_pair_comm hJ (fun a : L.ι × (α × β) => a.2.2) (fun a => a.1)
  have e3 := aux_entropyOf_triple_rotate hJ (fun a : L.ι × (α × β) => a.2.1)
    (fun a => a.2.2) (fun a => a.1)
  simp only [entropyOf] at e2 e3
  simp only [condEntropy, condMutualInfo, stoch_to_det.condH, stoch_to_det.condMI]
  rw [e2, e3]
  ring

/-- The constant code's score `I(X;Y)` is at most `L.score + I(W;X)`. -/
theorem mutualInfo_le_score_add {p : α × β → ℝ} (L : Latent p) :
    mutualInfo Prod.fst Prod.snd p ≤
      L.score + mutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1) L.joint := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have h1 := condMutualInfo_nonneg hJ (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1)
    (fun a => a.2.2)
  have h2 := condMutualInfo_nonneg hJ (fun a : L.ι × (α × β) => a.1) (fun a => a.2.2)
    (fun a => a.2.1)
  rw [mutualInfo_eq_latent L, aux_score_eq L]
  linarith

/-- The row code's score `H(X|Y)` is at most `L.score + H(X|W) - 2 I(X;Y|W)`. -/
theorem condEntropy_le_score_add {p : α × β → ℝ} (L : Latent p) :
    condEntropy Prod.fst Prod.snd p ≤
      L.score + condEntropy (fun a : L.ι × (α × β) => a.2.1) (fun a => a.1) L.joint
        - 2 * condMutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1)
          L.joint := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have h2 := condMutualInfo_nonneg hJ (fun a : L.ι × (α × β) => a.1) (fun a => a.2.2)
    (fun a => a.2.1)
  rw [condEntropy_eq_latent L, aux_score_eq L]
  linarith

/-- Conditioning the label on the whole observed pair gives at most `H(W|X)`:
`H(W | X, Y) ≤ H(W | X)`. -/
theorem condEntropy_label_le {p : α × β → ℝ} (L : Latent p) :
    condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2) L.joint ≤
      condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1) L.joint := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have hc := condMutualInfo_nonneg hJ (fun a : L.ι × (α × β) => a.1) (fun a => a.2.2)
    (fun a => a.2.1)
  have e1 := aux_entropyOf_triple_swap_inner hJ (fun a : L.ι × (α × β) => a.1)
    (fun a => a.2.2) (fun a => a.2.1)
  have e2 := aux_entropyOf_pair_comm hJ (fun a : L.ι × (α × β) => a.2.2) (fun a => a.2.1)
  simp only [entropyOf] at e1 e2
  simp only [condMutualInfo, stoch_to_det.condMI] at hc
  rw [e1, e2] at hc
  show stoch_to_det.Hvar (fun a : L.ι × (α × β) => (a.1, (a.2.1, a.2.2))) L.joint
      - stoch_to_det.Hvar (fun a : L.ι × (α × β) => (a.2.1, a.2.2)) L.joint ≤
    stoch_to_det.Hvar (fun a : L.ι × (α × β) => (a.1, a.2.1)) L.joint
      - stoch_to_det.Hvar (fun a : L.ι × (α × β) => a.2.1) L.joint
  linarith

end

end BinaryRow

end StochasticToDeterministicLatents
