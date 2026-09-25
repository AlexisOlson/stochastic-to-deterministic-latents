import StochasticToDeterministicLatents.BinaryRow.Shannon

/-!
# Latents from joint laws, transposition, and elementary bounds

Generic facts about the stochastic and deterministic optima on a finite product alphabet.

* `latentOfJoint` turns a joint law `r` of a finite label and the observed pair, whose marginal
  is `p`, into a latent of `p` with joint law `r` (`latentOfJoint_joint`). So the score of any
  such joint law bounds `tau p` (`tau_le_of_joint`).
* Transposing the observed pair preserves both optima (`tau_swap`, `T_swap`).
* The score of any function of the observed pair into a finite type bounds `T`
  (`T_le_functionScore`). Constant, row, and column codes give the three elementary bounds
  `T ≤ I(X;Y)`, `T ≤ H(X | Y)` and `T ≤ H(Y | X)`, and `tau ≤ I(X;Y)`.

All information quantities are in bits.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose latent
structure, function latents, and `T_le_score` and `tau_le_T` these proofs use. The component
construction for zero-mass labels follows its conditioned components.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ## The prior, the components and the mixture of a joint law -/

omit [DecidableEq α] [DecidableEq β] in
/-- The observed marginal of a joint law is a probability law. -/
theorem isPMF_of_marginal {p : α × β → ℝ} {ι : Type} [Fintype ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (hm : ∀ z, ∑ i, r (i, z) = p z) : IsPMF p := by
  refine ⟨fun z => ?_, ?_⟩
  · rw [← hm z]
    exact Finset.sum_nonneg fun i _ => hr.nonneg (i, z)
  · have htot : ∑ w, r w = 1 := by simpa [stoch_to_det.mass] using hr.total
    unfold stoch_to_det.mass
    calc
      ∑ z, p z = ∑ z, ∑ i, r (i, z) := Finset.sum_congr rfl fun z _ => (hm z).symm
      _ = ∑ i, ∑ z, r (i, z) := Finset.sum_comm
      _ = ∑ w, r w := (Fintype.sum_prod_type r).symm
      _ = 1 := htot

omit [DecidableEq α] [DecidableEq β] in
/-- A label has prior mass zero exactly when every joint cell of that label is zero. -/
private theorem prior_eq_zero_iff {ι : Type} [Fintype ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (i : ι) :
    ∑ z, r (i, z) = 0 ↔ ∀ z, r (i, z) = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hr.nonneg (i, z))]
  simp

omit [DecidableEq α] [DecidableEq β] in
/-- The label marginal of a joint law is a probability law. -/
private theorem prior_isPMF_of_joint {ι : Type} [Fintype ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) :
    IsPMF (fun i : ι => ∑ z, r (i, z)) := by
  refine ⟨fun i => Finset.sum_nonneg fun z _ => hr.nonneg (i, z), ?_⟩
  have htot : ∑ w, r w = 1 := by simpa [stoch_to_det.mass] using hr.total
  unfold stoch_to_det.mass
  exact (Fintype.sum_prod_type r).symm.trans htot

omit [DecidableEq α] [DecidableEq β] in
/-- Prior times component recovers the joint cell, including at labels of zero mass. -/
private theorem prior_mul_comp {p : α × β → ℝ} {ι : Type} [Fintype ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (i : ι) (z : α × β) :
    (∑ z', r (i, z')) *
        (if ∑ z', r (i, z') = 0 then p z else r (i, z) / ∑ z', r (i, z')) = r (i, z) := by
  by_cases h : ∑ z', r (i, z') = 0
  · rw [if_pos h, h, zero_mul]
    exact ((prior_eq_zero_iff r hr i).mp h z).symm
  · rw [if_neg h]
    field_simp

omit [DecidableEq α] [DecidableEq β] in
/-- Each component of the latent built from a joint law is a probability law. -/
private theorem comp_isPMF_of_joint {p : α × β → ℝ} {ι : Type} [Fintype ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (hm : ∀ z, ∑ i, r (i, z) = p z) (i : ι) :
    IsPMF (fun z => if ∑ z', r (i, z') = 0 then p z else r (i, z) / ∑ z', r (i, z')) := by
  by_cases h : ∑ z', r (i, z') = 0
  · have hfun : (fun z => if ∑ z', r (i, z') = 0 then p z else r (i, z) / ∑ z', r (i, z')) =
        p := funext fun z => if_pos h
    rw [hfun]
    exact isPMF_of_marginal r hr hm
  · have hfun : (fun z => if ∑ z', r (i, z') = 0 then p z else r (i, z) / ∑ z', r (i, z')) =
        fun z => r (i, z) / ∑ z', r (i, z') := funext fun z => if_neg h
    rw [hfun]
    have hpos : 0 ≤ ∑ z', r (i, z') := Finset.sum_nonneg fun z _ => hr.nonneg (i, z)
    refine ⟨fun z => div_nonneg (hr.nonneg (i, z)) hpos, ?_⟩
    unfold stoch_to_det.mass
    rw [← Finset.sum_div, div_self h]

omit [DecidableEq α] [DecidableEq β] in
/-- The mixture of the components with the label marginal is the observed law. -/
private theorem mixture_of_joint {p : α × β → ℝ} {ι : Type} [Fintype ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (hm : ∀ z, ∑ i, r (i, z) = p z) (z : α × β) :
    ∑ i, (∑ z', r (i, z')) *
        (if ∑ z', r (i, z') = 0 then p z else r (i, z) / ∑ z', r (i, z')) = p z :=
  (Finset.sum_congr rfl fun i _ => prior_mul_comp r hr i z).trans (hm z)

/-! ## A latent from a joint law of label and observation -/

/-- The latent whose joint law of label and observed pair is `r`. A label of zero mass gets
the component `p`, which the mixture weights by zero; such labels stay in the label type.
The label type is in `Type` because upstream `Latent` requires it. -/
def latentOfJoint {p : α × β → ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (hm : ∀ z, ∑ i, r (i, z) = p z) : Latent p where
  ι := ι
  fin := inferInstance
  dec := inferInstance
  prior i := ∑ z, r (i, z)
  comp i z := if ∑ z', r (i, z') = 0 then p z else r (i, z) / ∑ z', r (i, z')
  prior_isPMF := prior_isPMF_of_joint r hr
  comp_isPMF := comp_isPMF_of_joint r hr hm
  mixture := mixture_of_joint r hr hm

omit [DecidableEq α] [DecidableEq β] in
/-- The joint law of `latentOfJoint r` is `r`. -/
theorem latentOfJoint_joint {p : α × β → ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (hm : ∀ z, ∑ i, r (i, z) = p z) :
    (latentOfJoint r hr hm).joint = r := by
  funext w
  exact prior_mul_comp r hr w.1 w.2

/-- The score of the latent built from a joint law `r` is the sum of its three conditional
mutual informations under `r`. -/
theorem latentOfJoint_score {p : α × β → ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (hm : ∀ z, ∑ i, r (i, z) = p z) :
    (latentOfJoint r hr hm).score =
      condMutualInfo (fun a : ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) r
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2) r
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1) r := by
  have hj : stoch_to_det.Latent.joint (latentOfJoint r hr hm) = r := latentOfJoint_joint r hr hm
  exact congrArg (fun q : ι × (α × β) → ℝ =>
      condMutualInfo (fun a : ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) q
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2) q
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1) q) hj

/-- Any joint law of a finite label with the observed pair bounds the stochastic optimum by its
score. -/
theorem tau_le_of_joint {p : α × β → ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι × (α × β) → ℝ) (hr : IsPMF r) (hm : ∀ z, ∑ i, r (i, z) = p z) :
    tau p ≤
      condMutualInfo (fun a : ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) r
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2) r
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1) r :=
  (tau_le_score (latentOfJoint r hr hm)).trans_eq (latentOfJoint_score r hr hm)

/-! ## Information identities on one ambient law -/

section Toolkit

variable {Ω Ω' A B C D : Type*} [Fintype Ω] [Fintype Ω']
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

omit [Fintype Ω'] in
/-- A probability law lives on a nonempty type. -/
theorem nonempty_of_isPMF {m : Ω → ℝ} (hm : IsPMF m) : Nonempty Ω := by
  by_contra h
  let _ : IsEmpty Ω := not_nonempty_iff.mp h
  have htot := hm.total
  simp [stoch_to_det.mass] at htot

omit [Fintype Ω'] in
/-- A constant variable has zero entropy. -/
theorem entropyOf_const {m : Ω → ℝ} (hm : IsPMF m) (c : C) :
    entropyOf (fun _ : Ω => c) m = 0 := by
  have hsum : ∑ ω, m ω = 1 := by simpa [stoch_to_det.mass] using hm.total
  have hunit : stoch_to_det.Hvar (fun _ : Ω => ()) m = 0 := by
    simp [stoch_to_det.Hvar, stoch_to_det.H, stoch_to_det.push, stoch_to_det.mass, hsum]
  apply le_antisymm
  · exact (stoch_to_det.Hvar_comp_le hm (fun _ : Ω => ()) (fun _ => c)).trans_eq hunit
  · exact stoch_to_det.H_nonneg_of_isPMF (stoch_to_det.isPMF_push hm)

omit [Fintype Ω'] in
/-- Pairing a variable with a constant does not change its entropy. -/
private theorem entropyOf_pair_const {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (c : C) :
    entropyOf (fun ω => (f ω, c)) m = entropyOf f m :=
  stoch_to_det.Hvar_eq_of_leftInverse hm f (fun a => (a, c)) Prod.fst (fun _ => rfl)

omit [Fintype Ω'] in
/-- Appending a constant to a pair does not change its entropy. -/
private theorem entropyOf_triple_const {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B)
    (c : C) :
    entropyOf (fun ω => (f ω, g ω, c)) m = entropyOf (fun ω => (f ω, g ω)) m :=
  stoch_to_det.Hvar_eq_of_leftInverse hm (fun ω => (f ω, g ω)) (fun x => (x.1, x.2, c))
    (fun y => (y.1, y.2.1)) (fun _ => rfl)

omit [Fintype Ω'] in
/-- Conditioning on a constant: `I(f; g | c) = I(f; g)`. -/
theorem condMutualInfo_const_eq_mutualInfo {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B)
    (c : C) :
    condMutualInfo f g (fun _ => c) m = mutualInfo f g m := by
  have h1 := entropyOf_pair_const hm f c
  have h2 := entropyOf_pair_const hm g c
  have h3 := entropyOf_triple_const hm f g c
  have h4 := entropyOf_const hm c
  simp only [entropyOf] at h1 h2 h3 h4
  simp only [condMutualInfo, mutualInfo, stoch_to_det.condMI, stoch_to_det.MI]
  rw [h1, h2, h3, h4]
  ring

omit [Fintype Ω'] in
/-- A constant has zero conditional entropy: `H(c | g) = 0`. -/
private theorem condEntropy_const {m : Ω → ℝ} (hm : IsPMF m) (g : Ω → B) (c : C) :
    condEntropy (fun _ : Ω => c) g m = 0 := by
  have h : stoch_to_det.Hvar (fun ω => (c, g ω)) m = stoch_to_det.Hvar g m :=
    stoch_to_det.Hvar_eq_of_leftInverse hm g (fun b => (c, b)) Prod.snd (fun _ => rfl)
  simp only [condEntropy, stoch_to_det.condH]
  rw [h, sub_self]

omit [Fintype Ω'] in
/-- A variable is conditionally independent of anything given itself:
`I(f; g | f) = 0`. -/
theorem condMutualInfo_given_self_eq_zero {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) :
    condMutualInfo f g f m = 0 := by
  have h1 : stoch_to_det.Hvar (fun ω => (f ω, f ω)) m = stoch_to_det.Hvar f m :=
    stoch_to_det.Hvar_eq_of_leftInverse hm f (fun a => (a, a)) Prod.fst (fun _ => rfl)
  have h2 : stoch_to_det.Hvar (fun ω => (f ω, g ω, f ω)) m =
      stoch_to_det.Hvar (fun ω => (f ω, g ω)) m :=
    stoch_to_det.Hvar_eq_of_leftInverse hm (fun ω => (f ω, g ω)) (fun x => (x.1, x.2, x.1))
      (fun y => (y.1, y.2.1)) (fun _ => rfl)
  have h3 : entropyOf (fun ω => (g ω, f ω)) m = entropyOf (fun ω => (f ω, g ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => (f ω, g ω)) (Equiv.prodComm A B)
  simp only [entropyOf] at h3
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [h1, h2, h3]
  ring

omit [Fintype Ω'] in
/-- Recoding the conditioning variable by an equivalence preserves conditional mutual
information. -/
private theorem condMutualInfo_equiv_right {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B)
    (h : Ω → C) (e : C ≃ D) :
    condMutualInfo f g (fun ω => e (h ω)) m = condMutualInfo f g h m := by
  have h1 : entropyOf (fun ω => (f ω, e (h ω))) m = entropyOf (fun ω => (f ω, h ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => (f ω, h ω)) (Equiv.prodCongr (Equiv.refl A) e)
  have h2 : entropyOf (fun ω => (g ω, e (h ω))) m = entropyOf (fun ω => (g ω, h ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => (g ω, h ω)) (Equiv.prodCongr (Equiv.refl B) e)
  have h3 : entropyOf (fun ω => (f ω, g ω, e (h ω))) m =
      entropyOf (fun ω => (f ω, g ω, h ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => (f ω, g ω, h ω))
      (Equiv.prodCongr (Equiv.refl A) (Equiv.prodCongr (Equiv.refl B) e))
  have h4 : entropyOf (fun ω => e (h ω)) m = entropyOf h m := entropyOf_equiv hm h e
  simp only [entropyOf] at h1 h2 h3 h4
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [h1, h2, h3, h4]

omit [Fintype Ω'] in
/-- Recoding the conditioned variable by an equivalence preserves conditional entropy. -/
private theorem condEntropy_equiv_left {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B)
    (e : A ≃ D) :
    condEntropy (fun ω => e (f ω)) g m = condEntropy f g m := by
  have h1 : entropyOf (fun ω => (e (f ω), g ω)) m = entropyOf (fun ω => (f ω, g ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => (f ω, g ω)) (Equiv.prodCongr e (Equiv.refl B))
  simp only [entropyOf] at h1
  simp only [condEntropy, stoch_to_det.condH]
  rw [h1]

/-- Entropy of a variable under a law relabelled along a bijection `σ` with inverse `τ`. -/
private theorem entropyOf_comp_bij (m : Ω → ℝ) (σ : Ω' → Ω) (τ : Ω → Ω')
    (hστ : ∀ ω, σ (τ ω) = ω) (hτσ : ∀ w, τ (σ w) = w) (F : Ω' → A) :
    entropyOf F (fun w => m (σ w)) = entropyOf (fun ω => F (τ ω)) m := by
  unfold entropyOf stoch_to_det.Hvar
  congr 1
  funext c
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Fintype.sum_equiv ⟨σ, τ, hτσ, hστ⟩ _ _ (fun w => by simp [hτσ])

/-- Conditional mutual information under a law relabelled along a bijection. -/
private theorem condMutualInfo_comp_bij (m : Ω → ℝ) (σ : Ω' → Ω) (τ : Ω → Ω')
    (hστ : ∀ ω, σ (τ ω) = ω) (hτσ : ∀ w, τ (σ w) = w)
    (f : Ω' → A) (g : Ω' → B) (h : Ω' → C) :
    condMutualInfo f g h (fun w => m (σ w)) =
      condMutualInfo (fun ω => f (τ ω)) (fun ω => g (τ ω)) (fun ω => h (τ ω)) m := by
  have h1 := entropyOf_comp_bij m σ τ hστ hτσ (fun w => (f w, h w))
  have h2 := entropyOf_comp_bij m σ τ hστ hτσ (fun w => (g w, h w))
  have h3 := entropyOf_comp_bij m σ τ hστ hτσ (fun w => (f w, g w, h w))
  have h4 := entropyOf_comp_bij m σ τ hστ hτσ h
  simp only [entropyOf] at h1 h2 h3 h4
  unfold condMutualInfo stoch_to_det.condMI
  rw [h1, h2, h3, h4]

/-- Conditional entropy under a law relabelled along a bijection. -/
private theorem condEntropy_comp_bij (m : Ω → ℝ) (σ : Ω' → Ω) (τ : Ω → Ω')
    (hστ : ∀ ω, σ (τ ω) = ω) (hτσ : ∀ w, τ (σ w) = w)
    (f : Ω' → A) (g : Ω' → B) :
    condEntropy f g (fun w => m (σ w)) =
      condEntropy (fun ω => f (τ ω)) (fun ω => g (τ ω)) m := by
  have h1 := entropyOf_comp_bij m σ τ hστ hτσ (fun w => (f w, g w))
  have h2 := entropyOf_comp_bij m σ τ hστ hτσ g
  simp only [entropyOf] at h1 h2
  unfold condEntropy stoch_to_det.condH
  rw [h1, h2]

end Toolkit

/-! ## Any finite code bounds the deterministic optimum -/

/-- For a code type in `Type`: the upstream function latent is deterministic, so its
score bounds `T`. -/
private theorem T_le_functionScore_type {p : α × β → ℝ} (hp : IsPMF p)
    {γ : Type} [Fintype γ] [DecidableEq γ] (f : α × β → γ) :
    T p ≤ condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p
      + condEntropy f Prod.snd p := by
  rw [T_eq_upstream hp]
  have h := stoch_to_det.T_le_score (Latent.ofFunction hp f) (Latent.ofFunction_isDet hp f)
  exact h.trans_eq (Latent.ofFunction_score_eq_detScore hp f)

/-- The score of any function of the observed pair into a finite type bounds the
deterministic optimum. A code type outside `Type` is recoded through `Fin`. -/
theorem T_le_functionScore {p : α × β → ℝ} (hp : IsPMF p)
    {γ : Type*} [Fintype γ] [DecidableEq γ] (f : α × β → γ) :
    T p ≤ condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p
      + condEntropy f Prod.snd p := by
  have h := T_le_functionScore_type hp (fun z => Fintype.equivFin γ (f z))
  rwa [condMutualInfo_equiv_right hp, condEntropy_equiv_left hp,
    condEntropy_equiv_left hp] at h

/-! ## Transposing a law and a latent -/

omit [DecidableEq α] [DecidableEq β] in
/-- Transposing a probability law gives a probability law. -/
theorem isPMF_swap {q : α × β → ℝ} (hq : IsPMF q) :
    IsPMF (fun z : β × α => q z.swap) := by
  refine ⟨fun z => hq.nonneg z.swap, ?_⟩
  have htot : ∑ z, q z = 1 := by simpa [stoch_to_det.mass] using hq.total
  unfold stoch_to_det.mass
  exact ((Equiv.prodComm β α).sum_comp q).trans htot

omit [DecidableEq α] [DecidableEq β] in
/-- The transposed latent: same labels and prior, each component transposed. -/
def swapLatent {p : α × β → ℝ} (L : Latent p) : Latent (fun z : β × α => p z.swap) where
  ι := L.ι
  fin := L.fin
  dec := L.dec
  prior := L.prior
  comp := fun v z => L.comp v z.swap
  prior_isPMF := L.prior_isPMF
  comp_isPMF := fun v => isPMF_swap (L.comp_isPMF v)
  mixture := fun z => L.mixture z.swap

/-- Transposition preserves the latent score. -/
theorem swapLatent_score {p : α × β → ℝ} (L : Latent p) :
    (swapLatent L).score = L.score := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have e1 : condMutualInfo (fun w : L.ι × (β × α) => w.2.1) (fun w => w.2.2) (fun w => w.1)
        (fun w => L.joint (w.1, w.2.swap)) =
      condMutualInfo (fun w : L.ι × (α × β) => w.2.2) (fun w => w.2.1) (fun w => w.1)
        L.joint :=
    condMutualInfo_comp_bij L.joint (fun w : L.ι × (β × α) => (w.1, w.2.swap))
      (fun w : L.ι × (α × β) => (w.1, w.2.swap)) (fun _ => rfl) (fun _ => rfl) _ _ _
  have e2 : condMutualInfo (fun w : L.ι × (β × α) => w.1) (fun w => w.2.1) (fun w => w.2.2)
        (fun w => L.joint (w.1, w.2.swap)) =
      condMutualInfo (fun w : L.ι × (α × β) => w.1) (fun w => w.2.2) (fun w => w.2.1)
        L.joint :=
    condMutualInfo_comp_bij L.joint (fun w : L.ι × (β × α) => (w.1, w.2.swap))
      (fun w : L.ι × (α × β) => (w.1, w.2.swap)) (fun _ => rfl) (fun _ => rfl) _ _ _
  have e3 : condMutualInfo (fun w : L.ι × (β × α) => w.1) (fun w => w.2.2) (fun w => w.2.1)
        (fun w => L.joint (w.1, w.2.swap)) =
      condMutualInfo (fun w : L.ι × (α × β) => w.1) (fun w => w.2.1) (fun w => w.2.2)
        L.joint :=
    condMutualInfo_comp_bij L.joint (fun w : L.ι × (β × α) => (w.1, w.2.swap))
      (fun w : L.ι × (α × β) => (w.1, w.2.swap)) (fun _ => rfl) (fun _ => rfl) _ _ _
  have c1 := condMutualInfo_comm hJ (fun w : L.ι × (α × β) => w.2.2) (fun w => w.2.1)
    (fun w => w.1)
  show condMutualInfo (fun w : L.ι × (β × α) => w.2.1) (fun w => w.2.2) (fun w => w.1)
        (fun w => L.joint (w.1, w.2.swap))
      + condMutualInfo (fun w : L.ι × (β × α) => w.1) (fun w => w.2.1) (fun w => w.2.2)
        (fun w => L.joint (w.1, w.2.swap))
      + condMutualInfo (fun w : L.ι × (β × α) => w.1) (fun w => w.2.2) (fun w => w.2.1)
        (fun w => L.joint (w.1, w.2.swap)) =
    condMutualInfo (fun w : L.ι × (α × β) => w.2.1) (fun w => w.2.2) (fun w => w.1) L.joint
      + condMutualInfo (fun w : L.ι × (α × β) => w.1) (fun w => w.2.1) (fun w => w.2.2)
        L.joint
      + condMutualInfo (fun w : L.ι × (α × β) => w.1) (fun w => w.2.2) (fun w => w.2.1)
        L.joint
  rw [e1, e2, e3, c1]
  ring

/-- Transposition does not raise the stochastic optimum. -/
private theorem tau_swap_le {p : α × β → ℝ} (hp : IsPMF p) :
    tau (fun z : β × α => p z.swap) ≤ tau p := by
  obtain ⟨L0, _⟩ := exists_optimalLatent hp
  have : Nonempty (stoch_to_det.Latent p) := ⟨L0⟩
  show stoch_to_det.tau (fun z : β × α => p z.swap) ≤ stoch_to_det.tau p
  unfold stoch_to_det.tau
  refine le_ciInf fun L => ?_
  exact (stoch_to_det.tau_le_score (swapLatent L)).trans_eq (swapLatent_score L)

/-- Transposition does not raise the deterministic optimum. -/
private theorem T_swap_le {p : α × β → ℝ} (hp : IsPMF p) :
    T (fun z : β × α => p z.swap) ≤ T p := by
  obtain ⟨g, hg⟩ := exists_optimalCode p
  have h := T_le_functionScore_type (isPMF_swap hp) (fun w : β × α => g w.swap)
  have e1 : condMutualInfo (Prod.fst : β × α → β) Prod.snd (fun w => g w.swap)
        (fun z : β × α => p z.swap) = condMutualInfo Prod.snd Prod.fst g p :=
    condMutualInfo_comp_bij p Prod.swap Prod.swap (fun _ => rfl) (fun _ => rfl) _ _ _
  have e2 : condEntropy (fun w : β × α => g w.swap) Prod.fst (fun z : β × α => p z.swap) =
      condEntropy g Prod.snd p :=
    condEntropy_comp_bij p Prod.swap Prod.swap (fun _ => rfl) (fun _ => rfl) _ _
  have e3 : condEntropy (fun w : β × α => g w.swap) Prod.snd (fun z : β × α => p z.swap) =
      condEntropy g Prod.fst p :=
    condEntropy_comp_bij p Prod.swap Prod.swap (fun _ => rfl) (fun _ => rfl) _ _
  have c1 := condMutualInfo_comm hp (Prod.snd : α × β → β) Prod.fst g
  rw [e1, e2, e3, c1] at h
  rw [← hg]
  unfold detScore
  linarith

/-! ## Transposition -/

/-- Transposing a law preserves the stochastic optimum: `tau (p ∘ swap) = tau p`. -/
theorem tau_swap {p : α × β → ℝ} (hp : IsPMF p) :
    tau (fun z : β × α => p z.swap) = tau p := by
  refine le_antisymm (tau_swap_le hp) ?_
  exact tau_swap_le (isPMF_swap hp)

/-- Transposing a law preserves the deterministic optimum: `T (p ∘ swap) = T p`. -/
theorem T_swap {p : α × β → ℝ} (hp : IsPMF p) :
    T (fun z : β × α => p z.swap) = T p := by
  refine le_antisymm (T_swap_le hp) ?_
  have h := T_swap_le (p := fun z : β × α => p z.swap) (isPMF_swap hp)
  calc
    T p = T (fun z : α × β => p z.swap.swap) :=
      congrArg T (funext fun z => congrArg p (Prod.swap_swap z).symm)
    _ ≤ T (fun z : β × α => p z.swap) := h

/-! ## The three elementary bounds -/

/-- The constant code scores the mutual information `I(X; Y)`. -/
theorem detScore_constantCode_eq {p : α × β → ℝ} (hp : IsPMF p) :
    detScore p constantCode = mutualInfo Prod.fst Prod.snd p := by
  obtain ⟨z0⟩ := nonempty_of_isPMF hp
  have hc : (constantCode : Code α β) = fun _ => constantCode z0 := funext fun _ => rfl
  unfold detScore
  rw [hc, condMutualInfo_const_eq_mutualInfo hp, condEntropy_const hp, condEntropy_const hp]
  ring

/-- The constant code bounds the deterministic optimum: `T p ≤ I(X; Y)`. -/
theorem T_le_mutualInfo {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ mutualInfo Prod.fst Prod.snd p :=
  (T_le_detScore p constantCode).trans_eq (detScore_constantCode_eq hp)

/-- The row code `g = X` scores `H(X | Y)`. -/
theorem T_le_condEntropy_row {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ condEntropy Prod.fst Prod.snd p := by
  have h := T_le_functionScore hp (Prod.fst : α × β → α)
  have h1 : condMutualInfo (Prod.fst : α × β → α) Prod.snd Prod.fst p = 0 :=
    condMutualInfo_given_self_eq_zero hp _ _
  have h2 : condEntropy (Prod.fst : α × β → α) Prod.fst p = 0 :=
    condEntropy_function_eq_zero hp Prod.fst id
  rw [h1, h2] at h
  linarith

/-- The column code `g = Y` scores `H(Y | X)`. -/
theorem T_le_condEntropy_col {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ condEntropy Prod.snd Prod.fst p := by
  have h := T_le_functionScore hp (Prod.snd : α × β → β)
  have h1 : condMutualInfo (Prod.fst : α × β → α) Prod.snd Prod.snd p = 0 := by
    rw [condMutualInfo_comm hp]
    exact condMutualInfo_given_self_eq_zero hp _ _
  have h2 : condEntropy (Prod.snd : α × β → β) Prod.snd p = 0 :=
    condEntropy_function_eq_zero hp Prod.snd id
  rw [h1, h2] at h
  linarith

/-- The stochastic optimum is at most the mutual information: `tau p ≤ I(X; Y)`. -/
theorem tau_le_mutualInfo {p : α × β → ℝ} (hp : IsPMF p) :
    tau p ≤ mutualInfo Prod.fst Prod.snd p :=
  calc
    tau p ≤ stoch_to_det.T p := stoch_to_det.tau_le_T hp
    _ = T p := (T_eq_upstream hp).symm
    _ ≤ mutualInfo Prod.fst Prod.snd p := T_le_mutualInfo hp

end

end BinaryRow

end StochasticToDeterministicLatents
