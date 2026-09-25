import StochasticToDeterministicLatents.BinaryRow.Foundation

/-!
# Purification

For every finite latent `L` of a probability law `p` on any finite `α × β`, some function of the
observed pair into the latent's labels has deterministic score at most
`L.score + 3 H(L | X, Y)` (`exists_purifiedCode`). Hence
`T p ≤ L.score + 3 H(L | X, Y)` (`T_le_score_add_three_condEntropy`). The same inequality in
`Phi` form is `exists_purified_phi`, through the block formula for the score of a function
(`functionScore_eq`). Here `Phi` is `3 H(X,Y) - 2 H(X) - 2 H(Y)`. The inequality holds for every
labelling that minimises the per-cell objective `purifyObjective` (`IsPurifiedCode`,
`IsPurifiedCode.score_le`), and such a labelling exists (`exists_isPurifiedCode`).

All information quantities are in bits. The proof works in natural logarithms internally, and
the factor `Real.log 2` cancels.

## Proof outline

Write `U` for the latent label, `J` for the latent's joint law, and `C = f(X,Y)` for a
labelling. Expanding the definitions, the score of `f` minus `L.score + 3 H(U | X, Y)` is
`[2 H(C,X) + 2 H(C,Y) - H(C)] - [2 H(U,X) + 2 H(U,Y) - H(U)]`. In natural logarithms the `U`
side is the `J`-average of `log J_U(u) - 2 log J_UX(u,x) - 2 log J_UY(u,y)`
(`purifyObjective`). Choosing `f z` to minimise this objective over the labels of positive joint
mass at `z` makes the `p`-average of the chosen objective at most the `J`-average. The remaining
gap is two conditional divergences, each with weight 2, and one divergence with weight 3, each
nonnegative by `log t ≤ t - 1`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose latent
structure, function latents, and `T_le_score` these proofs use. The purification argument is
original to this repository.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ## Generic finite-sum helpers -/

/-- Gibbs core: `∑ m (log a - log b) ≤ ∑ m (a / b) - ∑ m`, from `log t ≤ t - 1`. -/
private theorem aux_sum_log_le {Ω : Type*} [Fintype Ω] (m : Ω → ℝ) (hm : ∀ ω, 0 ≤ m ω)
    (a b : Ω → ℝ) (hab : ∀ ω, m ω ≠ 0 → 0 < a ω ∧ 0 < b ω) :
    ∑ ω, m ω * (Real.log (a ω) - Real.log (b ω)) ≤ ∑ ω, m ω * (a ω / b ω) - ∑ ω, m ω := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases h : m ω = 0
  · simp [h]
  · obtain ⟨ha, hb⟩ := hab ω h
    have hlog : Real.log (a ω) - Real.log (b ω) ≤ a ω / b ω - 1 := by
      rw [← Real.log_div ha.ne' hb.ne']
      exact Real.log_le_sub_one_of_pos (div_pos ha hb)
    calc m ω * (Real.log (a ω) - Real.log (b ω)) ≤ m ω * (a ω / b ω - 1) :=
          mul_le_mul_of_nonneg_left hlog (hm ω)
      _ = m ω * (a ω / b ω) - m ω := by ring

/-- A pushforward of a nonnegative measure is nonnegative. -/
private theorem aux_push_nonneg {Ω A : Type*} [Fintype Ω] [DecidableEq A] {m : Ω → ℝ}
    (hm : ∀ ω, 0 ≤ m ω) (g : Ω → A) (a : A) : 0 ≤ stoch_to_det.push g m a :=
  Finset.sum_nonneg fun ω _ => hm ω

/-- A cell's mass is at most the mass of its fibre. -/
private theorem aux_le_push {Ω A : Type*} [Fintype Ω] [DecidableEq A] {m : Ω → ℝ}
    (hm : ∀ ω, 0 ≤ m ω) (g : Ω → A) (ω : Ω) : m ω ≤ stoch_to_det.push g m (g ω) := by
  unfold stoch_to_det.push
  exact Finset.single_le_sum (f := m) (fun a _ => hm a)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- The pushforward of a probability law sums to one. -/
private theorem aux_sum_push_eq_one {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    {m : Ω → ℝ} (hm : IsPMF m) (g : Ω → A) : ∑ a, stoch_to_det.push g m a = 1 := by
  have h := (stoch_to_det.isPMF_push (f := g) hm).total
  unfold stoch_to_det.mass at h
  exact h

/-- The first marginal of a law on a product, as a sum over the second coordinate. -/
private theorem aux_push_fst_apply {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : A × B → ℝ) (a : A) : stoch_to_det.push Prod.fst M a = ∑ b, M (a, b) := by
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- Summing the law of a pair over its second coordinate gives the law of the first. -/
private theorem aux_sum_push_pair {Ω A B : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (m : Ω → ℝ) (g1 : Ω → A) (g2 : Ω → B) (a : A) :
    ∑ b, stoch_to_det.push (fun ω => (g1 ω, g2 ω)) m (a, b) = stoch_to_det.push g1 m a :=
  (aux_push_fst_apply (stoch_to_det.push (fun ω => (g1 ω, g2 ω)) m) a).symm.trans
    (congrFun (stoch_to_det.push_push (fun ω => (g1 ω, g2 ω)) Prod.fst m) a)

/-- Ratio bound: `∑ m (Q ∘ g) / (push g m ∘ g) ≤ ∑ Q` for nonnegative `Q`. -/
private theorem aux_sum_ratio_push_le {Ω K : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
    (m : Ω → ℝ) (g : Ω → K) (Q : K → ℝ) (hQ : ∀ k, 0 ≤ Q k) :
    ∑ ω, m ω * (Q (g ω) / stoch_to_det.push g m (g ω)) ≤ ∑ k, Q k := by
  rw [← stoch_to_det.sum_push_mul g m (fun k => Q k / stoch_to_det.push g m k)]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h : stoch_to_det.push g m k = 0
  · rw [h, zero_mul]
    exact hQ k
  · exact le_of_eq (by field_simp)

/-- Entropy of a variable in natural-log units, as a single expectation:
`log 2 · H(g) = -∑ m(ω) log P_g(g ω)`. -/
private theorem aux_log_two_mul_Hvar {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    {m : Ω → ℝ} (hm : IsPMF m) (g : Ω → A) :
    Real.log 2 * stoch_to_det.Hvar g m =
      -∑ ω, m ω * Real.log (stoch_to_det.push g m (g ω)) := by
  calc Real.log 2 * stoch_to_det.Hvar g m
        = ∑ a, Real.negMulLog (stoch_to_det.push g m a) := log_two_mul_entropyOf hm g
    _ = ∑ a, -(stoch_to_det.push g m a * Real.log (stoch_to_det.push g m a)) :=
        Finset.sum_congr rfl fun a _ => by rw [Real.negMulLog]; ring
    _ = -∑ a, stoch_to_det.push g m a * Real.log (stoch_to_det.push g m a) := by
        rw [Finset.sum_neg_distrib]
    _ = -∑ ω, m ω * Real.log (stoch_to_det.push g m (g ω)) := by
        rw [stoch_to_det.sum_push_mul g m (fun a => Real.log (stoch_to_det.push g m a))]

/-! ## The latent's joint law -/

/-- The observed marginal of a latent's joint law is the observed law. -/
private theorem aux_push_snd_joint {p : α × β → ℝ} (L : Latent p) :
    stoch_to_det.push (fun w : L.ι × (α × β) => w.2) L.joint = p := by
  funext z
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simpa [Latent.joint, stoch_to_det.Latent.joint] using L.mixture z

/-- A variable of the observed pair has the same entropy under the joint law as under `p`. -/
private theorem aux_Hvar_snd_joint {p : α × β → ℝ} (L : Latent p) {A : Type*} [Fintype A]
    [DecidableEq A] (F : α × β → A) :
    stoch_to_det.Hvar (fun w : L.ι × (α × β) => F w.2) L.joint = stoch_to_det.Hvar F p := by
  have h := stoch_to_det.push_push (fun w : L.ι × (α × β) => w.2) F L.joint
  rw [aux_push_snd_joint L] at h
  exact (congrArg stoch_to_det.H h).symm

/-- Prior times `Phi` of a component is `Phi` of the unnormalised joint slice. -/
private theorem aux_prior_mul_Phi {p : α × β → ℝ} (L : Latent p) (v : L.ι) :
    L.prior v * Phi (L.comp v) = Phi (fun z => L.joint (v, z)) :=
  (stoch_to_det.Phi_smul (L.comp_isPMF v).isFinMeas (L.prior_isPMF.nonneg v)).symm

/-! ## Blocks of a function of the observed pair -/

/-- Mass times `Phi` of a normalised block law is `Phi` of the unnormalised block. -/
private theorem aux_mass_mul_Phi_block {p : α × β → ℝ} (hp : IsPMF p) {γ : Type*} [DecidableEq γ]
    (f : α × β → γ) (c : γ) :
    (∑ z, if f z = c then p z else 0) *
        Phi (fun z => if f z = c ∧ (∑ z', if f z' = c then p z' else 0) ≠ 0 then
          p z / (∑ z', if f z' = c then p z' else 0) else 0) =
      Phi (fun z => if f z = c then p z else 0) := by
  have hK : ∀ z, 0 ≤ (if f z = c then p z else 0) := fun z => by
    split_ifs
    · exact hp.nonneg z
    · exact le_rfl
  by_cases hS : (∑ z', if f z' = c then p z' else 0) = 0
  · have hzero : ∀ z, (if f z = c then p z else 0) = 0 := fun z =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hK z)).mp hS z (Finset.mem_univ z)
    have hfun : (fun z => if f z = c then p z else 0) = fun z => (0 : ℝ) * p z :=
      funext fun z => by rw [hzero z, zero_mul]
    rw [hS, zero_mul, hfun]
    exact ((stoch_to_det.Phi_smul hp.isFinMeas le_rfl).trans (zero_mul _)).symm
  · have hSnn : 0 ≤ (∑ z', if f z' = c then p z' else 0) :=
      Finset.sum_nonneg fun z _ => hK z
    have hfun : (fun z => if f z = c ∧ (∑ z', if f z' = c then p z' else 0) ≠ 0 then
          p z / (∑ z', if f z' = c then p z' else 0) else 0) =
        fun z => (∑ z', if f z' = c then p z' else 0)⁻¹ * (if f z = c then p z else 0) := by
      funext z
      by_cases hz : f z = c
      · simp [hz, hS, div_eq_inv_mul]
      · simp [hz]
    rw [hfun]
    have h := stoch_to_det.Phi_smul (m := fun z => if f z = c then p z else 0) hK
      (inv_nonneg.mpr hSnn)
    calc (∑ z', if f z' = c then p z' else 0) *
          stoch_to_det.Phi (fun z => (∑ z', if f z' = c then p z' else 0)⁻¹ *
            (if f z = c then p z else 0))
        = (∑ z', if f z' = c then p z' else 0) *
            ((∑ z', if f z' = c then p z' else 0)⁻¹ *
              stoch_to_det.Phi (fun z => if f z = c then p z else 0)) := by rw [h]
      _ = stoch_to_det.Phi (fun z => if f z = c then p z else 0) := by
          rw [← mul_assoc, mul_inv_cancel₀ hS, one_mul]

/-- The graph pushforward evaluated at a labelled cell. -/
private theorem aux_push_graph_apply (p : α × β → ℝ) {γ : Type*}
    [DecidableEq γ] (f : α × β → γ) (c : γ) (z : α × β) :
    stoch_to_det.push (fun z => (f z, z)) p (c, z) = if f z = c then p z else 0 := by
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Finset.sum_eq_single z]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ z) h

/-- The deterministic score `I(X;Y | C) + H(C | X) + H(C | Y)` of a function `C = f(X,Y)` is
`Psi p` minus the mass-weighted sum of `Phi` over the blocks of `f`; a block of zero mass
contributes zero. -/
theorem functionScore_eq {p : α × β → ℝ} (hp : IsPMF p)
    {γ : Type} [Fintype γ] [DecidableEq γ] (f : α × β → γ) :
    condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p + condEntropy f Prod.snd p =
      Psi p - ∑ c, (∑ z, if f z = c then p z else 0) *
        Phi (fun z => if f z = c ∧ (∑ z', if f z' = c then p z' else 0) ≠ 0 then
          p z / (∑ z', if f z' = c then p z' else 0) else 0) := by
  have h0 := Latent.ofFunction_score_eq_detScore hp f
  have h1 := latent_score_eq hp (Latent.ofFunction hp f)
  show stoch_to_det.detScore p f = _
  rw [← h0, h1]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (aux_prior_mul_Phi (Latent.ofFunction hp f) c).trans ?_
  rw [aux_mass_mul_Phi_block hp f c]
  congr 1
  funext z
  exact (congrFun (stoch_to_det.Latent.ofFunction_joint_eq_push hp f) (c, z)).trans
    (aux_push_graph_apply p f c z)

/-! ## Entropy bookkeeping -/

/-- The deterministic score in joint entropies:
`2 H(C,X) + 2 H(C,Y) - H(C) - H(X,Y) - H(X) - H(Y)`. -/
private theorem aux_detScore_eq {p : α × β → ℝ} (hp : IsPMF p) {γ : Type*} [Fintype γ]
    [DecidableEq γ] (f : α × β → γ) :
    condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p + condEntropy f Prod.snd p =
      2 * stoch_to_det.Hvar (fun z : α × β => (f z, z.1)) p
        + 2 * stoch_to_det.Hvar (fun z : α × β => (f z, z.2)) p
        - stoch_to_det.Hvar f p - stoch_to_det.Hvar (fun z : α × β => z) p
        - stoch_to_det.Hvar (Prod.fst : α × β → α) p
        - stoch_to_det.Hvar (Prod.snd : α × β → β) p := by
  have s1 : stoch_to_det.Hvar (fun z : α × β => (z.1, f z)) p =
      stoch_to_det.Hvar (fun z : α × β => (f z, z.1)) p :=
    stoch_to_det.Hvar_equiv hp (fun z : α × β => (f z, z.1)) (Equiv.prodComm γ α)
  have s2 : stoch_to_det.Hvar (fun z : α × β => (z.2, f z)) p =
      stoch_to_det.Hvar (fun z : α × β => (f z, z.2)) p :=
    stoch_to_det.Hvar_equiv hp (fun z : α × β => (f z, z.2)) (Equiv.prodComm γ β)
  have s3 : stoch_to_det.Hvar (fun z : α × β => (z.1, z.2, f z)) p =
      stoch_to_det.Hvar (fun z : α × β => z) p :=
    stoch_to_det.Hvar_eq_of_leftInverse hp (fun z : α × β => z) (fun z => (z.1, z.2, f z))
      (fun t => (t.1, t.2.1)) (fun z => rfl)
  simp only [condMutualInfo, condEntropy, stoch_to_det.condMI, stoch_to_det.condH]
  linarith

/-- The latent score plus `3 H(U | X,Y)` in joint entropies:
`2 H(U,X) + 2 H(U,Y) - H(U) - H(X,Y) - H(X) - H(Y)`. -/
private theorem aux_score_add_eq {p : α × β → ℝ} (L : Latent p) :
    L.score + 3 * condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2) L.joint =
      2 * stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.1)) L.joint
        + 2 * stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.2)) L.joint
        - stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.1) L.joint
        - stoch_to_det.Hvar (fun z : α × β => z) p
        - stoch_to_det.Hvar (Prod.fst : α × β → α) p
        - stoch_to_det.Hvar (Prod.snd : α × β → β) p := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have t1 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.2.1, w.1)) L.joint =
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.1)) L.joint :=
    stoch_to_det.Hvar_equiv hJ (fun w : L.ι × (α × β) => (w.1, w.2.1)) (Equiv.prodComm _ _)
  have t2 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.2.2, w.1)) L.joint =
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.2)) L.joint :=
    stoch_to_det.Hvar_equiv hJ (fun w : L.ι × (α × β) => (w.1, w.2.2)) (Equiv.prodComm _ _)
  let e3 : L.ι × (α × β) ≃ α × β × L.ι :=
    { toFun := fun a => (a.2.1, a.2.2, a.1)
      invFun := fun b => (b.2.2, (b.1, b.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have t3 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.2.1, w.2.2, w.1)) L.joint =
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2)) L.joint :=
    stoch_to_det.Hvar_equiv hJ (fun w : L.ι × (α × β) => (w.1, w.2)) e3
  have t4 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.1, w.2.2)) L.joint =
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2)) L.joint := rfl
  have t5 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.2, w.2.1)) L.joint =
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2)) L.joint :=
    stoch_to_det.Hvar_equiv hJ (fun w : L.ι × (α × β) => (w.1, w.2))
      (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))
  have t6 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.2.2, w.2.1)) L.joint =
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.2) L.joint :=
    stoch_to_det.Hvar_equiv hJ (fun w : L.ι × (α × β) => w.2) (Equiv.prodComm _ _)
  have t7 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.2.1, w.2.2)) L.joint =
      stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.2) L.joint := rfl
  have m1 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.2) L.joint =
      stoch_to_det.Hvar (fun z : α × β => z) p := aux_Hvar_snd_joint L (fun z => z)
  have m2 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.2.1) L.joint =
      stoch_to_det.Hvar (Prod.fst : α × β → α) p := aux_Hvar_snd_joint L Prod.fst
  have m3 : stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.2.2) L.joint =
      stoch_to_det.Hvar (Prod.snd : α × β → β) p := aux_Hvar_snd_joint L Prod.snd
  simp only [Latent.score, stoch_to_det.Latent.score, condEntropy, stoch_to_det.condMI,
    stoch_to_det.condH]
  linarith

/-! ## The cellwise minimiser -/

/-- The per-cell objective of label `u` at cell `z`, in natural-log units:
`log J_U(u) - 2 log J_UX(u, x) - 2 log J_UY(u, y)`, built from marginals of the joint law.
Only differences between labels at a fixed cell matter. At a cell `z` of positive mass and a
label `u` of positive joint mass there, it equals
`3 log q(z) - 2 log q_X(x) - 2 log q_Y(y) - 3 log θ_u(z)` minus `3 log p(z)`, where
`q = L.comp u` and `θ_u(z)` is the posterior of `u`; the difference does not depend on `u`. -/
def purifyObjective {p : α × β → ℝ} (L : Latent p) (u : L.ι) (z : α × β) : ℝ :=
  Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint u)
    - 2 * Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, w.2.1)) L.joint (u, z.1))
    - 2 * Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, w.2.2)) L.joint (u, z.2))

/-- A labelling by a minimiser of `purifyObjective` among the labels of positive joint mass. -/
private theorem aux_exists_argmin {p : α × β → ℝ} (L : Latent p) :
    ∃ f : α × β → L.ι, ∀ z, (p z ≠ 0 → L.joint (f z, z) ≠ 0) ∧
      ∀ u, L.joint (u, z) ≠ 0 → purifyObjective L (f z) z ≤ purifyObjective L u z := by
  have h : ∀ z, ∃ c : L.ι, (p z ≠ 0 → L.joint (c, z) ≠ 0) ∧
      ∀ u, L.joint (u, z) ≠ 0 → purifyObjective L c z ≤ purifyObjective L u z := by
    intro z
    by_cases hS : (Finset.univ.filter (fun u => L.joint (u, z) ≠ 0)).Nonempty
    · obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image _ (fun u => purifyObjective L u z) hS
      exact ⟨c, fun _ => (Finset.mem_filter.mp hc).2,
        fun u hu => hmin u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)⟩
    · refine ⟨Classical.arbitrary _, fun hpz => ?_, fun u hu => ?_⟩
      · exfalso
        apply hpz
        rw [← L.mixture z]
        refine Finset.sum_eq_zero fun u _ => ?_
        by_contra hne
        exact hS ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩
      · exact absurd ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩ hS
  choose f hf using h
  exact ⟨f, hf⟩

/-- Cellwise minimisation: the `p`-average of the chosen objective is at most the joint
average of the objective. -/
private theorem aux_sum_obj_le {p : α × β → ℝ} (L : Latent p) (f : α × β → L.ι)
    (hmin : ∀ z u, L.joint (u, z) ≠ 0 → purifyObjective L (f z) z ≤ purifyObjective L u z) :
    ∑ z, p z * purifyObjective L (f z) z ≤ ∑ w, L.joint w * purifyObjective L w.1 w.2 := by
  have e : ∑ w : L.ι × (α × β), L.joint w * purifyObjective L w.1 w.2 =
      ∑ z : α × β, ∑ u : L.ι, L.joint (u, z) * purifyObjective L u z :=
    (Fintype.sum_prod_type _).trans Finset.sum_comm
  rw [e]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [← L.mixture z, Finset.sum_mul]
  refine Finset.sum_le_sum fun u _ => ?_
  change L.joint (u, z) * purifyObjective L (f z) z ≤ L.joint (u, z) * purifyObjective L u z
  by_cases h : L.joint (u, z) = 0
  · rw [h, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hmin z u h) (L.joint_isPMF.nonneg _)

/-- The joint average of the objective, split into three log-marginal sums. -/
private theorem aux_sum_joint_obj {p : α × β → ℝ} (L : Latent p) :
    ∑ w, L.joint w * purifyObjective L w.1 w.2 =
      ∑ w, L.joint w * Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint w.1)
      - 2 * ∑ w, L.joint w * Real.log
          (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, w.2.1)) L.joint (w.1, w.2.1))
      - 2 * ∑ w, L.joint w * Real.log
          (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, w.2.2)) L.joint (w.1, w.2.2)) := by
  unfold purifyObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The `p`-average of the chosen objective, split into three log-marginal sums. -/
private theorem aux_sum_p_obj {p : α × β → ℝ} (L : Latent p) (f : α × β → L.ι) :
    ∑ z, p z * purifyObjective L (f z) z =
      ∑ z, p z * Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))
      - 2 * ∑ z, p z * Real.log
          (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, w.2.1)) L.joint (f z, z.1))
      - 2 * ∑ z, p z * Real.log
          (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, w.2.2)) L.joint (f z, z.2)) := by
  unfold purifyObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => by ring

/-! ## The divergence pieces -/

omit [DecidableEq α] [DecidableEq β] in
/-- A conditional divergence is nonnegative: with `C = f(Z)` and a coordinate `S = s(Z)`,
`∑ p [log P(C,S) + log J(U=C) - log J(U=C, S) - log P(C)] ≥ 0`. -/
private theorem aux_piece {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) (f : α × β → L.ι)
    (hf : ∀ z, p z ≠ 0 → L.joint (f z, z) ≠ 0) {K : Type*} [Fintype K] [DecidableEq K]
    (s : α × β → K) :
    0 ≤ ∑ z, p z * (Real.log (stoch_to_det.push (fun z => (f z, s z)) p (f z, s z))
      + Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))
      - Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z))
      - Real.log (stoch_to_det.push f p (f z))) := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have hpos : ∀ z, p z ≠ 0 →
      0 < stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z) ∧
      0 < stoch_to_det.push f p (f z) ∧
      0 < stoch_to_det.push (fun z => (f z, s z)) p (f z, s z) ∧
      0 < stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z) := by
    intro z hz
    have hpz : 0 < p z := lt_of_le_of_ne (hp.nonneg z) (Ne.symm hz)
    have hJz : 0 < L.joint (f z, z) := lt_of_le_of_ne (hJ.nonneg _) (Ne.symm (hf z hz))
    exact ⟨lt_of_lt_of_le hJz
        (aux_le_push hJ.nonneg (fun w : L.ι × (α × β) => (w.1, s w.2)) (f z, z)),
      lt_of_lt_of_le hpz (aux_le_push hp.nonneg f z),
      lt_of_lt_of_le hpz (aux_le_push hp.nonneg (fun z => (f z, s z)) z),
      lt_of_lt_of_le hJz (aux_le_push hJ.nonneg (fun w : L.ι × (α × β) => w.1) (f z, z))⟩
  have hlog := aux_sum_log_le p hp.nonneg
    (fun z => stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z) *
      stoch_to_det.push f p (f z))
    (fun z => stoch_to_det.push (fun z => (f z, s z)) p (f z, s z) *
      stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))
    (fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := hpos z hz
      exact ⟨mul_pos h1 h2, mul_pos h3 h4⟩)
  have hQ : ∀ k : L.ι × K, 0 ≤
      stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint k *
        stoch_to_det.push f p k.1 /
          stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint k.1 := fun k =>
    div_nonneg (mul_nonneg (aux_push_nonneg hJ.nonneg _ _) (aux_push_nonneg hp.nonneg _ _))
      (aux_push_nonneg hJ.nonneg _ _)
  have hQsum : ∑ k : L.ι × K,
      stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint k *
        stoch_to_det.push f p k.1 /
          stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint k.1 ≤ 1 := by
    calc ∑ k : L.ι × K,
          stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint k *
            stoch_to_det.push f p k.1 /
              stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint k.1
        = ∑ c : L.ι, ∑ t : K,
          stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (c, t) *
            stoch_to_det.push f p c /
              stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint c :=
          Fintype.sum_prod_type _
      _ = ∑ c : L.ι,
          (∑ t : K, stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (c, t)) *
            stoch_to_det.push f p c /
              stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint c :=
          Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul, Finset.sum_div]
      _ = ∑ c : L.ι,
          stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint c *
            stoch_to_det.push f p c /
              stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint c :=
          Finset.sum_congr rfl fun c _ => congrArg
            (fun t => t * stoch_to_det.push f p c /
              stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint c)
            (aux_sum_push_pair L.joint (fun w : L.ι × (α × β) => w.1)
              (fun w : L.ι × (α × β) => s w.2) c)
      _ ≤ ∑ c : L.ι, stoch_to_det.push f p c := by
          refine Finset.sum_le_sum fun c _ => ?_
          by_cases h : stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint c = 0
          · rw [h, zero_mul, zero_div]
            exact aux_push_nonneg hp.nonneg _ _
          · exact le_of_eq (by field_simp)
      _ = 1 := aux_sum_push_eq_one hp f
  have hratio : ∑ z, p z *
      (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z) *
          stoch_to_det.push f p (f z) /
        (stoch_to_det.push (fun z => (f z, s z)) p (f z, s z) *
          stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))) ≤ 1 := by
    calc ∑ z, p z *
          (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z) *
              stoch_to_det.push f p (f z) /
            (stoch_to_det.push (fun z => (f z, s z)) p (f z, s z) *
              stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z)))
        = ∑ z, p z *
          ((stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z) *
              stoch_to_det.push f p (f z) /
                stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z)) /
            stoch_to_det.push (fun z => (f z, s z)) p (f z, s z)) :=
          Finset.sum_congr rfl fun z _ => by ring
      _ ≤ _ := aux_sum_ratio_push_le p (fun z => (f z, s z)) _ hQ
      _ ≤ 1 := hQsum
  have hone : ∑ z, p z = 1 := hp.total
  have heq : ∑ z, p z * (Real.log (stoch_to_det.push (fun z => (f z, s z)) p (f z, s z))
      + Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))
      - Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z))
      - Real.log (stoch_to_det.push f p (f z))) =
      -∑ z, p z * (Real.log
        (stoch_to_det.push (fun w : L.ι × (α × β) => (w.1, s w.2)) L.joint (f z, s z) *
          stoch_to_det.push f p (f z)) -
        Real.log (stoch_to_det.push (fun z => (f z, s z)) p (f z, s z) *
          stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : p z = 0
    · simp [h]
    · obtain ⟨h1, h2, h3, h4⟩ := hpos z h
      rw [Real.log_mul h1.ne' h2.ne', Real.log_mul h3.ne' h4.ne']
      ring
  rw [heq]
  linarith

omit [DecidableEq α] [DecidableEq β] in
/-- An ordinary divergence is nonnegative: `∑ p [log P(C) - log J(U=C)] ≥ 0`. -/
private theorem aux_piece_c {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) (f : α × β → L.ι)
    (hf : ∀ z, p z ≠ 0 → L.joint (f z, z) ≠ 0) :
    0 ≤ ∑ z, p z * (Real.log (stoch_to_det.push f p (f z))
      - Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))) := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have hlog := aux_sum_log_le p hp.nonneg
    (fun z => stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))
    (fun z => stoch_to_det.push f p (f z))
    (fun z hz => by
      have hpz : 0 < p z := lt_of_le_of_ne (hp.nonneg z) (Ne.symm hz)
      have hJz : 0 < L.joint (f z, z) := lt_of_le_of_ne (hJ.nonneg _) (Ne.symm (hf z hz))
      exact ⟨lt_of_lt_of_le hJz
          (aux_le_push hJ.nonneg (fun w : L.ι × (α × β) => w.1) (f z, z)),
        lt_of_lt_of_le hpz (aux_le_push hp.nonneg f z)⟩)
  have hratio : ∑ z, p z * (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z) /
      stoch_to_det.push f p (f z)) ≤ 1 :=
    (aux_sum_ratio_push_le p f
      (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint)
      (aux_push_nonneg hJ.nonneg _)).trans_eq (aux_sum_push_eq_one hJ _)
  have hone : ∑ z, p z = 1 := hp.total
  have heq : ∑ z, p z * (Real.log (stoch_to_det.push f p (f z))
      - Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))) =
      -∑ z, p z * (Real.log (stoch_to_det.push (fun w : L.ι × (α × β) => w.1) L.joint (f z))
        - Real.log (stoch_to_det.push f p (f z))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [heq]
  linarith

/-! ## The core inequality -/

/-- For the minimising labelling, `2 H(C,X) + 2 H(C,Y) - H(C) ≤ 2 H(U,X) + 2 H(U,Y) - H(U)`. -/
private theorem aux_core {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) (f : α × β → L.ι)
    (hf : ∀ z, (p z ≠ 0 → L.joint (f z, z) ≠ 0) ∧
      ∀ u, L.joint (u, z) ≠ 0 → purifyObjective L (f z) z ≤ purifyObjective L u z) :
    2 * stoch_to_det.Hvar (fun z : α × β => (f z, z.1)) p
        + 2 * stoch_to_det.Hvar (fun z : α × β => (f z, z.2)) p
        - stoch_to_det.Hvar f p ≤
      2 * stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.1)) L.joint
        + 2 * stoch_to_det.Hvar (fun w : L.ι × (α × β) => (w.1, w.2.2)) L.joint
        - stoch_to_det.Hvar (fun w : L.ι × (α × β) => w.1) L.joint := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  have hκ : 0 < Real.log 2 := Real.log_pos one_lt_two
  have eA1 := aux_log_two_mul_Hvar hp (fun z : α × β => (f z, z.1))
  have eA2 := aux_log_two_mul_Hvar hp (fun z : α × β => (f z, z.2))
  have eA0 := aux_log_two_mul_Hvar hp f
  have eB1 := aux_log_two_mul_Hvar hJ (fun w : L.ι × (α × β) => (w.1, w.2.1))
  have eB2 := aux_log_two_mul_Hvar hJ (fun w : L.ι × (α × β) => (w.1, w.2.2))
  have eB0 := aux_log_two_mul_Hvar hJ (fun w : L.ι × (α × β) => w.1)
  have hobjJ := aux_sum_joint_obj L
  have hobjp := aux_sum_p_obj L f
  have hcell := aux_sum_obj_le L f (fun z u h => (hf z).2 u h)
  have ha := aux_piece hp L f (fun z => (hf z).1) (Prod.fst : α × β → α)
  have hb := aux_piece hp L f (fun z => (hf z).1) (Prod.snd : α × β → β)
  have hc := aux_piece_c hp L f (fun z => (hf z).1)
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at ha hb hc
  apply (mul_le_mul_iff_of_pos_left hκ).mp
  linarith

/-! ## Purified codes -/

/-- A purified code of `L`: at every cell of positive mass it picks a label of positive joint
mass there, and that label minimises `purifyObjective L · z` among the labels of positive joint
mass at `z`. At a cell of zero mass any label is allowed. -/
def IsPurifiedCode {p : α × β → ℝ} (L : Latent p) (f : α × β → L.ι) : Prop :=
  ∀ z, (p z ≠ 0 → L.joint (f z, z) ≠ 0) ∧
    ∀ u, L.joint (u, z) ≠ 0 → purifyObjective L (f z) z ≤ purifyObjective L u z

/-- Every latent has a purified code. -/
theorem exists_isPurifiedCode {p : α × β → ℝ} (L : Latent p) :
    ∃ f : α × β → L.ι, IsPurifiedCode L f :=
  aux_exists_argmin L

/-- Purification for a given purified code: its score is at most `L.score + 3 H(L | X, Y)`,
in bits. -/
theorem IsPurifiedCode.score_le {p : α × β → ℝ} (hp : IsPMF p) {L : Latent p}
    {f : α × β → L.ι} (hf : IsPurifiedCode L f) :
    condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p + condEntropy f Prod.snd p ≤
      L.score + 3 * condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2) L.joint := by
  rw [aux_detScore_eq hp f, aux_score_add_eq L]
  have := aux_core hp L f hf
  linarith

/-- Purification in score form. -/
private theorem aux_exists_purified_score {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) :
    ∃ f : α × β → L.ι,
      condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p + condEntropy f Prod.snd p ≤
        L.score + 3 * condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2) L.joint := by
  obtain ⟨f, hf⟩ := exists_isPurifiedCode L
  exact ⟨f, hf.score_le hp⟩

/-- Purification in `Phi` form: some labelling of the observed pair by the latent's labels has
block-averaged `Phi` at least the latent's prior-averaged `Phi` minus `3 H(L | X, Y)`, in
bits. -/
theorem exists_purified_phi {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) :
    ∃ f : α × β → L.ι,
      ∑ v, L.prior v * Phi (L.comp v) ≤
        ∑ c, (∑ z, if f z = c then p z else 0) *
          Phi (fun z => if f z = c ∧ (∑ z', if f z' = c then p z' else 0) ≠ 0 then
            p z / (∑ z', if f z' = c then p z' else 0) else 0)
        + 3 * condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2) L.joint := by
  obtain ⟨f, hf⟩ := aux_exists_purified_score hp L
  refine ⟨f, ?_⟩
  have h1 := functionScore_eq hp f
  have h2 := latent_score_eq hp L
  linarith

/-- Purification: for every finite latent `L`, some function of the observed pair into `L`'s
labels has deterministic score at most `L.score + 3 H(L | X, Y)`, in bits. -/
theorem exists_purifiedCode {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) :
    ∃ f : α × β → L.ι,
      condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p + condEntropy f Prod.snd p ≤
        L.score + 3 * condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2) L.joint := by
  obtain ⟨f, hf⟩ := exists_purified_phi hp L
  refine ⟨f, ?_⟩
  have h1 := functionScore_eq hp f
  have h2 := latent_score_eq hp L
  linarith

/-- For every finite latent `L` of a probability law `p`,
`T p ≤ L.score + 3 H(L | X, Y)`, with the conditional entropy of the label given the observed
pair taken under `L.joint`, in bits. -/
theorem T_le_score_add_three_condEntropy {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) :
    T p ≤ L.score + 3 * condEntropy (fun a : L.ι × (α × β) => a.1) (fun a => a.2) L.joint := by
  obtain ⟨f, hf⟩ := exists_purifiedCode hp L
  exact (T_le_functionScore hp f).trans hf

end

end BinaryRow

end StochasticToDeterministicLatents
