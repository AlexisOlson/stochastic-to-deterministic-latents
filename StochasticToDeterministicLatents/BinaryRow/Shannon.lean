import StochasticToDeterministicLatents.Bridge

/-!
# Shannon toolkit for the binary-row bounds

Identities between the library's information quantities on one ambient law, used to move
between the latent's joint law and the laws built from it: a chain rule for the second
argument of a conditional mutual information, its symmetry, the exchange identity
`I(G;X) - I(L;X) = I(G;X|L) - I(L;X|G)`, the vanishing conditional entropy of a function of
the conditioner, and the transport of conditional mutual information along an arbitrary map
of the sample space. It also relabels a latent along an equivalence of its label type without
changing its score, and converts the entropy of a variable from bits to natural-log units.

Every information quantity here is in bits. The right-hand side of `log_two_mul_entropyOf` is
in natural-log units: bits times `Real.log 2`.

Nothing here is specific to binary alphabets. The equivalence-only transports already in the
library are `Binary.condMutualInfo_congr_equiv` and `Binary.condMutualInfo_pushforward`
(`Binary/Symmetry.lean`); `condMutualInfo_pushforward_comp` extends the latter to any map.
`relabelLatent L e` is, on binary cells, `Latent.reindex L e.symm`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
`condMutualInfo_chain_pair` and `mutualInfo_sub_mutualInfo`, with the private helpers
`pairEntropy_comm` and `tripleEntropy_reverse`, restate with the same proofs four private
lemmas of `Pricing` (the second as `mutualInfo_difference_in_conditionals` there); the rest is
original to this repository and uses only the upstream entropy interface.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ## Relabelling a latent along an equivalence -/

omit [DecidableEq α] [DecidableEq β] in
private theorem prior_isPMF_relabel {p : α × β → ℝ} (L : Latent p) {ι' : Type} [Fintype ι']
    (e : L.ι ≃ ι') : IsPMF (fun v : ι' => L.prior (e.symm v)) := by
  refine ⟨fun v => L.prior_isPMF.nonneg (e.symm v), ?_⟩
  unfold stoch_to_det.mass
  calc
    ∑ v, L.prior (e.symm v) = ∑ u, L.prior u := e.symm.sum_comp L.prior
    _ = 1 := by simpa [stoch_to_det.mass] using L.prior_isPMF.total

omit [DecidableEq α] [DecidableEq β] in
private theorem mixture_relabel {p : α × β → ℝ} (L : Latent p) {ι' : Type} [Fintype ι']
    (e : L.ι ≃ ι') (z : α × β) :
    ∑ v : ι', L.prior (e.symm v) * L.comp (e.symm v) z = p z := by
  calc
    ∑ v : ι', L.prior (e.symm v) * L.comp (e.symm v) z =
        ∑ u, L.prior u * L.comp u z :=
      e.symm.sum_comp (fun u => L.prior u * L.comp u z)
    _ = p z := L.mixture z

omit [DecidableEq α] [DecidableEq β] in
/-- Transport a latent along an equivalence `e` of its label type: the label `v` of the new
latent carries the prior weight and component law of the old label `e.symm v`. -/
def relabelLatent {p : α × β → ℝ} (L : Latent p) {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (e : L.ι ≃ ι') : Latent p where
  ι := ι'
  fin := inferInstance
  dec := inferInstance
  prior := fun v => L.prior (e.symm v)
  comp := fun v => L.comp (e.symm v)
  prior_isPMF := prior_isPMF_relabel L e
  comp_isPMF := fun v => L.comp_isPMF (e.symm v)
  mixture := mixture_relabel L e

omit [DecidableEq α] [DecidableEq β] in
/-- The observed law of any latent is a probability law: a mixture of probability laws with a
probability-law prior. -/
theorem isPMF_of_latent {p : α × β → ℝ} (L : Latent p) : IsPMF p := by
  refine ⟨fun z => ?_, ?_⟩
  · rw [← L.mixture z]
    exact Finset.sum_nonneg fun v _ =>
      mul_nonneg (L.prior_isPMF.nonneg v) ((L.comp_isPMF v).nonneg z)
  · have hcomp : ∀ v, ∑ z, L.comp v z = 1 := fun v => by
      simpa [stoch_to_det.mass] using (L.comp_isPMF v).total
    have hprior : ∑ v, L.prior v = 1 := by
      simpa [stoch_to_det.mass] using L.prior_isPMF.total
    unfold stoch_to_det.mass
    calc
      ∑ z, p z = ∑ z, ∑ v, L.prior v * L.comp v z :=
        Finset.sum_congr rfl fun z _ => (L.mixture z).symm
      _ = ∑ v, ∑ z, L.prior v * L.comp v z := Finset.sum_comm
      _ = ∑ v, L.prior v * ∑ z, L.comp v z :=
        Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ v, L.prior v := by simp [hcomp]
      _ = 1 := hprior

/-- Relabelling a latent along an equivalence of its label type preserves its score. -/
theorem relabelLatent_score {p : α × β → ℝ} (L : Latent p) {ι' : Type} [Fintype ι']
    [DecidableEq ι'] (e : L.ι ≃ ι') : (relabelLatent L e).score = L.score := by
  have hp : IsPMF p := isPMF_of_latent L
  rw [latent_score_eq hp (relabelLatent L e), latent_score_eq hp L]
  congr 1
  exact e.symm.sum_comp (fun u => L.prior u * Phi (L.comp u))

/-! ## Identities on one ambient law -/

section Toolkit

variable {Ω ι κ δ ε : Type*} [Fintype Ω]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype δ] [DecidableEq δ] [Fintype ε] [DecidableEq ε]

private theorem pairEntropy_comm
    {Ω κ δ : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → κ) (g : Ω → δ) :
    entropyOf (fun ω => (f ω, g ω)) m =
      entropyOf (fun ω => (g ω, f ω)) m := by
  symm
  simpa using entropyOf_equiv hm (fun ω => (f ω, g ω)) (Equiv.prodComm κ δ)

private theorem tripleEntropy_reverse
    {Ω κ δ ε : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → κ) (g : Ω → δ) (h : Ω → ε) :
    entropyOf (fun ω => (f ω, (g ω, h ω))) m =
      entropyOf (fun ω => (h ω, (g ω, f ω))) m := by
  let e : κ × (δ × ε) ≃ ε × (δ × κ) :=
    { toFun := fun a => (a.2.2, (a.2.1, a.1))
      invFun := fun a => (a.2.2, (a.2.1, a.1))
      left_inv := by intro a; rcases a with ⟨a, b, c⟩; rfl
      right_inv := by intro a; rcases a with ⟨c, b, a⟩; rfl }
  symm
  simpa [e] using entropyOf_equiv hm (fun ω => (f ω, (g ω, h ω))) e

private theorem tripleEntropy_swapFirst
    {Ω κ δ ε : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → κ) (g : Ω → δ) (h : Ω → ε) :
    entropyOf (fun ω => (f ω, (g ω, h ω))) m =
      entropyOf (fun ω => (g ω, (f ω, h ω))) m := by
  let e : κ × (δ × ε) ≃ δ × (κ × ε) :=
    { toFun := fun a => (a.2.1, (a.1, a.2.2))
      invFun := fun a => (a.2.1, (a.1, a.2.2))
      left_inv := by intro a; rcases a with ⟨a, b, c⟩; rfl
      right_inv := by intro a; rcases a with ⟨b, a, c⟩; rfl }
  symm
  simpa [e] using entropyOf_equiv hm (fun ω => (f ω, (g ω, h ω))) e

/-- Chain rule for the second argument of a conditional mutual information:
`I(L; (X,Y) | G) = I(L; X | G) + I(L; Y | X, G)`, in bits. -/
theorem condMutualInfo_chain_pair {m : Ω → ℝ} (hm : IsPMF m)
    (l : Ω → ι) (x : Ω → κ) (y : Ω → δ) (g : Ω → ε) :
    condMutualInfo l (fun ω => (x ω, y ω)) g m =
      condMutualInfo l x g m + condMutualInfo l y (fun ω => (x ω, g ω)) m := by
  let e : δ × (κ × ε) ≃ (κ × δ) × ε :=
    { toFun := fun a => ((a.2.1, a.1), a.2.2)
      invFun := fun a => (a.1.2, (a.1.1, a.2))
      left_inv := by intro a; rcases a with ⟨y, x, g⟩; rfl
      right_inv := by intro a; rcases a with ⟨⟨x, y⟩, g⟩; rfl }
  have hyxg :
      entropyOf (fun ω => (y ω, (x ω, g ω))) m =
        entropyOf (fun ω => ((x ω, y ω), g ω)) m := by
    symm
    simpa [e] using entropyOf_equiv hm (fun ω => (y ω, (x ω, g ω))) e
  have hlyxg :
      entropyOf (fun ω => (l ω, (y ω, (x ω, g ω)))) m =
        entropyOf (fun ω => (l ω, ((x ω, y ω), g ω))) m := by
    symm
    simpa [e] using entropyOf_equiv hm (fun ω => (l ω, (y ω, (x ω, g ω))))
      (Equiv.prodCongr (Equiv.refl ι) e)
  simp only [entropyOf] at hyxg hlyxg
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [hyxg, hlyxg]
  ring

/-- Conditional mutual information is symmetric in its first two arguments:
`I(f; g | h) = I(g; f | h)`. -/
theorem condMutualInfo_comm {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → ι) (g : Ω → κ) (h : Ω → ε) :
    condMutualInfo f g h m = condMutualInfo g f h m := by
  have htrip := tripleEntropy_swapFirst hm f g h
  simp only [entropyOf] at htrip
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [htrip]
  ring

/-- Exchanging which variable carries the information about `x`:
`I(G; X) - I(L; X) = I(G; X | L) - I(L; X | G)`. -/
theorem mutualInfo_sub_mutualInfo {m : Ω → ℝ} (hm : IsPMF m)
    (g : Ω → ι) (l : Ω → κ) (x : Ω → δ) :
    mutualInfo g x m - mutualInfo l x m =
      condMutualInfo g x l m - condMutualInfo l x g m := by
  have hgl := pairEntropy_comm hm g l
  have hxl := pairEntropy_comm hm x l
  have hxg := pairEntropy_comm hm x g
  have htrip := tripleEntropy_reverse hm g x l
  simp only [entropyOf] at hgl hxl hxg htrip
  simp only [mutualInfo, condMutualInfo, stoch_to_det.MI, stoch_to_det.condMI]
  rw [hgl, hxl, hxg, htrip]
  ring

private theorem entropyOf_graph {m : Ω → ℝ} (hm : IsPMF m) (g : Ω → κ) (φ : κ → ι) :
    entropyOf (fun ω => (φ (g ω), g ω)) m = entropyOf g m := by
  let enc : κ → ι × κ := fun a => (φ a, a)
  have h := stoch_to_det.Hvar_eq_of_leftInverse hm g enc Prod.snd (by intro a; rfl)
  simpa [enc, Function.comp_def] using h

/-- The conditional entropy of a function of the conditioning variable vanishes:
`H(φ(G) | G) = 0`. -/
theorem condEntropy_function_eq_zero {m : Ω → ℝ} (hm : IsPMF m)
    (g : Ω → κ) (φ : κ → ι) :
    condEntropy (fun ω => φ (g ω)) g m = 0 := by
  have hgraph := entropyOf_graph hm g φ
  simp only [entropyOf] at hgraph
  simp only [condEntropy, stoch_to_det.condH]
  rw [hgraph]
  ring

/-- The entropy of a variable on a law pushed forward along any map is the entropy of the
composed variable on the original law. -/
theorem entropyOf_pushforward_comp {Ω' A : Type*} [Fintype Ω'] [DecidableEq Ω']
    [Fintype A] [DecidableEq A] (m : Ω → ℝ) (φ : Ω → Ω') (f : Ω' → A) :
    entropyOf f (pushforward φ m) = entropyOf (fun ω => f (φ ω)) m := by
  unfold entropyOf stoch_to_det.Hvar pushforward
  rw [stoch_to_det.push_push]
  rfl

/-- Conditional mutual information of variables on a law pushed forward along any map is that
of the composed variables on the original law. `Binary.condMutualInfo_pushforward` is the
special case of an equivalence. -/
theorem condMutualInfo_pushforward_comp {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω']
    (m : Ω → ℝ) (φ : Ω → Ω')
    (f : Ω' → ι) (g : Ω' → κ) (h : Ω' → ε) :
    condMutualInfo f g h (pushforward φ m) =
      condMutualInfo (fun ω => f (φ ω)) (fun ω => g (φ ω)) (fun ω => h (φ ω)) m := by
  have hfh := entropyOf_pushforward_comp m φ (fun z => (f z, h z))
  have hgh := entropyOf_pushforward_comp m φ (fun z => (g z, h z))
  have hfgh := entropyOf_pushforward_comp m φ (fun z => (f z, g z, h z))
  have hh := entropyOf_pushforward_comp m φ h
  simp only [entropyOf] at hfh hgh hfgh hh
  unfold condMutualInfo stoch_to_det.condMI
  rw [hfh, hgh, hfgh, hh]

end Toolkit

/-! ## Bits to natural-log units -/

/-- The entropy of a variable in bits, times `Real.log 2`, is its natural-log entropy
`∑ a, negMulLog (P(f = a))`. -/
theorem log_two_mul_entropyOf {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) :
    Real.log 2 * entropyOf f m = ∑ a, Real.negMulLog (pushforward f m a) := by
  have hp := stoch_to_det.isPMF_push (f := f) hm
  have h := stoch_to_det.H_eq_negMulLog hp.isFinMeas
  rw [hp.total, Real.log_one, mul_zero, zero_add] at h
  unfold entropyOf stoch_to_det.Hvar
  exact h

end

end BinaryRow

end StochasticToDeterministicLatents
