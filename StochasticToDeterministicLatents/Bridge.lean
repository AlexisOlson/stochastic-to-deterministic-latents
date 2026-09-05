import StochasticToDeterministicLatents.Latent
import StochasticToDeterministicLatents.Deterministic
import stoch_to_det.Envelope
import stoch_to_det.Duality
import stoch_to_det.Seed
import stoch_to_det.Quotient

/-!
# Bridge to upstream envelope machinery

This module is the library's only import point for the upstream envelope,
duality, seed, and quotient machinery. It exposes attained stochastic
optimizers and contact data, and identifies the local deterministic score
and optimum with their upstream definitions. Its definitions are reducible
aliases; its theorems are definitional bridges or exact restatements.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
The upstream interfaces are adapted as public aliases and exact theorem
wrappers, with the two local-objective identification bridges.
-/

namespace StochasticToDeterministicLatents

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-! ## Objective bridges and envelope identity -/

/-- The public deterministic score is definitionally the upstream score on
the canonical code alphabet. -/
theorem detScore_eq_upstream (p : α × β → ℝ) (g : Code α β) :
    detScore p g = stoch_to_det.detScore p g :=
  rfl

/-- On probability laws, the public code-space optimum equals the upstream
optimum over bundled deterministic latents. -/
theorem T_eq_upstream {p : α × β → ℝ} (hp : IsPMF p) :
    T p = stoch_to_det.T p := by
  rw [stoch_to_det.T_eq_iInf_detScore_codes hp]
  rfl

/-- The entropy combination `Ψ(p) = 2 H(X,Y) - H(X) - H(Y)`, in bits. -/
noncomputable abbrev Psi (p : α × β → ℝ) : ℝ :=
  stoch_to_det.Psi p

/-- The entropy combination `Φ(p) = 3 H(X,Y) - 2 H(X) - 2 H(Y)`, in bits. -/
noncomputable abbrev Phi (p : α × β → ℝ) : ℝ :=
  stoch_to_det.Phi p

/-- The stochastic optimum is attained by a finite latent. -/
theorem exists_optimalLatent {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ L : Latent p, L.score = tau p :=
  stoch_to_det.exists_tau_optimal_latent hp

/-- A latent score is `Ψ(p)` minus the prior average of `Φ` over its
component laws. -/
theorem latent_score_eq {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p) :
    L.score = Psi p - ∑ v, L.prior v * Phi (L.comp v) :=
  stoch_to_det.Latent.score_eq hp L

/-! ## Continuity of entropy -/

/-- Entropy in bits written through `Real.negMulLog`, which is continuous on
all of `γ → ℝ`; it agrees with `entropy` on probability laws. -/
noncomputable abbrev continuousEntropy {γ : Type*} [Fintype γ] (m : γ → ℝ) : ℝ :=
  stoch_to_det.continuousEntropy m

/-- On a probability law the two entropy expressions agree. -/
theorem entropy_eq_continuousEntropy {γ : Type*} [Fintype γ] {m : γ → ℝ}
    (hm : IsPMF m) : entropy m = continuousEntropy m :=
  stoch_to_det.H_eq_continuousEntropy hm

/-- The `negMulLog` entropy expression is continuous. -/
theorem continuous_continuousEntropy {γ : Type*} [Fintype γ] :
    Continuous (continuousEntropy : (γ → ℝ) → ℝ) :=
  stoch_to_det.continuous_continuousEntropy

/-- Pushing a measure forward along a map is continuous in the measure. -/
theorem continuous_pushforward {γ δ : Type*} [Fintype γ] [Fintype δ]
    [DecidableEq δ] (f : γ → δ) :
    Continuous (fun m : γ → ℝ => pushforward f m) :=
  stoch_to_det.continuous_push_map f

/-! ## Function-induced deterministic latents -/

namespace Latent

/-- The predicate that a latent is a deterministic function of its observed
pair. -/
abbrev IsDet {p : α × β → ℝ} (L : Latent p) : Prop :=
  stoch_to_det.Latent.IsDet L

/-- The finite latent induced by a deterministic function of the observed
pair. -/
noncomputable abbrev ofFunction {p : α × β → ℝ}
    {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) : Latent p :=
  stoch_to_det.Latent.ofFunction hp f

/-- A function-induced latent is deterministic. -/
theorem ofFunction_isDet {p : α × β → ℝ}
    {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) :
    (ofFunction hp f).IsDet :=
  stoch_to_det.Latent.ofFunction_isDet hp f

/-- The score of a function-induced latent is the upstream deterministic
score of that function. -/
theorem ofFunction_score_eq_detScore {p : α × β → ℝ}
    {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) :
    (ofFunction hp f).score = stoch_to_det.detScore p f :=
  stoch_to_det.Latent.ofFunction_score_eq_detScore hp f

end Latent

/-! ## Duality and contacts -/

/-- The support of a law: the cells carrying nonzero mass. -/
noncomputable abbrev support (m : α × β → ℝ) : Finset (α × β) :=
  stoch_to_det.support m

/-- A cell set is connected when any two of its cells are joined by a chain of
cells of the set, consecutive cells sharing a row or a column. -/
abbrev IsConnected (S : Finset (α × β)) : Prop :=
  stoch_to_det.IsConnected S

/-- The dual kernel functional `Λ_w(u,v)` on a finite support. -/
noncomputable abbrev Lambda (S : Finset (α × β)) (w : α × β → ℝ)
    (u : α → ℝ) (v : β → ℝ) : ℝ :=
  stoch_to_det.Lambda S w u v

/-- The predicate that a kernel is strictly positive on the given cell set and
satisfies `Lambda S w u v ≤ 1` for every pair of probability laws `u` on the
rows and `v` on the columns. -/
abbrev Feasible (S : Finset (α × β)) (w : α × β → ℝ) : Prop :=
  stoch_to_det.Feasible S w

/-- The predicate that a probability law is a contact of a kernel on a
specified support. -/
abbrev IsContact (S : Finset (α × β)) (w : α × β → ℝ)
    (q : α × β → ℝ) : Prop :=
  stoch_to_det.IsContact S w q

/-- A contact of a feasible kernel on a connected cell set has support exactly
that set. -/
theorem contact_support_eq {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q : α × β → ℝ} (hq : IsContact S w q) :
    support q = S :=
  stoch_to_det.contact_support_eq hw hS hq

/-! ## Seed setup -/

/-- A probability law with connected support, a latent attaining the stochastic
optimum with strictly positive prior, and a feasible kernel of which every
component law of that latent is a contact. -/
abbrev SeedSetup (p : α × β → ℝ) :=
  stoch_to_det.SeedSetup p

/-- A seed setup exists for every probability law with connected support. -/
theorem exists_seedSetup {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) : Nonempty (SeedSetup p) :=
  stoch_to_det.exists_seedSetup hp hconn

namespace SeedSetup

variable {p : α × β → ℝ}

/-- The attained stochastic latent in a seed setup. -/
abbrev L (D : SeedSetup p) : Latent p :=
  stoch_to_det.SeedSetup.L D

/-- The feasible common-contact kernel in a seed setup. -/
abbrev w (D : SeedSetup p) : α × β → ℝ :=
  stoch_to_det.SeedSetup.w D

/-- The setup's latent attains the stochastic optimum. -/
theorem optimal (D : SeedSetup p) : D.L.score = tau p :=
  stoch_to_det.SeedSetup.optimal D

/-- Every positive latent component is a contact of the setup's kernel. -/
theorem contact (D : SeedSetup p) :
    ∀ v, D.L.prior v ≠ 0 → IsContact (support p) D.w (D.L.comp v) :=
  stoch_to_det.SeedSetup.contact D

/-- The setup's kernel is feasible. -/
theorem feasible (D : SeedSetup p) : Feasible (support p) D.w :=
  stoch_to_det.SeedSetup.feasible D

/-- The law's support is connected. -/
theorem conn (D : SeedSetup p) : IsConnected (support p) :=
  stoch_to_det.SeedSetup.conn D

/-- Every prior weight in the setup is strictly positive. -/
theorem prior_pos (D : SeedSetup p) : ∀ v, 0 < D.L.prior v :=
  stoch_to_det.SeedSetup.prior_pos D

/-- The setup's observed law is a probability mass function. -/
theorem isPMF (D : SeedSetup p) : IsPMF p :=
  stoch_to_det.SeedSetup.isPMF D

end SeedSetup

/-! ## Quotient by equal component laws -/

/-- A quotient of latent labels whose clusters are exactly the equal-component
fibres. -/
abbrev Clustering {p : α × β → ℝ} (D : SeedSetup p) : Type 1 :=
  stoch_to_det.Clustering D

namespace Clustering

variable {p : α × β → ℝ} {D : SeedSetup p}

/-- The finite cluster index type. -/
abbrev κ (K : Clustering D) : Type :=
  stoch_to_det.Clustering.κ K

/-- The map from latent labels to cluster indices. -/
abbrev cl (K : Clustering D) : D.L.ι → K.κ :=
  stoch_to_det.Clustering.cl K

/-- The common component probability law of a cluster. -/
noncomputable abbrev Q (K : Clustering D) (c : K.κ) : α × β → ℝ :=
  stoch_to_det.Clustering.Q K c

/-- The total prior mass of a cluster. -/
noncomputable abbrev s (K : Clustering D) (c : K.κ) : ℝ :=
  stoch_to_det.Clustering.s K c

/-- Two labels share a cluster exactly when their component laws coincide. -/
theorem spec (K : Clustering D) (ℓ ℓ' : D.L.ι) :
    K.cl ℓ = K.cl ℓ' ↔ D.L.comp ℓ = D.L.comp ℓ' :=
  stoch_to_det.Clustering.spec K ℓ ℓ'

/-- The cluster map is surjective. -/
theorem surj (K : Clustering D) : Function.Surjective K.cl :=
  stoch_to_det.Clustering.surj K

/-- Distinct clusters have distinct component laws. -/
theorem Q_injective (K : Clustering D) : Function.Injective K.Q :=
  stoch_to_det.Clustering.Q_injective K

/-- Every cluster component law is a contact of the setup's kernel. -/
theorem Q_isContact (K : Clustering D) (c : K.κ) :
    IsContact (support p) D.w (K.Q c) :=
  stoch_to_det.Clustering.Q_isContact K c

end Clustering

/-- Every seed setup admits a clustering of its latent labels. -/
theorem exists_clustering {p : α × β → ℝ} (D : SeedSetup p) :
    Nonempty (Clustering D) :=
  stoch_to_det.exists_clustering D

end StochasticToDeterministicLatents
