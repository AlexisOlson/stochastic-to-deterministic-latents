import StochasticToDeterministicLatents.Information
import stoch_to_det.Functionals

/-!
# Finite stochastic latents

This module exposes finite-mixture latents, their scores, and the stochastic
optimum. Reducible aliases keep these objects definitionally identical to
the pinned foundation, so later pricing and binary arguments can use its
representation and proofs directly.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Definitions are exposed through reducible aliases and theorem wrappers;
the upstream implementation is not copied.
-/

namespace StochasticToDeterministicLatents

/-- A finite mixture representation of a joint law `p` on `α × β`. -/
abbrev Latent {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) :=
  stoch_to_det.Latent p

namespace Latent

variable {α β : Type*} [Fintype α] [Fintype β]
variable {p : α × β → ℝ}

/-- The joint law of the latent label and the observed pair. -/
noncomputable abbrev joint (L : Latent p) : L.ι × (α × β) → ℝ :=
  stoch_to_det.Latent.joint L

/-- The joint law associated with a latent is a probability mass function. -/
theorem joint_isPMF (L : Latent p) : IsPMF L.joint := by
  classical
  exact stoch_to_det.Latent.joint_isPMF L

variable [DecidableEq α] [DecidableEq β]

/-- The stochastic latent score
`I(X;Y | L) + I(L;X | Y) + I(L;Y | X)`. -/
noncomputable abbrev score (L : Latent p) : ℝ :=
  stoch_to_det.Latent.score L

/-- Every finite stochastic latent has nonnegative score. -/
theorem score_nonneg (L : Latent p) : 0 ≤ L.score :=
  stoch_to_det.Latent.score_nonneg L

end Latent

/-- The stochastic optimum: the infimum of `Latent.score` over finite mixture
representations of `p`. -/
noncomputable abbrev tau {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (p : α × β → ℝ) : ℝ :=
  stoch_to_det.tau p

/-- The stochastic optimum is nonnegative. -/
theorem tau_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (p : α × β → ℝ) : 0 ≤ tau p :=
  stoch_to_det.tau_nonneg p

/-- The stochastic optimum is at most the score of every supplied latent. -/
theorem tau_le_score {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {p : α × β → ℝ} (L : Latent p) :
    tau p ≤ L.score :=
  stoch_to_det.tau_le_score L

end StochasticToDeterministicLatents
