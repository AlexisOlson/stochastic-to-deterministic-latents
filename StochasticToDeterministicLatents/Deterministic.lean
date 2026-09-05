import StochasticToDeterministicLatents.Information

/-!
# Deterministic codes and their objective

This module gives a code-first formulation of the deterministic optimization
problem. A code uses a fixed alphabet with one label available for every
observation cell, which is enough to represent every partition of the finite
observation space.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
The deterministic objective is rewritten over the public canonical code
alphabet.
-/

namespace StochasticToDeterministicLatents

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- A canonical finite deterministic code on the observation space. There is one
available label for every observation cell. -/
abbrev Code (α β : Type*) [Fintype α] [Fintype β] :=
  α × β → Fin (Fintype.card (α × β))

/-- The deterministic score
`I(X;Y | g) + H(g | X) + H(g | Y)` under the joint law `p`. -/
noncomputable def detScore (p : α × β → ℝ) (g : Code α β) : ℝ :=
  condMutualInfo Prod.fst Prod.snd g p
    + condEntropy g Prod.fst p
    + condEntropy g Prod.snd p

/-- The best deterministic score over the canonical finite code space. -/
noncomputable def T (p : α × β → ℝ) : ℝ :=
  ⨅ g : Code α β, detScore p g

/-- The constant code. On an empty observation space this is the unique empty
function; every actual input cell itself witnesses that label `0` is available. -/
def constantCode : Code α β :=
  fun z => ⟨0, Fintype.card_pos_iff.mpr ⟨z⟩⟩

private theorem exists_minimalCode (p : α × β → ℝ) :
    ∃ g : Code α β, ∀ h : Code α β, detScore p g ≤ detScore p h := by
  classical
  let g₀ : Code α β := constantCode
  have hcodes : (Finset.univ : Finset (Code α β)).Nonempty :=
    ⟨g₀, Finset.mem_univ _⟩
  obtain ⟨g, _hg, hminimal⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset (Code α β)) (fun h => detScore p h) hcodes
  exact ⟨g, fun h => hminimal h (Finset.mem_univ _)⟩

/-- The deterministic score of any code is nonnegative under a probability law. -/
theorem detScore_nonneg {p : α × β → ℝ} (hp : IsPMF p) (g : Code α β) :
    0 ≤ detScore p g := by
  unfold detScore
  exact add_nonneg
    (add_nonneg
      (condMutualInfo_nonneg hp Prod.fst Prod.snd g)
      (condEntropy_nonneg hp g Prod.fst))
    (condEntropy_nonneg hp g Prod.snd)

/-- The optimum is at most the score of any supplied canonical code. -/
theorem T_le_detScore (p : α × β → ℝ) (g : Code α β) :
    T p ≤ detScore p g := by
  obtain ⟨g₀, hminimal⟩ := exists_minimalCode p
  unfold T
  have hb : BddBelow (Set.range fun h : Code α β => detScore p h) :=
    ⟨detScore p g₀, by
      rintro _ ⟨h, rfl⟩
      exact hminimal h⟩
  exact ciInf_le hb g

/-- The deterministic optimum is nonnegative under a probability law. -/
theorem T_nonneg {p : α × β → ℝ} (hp : IsPMF p) : 0 ≤ T p := by
  unfold T
  exact Real.iInf_nonneg fun g => detScore_nonneg hp g

/-- The finite infimum defining `T` is attained. -/
theorem exists_optimalCode (p : α × β → ℝ) :
    ∃ g : Code α β, detScore p g = T p := by
  obtain ⟨g, hminimal⟩ := exists_minimalCode p
  let _ : Nonempty (Code α β) := ⟨constantCode⟩
  refine ⟨g, le_antisymm ?_ (T_le_detScore p g)⟩
  unfold T
  exact le_ciInf hminimal

end StochasticToDeterministicLatents
