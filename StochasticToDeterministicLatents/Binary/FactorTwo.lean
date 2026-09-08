/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Renamed, restated over the
public interfaces of this library, and re-proved where the argument differs.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterEndpoints
import StochasticToDeterministicLatents.Binary.FactorTwo.ConstantBound
import StochasticToDeterministicLatents.Binary.FactorTwo.SingletonBound
import StochasticToDeterministicLatents.Binary.FactorTwo.Gates

/-!
# The binary factor-two theorem

For every binary probability law, the deterministic optimum is at most twice
the stochastic one.

`Gates.lean` reduces this to a one-dimensional question at each contact chord:
it is enough that, for every chord domain, either the constant code's margin is
nonnegative at the midpoint of the chord, or the isolating code's margin is
nonnegative at both ends, or there is one interior point where both margins are
nonnegative and the isolating margin is nonnegative at the midpoint as well.
`gates_of_chordDomain` supplies that disjunction at every chord domain, by a
case split on the off-diagonal mass:

* **at least `1/8`**: `center_constantMargin_pos` puts the constant code's
  margin strictly above zero at the midpoint, which is the first branch;
* **at most `1/8`**: the fixed cut `diagonalMass p - 3 * chordBottom p u` is an
  interior point of the chord by `fixedCut_mem_chord`, both margins are
  positive there by `fixedCut_constantMargin_gt` and
  `fixedCut_singletonMargin_gt`, and the isolating margin at the midpoint is
  nonnegative by `center_singletonMargin_nonneg`.  That is the third branch.

The two branches meet at `1/8`, where either applies.

**Units.**  The two fixed-cut bounds are stated in natural-log units against a
positive multiple of `chordBottom`, and the margins themselves are in bits;
each conversion is one step against `Real.log_pos` and `chordBottom_pos`.

**What is proved here and what is not.**  `T_le_two_mul_tau` is the inequality
for every probability law.  It says nothing about which code attains it: no
declaration in this tree exhibits a latent or a deterministic code realising
the bound, and the full-support witness clause of the factor-two claim is not
proved anywhere here.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and module
boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-- **Every chord domain satisfies one of the three gates.**  Above an eighth
of off-diagonal mass the constant code's margin at the midpoint is
nonnegative; at or below an eighth the fixed cut witnesses the crossover
branch.  This is the hypothesis `T_le_two_tau_of_gates` quantifies over. -/
theorem gates_of_chordDomain (h : ChordDomain p u) :
    0 ≤ constantMargin p u (chordMidpoint p)
      ∨ (0 ≤ singletonMargin p u (chordMidpoint p)
          ∧ 0 ≤ singletonMargin p u (chordTop p u))
      ∨ (∃ t ∈ Set.Icc (chordMidpoint p) (chordTop p u),
          0 ≤ singletonMargin p u (chordMidpoint p)
            ∧ 0 ≤ singletonMargin p u t ∧ 0 ≤ constantMargin p u t) := by
  rcases le_total (offDiagonalMass p) ((1 : ℝ) / 8) with hv | hv
  · have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
    have hD := chordBottom_pos h
    have hconst : 0 ≤ constantMargin p u (fixedCut p u) := by
      have hgt := fixedCut_constantMargin_gt h hv
      nlinarith
    have hsing : 0 ≤ singletonMargin p u (fixedCut p u) := by
      have hgt := fixedCut_singletonMargin_gt h hv
      nlinarith
    exact Or.inr (Or.inr ⟨fixedCut p u,
      Set.Ioo_subset_Icc_self (fixedCut_mem_chord h hv),
      center_singletonMargin_nonneg h hv, hsing, hconst⟩)
  · exact Or.inl (center_constantMargin_pos h hv).le

/-- **The binary factor-two theorem.**  For every binary probability law the
deterministic optimum is at most twice the stochastic one. -/
theorem T_le_two_mul_tau (hp : IsPMF p) : T p ≤ 2 * tau p :=
  T_le_two_tau_of_gates (fun _ _ h => gates_of_chordDomain h) hp

end StochasticToDeterministicLatents.Binary
