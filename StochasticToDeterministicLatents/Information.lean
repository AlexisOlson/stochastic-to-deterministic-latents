import stoch_to_det.Entropy

/-!
# Finite information quantities

This module gives finite entropy, conditional entropy, and mutual information
descriptive public names and basic theorem wrappers. Entropy and information
are measured in bits. The entropy of a nonnegative finite measure is
one-homogeneous; on a probability law it is Shannon entropy.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Definitions are exposed through reducible aliases and theorem wrappers;
the upstream implementation is not copied.
-/

namespace StochasticToDeterministicLatents

/-- Total mass of a real-valued function on a finite type. -/
noncomputable abbrev mass {Ω : Type*} [Fintype Ω] (m : Ω → ℝ) : ℝ :=
  stoch_to_det.mass m

/-- A nonnegative real-valued finite measure. -/
abbrev IsFiniteMeasure {Ω : Type*} [Fintype Ω] (m : Ω → ℝ) : Prop :=
  stoch_to_det.IsFinMeas m

/-- A probability mass function on a finite type. -/
abbrev IsPMF {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) : Prop :=
  stoch_to_det.IsPMF p

/-- One-homogeneous Shannon entropy, in bits. -/
noncomputable abbrev entropy {Ω : Type*} [Fintype Ω] (m : Ω → ℝ) : ℝ :=
  stoch_to_det.H m

/-- Push a finite measure forward along a function. -/
noncomputable abbrev pushforward {Ω A : Type*} [Fintype Ω] [DecidableEq A]
    (f : Ω → A) (m : Ω → ℝ) : A → ℝ :=
  stoch_to_det.push f m

/-- Entropy of a finite-valued random variable under a finite measure. -/
noncomputable abbrev entropyOf {Ω A : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] (f : Ω → A) (m : Ω → ℝ) : ℝ :=
  stoch_to_det.Hvar f m

/-- Conditional entropy `H(f | g)`, in bits. -/
noncomputable abbrev condEntropy {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (f : Ω → A) (g : Ω → B) (m : Ω → ℝ) : ℝ :=
  stoch_to_det.condH f g m

/-- Mutual information `I(f ; g)`, in bits. -/
noncomputable abbrev mutualInfo {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (f : Ω → A) (g : Ω → B) (m : Ω → ℝ) : ℝ :=
  stoch_to_det.MI f g m

/-- Conditional mutual information `I(f ; g | h)`, in bits. -/
noncomputable abbrev condMutualInfo {Ω A B C : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (f : Ω → A) (g : Ω → B) (h : Ω → C) (m : Ω → ℝ) : ℝ :=
  stoch_to_det.condMI f g h m

/-- A probability mass function is, in particular, a nonnegative finite
measure. -/
theorem IsPMF.isFiniteMeasure {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : IsPMF p) : IsFiniteMeasure p :=
  hp.isFinMeas

/-- Entropy of a probability mass function is nonnegative. -/
theorem entropy_nonneg {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : IsPMF p) : 0 ≤ entropy p :=
  stoch_to_det.H_nonneg_of_isPMF hp

/-- A deterministic pushforward of a probability mass function is a
probability mass function. -/
theorem pushforward_isPMF {Ω A : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] {f : Ω → A} {p : Ω → ℝ}
    (hp : IsPMF p) : IsPMF (pushforward f p) :=
  stoch_to_det.isPMF_push hp

/-- Entropy cannot increase under a deterministic map. -/
theorem entropy_pushforward_le {Ω A : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] {f : Ω → A} {p : Ω → ℝ}
    (hp : IsPMF p) : entropy (pushforward f p) ≤ entropy p :=
  stoch_to_det.H_push_le hp

/-- Relabeling a random variable by an equivalence preserves its entropy. -/
theorem entropyOf_equiv {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {p : Ω → ℝ} (hp : IsPMF p) (f : Ω → A) (e : A ≃ B) :
    entropyOf (fun ω => e (f ω)) p = entropyOf f p :=
  stoch_to_det.Hvar_equiv hp f e

/-- Conditional entropy of finite random variables is nonnegative. -/
theorem condEntropy_nonneg {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {p : Ω → ℝ} (hp : IsPMF p) (f : Ω → A) (g : Ω → B) :
    0 ≤ condEntropy f g p := by
  apply sub_nonneg.mpr
  exact stoch_to_det.Hvar_comp_le hp (fun ω => (f ω, g ω)) Prod.snd

/-- Mutual information of finite random variables is nonnegative. -/
theorem mutualInfo_nonneg {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {p : Ω → ℝ} (hp : IsPMF p) (f : Ω → A) (g : Ω → B) :
    0 ≤ mutualInfo f g p :=
  stoch_to_det.MI_nonneg hp f g

/-- Conditional mutual information of finite random variables is
nonnegative. -/
theorem condMutualInfo_nonneg {Ω A B C : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    {p : Ω → ℝ} (hp : IsPMF p)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    0 ≤ condMutualInfo f g h p :=
  stoch_to_det.condMI_nonneg hp f g h

end StochasticToDeterministicLatents
