import StochasticToDeterministicLatents.Binary.Symmetry
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Transpose normal form for binary optimizers

A full-support binary law admits an optimizer whose duplicate quotient has
one or two classes. The two-class branch yields an oriented transpose chart.
This module proves the contact classification and transpose reconstruction
used by `Binary.NormalForm`, using positive cube-root parameters, a contact
polynomial, and reconstruction from four moments.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

noncomputable section

open Finset Polynomial

/-! ## Quotienting duplicate latent components -/

namespace Clustering

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)

private lemma quotient_component_eq (i : D.L.ι) : K.Q (K.cl i) = D.L.comp i := by
  unfold Q stoch_to_det.Clustering.Q
  exact (K.spec _ _).mp (Classical.choose_spec (K.surj (K.cl i)))

private lemma clusterMass_nonneg (c : K.κ) : 0 ≤ K.s c := by
  unfold s stoch_to_det.Clustering.s
  exact Finset.sum_nonneg fun i _ => D.L.prior_isPMF.nonneg i

private lemma sum_clusterMass : ∑ c, K.s c = 1 := by
  classical
  unfold s stoch_to_det.Clustering.s
  rw [Finset.sum_fiberwise]
  simpa [stoch_to_det.mass] using D.L.prior_isPMF.total

/-- Merge equal component laws, adding their prior weights. -/
noncomputable def quotientLatent : Latent p where
  ι := K.κ
  fin := K.fin
  dec := K.dec
  prior := K.s
  comp := K.Q
  prior_isPMF := ⟨K.clusterMass_nonneg, by
    rw [stoch_to_det.mass]
    exact K.sum_clusterMass⟩
  comp_isPMF := fun c => by
    unfold Q stoch_to_det.Clustering.Q
    exact D.L.comp_isPMF _
  mixture := by
    classical
    intro z
    calc
      (∑ c, K.s c * K.Q c z) =
          ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
            D.L.prior i * K.Q c z := by
        unfold s stoch_to_det.Clustering.s
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
      _ = ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
            D.L.prior i * K.Q (K.cl i) z := by
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = ∑ i, D.L.prior i * K.Q (K.cl i) z :=
        Finset.sum_fiberwise univ K.cl _
      _ = ∑ i, D.L.prior i * D.L.comp i z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [K.quotient_component_eq i]
      _ = p z := D.L.mixture z

private lemma entropyOf_lift {r : α × β → ℝ} (V : Latent r)
    {γ : Type*} [Fintype γ] [DecidableEq γ] (f : α × β → γ) :
    entropyOf (fun w : V.ι × (α × β) => f w.2) V.joint = entropyOf f r := by
  unfold entropyOf stoch_to_det.Hvar
  congr 1
  calc
    pushforward (fun w : V.ι × (α × β) => f w.2) V.joint =
        pushforward f (pushforward (fun w : V.ι × (α × β) => w.2) V.joint) := by
      symm
      simpa [Function.comp_def] using
        stoch_to_det.push_push (fun w : V.ι × (α × β) => w.2) f V.joint
    _ = pushforward f r := by
      congr 1
      funext z
      unfold pushforward stoch_to_det.push Latent.joint stoch_to_det.Latent.joint
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      simpa using V.mixture z

private lemma mutualInfo_prior_lift {r : α × β → ℝ} (V : Latent r)
    {γ : Type*} [Fintype γ] [DecidableEq γ] (f : α × β → γ) :
    mutualInfo (fun w : V.ι × (α × β) => w.1) (fun w => f w.2) V.joint =
      entropyOf f r - ∑ v, V.prior v * entropyOf f (V.comp v) := by
  have hprior : entropyOf (fun w : V.ι × (α × β) => w.1) V.joint =
      entropy V.prior := by
    unfold entropyOf stoch_to_det.Hvar
    congr 1
    funext v
    unfold stoch_to_det.push Latent.joint stoch_to_det.Latent.joint
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Prod.fst]
    calc
      (∑ x, ∑ y, if x = v then V.prior x * V.comp x y else 0) =
          ∑ x, if x = v then V.prior x * (∑ y, V.comp x y) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = v <;> simp [hx, Finset.mul_sum]
      _ = V.prior v := by
        simp [show ∀ x, ∑ y, V.comp x y = 1 from fun x => by
          simpa [stoch_to_det.mass] using (V.comp_isPMF x).total]
  have hpair :
      entropyOf (fun w : V.ι × (α × β) => (w.1, f w.2)) V.joint =
        entropy V.prior + ∑ v, V.prior v * entropyOf f (V.comp v) := by
    have hd := stoch_to_det.Hvar_pair_eq_sum_fibers V.joint_isPMF
      (fun w : V.ι × (α × β) => f w.2) (fun w => w.1)
    change stoch_to_det.Hvar (fun w : V.ι × (α × β) => w.1) V.joint =
      stoch_to_det.H V.prior at hprior
    rw [hprior] at hd
    have hs : ∀ v, entropy
        (pushforward (fun w : V.ι × (α × β) => f w.2)
          (fun w => if w.1 = v then V.joint w else 0)) =
        V.prior v * entropyOf f (V.comp v) := by
      intro v
      have hp : pushforward (fun w : V.ι × (α × β) => f w.2)
          (fun w => if w.1 = v then V.joint w else 0) =
          fun g => V.prior v * pushforward f (V.comp v) g := by
        funext g
        change stoch_to_det.push (fun w : V.ι × (α × β) => f w.2)
            (fun w => if w.1 = v then V.joint w else 0) g =
          V.prior v * stoch_to_det.push f (V.comp v) g
        unfold stoch_to_det.push Latent.joint stoch_to_det.Latent.joint
        rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
        simp only [Prod.fst, Prod.snd]
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : f z = g <;> simp [hz]
      rw [hp]
      simpa [entropyOf, entropy, stoch_to_det.Hvar] using
        stoch_to_det.H_smul (stoch_to_det.isFinMeas_push (V.comp_isPMF v).isFinMeas)
          (V.prior_isPMF.nonneg v)
    have hswap :
        entropyOf (fun w : V.ι × (α × β) => (w.1, f w.2)) V.joint =
          entropyOf (fun w => (f w.2, w.1)) V.joint := by
      simpa using stoch_to_det.Hvar_equiv V.joint_isPMF (fun w => (f w.2, w.1))
        (Equiv.prodComm γ V.ι)
    change stoch_to_det.Hvar (fun w : V.ι × (α × β) => (w.1, f w.2)) V.joint =
      stoch_to_det.H V.prior + ∑ v, V.prior v * stoch_to_det.Hvar f (V.comp v)
    change stoch_to_det.Hvar (fun w : V.ι × (α × β) => (w.1, f w.2)) V.joint =
      stoch_to_det.Hvar (fun w => (f w.2, w.1)) V.joint at hswap
    rw [hswap, hd]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    exact hs v
  change stoch_to_det.MI (fun w : V.ι × (α × β) => w.1) (fun w => f w.2) V.joint =
    stoch_to_det.Hvar f r - ∑ v, V.prior v * stoch_to_det.Hvar f (V.comp v)
  change stoch_to_det.Hvar (fun w : V.ι × (α × β) => w.1) V.joint =
    stoch_to_det.H V.prior at hprior
  change stoch_to_det.Hvar (fun w : V.ι × (α × β) => (w.1, f w.2)) V.joint =
    stoch_to_det.H V.prior + ∑ v, V.prior v * stoch_to_det.Hvar f (V.comp v) at hpair
  have hlift := entropyOf_lift V f
  change stoch_to_det.Hvar (fun w : V.ι × (α × β) => f w.2) V.joint =
    stoch_to_det.Hvar f r at hlift
  unfold stoch_to_det.MI
  rw [hprior, hlift, hpair]
  ring

private lemma quotient_mutualInfo_eq {γ : Type*} [Fintype γ] [DecidableEq γ]
    (f : α × β → γ) :
    mutualInfo (fun w : K.quotientLatent.ι × (α × β) => w.1) (fun w => f w.2)
        K.quotientLatent.joint =
      mutualInfo (fun w : D.L.ι × (α × β) => w.1) (fun w => f w.2) D.L.joint := by
  rw [mutualInfo_prior_lift K.quotientLatent f, mutualInfo_prior_lift D.L f]
  congr 1
  calc
    (∑ c, K.quotientLatent.prior c * entropyOf f (K.quotientLatent.comp c)) =
      ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
        D.L.prior i * entropyOf f (K.Q c) := by
        unfold quotientLatent s stoch_to_det.Clustering.s
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
    _ = ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
          D.L.prior i * entropyOf f (K.Q (K.cl i)) := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, D.L.prior i * entropyOf f (K.Q (K.cl i)) :=
      Finset.sum_fiberwise univ K.cl _
    _ = ∑ i, D.L.prior i * entropyOf f (D.L.comp i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [K.quotient_component_eq i]

private lemma w3Cost_eq_mutualInfo_formula {r : α × β → ℝ} (V : Latent r)
    (g : Code α β) :
    w3Cost V g =
      mutualInfo (fun w : V.ι × (α × β) => w.1) (fun w => w.2) V.joint +
      3 * entropyOf g r - 4 * mutualInfo (fun w : V.ι × (α × β) => w.1)
        (fun w => g w.2) V.joint := by
  have hZG : entropyOf (fun w : V.ι × (α × β) => (w.2, g w.2)) V.joint =
      entropyOf (fun w => w.2) V.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse V.joint_isPMF
      (fun w : V.ι × (α × β) => w.2) (fun z => (z, g z)) Prod.fst (by intro z; rfl)
  have hLZG : entropyOf (fun w : V.ι × (α × β) => (w.1, w.2, g w.2)) V.joint =
      entropyOf (fun w => (w.1, w.2)) V.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse V.joint_isPMF
      (fun w : V.ι × (α × β) => (w.1, w.2))
      (fun x => (x.1, x.2, g x.2)) (fun x => (x.1, x.2.1)) (by intro x; rfl)
  have hGL : entropyOf (fun w : V.ι × (α × β) => (g w.2, w.1)) V.joint =
      entropyOf (fun w => (w.1, g w.2)) V.joint := by
    symm
    simpa using stoch_to_det.Hvar_equiv V.joint_isPMF (fun w => (g w.2, w.1))
      (Equiv.prodComm _ _)
  have hliftG := entropyOf_lift V g
  change stoch_to_det.Hvar (fun w : V.ι × (α × β) => (w.2, g w.2)) V.joint =
    stoch_to_det.Hvar (fun w => w.2) V.joint at hZG
  change stoch_to_det.Hvar (fun w : V.ι × (α × β) => (w.1, w.2, g w.2)) V.joint =
    stoch_to_det.Hvar (fun w => (w.1, w.2)) V.joint at hLZG
  change stoch_to_det.Hvar (fun w : V.ι × (α × β) => (g w.2, w.1)) V.joint =
    stoch_to_det.Hvar (fun w => (w.1, g w.2)) V.joint at hGL
  change stoch_to_det.Hvar (fun w : V.ι × (α × β) => g w.2) V.joint =
    stoch_to_det.Hvar g r at hliftG
  unfold w3Cost condMutualInfo condEntropy mutualInfo
    stoch_to_det.condMI stoch_to_det.condH stoch_to_det.MI
  rw [hZG, hLZG, hliftG, hGL]
  ring

/-- Quotienting duplicate components preserves the stochastic score. -/
theorem quotientLatent_score_eq : K.quotientLatent.score = D.L.score := by
  rw [latent_score_eq D.isPMF K.quotientLatent, latent_score_eq D.isPMF D.L]
  apply congrArg (Psi p - ·)
  calc
    (∑ c, K.quotientLatent.prior c * Phi (K.quotientLatent.comp c)) =
      ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
        D.L.prior i * Phi (K.Q c) := by
        unfold quotientLatent s stoch_to_det.Clustering.s
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
    _ = ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
        D.L.prior i * Phi (K.Q (K.cl i)) := by
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, D.L.prior i * Phi (K.Q (K.cl i)) :=
      Finset.sum_fiberwise univ K.cl _
    _ = ∑ i, D.L.prior i * Phi (D.L.comp i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [K.quotient_component_eq i]

/-- Quotienting duplicate components preserves every deterministic-code cost. -/
theorem quotientLatent_w3Cost_eq (g : Code α β) :
    w3Cost K.quotientLatent g = w3Cost D.L g := by
  rw [w3Cost_eq_mutualInfo_formula K.quotientLatent g,
    w3Cost_eq_mutualInfo_formula D.L g,
    K.quotient_mutualInfo_eq (fun z => z), K.quotient_mutualInfo_eq g]

/-- Quotienting duplicate components preserves the optimal deterministic-code cost. -/
theorem quotientLatent_w3_eq : w3 K.quotientLatent = w3 D.L := by
  unfold w3
  congr 1
  funext g
  exact K.quotientLatent_w3Cost_eq g

/-- Every quotient cluster has positive prior mass. -/
theorem s_pos (c : K.κ) : 0 < K.s c := by
  obtain ⟨i, hi⟩ := K.surj c
  have hle : D.L.prior i ≤ K.s c := by
    unfold s stoch_to_det.Clustering.s
    exact Finset.single_le_sum
      (fun j _ => D.L.prior_isPMF.nonneg j) (by simp [hi])
  exact (D.prior_pos i).trans_le hle

/-- Package the duplicate quotient with the original kernel and optimizer data. -/
noncomputable def quotientSeedSetup : SeedSetup p where
  isPMF := D.isPMF
  conn := D.conn
  L := K.quotientLatent
  w := D.w
  feasible := D.feasible
  optimal := K.quotientLatent_score_eq.trans D.optimal
  contact := fun c _ => K.Q_isContact c
  prior_pos := K.s_pos

end Clustering

/-! ## Binary normal-form interfaces -/

namespace Binary

/-- A full-support binary law admits an attained seed setup with positive prior. -/
theorem exists_fullSupport_seedSetup
    {p : Cell → ℝ} (hp : IsPMF p) (hfull : ∀ z, 0 < p z) :
    Nonempty (SeedSetup p) := by
  apply exists_seedSetup hp
  rw [support_eq_univ_of_pos hfull]
  exact univ_isConnected

/-- Any three full-support contacts of a common feasible binary kernel contain a duplicate. -/
def ContactClassification : Prop :=
  ∀ w : Cell → ℝ,
    Feasible (univ : Finset Cell) w →
    ∀ q r s : Cell → ℝ,
      IsContact (univ : Finset Cell) w q →
      IsContact (univ : Finset Cell) w r →
      IsContact (univ : Finset Cell) w s →
      q = r ∨ q = s ∨ r = s

/-- Contact classification forces a duplicate among any three quotient indices. -/
theorem clustering_three_indices_duplicate
    (hclass : ContactClassification)
    {p : Cell → ℝ} (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) (a b c : K.κ) :
    a = b ∨ a = c ∨ b = c := by
  have hsupp : support p = (univ : Finset Cell) := support_eq_univ_of_pos hfull
  have hdup := hclass D.w (by simpa [hsupp] using D.feasible)
    (K.Q a) (K.Q b) (K.Q c)
    (by simpa [hsupp] using K.Q_isContact a)
    (by simpa [hsupp] using K.Q_isContact b)
    (by simpa [hsupp] using K.Q_isContact c)
  rcases hdup with hab | hac | hbc
  · exact Or.inl (K.Q_injective hab)
  · exact Or.inr (Or.inl (K.Q_injective hac))
  · exact Or.inr (Or.inr (K.Q_injective hbc))

/-- The eight cell symmetries used to orient a binary chart. -/
def chartCellEquiv : Fin 8 → (Cell ≃ Cell) :=
  ![Equiv.refl _, swapRowsCell, swapColumnsCell,
    swapRowsCell.trans swapColumnsCell, transposeCell,
    transposeCell.trans swapRowsCell, transposeCell.trans swapColumnsCell,
    transposeCell.trans (swapRowsCell.trans swapColumnsCell)]

/-- An oriented two-class chart with a strict off-diagonal choice. -/
structure ChartCandidate {p : Cell → ℝ} {D : SeedSetup p}
    (K : Clustering D) (j : Fin 8) where
  classEquiv : K.κ ≃ Bit
  transpose_pair :
    pushforward (chartCellEquiv j) (K.Q (classEquiv.symm 1)) =
      fun z => pushforward (chartCellEquiv j)
        (K.Q (classEquiv.symm 0)) (transposeCell.symm z)
  strict_offDiag :
    pushforward (chartCellEquiv j) (K.Q (classEquiv.symm 0)) (1, 0) <
      pushforward (chartCellEquiv j) (K.Q (classEquiv.symm 0)) (0, 1)
  minority : K.s (classEquiv.symm 1) ≤ 1 / 2
  q0_pos : ∀ z, 0 < pushforward (chartCellEquiv j) (K.Q (classEquiv.symm 0)) z

/-- Admissibility of a chart orientation. -/
def ChartAdmissible {p : Cell → ℝ} {D : SeedSetup p}
    (K : Clustering D) (j : Fin 8) : Prop :=
  Nonempty (ChartCandidate K j)

/-- The statement that every full-support binary law has an attained optimizer whose
duplicate quotient has one class, or two classes admitting an oriented transpose chart.

The dichotomy is on the number of classes of the duplicate quotient, not on the label
type of the optimizer itself. It is proved below as `selectedOptimizerNormalForm`. -/
def SelectedOptimizerNormalForm : Prop :=
  ∀ (p : Cell → ℝ), IsPMF p → (∀ z, 0 < p z) →
    ∃ (D : SeedSetup p) (K : Clustering D),
      Fintype.card K.κ = 1 ∨
      (Fintype.card K.κ = 2 ∧ ∃ j, ChartAdmissible K j)

/-! ## Algebraic conditions used by the reconstruction -/

/-- Row marginal of a binary table. -/
def rowMarginal (q : Cell → ℝ) (i : Bit) : ℝ := q (i, 0) + q (i, 1)

/-- Column marginal of a binary table. -/
def columnMarginal (q : Cell → ℝ) (j : Bit) : ℝ := q (0, j) + q (1, j)

/-- Positive cube-root parametrization of the row marginal. -/
def RowCubeParameter (q : Cell → ℝ) (x : ℝ) : Prop :=
  0 < x ∧ rowMarginal q 0 = 1 / (1 + x ^ 3) ∧
    rowMarginal q 1 = x ^ 3 / (1 + x ^ 3)

/-- Positive cube-root parametrization of the column marginal. -/
def ColumnCubeParameter (q : Cell → ℝ) (y : ℝ) : Prop :=
  0 < y ∧ columnMarginal q 0 = 1 / (1 + y ^ 3) ∧
    columnMarginal q 1 = y ^ 3 / (1 + y ^ 3)

/-- The feasibility polynomial evaluated at a positive row parameter. -/
def feasibilityExpression (w : Cell → ℝ) (x : ℝ) : ℝ :=
  (1 + x ^ 3) ^ 2 - (w (0, 0) + w (1, 0) * x ^ 2) ^ 3 -
    (w (0, 1) + w (1, 1) * x ^ 2) ^ 3

/-- The real-power identities for a positive cube-root ratio. -/
def PositiveCubeRootIdentities : Prop :=
  ∀ u0 u1 : ℝ, 0 < u0 → 0 < u1 →
    let x := (u1 / u0) ^ ((3 : ℝ)⁻¹)
    0 < x ∧ x ^ 3 = u1 / u0 ∧
    u1 ^ ((2 : ℝ) / 3) = x ^ 2 * u0 ^ ((2 : ℝ) / 3) ∧
    (u0 + u1 = 1 → u0 = 1 / (1 + x ^ 3) ∧ u1 = x ^ 3 / (1 + x ^ 3))

/-- Every binary contact admits a positive row cube parameter. -/
def ContactHasRowCubeParameter : Prop :=
  ∀ w q : Cell → ℝ, Feasible (univ : Finset Cell) w →
    IsContact (univ : Finset Cell) w q → ∃ x : ℝ, RowCubeParameter q x

/-- Exact maximization and equality characterization for two positive coefficients. -/
def TwoThirdsPowerMaximum : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B →
    (∀ v : Bit → ℝ, IsPMF v →
      A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3) ≤
          (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) ∧
      (A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3) =
          (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) →
        v 0 = A ^ 3 / (A ^ 3 + B ^ 3) ∧
        v 1 = B ^ 3 / (A ^ 3 + B ^ 3))) ∧
    (A * (A ^ 3 / (A ^ 3 + B ^ 3)) ^ ((2 : ℝ) / 3) +
      B * (B ^ 3 / (A ^ 3 + B ^ 3)) ^ ((2 : ℝ) / 3) =
      (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3))

/-- Feasibility makes the feasibility expression nonnegative on positive parameters. -/
def FeasibilityExpressionNonnegative : Prop :=
  ∀ w : Cell → ℝ, Feasible (univ : Finset Cell) w →
    ∀ x : ℝ, 0 < x → 0 ≤ feasibilityExpression w x

/-- A contact parameter is a root and determines a column best response. -/
def ContactParameterBestResponse : Prop :=
  ∀ w q : Cell → ℝ, Feasible (univ : Finset Cell) w →
    IsContact (univ : Finset Cell) w q →
    ∀ x : ℝ, RowCubeParameter q x →
      feasibilityExpression w x = 0 ∧
      ∃ y : ℝ, ColumnCubeParameter q y ∧
        y = (w (0, 1) + w (1, 1) * x ^ 2) /
          (w (0, 0) + w (1, 0) * x ^ 2)

/-- The positive row cube parameter determines a contact uniquely. -/
def ContactParameterInjective : Prop :=
  ∀ w q r : Cell → ℝ, Feasible (univ : Finset Cell) w →
    IsContact (univ : Finset Cell) w q → IsContact (univ : Finset Cell) w r →
    ∀ x : ℝ, RowCubeParameter q x → RowCubeParameter r x → q = r

/-- Both endpoint coefficients of the feasibility polynomial are positive. -/
def FeasibilityEndpointCoefficientsPositive : Prop :=
  ∀ w : Cell → ℝ, Feasible (univ : Finset Cell) w →
    0 < 1 - w (0, 0) ^ 3 - w (0, 1) ^ 3 ∧
    0 < 1 - w (1, 0) ^ 3 - w (1, 1) ^ 3

/-- A positive zero of a polynomial nonnegative on the positive ray is a double root. -/
def PositiveRootSquareDivides : Prop :=
  ∀ P : Polynomial ℝ, ∀ x : ℝ, 0 < x →
    (∀ y : ℝ, 0 < y → 0 ≤ P.eval y) → P.eval x = 0 →
    (Polynomial.X - Polynomial.C x) ^ 2 ∣ P

/-- A nonzero sextic with zero degree-five coefficient cannot have three distinct
positive double roots. -/
def ThreePositiveDoubleRootsImpossible : Prop :=
  ∀ (P : Polynomial ℝ) (x y z : ℝ), P ≠ 0 → P.natDegree ≤ 6 → P.coeff 5 = 0 →
    0 < x → 0 < y → 0 < z → x ≠ y → x ≠ z → y ≠ z →
    (Polynomial.X - Polynomial.C x) ^ 2 ∣ P →
    (Polynomial.X - Polynomial.C y) ^ 2 ∣ P →
    (Polynomial.X - Polynomial.C z) ^ 2 ∣ P → False

/-- Two positive double roots force the explicit feasibility factorization. -/
def TwoContactPolynomialFactorization : Prop :=
  ∀ w : Cell → ℝ, Feasible (univ : Finset Cell) w →
    ∀ s t : ℝ, 0 < s → 0 < t → s ≠ t →
    (∀ P : Polynomial ℝ, (∀ x, P.eval x = feasibilityExpression w x) →
      (Polynomial.X - Polynomial.C s) ^ 2 ∣ P →
      (Polynomial.X - Polynomial.C t) ^ 2 ∣ P →
      ∀ x : ℝ, feasibilityExpression w x =
        (x - s) ^ 2 * (x - t) ^ 2 * (x ^ 2 + 2 * (s + t) * x + s * t) /
          (s + t) ^ 3)

/-- Coefficient comparison in the two-contact factorization. -/
def TwoContactMomentIdentities : Prop :=
  ∀ a b c d s t : ℝ, 0 < s → 0 < t →
    let R := s + t
    let T := s * t
    let K := R ^ 2 - T
    (∀ x : ℝ, (1 + x ^ 3) ^ 2 - (a + c * x ^ 2) ^ 3 -
      (b + d * x ^ 2) ^ 3 =
      (x - s) ^ 2 * (x - t) ^ 2 * (x ^ 2 + 2 * R * x + T) / R ^ 3) →
    a ^ 3 + b ^ 3 = (R ^ 3 - T ^ 3) / R ^ 3 ∧
    a ^ 2 * c + b ^ 2 * d = T * K / R ^ 3 ∧
    a * c ^ 2 + b * d ^ 2 = K / R ^ 3 ∧
    c ^ 3 + d ^ 3 = (R ^ 3 - 1) / R ^ 3

/-- The two-node Hankel determinant identity. -/
def TwoNodeHankelIdentity : Prop :=
  ∀ u1 u2 r1 r2 : ℝ,
    let m0 := u1 + u2
    let m1 := u1 * r1 + u2 * r2
    let m2 := u1 * r1 ^ 2 + u2 * r2 ^ 2
    m0 * m2 - m1 ^ 2 = u1 * u2 * (r1 - r2) ^ 2

/-- Two consecutive recurrence equations uniquely determine their coefficients. -/
def TwoNodeRecurrenceUnique : Prop :=
  ∀ m0 m1 m2 m3 e1 e2 e1' e2' : ℝ,
    m0 * m2 - m1 ^ 2 ≠ 0 →
    m2 = e1 * m1 - e2 * m0 → m3 = e1 * m2 - e2 * m1 →
    m2 = e1' * m1 - e2' * m0 → m3 = e1' * m2 - e2' * m1 →
    e1 = e1' ∧ e2 = e2'

/-- Positive two-cube decompositions are unique up to exchanging the two nodes. -/
def PositiveTwoCubeDecompositionUnique : Prop :=
  ∀ a b c d a' b' c' d' : ℝ,
    0 < a → 0 < b → 0 < c → 0 < d →
    0 < a' → 0 < b' → 0 < c' → 0 < d' → c / a ≠ d / b →
    (∀ z : ℝ, (a + c * z) ^ 3 + (b + d * z) ^ 3 =
      (a' + c' * z) ^ 3 + (b' + d' * z) ^ 3) →
    (a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∨
      (a = b' ∧ b = a' ∧ c = d' ∧ d = c')

/-- Distinct contacts give distinct kernel column ratios. -/
def DistinctContactsHaveDistinctKernelNodes : Prop :=
  ∀ w q r : Cell → ℝ, Feasible (univ : Finset Cell) w →
    IsContact (univ : Finset Cell) w q → IsContact (univ : Finset Cell) w r →
    q ≠ r → w (1, 0) / w (0, 0) ≠ w (1, 1) / w (0, 1)

/-- Normal-form identities for the two-root factorization parameters. -/
def FactorHankelNormalForm : Prop :=
  ∀ s t : ℝ, 0 < s → 0 < t →
    let R := s + t
    let T := s * t
    let K := R ^ 2 - T
    let A := R - T ^ 2
    let D := R * T - 1
    let U := (1 + s ^ 3) * (1 + t ^ 3)
    A ^ 3 + K ^ 3 = (R ^ 3 - T ^ 3) * U ∧
      A ^ 2 + K * D = T * U

/-- Four reconstructed moments force the symmetric kernel model, up to column swap. -/
def SymmetricKernelReconstruction : Prop :=
  ∀ w : Cell → ℝ, (∀ z, 0 < w z) → ∀ s t : ℝ,
    0 < s → 0 < t → s ≠ t →
    let R := s + t
    let T := s * t
    let K := R ^ 2 - T
    let A := R - T ^ 2
    let D := R * T - 1
    let U := (1 + s ^ 3) * (1 + t ^ 3)
    let m0 := (R ^ 3 - T ^ 3) / R ^ 3
    let m1 := T * K / R ^ 3
    let m2 := K / R ^ 3
    let m3 := (R ^ 3 - 1) / R ^ 3
    w (0, 0) ^ 3 + w (0, 1) ^ 3 = m0 →
    w (0, 0) ^ 2 * w (1, 0) + w (0, 1) ^ 2 * w (1, 1) = m1 →
    w (0, 0) * w (1, 0) ^ 2 + w (0, 1) * w (1, 1) ^ 2 = m2 →
    w (1, 0) ^ 3 + w (1, 1) ^ 3 = m3 →
    w (1, 0) / w (0, 0) ≠ w (1, 1) / w (0, 1) →
    ∃ h : ℝ, 0 < h ∧ h ^ 3 = 1 / (R ^ 3 * U) ∧
      let ws : Cell → ℝ := fun z =>
        if z = (0, 0) then h * A else if z = (0, 1) then h * K
        else if z = (1, 0) then h * K else h * D
      w = ws ∨ pushforward swapColumnsCell w = ws

/-- In the symmetric model, the column best response exchanges the two roots. -/
def SymmetricBestResponseSwapsRoots : Prop :=
  ∀ s t : ℝ, 0 < s → 0 < t →
    let R := s + t
    let T := s * t
    let K := R ^ 2 - T
    let A := R - T ^ 2
    let D := R * T - 1
    A + K * s ^ 2 = R * (1 + s ^ 3) ∧
    K + D * s ^ 2 = t * R * (1 + s ^ 3) ∧
    A + K * t ^ 2 = R * (1 + t ^ 3) ∧
    K + D * t ^ 2 = s * R * (1 + t ^ 3)

/-- Transposition preserves contact for a transpose-symmetric kernel. -/
def ContactTransposeOfSymmetricKernel : Prop :=
  ∀ w q : Cell → ℝ, (∀ z, w (transposeCell z) = w z) →
    IsContact (univ : Finset Cell) w q →
    IsContact (univ : Finset Cell) w (fun z => q (transposeCell.symm z))

/-- The four non-transposing chart symmetries preserve contact. -/
def ContactPushforwardAlongChart : Prop :=
  ∀ w q : Cell → ℝ, ∀ g : Cell ≃ Cell,
    (g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
      g = swapRowsCell.trans swapColumnsCell) →
    IsContact (univ : Finset Cell) w q →
    IsContact (univ : Finset Cell) (pushforward g w) (pushforward g q)

/-- The four non-transposing chart symmetries preserve feasibility. -/
def FeasiblePushforwardAlongChart : Prop :=
  ∀ w : Cell → ℝ, ∀ g : Cell ≃ Cell,
    (g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
      g = swapRowsCell.trans swapColumnsCell) →
    Feasible (univ : Finset Cell) w →
    Feasible (univ : Finset Cell) (pushforward g w)

/-- A non-transpose-invariant table can be oriented by identity or transpose. -/
def TransposePairCanOrientOffDiagonal : Prop :=
  ∀ q : Cell → ℝ, q ≠ (fun z => q (transposeCell.symm z)) →
    ∃ e : Cell ≃ Cell, (e = Equiv.refl _ ∨ e = transposeCell) ∧
      pushforward e q (1, 0) < pushforward e q (0, 1)

/-- The complete algebraic and transport hypotheses for the normal-form derivation. -/
def NormalFormConditions : Prop :=
  PositiveCubeRootIdentities ∧ ContactHasRowCubeParameter ∧ TwoThirdsPowerMaximum ∧
  FeasibilityExpressionNonnegative ∧ ContactParameterBestResponse ∧
  ContactParameterInjective ∧ FeasibilityEndpointCoefficientsPositive ∧
  PositiveRootSquareDivides ∧ ThreePositiveDoubleRootsImpossible ∧
  TwoContactPolynomialFactorization ∧ TwoContactMomentIdentities ∧
  TwoNodeHankelIdentity ∧ TwoNodeRecurrenceUnique ∧
  PositiveTwoCubeDecompositionUnique ∧ DistinctContactsHaveDistinctKernelNodes ∧
  FactorHankelNormalForm ∧ SymmetricKernelReconstruction ∧
  SymmetricBestResponseSwapsRoots ∧ ContactTransposeOfSymmetricKernel ∧
  ContactPushforwardAlongChart ∧ FeasiblePushforwardAlongChart ∧
  TransposePairCanOrientOffDiagonal

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

open Finset Polynomial

namespace Binary

/-! ## Real-power and cube-parameter lemmas -/

/-- The positive cube-root ratio satisfies the required power identities. -/
theorem positiveCubeRootIdentities : PositiveCubeRootIdentities := by
  intro u0 u1 hu0 hu1
  let d := u1 / u0
  let x := d ^ ((3 : ℝ)⁻¹)
  let e := (2 : ℝ) / 3
  have hd : 0 < d := div_pos hu1 hu0
  have hx : 0 < x := Real.rpow_pos_of_pos hd ((3 : ℝ)⁻¹)
  have hx3 : x ^ 3 = d := by
    simpa [x] using
      (Real.rpow_inv_natCast_pow (n := 3) hd.le (by norm_num : (3 : ℕ) ≠ 0))
  have hx2 : x ^ 2 = d ^ e := by
    calc
      x ^ 2 = d ^ (((3 : ℝ)⁻¹) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hd.le ((3 : ℝ)⁻¹) 2).symm
      _ = d ^ ((2 : ℝ) / 3) := by norm_num
  have hu0e_pos : 0 < u0 ^ e := Real.rpow_pos_of_pos hu0 e
  have hscale : u1 ^ e = x ^ 2 * u0 ^ e := by
    calc
      u1 ^ e = (u1 ^ e / u0 ^ e) * u0 ^ e :=
        (div_mul_cancel₀ _ hu0e_pos.ne').symm
      _ = d ^ e * u0 ^ e := by rw [Real.div_rpow hu1.le hu0.le]
      _ = x ^ 2 * u0 ^ e := by rw [hx2]
  refine ⟨hx, ?_, hscale, ?_⟩
  · simpa [d] using hx3
  · intro hsum
    have hx3mul : x ^ 3 * u0 = u1 := by
      rw [hx3]
      exact div_mul_cancel₀ u1 hu0.ne'
    have hden : 0 < 1 + x ^ 3 := by positivity
    have hu0form : u0 = 1 / (1 + x ^ 3) := by
      apply (eq_div_iff hden.ne').2
      nlinarith [hx3mul]
    refine ⟨hu0form, ?_⟩
    calc
      u1 = x ^ 3 * u0 := hx3mul.symm
      _ = x ^ 3 * (1 / (1 + x ^ 3)) := by rw [hu0form]
      _ = x ^ 3 / (1 + x ^ 3) := by simp [div_eq_mul_inv]

/-- The exact two-term two-thirds-power maximum and its equality case. -/
theorem twoThirdsPowerMaximum : TwoThirdsPowerMaximum := by
  intro A B hA hB
  let D := A ^ 3 + B ^ 3
  let pA := A ^ 3 / D
  let pB := B ^ 3 / D
  let r : ℝ := (3 : ℝ)⁻¹
  let e : ℝ := 2 / 3
  let c := D ^ r
  have hD : 0 < D := by dsimp [D]; positivity
  have hpA : 0 < pA := div_pos (by positivity) hD
  have hpB : 0 < pB := div_pos (by positivity) hD
  have hc : 0 < c := Real.rpow_pos_of_pos hD r
  have hp_sum : pA + pB = 1 := by
    dsimp [pA, pB]
    field_simp [hD.ne']
    ring
  have hDpA : D * pA = A ^ 3 := by
    dsimp [pA]
    field_simp [hD.ne']
  have hDpB : D * pB = B ^ 3 := by
    dsimp [pB]
    field_simp [hD.ne']
  have hcA : c * pA ^ r = A := by
    calc
      c * pA ^ r = D ^ r * pA ^ r := rfl
      _ = (D * pA) ^ r := (Real.mul_rpow hD.le hpA.le).symm
      _ = (A ^ 3) ^ r := by rw [hDpA]
      _ = A := by
        simpa [r, one_div] using
          (Real.pow_rpow_inv_natCast (n := 3) hA.le (by norm_num : (3 : ℕ) ≠ 0))
  have hcB : c * pB ^ r = B := by
    calc
      c * pB ^ r = D ^ r * pB ^ r := rfl
      _ = (D * pB) ^ r := (Real.mul_rpow hD.le hpB.le).symm
      _ = (B ^ 3) ^ r := by rw [hDpB]
      _ = B := by
        simpa [r, one_div] using
          (Real.pow_rpow_inv_natCast (n := 3) hB.le (by norm_num : (3 : ℕ) ≠ 0))
  have hamgm (p s : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) :
      p ^ r * s ^ e ≤ r * p + e * s := by
    exact Real.geom_mean_le_arith_mean2_weighted
      (w₁ := r) (w₂ := e) (p₁ := p) (p₂ := s)
      (by norm_num [r]) (by norm_num [e]) hp hs (by norm_num [r, e])
  have hamgm_eq (p s : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) :
      p ^ r * s ^ e = r * p + e * s ↔ p = s := by
    exact Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
      (w₁ := r) (w₂ := e) (p₁ := p) (p₂ := s)
      (by norm_num [r]) (by norm_num [e]) hp hs (by norm_num [r, e])
  constructor
  · intro v hv
    have hs0 : 0 ≤ v 0 := hv.nonneg 0
    have hs1 : 0 ≤ v 1 := hv.nonneg 1
    have hvsum : v 0 + v 1 = 1 := by simpa [stoch_to_det.mass] using hv.total
    have h0 := hamgm pA (v 0) hpA.le hs0
    have h1 := hamgm pB (v 1) hpB.le hs1
    have hc0 : c * (pA ^ r * v 0 ^ e) ≤ c * (r * pA + e * v 0) :=
      mul_le_mul_of_nonneg_left h0 hc.le
    have hc1 : c * (pB ^ r * v 1 ^ e) ≤ c * (r * pB + e * v 1) :=
      mul_le_mul_of_nonneg_left h1 hc.le
    have hright :
        c * (r * pA + e * v 0) + c * (r * pB + e * v 1) = c := by
      calc
        _ = c * (r * (pA + pB) + e * (v 0 + v 1)) := by ring
        _ = c := by rw [hp_sum, hvsum]; norm_num [r, e]
    have hleft0 : c * (pA ^ r * v 0 ^ e) = A * v 0 ^ e := by
      rw [← mul_assoc, hcA]
    have hleft1 : c * (pB ^ r * v 1 ^ e) = B * v 1 ^ e := by
      rw [← mul_assoc, hcB]
    have hbound : A * v 0 ^ e + B * v 1 ^ e ≤ c := by
      calc
        _ = c * (pA ^ r * v 0 ^ e) + c * (pB ^ r * v 1 ^ e) := by
          rw [hleft0, hleft1]
        _ ≤ c * (r * pA + e * v 0) + c * (r * pB + e * v 1) :=
          add_le_add hc0 hc1
        _ = c := hright
    refine ⟨?_, ?_⟩
    · simpa [e, c, D] using hbound
    · intro heq
      have heq' : A * v 0 ^ e + B * v 1 ^ e = c := by simpa [e, c, D] using heq
      have hscaled0 : c * (pA ^ r * v 0 ^ e) = c * (r * pA + e * v 0) := by
        rw [hleft0]
        linarith [hc1, hright]
      have hscaled1 : c * (pB ^ r * v 1 ^ e) = c * (r * pB + e * v 1) := by
        rw [hleft1]
        linarith [hc0, hright]
      have he0 : pA ^ r * v 0 ^ e = r * pA + e * v 0 :=
        mul_left_cancel₀ hc.ne' hscaled0
      have he1 : pB ^ r * v 1 ^ e = r * pB + e * v 1 :=
        mul_left_cancel₀ hc.ne' hscaled1
      have hpAv : pA = v 0 := (hamgm_eq pA (v 0) hpA.le hs0).mp he0
      have hpBv : pB = v 1 := (hamgm_eq pB (v 1) hpB.le hs1).mp he1
      simpa [pA, pB] using And.intro hpAv.symm hpBv.symm
  · have heA : pA ^ r * pA ^ e = r * pA + e * pA :=
      (hamgm_eq pA pA hpA.le hpA.le).mpr rfl
    have heB : pB ^ r * pB ^ e = r * pB + e * pB :=
      (hamgm_eq pB pB hpB.le hpB.le).mpr rfl
    have hattain : A * pA ^ e + B * pB ^ e = c := by
      calc
        A * pA ^ e + B * pB ^ e =
            c * (pA ^ r * pA ^ e) + c * (pB ^ r * pB ^ e) := by
              rw [← mul_assoc, hcA, ← mul_assoc, hcB]
        _ = c * (r * pA + e * pA) + c * (r * pB + e * pB) := by rw [heA, heB]
        _ = c := by
          calc
            _ = c * ((r + e) * (pA + pB)) := by ring
            _ = c := by rw [hp_sum]; norm_num [r, e]
    simpa [pA, pB, e, c, D] using hattain

/-- A row marginal is the sum over the two columns. -/
theorem rowMarginal_eq_sum (q : Cell → ℝ) (i : Bit) :
    rowMarginal q i = ∑ j, q (i, j) := by
  simp [rowMarginal, Fin.sum_univ_two]

/-- A column marginal is the sum over the two rows. -/
theorem columnMarginal_eq_sum (q : Cell → ℝ) (j : Bit) :
    columnMarginal q j = ∑ i, q (i, j) := by
  simp [columnMarginal, Fin.sum_univ_two]

/-- Pushing forward by the first projection gives the row marginal. -/
theorem pushforward_fst_eq_rowMarginal (q : Cell → ℝ) :
    pushforward Prod.fst q = rowMarginal q := by
  funext i
  unfold pushforward stoch_to_det.push
  rw [show (univ.filter fun z : Cell => z.1 = i) =
      univ.image fun j : Bit => (i, j) by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hz
      exact ⟨z.2, by ext <;> simp [hz]⟩
    · rintro ⟨j, rfl⟩
      rfl]
  rw [sum_image]
  · exact (rowMarginal_eq_sum q i).symm
  · intro a _ b _ h
    exact congrArg Prod.snd h

/-- Pushing forward by the second projection gives the column marginal. -/
theorem pushforward_snd_eq_columnMarginal (q : Cell → ℝ) :
    pushforward Prod.snd q = columnMarginal q := by
  funext j
  unfold pushforward stoch_to_det.push
  rw [show (univ.filter fun z : Cell => z.2 = j) =
      univ.image fun i : Bit => (i, j) by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hz
      exact ⟨z.1, by ext <;> simp [hz]⟩
    · rintro ⟨i, rfl⟩
      rfl]
  rw [sum_image]
  · exact (columnMarginal_eq_sum q j).symm
  · intro a _ b _ h
    exact congrArg Prod.fst h

/-- A binary PMF sums to one in its two displayed coordinates. -/
theorem binaryPMF_sum {v : Bit → ℝ} (hv : IsPMF v) : v 0 + v 1 = 1 := by
  simpa [stoch_to_det.mass, Fin.sum_univ_two] using hv.total

/-- At least one coordinate of a binary PMF is positive. -/
theorem binaryPMF_some_pos {v : Bit → ℝ} (hv : IsPMF v) :
    0 < v 0 ∨ 0 < v 1 := by
  have hs := binaryPMF_sum hv
  have h0 := hv.nonneg 0
  have h1 := hv.nonneg 1
  rcases lt_or_eq_of_le h0 with h0 | h0
  · exact Or.inl h0
  · right
    linarith

/-- A positive weighted sum of two nonnegative two-thirds powers is positive when one
input is positive. -/
theorem positive_twoTerm_rpow {A B s0 s1 : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1)
    (hs : 0 < s0 ∨ 0 < s1) :
    0 < A * s0 ^ ((2 : ℝ) / 3) + B * s1 ^ ((2 : ℝ) / 3) := by
  rcases hs with hs | hs
  · have hp : 0 < s0 ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hs _
    have hn : 0 ≤ s1 ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hs1 _
    positivity
  · have hp : 0 < s1 ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hs _
    have hn : 0 ≤ s0 ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hs0 _
    positivity

/-- The binary law proportional to the cubes of two coefficients. -/
def cubeLaw (A B : ℝ) : Bit → ℝ := fun i =>
  if i = 0 then A ^ 3 / (A ^ 3 + B ^ 3) else B ^ 3 / (A ^ 3 + B ^ 3)

/-- Positive coefficients define a PMF through `cubeLaw`. -/
theorem cubeLaw_isPMF {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IsPMF (cubeLaw A B) := by
  have hD : 0 < A ^ 3 + B ^ 3 := by positivity
  constructor
  · intro i
    fin_cases i <;> simp [cubeLaw] <;> positivity
  · simp [stoch_to_det.mass, Fin.sum_univ_two, cubeLaw]
    field_simp [hD.ne']

/-- Cubing a nonnegative one-third power returns the base. -/
theorem oneThird_rpow_cube {D : ℝ} (hD : 0 ≤ D) :
    (D ^ ((1 : ℝ) / 3)) ^ 3 = D := by
  simpa [one_div] using
    (Real.rpow_inv_natCast_pow (n := 3) hD (by norm_num : (3 : ℕ) ≠ 0))

/-- Cubing a nonnegative two-thirds power gives the square. -/
theorem twoThirds_rpow_cube {a : ℝ} (ha : 0 ≤ a) :
    (a ^ ((2 : ℝ) / 3)) ^ 3 = a ^ 2 := by
  calc
    (a ^ ((2 : ℝ) / 3)) ^ 3 = a ^ (((2 : ℝ) / 3) * (3 : ℕ)) :=
      (Real.rpow_mul_natCast ha _ _).symm
    _ = a ^ (2 : ℝ) := by norm_num
    _ = a ^ 2 := Real.rpow_natCast _ _

/-- A uniform cap on the two-term response bounds its cube-sum by one. -/
theorem twoThirds_root_le_one {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hcap : ∀ v : Bit → ℝ, IsPMF v →
      A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3) ≤ 1) :
    (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) ≤ 1 ∧ A ^ 3 + B ^ 3 ≤ 1 := by
  have hmax := twoThirdsPowerMaximum A B hA hB
  have hroot : (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) ≤ 1 := by
    rw [← hmax.2]
    exact hcap _ (cubeLaw_isPMF hA hB)
  refine ⟨hroot, ?_⟩
  have hD : 0 ≤ A ^ 3 + B ^ 3 := by positivity
  have hc := pow_le_pow_left₀ (Real.rpow_nonneg hD _) hroot 3
  rw [oneThird_rpow_cube hD] at hc
  simpa using hc

/-- Equality at the cap determines the cube law and makes the cube-sum one. -/
theorem twoThirds_eq_one_bestResponse {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {v : Bit → ℝ} (hv : IsPMF v)
    (hcap : ∀ t : Bit → ℝ, IsPMF t →
      A * t 0 ^ ((2 : ℝ) / 3) + B * t 1 ^ ((2 : ℝ) / 3) ≤ 1)
    (hattains : A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3) = 1) :
    A ^ 3 + B ^ 3 = 1 ∧
      v 0 = A ^ 3 / (A ^ 3 + B ^ 3) ∧ v 1 = B ^ 3 / (A ^ 3 + B ^ 3) := by
  have hmax := twoThirdsPowerMaximum A B hA hB
  have hle := (twoThirds_root_le_one hA hB hcap).1
  have hge : 1 ≤ (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) := by
    calc
      1 = A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3) := hattains.symm
      _ ≤ (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) := (hmax.1 v hv).1
  have hr : (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) = 1 := le_antisymm hle hge
  have hD : 0 ≤ A ^ 3 + B ^ 3 := by positivity
  have hsum : A ^ 3 + B ^ 3 = 1 := by
    calc
      A ^ 3 + B ^ 3 = ((A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3)) ^ 3 :=
        (oneThird_rpow_cube hD).symm
      _ = 1 := by rw [hr]; norm_num
  refine ⟨hsum, ?_⟩
  apply (hmax.1 v hv).2
  rw [hattains, hr]

/-- Expand `Lambda` by rows on a binary table. -/
theorem lambda_univ_eq_rows (w : Cell → ℝ) (u v : Bit → ℝ) :
    Lambda (univ : Finset Cell) w u v =
      (w (0, 0) * v 0 ^ ((2 : ℝ) / 3) + w (0, 1) * v 1 ^ ((2 : ℝ) / 3)) *
        u 0 ^ ((2 : ℝ) / 3) +
      (w (1, 0) * v 0 ^ ((2 : ℝ) / 3) + w (1, 1) * v 1 ^ ((2 : ℝ) / 3)) *
        u 1 ^ ((2 : ℝ) / 3) := by
  simp [Lambda, stoch_to_det.Lambda, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Expand `Lambda` by columns on a binary table. -/
theorem lambda_univ_eq_columns (w : Cell → ℝ) (u v : Bit → ℝ) :
    Lambda (univ : Finset Cell) w u v =
      (w (0, 0) * u 0 ^ ((2 : ℝ) / 3) + w (1, 0) * u 1 ^ ((2 : ℝ) / 3)) *
        v 0 ^ ((2 : ℝ) / 3) +
      (w (0, 1) * u 0 ^ ((2 : ℝ) / 3) + w (1, 1) * u 1 ^ ((2 : ℝ) / 3)) *
        v 1 ^ ((2 : ℝ) / 3) := by
  simp [Lambda, stoch_to_det.Lambda, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- A contact attains `Lambda = 1` at its row and column marginals. -/
theorem contact_lambda_eq_one {w q : Cell → ℝ}
    (hq : IsContact (univ : Finset Cell) w q) :
    Lambda (univ : Finset Cell) w (rowMarginal q) (columnMarginal q) = 1 := by
  rw [← pushforward_fst_eq_rowMarginal, ← pushforward_snd_eq_columnMarginal]
  change stoch_to_det.Lambda (univ : Finset Cell) w
      (stoch_to_det.mX q) (stoch_to_det.mY q) = 1
  rw [stoch_to_det.Lambda]
  have heq : ∀ z : Cell,
      w z * stoch_to_det.mX q z.1 ^ ((2 : ℝ) / 3) *
          stoch_to_det.mY q z.2 ^ ((2 : ℝ) / 3) = q z := by
    intro z
    exact (hq.2.2 z (mem_univ z)).symm
  simp_rw [heq]
  simpa [stoch_to_det.mass] using hq.1.total

/-- The normalized row parameter scales its two-thirds powers by the square of the
cube-root ratio. -/
theorem normalized_cubeParameter_rpow_scale {u0 u1 x : ℝ} (hx : 0 < x)
    (hu0 : u0 = 1 / (1 + x ^ 3)) (hu1 : u1 = x ^ 3 / (1 + x ^ 3)) :
    u1 ^ ((2 : ℝ) / 3) = x ^ 2 * u0 ^ ((2 : ℝ) / 3) := by
  have hden : 0 < 1 + x ^ 3 := by positivity
  have hp0 : 0 < u0 := by rw [hu0]; positivity
  have hp1 : 0 < u1 := by rw [hu1]; positivity
  let x' := (u1 / u0) ^ ((3 : ℝ)⁻¹)
  obtain ⟨hx'p, hx'cube, hscale, -⟩ := positiveCubeRootIdentities u0 u1 hp0 hp1
  have hcubes : x' ^ 3 = x ^ 3 := by
    rw [hx'cube, hu0, hu1]
    field_simp [hden.ne']
  have heq : x' = x :=
    (pow_left_inj₀ hx'p.le hx.le (by norm_num : (3 : ℕ) ≠ 0)).mp hcubes
  rw [← heq]
  exact hscale

/-- Every feasible binary contact has a positive row cube parameter. -/
theorem contact_hasRowCubeParameter : ContactHasRowCubeParameter := by
  intro w q hw hq
  let u := rowMarginal q
  let v := columnMarginal q
  have hu : IsPMF u := by
    change IsPMF (rowMarginal q)
    rw [← pushforward_fst_eq_rowMarginal]
    exact pushforward_isPMF hq.1
  have hv : IsPMF v := by
    change IsPMF (columnMarginal q)
    rw [← pushforward_snd_eq_columnMarginal]
    exact pushforward_isPMF hq.1
  let A := w (0, 0) * v 0 ^ ((2 : ℝ) / 3) + w (0, 1) * v 1 ^ ((2 : ℝ) / 3)
  let B := w (1, 0) * v 0 ^ ((2 : ℝ) / 3) + w (1, 1) * v 1 ^ ((2 : ℝ) / 3)
  have hA : 0 < A := positive_twoTerm_rpow (hw.1 _ (mem_univ _))
    (hw.1 _ (mem_univ _)) (hv.nonneg 0) (hv.nonneg 1) (binaryPMF_some_pos hv)
  have hB : 0 < B := positive_twoTerm_rpow (hw.1 _ (mem_univ _))
    (hw.1 _ (mem_univ _)) (hv.nonneg 0) (hv.nonneg 1) (binaryPMF_some_pos hv)
  have hcap : ∀ t : Bit → ℝ, IsPMF t →
      A * t 0 ^ ((2 : ℝ) / 3) + B * t 1 ^ ((2 : ℝ) / 3) ≤ 1 := by
    intro t ht
    rw [← lambda_univ_eq_rows w t v]
    exact hw.2 t v ht hv
  have hattains : A * u 0 ^ ((2 : ℝ) / 3) + B * u 1 ^ ((2 : ℝ) / 3) = 1 := by
    rw [← lambda_univ_eq_rows w u v]
    exact contact_lambda_eq_one hq
  obtain ⟨-, hu0, hu1⟩ := twoThirds_eq_one_bestResponse hA hB hu hcap hattains
  have hu0p : 0 < u 0 := by rw [hu0]; positivity
  have hu1p : 0 < u 1 := by rw [hu1]; positivity
  let x := (u 1 / u 0) ^ ((3 : ℝ)⁻¹)
  obtain ⟨hx, -, -, hnorm⟩ := positiveCubeRootIdentities (u 0) (u 1) hu0p hu1p
  have forms := hnorm (binaryPMF_sum hu)
  exact ⟨x, hx, forms.1, forms.2⟩

/-- Feasibility makes the feasibility expression nonnegative at every positive parameter. -/
theorem feasibilityExpression_nonneg : FeasibilityExpressionNonnegative := by
  intro w hw x hx
  let u := cubeLaw 1 x
  have hu : IsPMF u := cubeLaw_isPMF one_pos hx
  have hd : 0 < 1 + x ^ 3 := by positivity
  have hu0 : u 0 = 1 / (1 + x ^ 3) := by simp [u, cubeLaw]
  have hu1 : u 1 = x ^ 3 / (1 + x ^ 3) := by simp [u, cubeLaw]
  have hscale := normalized_cubeParameter_rpow_scale hx hu0 hu1
  let a0 := w (0, 0) + w (1, 0) * x ^ 2
  let a1 := w (0, 1) + w (1, 1) * x ^ 2
  let A := w (0, 0) * u 0 ^ ((2 : ℝ) / 3) + w (1, 0) * u 1 ^ ((2 : ℝ) / 3)
  let B := w (0, 1) * u 0 ^ ((2 : ℝ) / 3) + w (1, 1) * u 1 ^ ((2 : ℝ) / 3)
  have hu0p : 0 < u 0 := by rw [hu0]; positivity
  have hspos : 0 < u 0 ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hu0p _
  have ha0 : 0 < a0 := by
    dsimp [a0]
    have h00 := hw.1 (0, 0) (mem_univ _)
    have h10 := hw.1 (1, 0) (mem_univ _)
    positivity
  have ha1 : 0 < a1 := by
    dsimp [a1]
    have h01 := hw.1 (0, 1) (mem_univ _)
    have h11 := hw.1 (1, 1) (mem_univ _)
    positivity
  have hA : A = u 0 ^ ((2 : ℝ) / 3) * a0 := by
    dsimp [A, a0]
    rw [hscale]
    ring
  have hB : B = u 0 ^ ((2 : ℝ) / 3) * a1 := by
    dsimp [B, a1]
    rw [hscale]
    ring
  have hAp : 0 < A := by rw [hA]; positivity
  have hBp : 0 < B := by rw [hB]; positivity
  have hcap : ∀ v : Bit → ℝ, IsPMF v →
      A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3) ≤ 1 := by
    intro v hv
    rw [← lambda_univ_eq_columns w u v]
    exact hw.2 u v hu hv
  have hsum : A ^ 3 + B ^ 3 ≤ 1 := (twoThirds_root_le_one hAp hBp hcap).2
  have hs3 : (u 0 ^ ((2 : ℝ) / 3)) ^ 3 = (u 0) ^ 2 :=
    twoThirds_rpow_cube (hu.nonneg 0)
  rw [hA, hB, mul_pow, mul_pow, hs3, hu0] at hsum
  have hd2 : 0 < (1 + x ^ 3) ^ 2 := sq_pos_of_pos hd
  have hpoly : a0 ^ 3 + a1 ^ 3 ≤ (1 + x ^ 3) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsum hd2.le
    field_simp [hd.ne'] at hm
    nlinarith
  dsimp [feasibilityExpression, a0, a1]
  linarith

/-- Swap the two entries of a binary law. -/
def swapBitLaw (u : Bit → ℝ) : Bit → ℝ := fun i => if i = 0 then u 1 else u 0

/-- Swapping a binary law preserves the PMF property. -/
theorem swapBitLaw_isPMF {u : Bit → ℝ} (hu : IsPMF u) : IsPMF (swapBitLaw u) := by
  constructor
  · intro i
    fin_cases i <;> simp [swapBitLaw, hu.nonneg]
  · simpa [stoch_to_det.mass, Fin.sum_univ_two, swapBitLaw, add_comm] using hu.total

/-- A nested two-thirds-power cap is strict at either row endpoint. -/
theorem nested_twoThirds_endpoint_strict {A B C D : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hcap : ∀ u v : Bit → ℝ, IsPMF u → IsPMF v →
      (A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3)) *
          u 0 ^ ((2 : ℝ) / 3) +
      (C * v 0 ^ ((2 : ℝ) / 3) + D * v 1 ^ ((2 : ℝ) / 3)) *
          u 1 ^ ((2 : ℝ) / 3) ≤ 1) :
    A ^ 3 + B ^ 3 < 1 := by
  let v := cubeLaw A B
  have hv : IsPMF v := cubeLaw_isPMF hA hB
  let R := A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3)
  let S := C * v 0 ^ ((2 : ℝ) / 3) + D * v 1 ^ ((2 : ℝ) / 3)
  have hR : R = (A ^ 3 + B ^ 3) ^ ((1 : ℝ) / 3) := by
    simpa [R, v, cubeLaw] using (twoThirdsPowerMaximum A B hA hB).2
  have hRp : 0 < R := positive_twoTerm_rpow hA hB (hv.nonneg 0) (hv.nonneg 1)
    (binaryPMF_some_pos hv)
  have hSp : 0 < S := positive_twoTerm_rpow hC hD (hv.nonneg 0) (hv.nonneg 1)
    (binaryPMF_some_pos hv)
  have houter : ∀ u : Bit → ℝ, IsPMF u →
      R * u 0 ^ ((2 : ℝ) / 3) + S * u 1 ^ ((2 : ℝ) / 3) ≤ 1 := by
    intro u hu
    exact hcap u v hu hv
  have hrs : R ^ 3 + S ^ 3 ≤ 1 := (twoThirds_root_le_one hRp hSp houter).2
  have hAB : 0 ≤ A ^ 3 + B ^ 3 := by positivity
  have hR3 : R ^ 3 = A ^ 3 + B ^ 3 := by
    rw [hR]
    convert oneThird_rpow_cube hAB using 1 <;> norm_num
  have hS3 : 0 < S ^ 3 := by positivity
  nlinarith

/-- Feasibility makes each row endpoint cube-sum strictly less than one. -/
theorem feasible_row_endpoint_strict {w : Cell → ℝ}
    (hw : Feasible (univ : Finset Cell) w) (i : Bit) :
    w (i, 0) ^ 3 + w (i, 1) ^ 3 < 1 := by
  have hp (z : Cell) : 0 < w z := hw.1 z (mem_univ z)
  fin_cases i
  · apply nested_twoThirds_endpoint_strict (hp (0, 0)) (hp (0, 1))
      (hp (1, 0)) (hp (1, 1))
    intro u v hu hv
    rw [← lambda_univ_eq_rows w u v]
    exact hw.2 u v hu hv
  · apply nested_twoThirds_endpoint_strict (hp (1, 0)) (hp (1, 1))
      (hp (0, 0)) (hp (0, 1))
    intro u v hu hv
    have hs := hw.2 (swapBitLaw u) v (swapBitLaw_isPMF hu) hv
    change Lambda (univ : Finset Cell) w (swapBitLaw u) v ≤ 1 at hs
    rw [lambda_univ_eq_rows] at hs
    simpa [swapBitLaw, add_comm] using hs

/-- Both feasibility-polynomial endpoint coefficients are positive. -/
theorem feasibilityEndpointCoefficients_positive :
    FeasibilityEndpointCoefficientsPositive := by
  intro w hw
  have h0 := feasible_row_endpoint_strict hw 0
  have h1 := feasible_row_endpoint_strict hw 1
  constructor <;> nlinarith

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

open Finset Polynomial

namespace Binary


/-- A contact row parameter is a feasibility root and determines its column response. -/
theorem contactParameter_bestResponse : ContactParameterBestResponse := by
  intro w q hw hq x hrow
  let u := rowMarginal q
  let v := columnMarginal q
  have hu : IsPMF u := by
    change IsPMF (rowMarginal q)
    rw [← pushforward_fst_eq_rowMarginal]
    exact pushforward_isPMF hq.1
  have hv : IsPMF v := by
    change IsPMF (columnMarginal q)
    rw [← pushforward_snd_eq_columnMarginal]
    exact pushforward_isPMF hq.1
  have hx : 0 < x := hrow.1
  have hu0 : u 0 = 1 / (1 + x ^ 3) := hrow.2.1
  have hu1 : u 1 = x ^ 3 / (1 + x ^ 3) := hrow.2.2
  have hscale := normalized_cubeParameter_rpow_scale hx hu0 hu1
  let a0 := w (0, 0) + w (1, 0) * x ^ 2
  let a1 := w (0, 1) + w (1, 1) * x ^ 2
  let A := w (0, 0) * u 0 ^ ((2 : ℝ) / 3) + w (1, 0) * u 1 ^ ((2 : ℝ) / 3)
  let B := w (0, 1) * u 0 ^ ((2 : ℝ) / 3) + w (1, 1) * u 1 ^ ((2 : ℝ) / 3)
  have hden : 0 < 1 + x ^ 3 := by positivity
  have hu0p : 0 < u 0 := by rw [hu0]; positivity
  have hspos : 0 < u 0 ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hu0p _
  have ha0 : 0 < a0 := by
    dsimp [a0]
    have h00 := hw.1 (0, 0) (mem_univ _)
    have h10 := hw.1 (1, 0) (mem_univ _)
    positivity
  have ha1 : 0 < a1 := by
    dsimp [a1]
    have h01 := hw.1 (0, 1) (mem_univ _)
    have h11 := hw.1 (1, 1) (mem_univ _)
    positivity
  have hA : A = u 0 ^ ((2 : ℝ) / 3) * a0 := by
    dsimp [A, a0]
    rw [hscale]
    ring
  have hB : B = u 0 ^ ((2 : ℝ) / 3) * a1 := by
    dsimp [B, a1]
    rw [hscale]
    ring
  have hAp : 0 < A := by rw [hA]; positivity
  have hBp : 0 < B := by rw [hB]; positivity
  have hcap : ∀ t : Bit → ℝ, IsPMF t →
      A * t 0 ^ ((2 : ℝ) / 3) + B * t 1 ^ ((2 : ℝ) / 3) ≤ 1 := by
    intro t ht
    rw [← lambda_univ_eq_columns w u t]
    exact hw.2 u t hu ht
  have hattains : A * v 0 ^ ((2 : ℝ) / 3) + B * v 1 ^ ((2 : ℝ) / 3) = 1 := by
    rw [← lambda_univ_eq_columns w u v]
    exact contact_lambda_eq_one hq
  obtain ⟨hAB, hv0, hv1⟩ := twoThirds_eq_one_bestResponse hAp hBp hv hcap hattains
  have hs3 : (u 0 ^ ((2 : ℝ) / 3)) ^ 3 = (u 0) ^ 2 :=
    twoThirds_rpow_cube (hu.nonneg 0)
  have hpoly : feasibilityExpression w x = 0 := by
    rw [hA, hB, mul_pow, mul_pow, hs3, hu0] at hAB
    dsimp [feasibilityExpression, a0, a1]
    field_simp [hden.ne'] at hAB ⊢
    nlinarith
  refine ⟨hpoly, ?_⟩
  have hv0p : 0 < v 0 := by rw [hv0, hAB]; positivity
  have hv1p : 0 < v 1 := by rw [hv1, hAB]; positivity
  let y := (v 1 / v 0) ^ ((3 : ℝ)⁻¹)
  obtain ⟨hy, hycube, -, hnorm⟩ := positiveCubeRootIdentities (v 0) (v 1) hv0p hv1p
  have hforms := hnorm (binaryPMF_sum hv)
  have hycube' : y ^ 3 = (a1 / a0) ^ 3 := by
    rw [hycube, hv0, hv1, hA, hB]
    field_simp [hAB, hspos.ne', ha0.ne']
  have hyratio : y = a1 / a0 :=
    (pow_left_inj₀ hy.le (div_pos ha1 ha0).le (by norm_num : (3 : ℕ) ≠ 0)).mp hycube'
  exact ⟨y, ⟨hy, hforms.1, hforms.2⟩, by simpa [a0, a1] using hyratio⟩

/-- Equal positive row parameters force two contacts to coincide. -/
theorem contactParameter_injective : ContactParameterInjective := by
  intro w q r hw hq hr x hqx hrx
  obtain ⟨-, yq, hyq, hyqratio⟩ := contactParameter_bestResponse w q hw hq x hqx
  obtain ⟨-, yr, hyr, hyrratio⟩ := contactParameter_bestResponse w r hw hr x hrx
  have hy : yq = yr := hyqratio.trans hyrratio.symm
  have hX : rowMarginal q = rowMarginal r := by
    funext i
    fin_cases i
    · exact hqx.2.1.trans hrx.2.1.symm
    · exact hqx.2.2.trans hrx.2.2.symm
  have hY : columnMarginal q = columnMarginal r := by
    funext j
    fin_cases j
    · exact hyq.2.1.trans (hy ▸ hyr.2.1.symm)
    · exact hyq.2.2.trans (hy ▸ hyr.2.2.symm)
  funext z
  have hXq : stoch_to_det.mX q = rowMarginal q := by
    change pushforward Prod.fst q = rowMarginal q
    exact pushforward_fst_eq_rowMarginal q
  have hXr : stoch_to_det.mX r = rowMarginal r := by
    change pushforward Prod.fst r = rowMarginal r
    exact pushforward_fst_eq_rowMarginal r
  have hYq : stoch_to_det.mY q = columnMarginal q := by
    change pushforward Prod.snd q = columnMarginal q
    exact pushforward_snd_eq_columnMarginal q
  have hYr : stoch_to_det.mY r = columnMarginal r := by
    change pushforward Prod.snd r = columnMarginal r
    exact pushforward_snd_eq_columnMarginal r
  rw [hq.2.2 z (mem_univ z), hr.2.2 z (mem_univ z)]
  rw [hXq, hXr, hYq, hYr]
  rw [hX, hY]

/-- A positive contact row marginal is the cube of its response coefficient. -/
theorem contact_rowMarginal_eq_coefficient_cube {w q : Cell → ℝ}
    (hq : IsContact (univ : Finset Cell) w q)
    (i : Bit) (hui : 0 < rowMarginal q i) :
    rowMarginal q i =
      (w (i, 0) * columnMarginal q 0 ^ ((2 : ℝ) / 3) +
       w (i, 1) * columnMarginal q 1 ^ ((2 : ℝ) / 3)) ^ 3 := by
  let u := rowMarginal q i
  let R := w (i, 0) * columnMarginal q 0 ^ ((2 : ℝ) / 3) +
    w (i, 1) * columnMarginal q 1 ^ ((2 : ℝ) / 3)
  have heq : u = R * u ^ ((2 : ℝ) / 3) := by
    have hz0 := hq.2.2 (i, 0) (mem_univ (i, 0))
    have hz1 := hq.2.2 (i, 1) (mem_univ (i, 1))
    have hXq : stoch_to_det.mX q = rowMarginal q := by
      change pushforward Prod.fst q = rowMarginal q
      exact pushforward_fst_eq_rowMarginal q
    have hYq : stoch_to_det.mY q = columnMarginal q := by
      change pushforward Prod.snd q = columnMarginal q
      exact pushforward_snd_eq_columnMarginal q
    rw [hXq, hYq] at hz0 hz1
    calc
      u = q (i, 0) + q (i, 1) := by simp [u, rowMarginal]
      _ = (w (i, 0) * rowMarginal q i ^ ((2 : ℝ) / 3) *
            columnMarginal q 0 ^ ((2 : ℝ) / 3)) +
          (w (i, 1) * rowMarginal q i ^ ((2 : ℝ) / 3) *
            columnMarginal q 1 ^ ((2 : ℝ) / 3)) := congrArg₂ (· + ·) hz0 hz1
      _ = R * u ^ ((2 : ℝ) / 3) := by dsimp [R, u]; ring
  have hrpow := twoThirds_rpow_cube hui.le
  have hu2 : 0 < u ^ 2 := by dsimp [u]; positivity
  have hc := congrArg (fun z : ℝ => z ^ 3) heq
  rw [mul_pow, hrpow] at hc
  dsimp [u, R] at hc ⊢
  nlinarith

/-- Distinct contacts have distinct kernel column ratios. -/
theorem distinctContacts_haveDistinctKernelNodes :
    DistinctContactsHaveDistinctKernelNodes := by
  intro w q r hw hq hr hqr hnodes
  obtain ⟨xq, hxq⟩ := contact_hasRowCubeParameter w q hw hq
  obtain ⟨xr, hxr⟩ := contact_hasRowCubeParameter w r hw hr
  obtain ⟨-, yq, hyq, hyqratio⟩ := contactParameter_bestResponse w q hw hq xq hxq
  obtain ⟨-, yr, hyr, hyrratio⟩ := contactParameter_bestResponse w r hw hr xr hxr
  have hp00 : 0 < w (0, 0) := hw.1 _ (mem_univ _)
  have hp01 : 0 < w (0, 1) := hw.1 _ (mem_univ _)
  have hp10 : 0 < w (1, 0) := hw.1 _ (mem_univ _)
  have hp11 : 0 < w (1, 1) := hw.1 _ (mem_univ _)
  have hdet : w (1, 0) * w (0, 1) = w (1, 1) * w (0, 0) := by
    field_simp [hp00.ne', hp01.ne'] at hnodes
    nlinarith
  have hratio (x : ℝ) :
      (w (0, 1) + w (1, 1) * x ^ 2) / (w (0, 0) + w (1, 0) * x ^ 2) =
        w (0, 1) / w (0, 0) := by
    have hden : 0 < w (0, 0) + w (1, 0) * x ^ 2 := by positivity
    field_simp [hp00.ne', hden.ne']
    nlinarith
  have hy : yq = yr := by
    rw [hyqratio, hyrratio, hratio xq, hratio xr]
  have hY : columnMarginal q = columnMarginal r := by
    funext j
    fin_cases j
    · exact hyq.2.1.trans (hy ▸ hyr.2.1.symm)
    · exact hyq.2.2.trans (hy ▸ hyr.2.2.symm)
  have hX : rowMarginal q = rowMarginal r := by
    funext i
    have hdenq : 0 < 1 + xq ^ 3 := by have := hxq.1; positivity
    have hdenr : 0 < 1 + xr ^ 3 := by have := hxr.1; positivity
    have hqip : 0 < rowMarginal q i := by
      fin_cases i
      · simpa using (show 0 < rowMarginal q 0 by rw [hxq.2.1]; positivity)
      · simpa using (show 0 < rowMarginal q 1 by
          rw [hxq.2.2]; exact div_pos (pow_pos hxq.1 3) hdenq)
    have hrip : 0 < rowMarginal r i := by
      fin_cases i
      · simpa using (show 0 < rowMarginal r 0 by rw [hxr.2.1]; positivity)
      · simpa using (show 0 < rowMarginal r 1 by
          rw [hxr.2.2]; exact div_pos (pow_pos hxr.1 3) hdenr)
    rw [contact_rowMarginal_eq_coefficient_cube hq i hqip,
      contact_rowMarginal_eq_coefficient_cube hr i hrip, hY]
  apply hqr
  exact contactParameter_injective w q r hw hq hr xq hxq (by
    refine ⟨hxq.1, ?_, ?_⟩
    · rw [← hX]
      exact hxq.2.1
    · rw [← hX]
      exact hxq.2.2)

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

open Finset Polynomial

namespace Binary

/-! ## Polynomial multiplicity and factorization -/

/-- A positive root of a polynomial nonnegative on the positive ray has multiplicity at
least two. -/
theorem positiveRoot_square_dvd : PositiveRootSquareDivides := by
  intro P x hx hnonneg hroot
  by_cases hP : P = 0
  · simp [hP]
  have hminOn : IsMinOn (fun y : ℝ => P.eval y) (Set.Ioi 0) x := by
    intro y hy
    change P.eval x ≤ P.eval y
    rw [hroot]
    exact hnonneg y hy
  have hmin : IsLocalMin (fun y : ℝ => P.eval y) x :=
    hminOn.isLocalMin (Ioi_mem_nhds hx)
  have hder : P.derivative.eval x = 0 :=
    hmin.hasDerivAt_eq_zero (P.hasDerivAt x)
  apply (Polynomial.le_rootMultiplicity_iff hP).mp
  have hm := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).mpr ⟨hroot, hder⟩
  omega

private lemma three_root_squares_product_dvd
    (P : Polynomial ℝ) (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : (X - C x) ^ 2 ∣ P) (hy : (X - C y) ^ 2 ∣ P)
    (hz : (X - C z) ^ 2 ∣ P) :
    (X - C x) ^ 2 * (X - C y) ^ 2 * (X - C z) ^ 2 ∣ P := by
  have hu {a b : ℝ} (h : a ≠ b) : IsUnit (a - b) :=
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h)
  have hxy' : IsCoprime ((X - C x) ^ 2) ((X - C y) ^ 2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hu hxy)).pow
  have hxz' : IsCoprime ((X - C x) ^ 2) ((X - C z) ^ 2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hu hxz)).pow
  have hyz' : IsCoprime ((X - C y) ^ 2) ((X - C z) ^ 2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hu hyz)).pow
  exact (hxz'.mul_left hyz').mul_dvd (hxy'.mul_dvd hx hy) hz

private lemma cubic_product_square_coeff_five (x y z : ℝ) :
    (((X - C x) * (X - C y) * (X - C z)) ^ 2 : Polynomial ℝ).coeff 5 =
      -2 * (x + y + z) := by
  let A := x + y + z
  let B := x * y + x * z + y * z
  let D := x * y * z
  have hsparse :
      ((X - C x) * (X - C y) * (X - C z)) ^ 2 =
        X ^ 6 - C (2 * A) * X ^ 5 + C (A ^ 2 + 2 * B) * X ^ 4 -
          C (2 * D + 2 * A * B) * X ^ 3 + C (B ^ 2 + 2 * A * D) * X ^ 2 -
          C (2 * B * D) * X + C (D ^ 2) := by
    apply Polynomial.funext
    intro u
    simp
    dsimp [A, B, D]
    ring
  rw [hsparse]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
    if_false, if_true, Nat.reduceEqDiff]
  dsimp [A]
  ring

/-- Three distinct positive double roots contradict the missing degree-five coefficient of
a nonzero sextic. -/
theorem threePositiveDoubleRoots_impossible : ThreePositiveDoubleRootsImpossible := by
  intro P x y z hP hdeg hcoeff hx hy hz hxy hxz hyz hdx hdy hdz
  let g : Polynomial ℝ := (X - C x) * (X - C y) * (X - C z)
  have hd : g ^ 2 ∣ P := by
    have h := three_root_squares_product_dvd P x y z hxy hxz hyz hdx hdy hdz
    convert h using 1 <;> simp only [g] <;> ring
  obtain ⟨Q, hPQ⟩ := hd
  have hgmonic : g.Monic := by
    dsimp [g]
    exact ((monic_X_sub_C x).mul (monic_X_sub_C y)).mul (monic_X_sub_C z)
  have hgdeg : g.natDegree = 3 := by
    dsimp [g]
    simp [natDegree_mul, X_sub_C_ne_zero]
  have hg2monic : (g ^ 2).Monic := hgmonic.pow 2
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    simpa [h, hPQ]
  have hmuldeg := natDegree_mul hg2monic.ne_zero hQ
  have hQdeg : Q.natDegree = 0 := by
    rw [natDegree_pow, hgdeg] at hmuldeg
    rw [hPQ] at hdeg
    omega
  let c := Q.coeff 0
  have hQC : Q = C c := eq_C_of_natDegree_eq_zero hQdeg
  have hc : c ≠ 0 := by
    intro hc
    apply hQ
    rw [hQC, hc]
    simp
  rw [hQC] at hPQ
  have h5 : (g ^ 2).coeff 5 = -2 * (x + y + z) := by
    dsimp [g]
    exact cubic_product_square_coeff_five x y z
  rw [hPQ, mul_comm, coeff_C_mul, h5] at hcoeff
  have hsum : x + y + z ≠ 0 := by nlinarith
  exact (mul_ne_zero hc (mul_ne_zero (by norm_num) hsum)) hcoeff

private def explicitFeasibilityPolynomial (w : Cell → ℝ) : Polynomial ℝ :=
  (1 + X ^ 3) ^ 2 - (C (w (0, 0)) + C (w (1, 0)) * X ^ 2) ^ 3 -
    (C (w (0, 1)) + C (w (1, 1)) * X ^ 2) ^ 3

private lemma explicitFeasibilityPolynomial_eval (w : Cell → ℝ) (u : ℝ) :
    (explicitFeasibilityPolynomial w).eval u = feasibilityExpression w u := by
  simp [explicitFeasibilityPolynomial, feasibilityExpression] <;> ring

private lemma explicitFeasibilityPolynomial_coeffs (w : Cell → ℝ) :
    (explicitFeasibilityPolynomial w).coeff 5 = 0 ∧
    (explicitFeasibilityPolynomial w).coeff 3 = 2 ∧
    (explicitFeasibilityPolynomial w).coeff 1 = 0 := by
  let a := w (0, 0)
  let c := w (1, 0)
  let b := w (0, 1)
  let d := w (1, 1)
  have hsparse : explicitFeasibilityPolynomial w =
      C (1 - a ^ 3 - b ^ 3) + C (-3 * a ^ 2 * c - 3 * b ^ 2 * d) * X ^ 2 +
        C 2 * X ^ 3 + C (-3 * a * c ^ 2 - 3 * b * d ^ 2) * X ^ 4 +
        C (1 - c ^ 3 - d ^ 3) * X ^ 6 := by
    apply Polynomial.funext
    intro u
    simp [explicitFeasibilityPolynomial]
    dsimp [a, b, c, d]
    ring
  rw [hsparse]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
    if_false, if_true, Nat.reduceEqDiff]
  norm_num

private lemma explicitFeasibilityPolynomial_natDegree_le (w : Cell → ℝ) :
    (explicitFeasibilityPolynomial w).natDegree ≤ 6 := by
  unfold explicitFeasibilityPolynomial
  compute_degree

private lemma quartic_root_expansion (s t : ℝ) :
    let R := s + t
    let T := s * t
    (X - C s) ^ 2 * (X - C t) ^ 2 =
      X ^ 4 - C (2 * R) * X ^ 3 + C (R ^ 2 + 2 * T) * X ^ 2 -
        C (2 * R * T) * X + C (T ^ 2) := by
  dsimp
  apply Polynomial.funext
  intro u
  simp
  ring

private lemma sparse_sextic_coeff_five (a6 a5 a4 a3 a2 a1 a0 : ℝ) :
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 5 = a5 := by
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

private lemma sparse_sextic_coeff_three (a6 a5 a4 a3 a2 a1 a0 : ℝ) :
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 3 = a3 := by
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

private lemma sparse_sextic_coeff_one (a6 a5 a4 a3 a2 a1 a0 : ℝ) :
    (C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
      C a2 * X ^ 2 + C a1 * X + C a0 : Polynomial ℝ).coeff 1 = a1 := by
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- Two positive double roots give the explicit factorization of the feasibility
expression. -/
theorem twoContactPolynomial_factorization : TwoContactPolynomialFactorization := by
  intro w _ s t hs ht hst P hPeval hsdiv htdiv x
  let P0 := explicitFeasibilityPolynomial w
  have hP0 : P = P0 := Polynomial.funext fun u =>
    (hPeval u).trans (explicitFeasibilityPolynomial_eval w u).symm
  have hcs : P.coeff 5 = 0 := by
    rw [hP0]
    exact (explicitFeasibilityPolynomial_coeffs w).1
  have hc3 : P.coeff 3 = 2 := by
    rw [hP0]
    exact (explicitFeasibilityPolynomial_coeffs w).2.1
  have hc1 : P.coeff 1 = 0 := by
    rw [hP0]
    exact (explicitFeasibilityPolynomial_coeffs w).2.2
  let R := s + t
  let T := s * t
  let F : Polynomial ℝ := (X - C s) ^ 2 * (X - C t) ^ 2
  have hcop : IsCoprime ((X - C s) ^ 2) ((X - C t) ^ 2) := by
    apply (Polynomial.isCoprime_X_sub_C_of_isUnit_sub ?_).pow
    rw [isUnit_iff_ne_zero]
    exact sub_ne_zero.mpr hst
  have hFd : F ∣ P := hcop.mul_dvd hsdiv htdiv
  obtain ⟨Q, hPQ⟩ := hFd
  have hFmonic : F.Monic := by
    dsimp [F]
    exact (monic_X_sub_C s).pow 2 |>.mul ((monic_X_sub_C t).pow 2)
  have hFdeg : F.natDegree = 4 := by
    dsimp [F]
    simp [natDegree_mul, X_sub_C_ne_zero]
  have hQdeg : Q.natDegree ≤ 2 := by
    by_cases hQ : Q = 0
    · simp [hQ]
    have hm := natDegree_mul hFmonic.ne_zero hQ
    rw [hFdeg] at hm
    have hpdeg : P.natDegree ≤ 6 := by
      rw [hP0]
      exact explicitFeasibilityPolynomial_natDegree_le w
    rw [hPQ, hm] at hpdeg
    omega
  let q0 := Q.coeff 0
  let q1 := Q.coeff 1
  let q2 := Q.coeff 2
  have hQform : Q = C q2 * X ^ 2 + C q1 * X + C q0 := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp [q0]
    by_cases hn1 : n = 1
    · subst n
      simp [q1]
    by_cases hn2 : n = 2
    · subst n
      simp [q2]
    have hn : 2 < n := by omega
    have hzero : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQdeg hn)
    rw [hzero]
    simp [coeff_X, coeff_C, hn0, Ne.symm hn0, hn1, Ne.symm hn1, hn2, Ne.symm hn2]
  have hF : F = X ^ 4 - C (2 * R) * X ^ 3 + C (R ^ 2 + 2 * T) * X ^ 2 -
      C (2 * R * T) * X + C (T ^ 2) := by
    dsimp [F, R, T]
    exact quartic_root_expansion s t
  have hFQ : F * Q =
      C q2 * X ^ 6 + C (q1 - 2 * R * q2) * X ^ 5 +
      C (q0 - 2 * R * q1 + (R ^ 2 + 2 * T) * q2) * X ^ 4 +
      C (-2 * R * q0 + (R ^ 2 + 2 * T) * q1 - 2 * R * T * q2) * X ^ 3 +
      C ((R ^ 2 + 2 * T) * q0 - 2 * R * T * q1 + T ^ 2 * q2) * X ^ 2 +
      C (T ^ 2 * q1 - 2 * R * T * q0) * X + C (T ^ 2 * q0) := by
    rw [hF, hQform]
    apply Polynomial.funext
    intro u
    simp
    ring
  have e5 : q1 - 2 * R * q2 = 0 := by
    have hh := congrArg (fun p : Polynomial ℝ => p.coeff 5) hFQ
    rw [← hPQ, hcs, sparse_sextic_coeff_five] at hh
    linarith
  have e3 : -2 * R * T * q2 + (R ^ 2 + 2 * T) * q1 - 2 * R * q0 = 2 := by
    have hh := congrArg (fun p : Polynomial ℝ => p.coeff 3) hFQ
    rw [← hPQ, hc3, sparse_sextic_coeff_three] at hh
    linarith
  have e1 : T ^ 2 * q1 - 2 * R * T * q0 = 0 := by
    have hh := congrArg (fun p : Polynomial ℝ => p.coeff 1) hFQ
    rw [← hPQ, hc1, sparse_sextic_coeff_one] at hh
    linarith
  have hR : R ≠ 0 := by dsimp [R]; nlinarith
  have hT : T ≠ 0 := by dsimp [T]; exact mul_ne_zero (ne_of_gt hs) (ne_of_gt ht)
  have eq1 : q1 = 2 * R * q2 := by linarith
  have eq0 : q0 = T * q2 := by
    rw [eq1] at e1
    apply mul_left_cancel₀ hT
    nlinarith
  have eq2 : q2 = 1 / R ^ 3 := by
    rw [eq1, eq0] at e3
    field_simp [hR]
    nlinarith
  have hQeval : Q.eval x = (x ^ 2 + 2 * R * x + T) / R ^ 3 := by
    rw [hQform]
    simp
    rw [eq1, eq0, eq2]
    field_simp [hR]
  rw [← hPeval x, hPQ, eval_mul, hQeval]
  dsimp [F]
  simp
  dsimp [R, T]
  ring

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

open Polynomial

namespace Binary

/-! ## Moment identities and uniqueness -/

/-- The two-node Hankel determinant expands as a positive-weighted squared difference. -/
theorem twoNode_hankel_identity : TwoNodeHankelIdentity := by
  intro u1 u2 r1 r2
  dsimp only
  ring

/-- The factor parameters satisfy the Hankel normal-form identities. -/
theorem factor_hankel_normalForm : FactorHankelNormalForm := by
  intro s t hs ht
  dsimp only
  refine ⟨?_, ?_⟩ <;> ring

/-- The symmetric model exchanges its two positive best-response roots. -/
theorem symmetric_bestResponse_swaps_roots : SymmetricBestResponseSwapsRoots := by
  intro s t hs ht
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- A nonsingular two-node moment sequence has unique recurrence coefficients. -/
theorem twoNode_recurrence_unique : TwoNodeRecurrenceUnique := by
  intro m0 m1 m2 m3 e1 e2 e1' e2' hdet h2 h3 h2' h3'
  have ha : (e1 - e1') * m1 - (e2 - e2') * m0 = 0 := by linarith
  have hb : (e1 - e1') * m2 - (e2 - e2') * m1 = 0 := by linarith
  have hfirst : (e1 - e1') * (m0 * m2 - m1 ^ 2) = 0 := by
    linear_combination m0 * hb - m1 * ha
  have hsecond : (e2 - e2') * (m0 * m2 - m1 ^ 2) = 0 := by
    linear_combination m1 * hb - m2 * ha
  have he1 : e1 = e1' := by
    rcases mul_eq_zero.mp hfirst with h | h
    · linarith
    · exact (hdet h).elim
  constructor
  · exact he1
  · rcases mul_eq_zero.mp hsecond with h | h
    · linarith
    · exact (hdet h).elim

/-- Evaluating the factorization at seven points yields the four moment identities. -/
theorem twoContact_momentIdentities : TwoContactMomentIdentities := by
  intro a b c d s t hs ht
  dsimp only
  intro h
  have hR : s + t ≠ 0 := by positivity
  have h0 := h 0
  have hp1 := h 1
  have hm1 := h (-1)
  have hp2 := h 2
  have hm2 := h (-2)
  have hp3 := h 3
  have hm3 := h (-3)
  field_simp [hR] at h0 hp1 hm1 hp2 hm2 hp3 hm3
  ring_nf at h0 hp1 hm1 hp2 hm2 hp3 hm3
  constructor
  · field_simp [hR]
    linear_combination -h0
  constructor
  · field_simp [hR]
    linear_combination
      (-1 / 3 : ℝ) * ((-49 / 36 : ℝ) * h0 + (3 / 4 : ℝ) * (hp1 + hm1) +
        (-3 / 40 : ℝ) * (hp2 + hm2) + (1 / 180 : ℝ) * (hp3 + hm3))
  constructor
  · field_simp [hR]
    linear_combination
      (-1 / 3 : ℝ) * ((7 / 18 : ℝ) * h0 + (-13 / 48 : ℝ) * (hp1 + hm1) +
        (1 / 12 : ℝ) * (hp2 + hm2) + (-1 / 144 : ℝ) * (hp3 + hm3))
  · field_simp [hR]
    linear_combination
      -((-1 / 36 : ℝ) * h0 + (1 / 48 : ℝ) * (hp1 + hm1) +
        (-1 / 120 : ℝ) * (hp2 + hm2) + (1 / 720 : ℝ) * (hp3 + hm3))

/-- Cubic polynomial encoding four binomial moments. -/
noncomputable def momentPolynomial (m0 m1 m2 m3 : ℝ) : Polynomial ℝ :=
  C m0 * X ^ 0 + C (3 * m1) * X ^ 1 + C (3 * m2) * X ^ 2 + C m3 * X ^ 3

/-- Evaluation formula for `momentPolynomial`. -/
lemma momentPolynomial_eval (m0 m1 m2 m3 z : ℝ) :
    (momentPolynomial m0 m1 m2 m3).eval z =
      m0 + 3 * m1 * z + 3 * m2 * z ^ 2 + m3 * z ^ 3 := by
  simp [momentPolynomial]

/-- Constant coefficient of `momentPolynomial`. -/
lemma momentPolynomial_coeff_zero (m0 m1 m2 m3 : ℝ) :
    (momentPolynomial m0 m1 m2 m3).coeff 0 = m0 := by
  simp only [momentPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

/-- Linear coefficient of `momentPolynomial`. -/
lemma momentPolynomial_coeff_one (m0 m1 m2 m3 : ℝ) :
    (momentPolynomial m0 m1 m2 m3).coeff 1 = 3 * m1 := by
  simp only [momentPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

/-- Quadratic coefficient of `momentPolynomial`. -/
lemma momentPolynomial_coeff_two (m0 m1 m2 m3 : ℝ) :
    (momentPolynomial m0 m1 m2 m3).coeff 2 = 3 * m2 := by
  simp only [momentPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

/-- Cubic coefficient of `momentPolynomial`. -/
lemma momentPolynomial_coeff_three (m0 m1 m2 m3 : ℝ) :
    (momentPolynomial m0 m1 m2 m3).coeff 3 = m3 := by
  simp only [momentPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num

/-- Equality of two sums of cubes gives equality of their moment polynomials. -/
lemma momentPolynomial_eq_of_twoCube_eq
    {a b c d a' b' c' d' : ℝ}
    (h : ∀ z : ℝ, (a + c * z) ^ 3 + (b + d * z) ^ 3 =
      (a' + c' * z) ^ 3 + (b' + d' * z) ^ 3) :
    momentPolynomial (a ^ 3 + b ^ 3) (a ^ 2 * c + b ^ 2 * d)
        (a * c ^ 2 + b * d ^ 2) (c ^ 3 + d ^ 3) =
    momentPolynomial (a' ^ 3 + b' ^ 3) (a' ^ 2 * c' + b' ^ 2 * d')
        (a' * c' ^ 2 + b' * d' ^ 2) (c' ^ 3 + d' ^ 3) := by
  apply Polynomial.funext
  intro z
  rw [momentPolynomial_eval, momentPolynomial_eval]
  have hz := h z
  ring_nf at hz ⊢
  exact hz

/-- The four coefficients make `momentPolynomial` injective in its moments. -/
lemma momentPolynomial_injective
    {m0 m1 m2 m3 n0 n1 n2 n3 : ℝ}
    (h : momentPolynomial m0 m1 m2 m3 = momentPolynomial n0 n1 n2 n3) :
    m0 = n0 ∧ m1 = n1 ∧ m2 = n2 ∧ m3 = n3 := by
  have hc0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) h
  have hc1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) h
  have hc2 := congrArg (fun p : Polynomial ℝ => p.coeff 2) h
  have hc3 := congrArg (fun p : Polynomial ℝ => p.coeff 3) h
  rw [momentPolynomial_coeff_zero, momentPolynomial_coeff_zero] at hc0
  rw [momentPolynomial_coeff_one, momentPolynomial_coeff_one] at hc1
  rw [momentPolynomial_coeff_two, momentPolynomial_coeff_two] at hc2
  rw [momentPolynomial_coeff_three, momentPolynomial_coeff_three] at hc3
  refine ⟨hc0, ?_, ?_, hc3⟩
  · linarith only [hc1]
  · linarith only [hc2]

/-- Re-express the first three ratio moments of a nonzero column. -/
lemma cube_ratio_moments {a c : ℝ} (ha0 : a ≠ 0) :
    a ^ 3 * (c / a) = a ^ 2 * c ∧
    a ^ 3 * (c / a) ^ 2 = a * c ^ 2 ∧
    a ^ 3 * (c / a) ^ 3 = c ^ 3 := by
  constructor
  · field_simp [ha0]
  constructor
  · field_simp [ha0]
  · field_simp [ha0]

/-- Positive weights at distinct nodes have positive Hankel determinant. -/
lemma twoNode_hankel_pos {α β u v : ℝ} (hα : 0 < α) (hβ : 0 < β) (huv : u ≠ v) :
    0 < (α + β) * (α * u ^ 2 + β * v ^ 2) - (α * u + β * v) ^ 2 := by
  have h := twoNode_hankel_identity α β u v
  dsimp only at h
  rw [h]
  positivity

/-- Second moment recurrence for two nodes. -/
lemma twoNode_rec_two (α β u v : ℝ) :
    α * u ^ 2 + β * v ^ 2 =
      (u + v) * (α * u + β * v) - (u * v) * (α + β) := by
  ring

/-- Third moment recurrence for two nodes. -/
lemma twoNode_rec_three (α β u v : ℝ) :
    α * u ^ 3 + β * v ^ 3 =
      (u + v) * (α * u ^ 2 + β * v ^ 2) - (u * v) * (α * u + β * v) := by
  ring

/-- Two real pairs with the same sum and product agree up to exchange. -/
lemma pair_eq_or_swap_of_sum_prod
    {u v u' v' : ℝ} (hsum : u + v = u' + v') (hprod : u * v = u' * v') :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  have hz : (u - u') * (u - v') = 0 := by
    calc
      (u - u') * (u - v') = u ^ 2 - (u' + v') * u + u' * v' := by ring
      _ = u ^ 2 - (u + v) * u + u * v := by rw [← hsum, ← hprod]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hz with h | h
  · left
    constructor <;> linarith only [hsum, h]
  · right
    constructor <;> linarith only [hsum, h]

/-- Weights at two distinct nodes are determined by their first two moments. -/
lemma weights_eq_at_distinct_nodes
    {α β α' β' u v : ℝ} (huv : u ≠ v)
    (h0 : α + β = α' + β')
    (h1 : α * u + β * v = α' * u + β' * v) :
    α = α' ∧ β = β' := by
  have hx : (α - α') * (u - v) = 0 := by
    linear_combination h1 - v * h0
  have hα : α = α' := by
    rcases mul_eq_zero.mp hx with h | h
    · linarith only [h]
    · exfalso
      apply huv
      linarith only [h]
  refine ⟨hα, ?_⟩
  linarith only [h0, hα]

/-- A real number and its ratio companion are determined by its cube and a nonzero
denominator. -/
lemma column_eq_of_cube_and_ratio
    {a c a' c' : ℝ} (ha0 : a ≠ 0)
    (hcube : a ^ 3 = a' ^ 3) (hratio : c / a = c' / a') :
    a = a' ∧ c = c' := by
  have haa : a = a' := ((by decide : Odd 3).pow_inj).mp hcube
  refine ⟨haa, ?_⟩
  rw [← haa] at hratio
  exact (div_left_inj' ha0).mp hratio

/-- A positive two-cube decomposition is unique up to exchange. -/
theorem positiveTwoCube_decomposition_unique : PositiveTwoCubeDecompositionUnique := by
  intro a b c d a' b' c' d' ha hb hc hd ha' hb' hc' hd' huv hpoly
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have ha0' : a' ≠ 0 := ne_of_gt ha'
  have hb0' : b' ≠ 0 := ne_of_gt hb'
  let m0 := a ^ 3 + b ^ 3
  let m1 := a ^ 2 * c + b ^ 2 * d
  let m2 := a * c ^ 2 + b * d ^ 2
  let m3 := c ^ 3 + d ^ 3
  let n0 := a' ^ 3 + b' ^ 3
  let n1 := a' ^ 2 * c' + b' ^ 2 * d'
  let n2 := a' * c' ^ 2 + b' * d' ^ 2
  let n3 := c' ^ 3 + d' ^ 3
  have hm := momentPolynomial_injective (momentPolynomial_eq_of_twoCube_eq hpoly)
  rcases hm with ⟨hm0, hm1, hm2, hm3⟩
  change m0 = n0 at hm0
  change m1 = n1 at hm1
  change m2 = n2 at hm2
  change m3 = n3 at hm3
  let α := a ^ 3
  let β := b ^ 3
  let u := c / a
  let v := d / b
  let α' := a' ^ 3
  let β' := b' ^ 3
  let u' := c' / a'
  let v' := d' / b'
  rcases cube_ratio_moments ha0 with ⟨hau1, hau2, hau3⟩
  rcases cube_ratio_moments hb0 with ⟨hbv1, hbv2, hbv3⟩
  rcases cube_ratio_moments ha0' with ⟨hau1', hau2', hau3'⟩
  rcases cube_ratio_moments hb0' with ⟨hbv1', hbv2', hbv3'⟩
  have hm0ab : m0 = α + β := by rfl
  have hm1ab : m1 = α * u + β * v := by
    dsimp [m1, α, β, u, v]
    rw [hau1, hbv1]
  have hm2ab : m2 = α * u ^ 2 + β * v ^ 2 := by
    dsimp [m2, α, β, u, v]
    rw [hau2, hbv2]
  have hm3ab : m3 = α * u ^ 3 + β * v ^ 3 := by
    dsimp [m3, α, β, u, v]
    rw [hau3, hbv3]
  have hn0ab : n0 = α' + β' := by rfl
  have hn1ab : n1 = α' * u' + β' * v' := by
    dsimp [n1, α', β', u', v']
    rw [hau1', hbv1']
  have hn2ab : n2 = α' * u' ^ 2 + β' * v' ^ 2 := by
    dsimp [n2, α', β', u', v']
    rw [hau2', hbv2']
  have hn3ab : n3 = α' * u' ^ 3 + β' * v' ^ 3 := by
    dsimp [n3, α', β', u', v']
    rw [hau3', hbv3']
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have huv' : u ≠ v := huv
  have hdetpos : 0 < m0 * m2 - m1 ^ 2 := by
    rw [hm0ab, hm1ab, hm2ab]
    exact twoNode_hankel_pos hα hβ huv'
  have hdet0 : m0 * m2 - m1 ^ 2 ≠ 0 := ne_of_gt hdetpos
  have hrec2 : m2 = (u + v) * m1 - (u * v) * m0 := by
    rw [hm0ab, hm1ab, hm2ab]
    exact twoNode_rec_two α β u v
  have hrec3 : m3 = (u + v) * m2 - (u * v) * m1 := by
    rw [hm1ab, hm2ab, hm3ab]
    exact twoNode_rec_three α β u v
  have hrec2' : m2 = (u' + v') * m1 - (u' * v') * m0 := by
    rw [hm0, hm1, hm2, hn0ab, hn1ab, hn2ab]
    exact twoNode_rec_two α' β' u' v'
  have hrec3' : m3 = (u' + v') * m2 - (u' * v') * m1 := by
    rw [hm1, hm2, hm3, hn1ab, hn2ab, hn3ab]
    exact twoNode_rec_three α' β' u' v'
  obtain ⟨hsum, hprod⟩ := twoNode_recurrence_unique m0 m1 m2 m3
    (u + v) (u * v) (u' + v') (u' * v') hdet0 hrec2 hrec3 hrec2' hrec3'
  rcases pair_eq_or_swap_of_sum_prod hsum hprod with hnodes | hnodes
  · rcases hnodes with ⟨hu, hv⟩
    have hw0 : α + β = α' + β' := by
      rw [← hm0ab, ← hn0ab]
      exact hm0
    have hw1 : α * u + β * v = α' * u + β' * v := by
      rw [← hm1ab, hu, hv, ← hn1ab]
      exact hm1
    obtain ⟨hαeq, hβeq⟩ := weights_eq_at_distinct_nodes huv' hw0 hw1
    obtain ⟨haeq, hceq⟩ := column_eq_of_cube_and_ratio ha0 hαeq hu
    obtain ⟨hbeq, hdeq⟩ := column_eq_of_cube_and_ratio hb0 hβeq hv
    exact Or.inl ⟨haeq, hbeq, hceq, hdeq⟩
  · rcases hnodes with ⟨hu, hv⟩
    have hw0 : α + β = β' + α' := by
      rw [add_comm β' α', ← hn0ab, ← hm0ab]
      exact hm0
    have hw1 : α * u + β * v = β' * u + α' * v := by
      calc
        α * u + β * v = m1 := hm1ab.symm
        _ = n1 := hm1
        _ = α' * u' + β' * v' := hn1ab
        _ = β' * u + α' * v := by rw [hu, hv]; ring
    obtain ⟨hαeq, hβeq⟩ := weights_eq_at_distinct_nodes huv' hw0 hw1
    obtain ⟨haeq, hceq⟩ := column_eq_of_cube_and_ratio ha0 hαeq hu
    obtain ⟨hbeq, hdeq⟩ := column_eq_of_cube_and_ratio hb0 hβeq hv
    exact Or.inr ⟨haeq, hbeq, hceq, hdeq⟩

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

namespace Binary

/-! ## Symmetric-kernel reconstruction -/

/-- The quadratic factor `K` is positive at two positive roots. -/
lemma binary_K_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < (s + t) ^ 2 - s * t := by
  have h : (s + t) ^ 2 - s * t = s ^ 2 + s * t + t ^ 2 := by ring
  rw [h]
  positivity

/-- Positivity of the first kernel Hankel determinant. -/
lemma first_kernel_hankel_pos {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hnodes : c / a ≠ d / b) :
    0 < (a ^ 3 + b ^ 3) * (a * c ^ 2 + b * d ^ 2) -
      (a ^ 2 * c + b ^ 2 * d) ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h1 : a ^ 3 * (c / a) = a ^ 2 * c := by field_simp [ha0]
  have h2 : b ^ 3 * (d / b) = b ^ 2 * d := by field_simp [hb0]
  have h3 : a ^ 3 * (c / a) ^ 2 = a * c ^ 2 := by field_simp [ha0]
  have h4 : b ^ 3 * (d / b) ^ 2 = b * d ^ 2 := by field_simp [hb0]
  have h := twoNode_hankel_pos (show 0 < a ^ 3 by positivity)
    (show 0 < b ^ 3 by positivity) hnodes
  rw [h1, h2, h3, h4] at h
  exact h

/-- Positivity of the shifted kernel Hankel determinant. -/
lemma second_kernel_hankel_pos {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnodes : c / a ≠ d / b) :
    0 < (a ^ 2 * c + b ^ 2 * d) * (c ^ 3 + d ^ 3) -
      (a * c ^ 2 + b * d ^ 2) ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h1 : (a ^ 2 * c) * (c / a) = a * c ^ 2 := by field_simp [ha0]
  have h2 : (b ^ 2 * d) * (d / b) = b * d ^ 2 := by field_simp [hb0]
  have h3 : (a ^ 2 * c) * (c / a) ^ 2 = c ^ 3 := by field_simp [ha0]
  have h4 : (b ^ 2 * d) * (d / b) ^ 2 = d ^ 3 := by field_simp [hb0]
  have h := twoNode_hankel_pos (show 0 < a ^ 2 * c by positivity)
    (show 0 < b ^ 2 * d by positivity) hnodes
  rw [h1, h2, h3, h4] at h
  exact h

/-- Scalar normal form for the first Hankel determinant. -/
lemma delta_scalar_normalForm (R T : ℝ) (hR0 : R ≠ 0) :
    ((R ^ 3 - T ^ 3) / R ^ 3) * ((R ^ 2 - T) / R ^ 3) -
      (T * (R ^ 2 - T) / R ^ 3) ^ 2 =
      (R - T ^ 2) * (R ^ 2 - T) / R ^ 4 := by
  field_simp [hR0]
  ring

/-- Scalar normal form for the shifted Hankel determinant. -/
lemma epsilon_scalar_normalForm (R T : ℝ) (hR0 : R ≠ 0) :
    (T * (R ^ 2 - T) / R ^ 3) * ((R ^ 3 - 1) / R ^ 3) -
      ((R ^ 2 - T) / R ^ 3) ^ 2 =
      (R * T - 1) * (R ^ 2 - T) / R ^ 4 := by
  field_simp [hR0]
  ring

/-- Positivity of a normalized product with positive scale factors forces positivity of
its remaining factor. -/
lemma left_pos_of_hankel_normalForm {X K R : ℝ}
    (hR : 0 < R) (hK : 0 < K) (h : 0 < X * K / R ^ 4) : 0 < X := by
  have hden : 0 < R ^ 4 := by positivity
  have hmul : 0 < X * K := by
    rcases div_pos_iff.mp h with hp | hn
    · exact hp.1
    · exact False.elim ((not_lt_of_ge (le_of_lt hden)) hn.2)
  exact (mul_pos_iff_of_pos_right hK).mp hmul

/-- The third normal-form identity needed for moment reconstruction. -/
lemma normal_moment_two_identity (s t : ℝ) :
    let R := s + t
    let T := s * t
    let K := R ^ 2 - T
    let A := R - T ^ 2
    let D := R * T - 1
    let U := (1 + s ^ 3) * (1 + t ^ 3)
    A * K + D ^ 2 = U := by
  dsimp only
  ring

/-- The fourth normal-form identity needed for moment reconstruction. -/
lemma normal_moment_three_identity (s t : ℝ) :
    let R := s + t
    let T := s * t
    let K := R ^ 2 - T
    let D := R * T - 1
    let U := (1 + s ^ 3) * (1 + t ^ 3)
    K ^ 3 + D ^ 3 = (R ^ 3 - 1) * U := by
  dsimp only
  ring

/-- Positive normal-form parameters have a positive cubic scale. -/
lemma exists_positive_normal_scale {R U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    ∃ h : ℝ, 0 < h ∧ h ^ 3 = 1 / (R ^ 3 * U) := by
  let q : ℝ := 1 / (R ^ 3 * U)
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q ^ ((3 : ℝ)⁻¹), Real.rpow_pos_of_pos hq _, ?_⟩
  exact Real.rpow_inv_natCast_pow (x := q) (n := 3) (le_of_lt hq) (by norm_num)

/-- The candidate symmetric model has the zeroth required moment. -/
lemma candidate_moment_zero {h R T A K U : ℝ} (hR0 : R ≠ 0) (hU0 : U ≠ 0)
    (hh : h ^ 3 = 1 / (R ^ 3 * U)) (hid : A ^ 3 + K ^ 3 = (R ^ 3 - T ^ 3) * U) :
    (h * A) ^ 3 + (h * K) ^ 3 = (R ^ 3 - T ^ 3) / R ^ 3 := by
  calc
    _ = h ^ 3 * (A ^ 3 + K ^ 3) := by ring
    _ = (1 / (R ^ 3 * U)) * ((R ^ 3 - T ^ 3) * U) := by rw [hh, hid]
    _ = _ := by field_simp [hR0, hU0]

/-- The candidate symmetric model has the first required moment. -/
lemma candidate_moment_one {h R T A K D U : ℝ} (hR0 : R ≠ 0) (hU0 : U ≠ 0)
    (hh : h ^ 3 = 1 / (R ^ 3 * U)) (hid : A ^ 2 + K * D = T * U) :
    (h * A) ^ 2 * (h * K) + (h * K) ^ 2 * (h * D) = T * K / R ^ 3 := by
  calc
    _ = h ^ 3 * K * (A ^ 2 + K * D) := by ring
    _ = (1 / (R ^ 3 * U)) * K * (T * U) := by rw [hh, hid]
    _ = _ := by field_simp [hR0, hU0]

/-- The candidate symmetric model has the second required moment. -/
lemma candidate_moment_two {h R K A D U : ℝ} (hR0 : R ≠ 0) (hU0 : U ≠ 0)
    (hh : h ^ 3 = 1 / (R ^ 3 * U)) (hid : A * K + D ^ 2 = U) :
    (h * A) * (h * K) ^ 2 + (h * K) * (h * D) ^ 2 = K / R ^ 3 := by
  calc
    _ = h ^ 3 * K * (A * K + D ^ 2) := by ring
    _ = (1 / (R ^ 3 * U)) * K * U := by rw [hh, hid]
    _ = _ := by field_simp [hR0, hU0]

/-- The candidate symmetric model has the third required moment. -/
lemma candidate_moment_three {h R K D U : ℝ} (hR0 : R ≠ 0) (hU0 : U ≠ 0)
    (hh : h ^ 3 = 1 / (R ^ 3 * U)) (hid : K ^ 3 + D ^ 3 = (R ^ 3 - 1) * U) :
    (h * K) ^ 3 + (h * D) ^ 3 = (R ^ 3 - 1) / R ^ 3 := by
  calc
    _ = h ^ 3 * (K ^ 3 + D ^ 3) := by ring
    _ = (1 / (R ^ 3 * U)) * ((R ^ 3 - 1) * U) := by rw [hh, hid]
    _ = _ := by field_simp [hR0, hU0]

/-- Four binomial moments determine equality of the corresponding two-cube expressions. -/
lemma twoCube_eq_of_four_moments {a b c d a' b' c' d' : ℝ}
    (h0 : a ^ 3 + b ^ 3 = a' ^ 3 + b' ^ 3)
    (h1 : a ^ 2 * c + b ^ 2 * d = a' ^ 2 * c' + b' ^ 2 * d')
    (h2 : a * c ^ 2 + b * d ^ 2 = a' * c' ^ 2 + b' * d' ^ 2)
    (h3 : c ^ 3 + d ^ 3 = c' ^ 3 + d' ^ 3) :
    ∀ z : ℝ, (a + c * z) ^ 3 + (b + d * z) ^ 3 =
      (a' + c' * z) ^ 3 + (b' + d' * z) ^ 3 := by
  intro z
  linear_combination h0 + (3 * z) * h1 + (3 * z ^ 2) * h2 + (z ^ 3) * h3

/-- Extensionality for a binary matrix from its four entries. -/
lemma binary_matrix_ext {f g : Cell → ℝ}
    (h00 : f (0, 0) = g (0, 0)) (h01 : f (0, 1) = g (0, 1))
    (h10 : f (1, 0) = g (1, 0)) (h11 : f (1, 1) = g (1, 1)) : f = g := by
  funext z
  rcases z with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- Extensionality after swapping the columns of a binary matrix. -/
lemma swapColumns_matrix_ext {w ws : Cell → ℝ}
    (h00 : w (0, 1) = ws (0, 0)) (h01 : w (0, 0) = ws (0, 1))
    (h10 : w (1, 1) = ws (1, 0)) (h11 : w (1, 0) = ws (1, 1)) :
    pushforward swapColumnsCell w = ws := by
  apply binary_matrix_ext
  · rw [pushforward_apply_equiv]
    simpa [swapColumnsCell, bitFlip] using h00
  · rw [pushforward_apply_equiv]
    simpa [swapColumnsCell, bitFlip] using h01
  · rw [pushforward_apply_equiv]
    simpa [swapColumnsCell, bitFlip] using h10
  · rw [pushforward_apply_equiv]
    simpa [swapColumnsCell, bitFlip] using h11

/-- The four moments reconstruct a transpose-symmetric kernel, up to column swap. -/
theorem symmetricKernel_reconstruction : SymmetricKernelReconstruction := by
  intro w hfull s t hs ht _hst
  dsimp only
  intro hm0 hm1 hm2 hm3 hnodes
  let a := w (0, 0)
  let b := w (0, 1)
  let c := w (1, 0)
  let d := w (1, 1)
  let R := s + t
  let T := s * t
  let K := R ^ 2 - T
  let A := R - T ^ 2
  let D := R * T - 1
  let U := (1 + s ^ 3) * (1 + t ^ 3)
  change a ^ 3 + b ^ 3 = (R ^ 3 - T ^ 3) / R ^ 3 at hm0
  change a ^ 2 * c + b ^ 2 * d = T * K / R ^ 3 at hm1
  change a * c ^ 2 + b * d ^ 2 = K / R ^ 3 at hm2
  change c ^ 3 + d ^ 3 = (R ^ 3 - 1) / R ^ 3 at hm3
  change c / a ≠ d / b at hnodes
  have ha : 0 < a := hfull _
  have hb : 0 < b := hfull _
  have hc : 0 < c := hfull _
  have hd : 0 < d := hfull _
  have hR : 0 < R := by dsimp [R]; positivity
  have hK : 0 < K := by dsimp [K, R, T]; exact binary_K_pos hs ht
  have hU : 0 < U := by dsimp [U]; positivity
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hU0 : U ≠ 0 := ne_of_gt hU
  have hhank1 := first_kernel_hankel_pos ha hb hnodes
  rw [hm0, hm1, hm2] at hhank1
  rw [delta_scalar_normalForm R T hR0] at hhank1
  have hA : 0 < A := left_pos_of_hankel_normalForm hR hK hhank1
  have hhank2 := second_kernel_hankel_pos ha hb hc hd hnodes
  rw [hm1, hm2, hm3] at hhank2
  rw [epsilon_scalar_normalForm R T hR0] at hhank2
  have hD : 0 < D := left_pos_of_hankel_normalForm hR hK hhank2
  obtain ⟨hNF0, hNF1⟩ := factor_hankel_normalForm s t hs ht
  change A ^ 3 + K ^ 3 = (R ^ 3 - T ^ 3) * U at hNF0
  change A ^ 2 + K * D = T * U at hNF1
  have hNF2 : A * K + D ^ 2 = U := by
    simpa [A, K, D, U, R, T] using normal_moment_two_identity s t
  have hNF3 : K ^ 3 + D ^ 3 = (R ^ 3 - 1) * U := by
    simpa [K, D, U, R, T] using normal_moment_three_identity s t
  obtain ⟨h, hhpos, hhcube⟩ := exists_positive_normal_scale hR hU
  have ha' : 0 < h * A := mul_pos hhpos hA
  have hb' : 0 < h * K := mul_pos hhpos hK
  have hc' : 0 < h * K := hb'
  have hd' : 0 < h * D := mul_pos hhpos hD
  have cm0 := candidate_moment_zero hR0 hU0 hhcube hNF0
  have cm1 := candidate_moment_one hR0 hU0 hhcube hNF1
  have cm2 := candidate_moment_two hR0 hU0 hhcube hNF2
  have cm3 := candidate_moment_three hR0 hU0 hhcube hNF3
  have hpoly := twoCube_eq_of_four_moments (hm0.trans cm0.symm) (hm1.trans cm1.symm)
    (hm2.trans cm2.symm) (hm3.trans cm3.symm)
  let ws : Cell → ℝ := fun z =>
    if z = (0, 0) then h * A else if z = (0, 1) then h * K
    else if z = (1, 0) then h * K else h * D
  refine ⟨h, hhpos, hhcube, ?_⟩
  rcases positiveTwoCube_decomposition_unique a b c d (h * A) (h * K) (h * K) (h * D)
      ha hb hc hd ha' hb' hc' hd' hnodes hpoly with hsame | hswap
  · rcases hsame with ⟨haa, hbb, hcc, hdd⟩
    left
    apply binary_matrix_ext
    · simpa [ws] using haa
    · simpa [ws] using hbb
    · simpa [ws] using hcc
    · simpa [ws] using hdd
  · rcases hswap with ⟨hab, hba, hcd, hdc⟩
    right
    apply swapColumns_matrix_ext
    · simpa [ws] using hba
    · simpa [ws] using hab
    · simpa [ws] using hdc
    · simpa [ws] using hcd

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

open Finset

namespace Binary

/-! ## Contact and feasibility transport -/

/-- Identity or transpose orients a table with unequal off-diagonal entries. -/
theorem transposePair_canOrientOffDiagonal : TransposePairCanOrientOffDiagonal := by
  intro q hqne
  have hoff : q (0, 1) ≠ q (1, 0) := by
    intro heq
    apply hqne
    funext z
    rcases z with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> simp [transposeCell, heq]
  rcases lt_or_gt_of_ne hoff with h01_10 | h10_01
  · refine ⟨transposeCell, Or.inr rfl, ?_⟩
    rw [pushforward_apply_equiv, pushforward_apply_equiv]
    simpa [transposeCell] using h01_10
  · refine ⟨Equiv.refl _, Or.inl rfl, ?_⟩
    rw [pushforward_apply_equiv, pushforward_apply_equiv]
    simpa using h10_01

/-- Feasibility transports along the four non-transposing chart orientations. -/
theorem feasible_pushforwardAlongChart : FeasiblePushforwardAlongChart := by
  intro w g hg hw
  rcases hg with rfl | rfl | rfl | rfl
  · simpa [TableSymmetry.equiv] using feasible_pushforward TableSymmetry.refl hw
  · simpa [TableSymmetry.equiv] using feasible_pushforward TableSymmetry.swapRows hw
  · simpa [TableSymmetry.equiv] using feasible_pushforward TableSymmetry.swapColumns hw
  · simpa [TableSymmetry.equiv] using
      feasible_pushforward (TableSymmetry.comp .swapRows .swapColumns) hw

/-- Contact transports along the four non-transposing chart orientations. -/
theorem contact_pushforwardAlongChart : ContactPushforwardAlongChart := by
  intro w q g hg hq
  rcases hg with rfl | rfl | rfl | rfl
  · simpa [TableSymmetry.equiv] using isContact_pushforward TableSymmetry.refl hq
  · simpa [TableSymmetry.equiv] using isContact_pushforward TableSymmetry.swapRows hq
  · simpa [TableSymmetry.equiv] using isContact_pushforward TableSymmetry.swapColumns hq
  · simpa [TableSymmetry.equiv] using
      isContact_pushforward (TableSymmetry.comp .swapRows .swapColumns) hq

/-- Transposition preserves contact when the kernel is transpose-symmetric. -/
theorem contact_transposeOf_symmetricKernel : ContactTransposeOfSymmetricKernel := by
  intro w q hsym hq
  have hwEq : pushforward transposeCell w = w := by
    funext z
    rw [pushforward_apply_equiv]
    simpa [transposeCell] using hsym z
  have hc := isContact_pushforward TableSymmetry.transpose hq
  have hqEq : pushforward transposeCell q = fun z => q (transposeCell.symm z) := by
    funext z
    rw [pushforward_apply_equiv]
  simpa [TableSymmetry.equiv, hwEq, hqEq] using hc

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

open Finset Polynomial

namespace Binary


/-- Any two distinct contacts of a feasible binary kernel become a transpose pair after
one of the four non-transposing chart symmetries. -/
def TransposeNormalForm : Prop :=
  ∀ w : Cell → ℝ, Feasible (univ : Finset Cell) w →
    ∀ q r : Cell → ℝ, IsContact (univ : Finset Cell) w q →
      IsContact (univ : Finset Cell) w r → q ≠ r →
      ∃ g : Cell ≃ Cell,
        (g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
          g = swapRowsCell.trans swapColumnsCell) ∧
        pushforward g r = fun z => pushforward g q (transposeCell.symm z)

/-- The two geometric inputs needed to put a selected optimizer in transpose normal form. -/
def TransposeNormalFormInputs : Prop := ContactClassification ∧ TransposeNormalForm

/-- Polynomial realizing the binary feasibility expression. -/
def feasibilityPolynomial (w : Cell → ℝ) : Polynomial ℝ :=
  (1 + X ^ 3) ^ 2 - (C (w (0, 0)) + C (w (1, 0)) * X ^ 2) ^ 3 -
    (C (w (0, 1)) + C (w (1, 1)) * X ^ 2) ^ 3

/-- Evaluation of the feasibility polynomial. -/
theorem feasibilityPolynomial_eval (w : Cell → ℝ) (x : ℝ) :
    (feasibilityPolynomial w).eval x = feasibilityExpression w x := by
  simp [feasibilityPolynomial, feasibilityExpression]

private theorem feasibilityPolynomial_degree (w : Cell → ℝ) :
    (feasibilityPolynomial w).natDegree ≤ 6 := by
  simp only [feasibilityPolynomial]
  compute_degree

private theorem feasibilityPolynomial_coeff_five (w : Cell → ℝ) :
    (feasibilityPolynomial w).coeff 5 = 0 := by
  have hcube (a b : ℝ) : ((C a + C b * X ^ 2) ^ 3 : Polynomial ℝ).coeff 5 = 0 := by
    rw [show (C a + C b * X ^ 2) ^ 3 =
        C (a ^ 3) + C (3 * a ^ 2 * b) * X ^ 2 +
          C (3 * a * b ^ 2) * X ^ 4 + C (b ^ 3) * X ^ 6 by
      simp only [C_mul, C_pow, C_ofNat]
      ring]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    norm_num
  have hbase : (((1 : Polynomial ℝ) + X ^ 3) ^ 2).coeff 5 = 0 := by
    rw [show ((1 : Polynomial ℝ) + X ^ 3) ^ 2 = 1 + 2 * X ^ 3 + X ^ 6 by ring]
    simp [coeff_one, coeff_X_pow]
  simp only [feasibilityPolynomial, coeff_sub, hbase, hcube, sub_zero]

private theorem rowCubeParameter_refl {q : Cell → ℝ} {x : ℝ}
    (h : RowCubeParameter q x) : RowCubeParameter (pushforward (Equiv.refl _) q) x := by
  rcases h with ⟨hx, h0, h1⟩
  refine ⟨hx, ?_, ?_⟩
  · rw [show rowMarginal (pushforward (Equiv.refl _) q) 0 = rowMarginal q 0 by
      simp only [rowMarginal]
      rw [pushforward_apply_equiv, pushforward_apply_equiv]
      rfl]
    exact h0
  · rw [show rowMarginal (pushforward (Equiv.refl _) q) 1 = rowMarginal q 1 by
      simp only [rowMarginal]
      rw [pushforward_apply_equiv, pushforward_apply_equiv]
      rfl]
    exact h1

/-- Swapping columns preserves a row cube parameter. -/
theorem rowCubeParameter_swapColumns {q : Cell → ℝ} {x : ℝ}
    (h : RowCubeParameter q x) :
    RowCubeParameter (pushforward swapColumnsCell q) x := by
  rcases h with ⟨hx, h0, h1⟩
  refine ⟨hx, ?_, ?_⟩
  · rw [show rowMarginal (pushforward swapColumnsCell q) 0 = rowMarginal q 0 by
      simp only [rowMarginal, pushforward_apply_equiv]
      change q (0, bitFlip.symm 0) + q (0, bitFlip.symm 1) = _
      norm_num [bitFlip, Equiv.swap_apply_def, add_comm]]
    exact h0
  · rw [show rowMarginal (pushforward swapColumnsCell q) 1 = rowMarginal q 1 by
      simp only [rowMarginal, pushforward_apply_equiv]
      change q (1, bitFlip.symm 0) + q (1, bitFlip.symm 1) = _
      norm_num [bitFlip, Equiv.swap_apply_def, add_comm]]
    exact h1

private theorem transpose_columnCubeParameter {q : Cell → ℝ} {x : ℝ}
    (h : ColumnCubeParameter q x) :
    RowCubeParameter (fun z => q (transposeCell.symm z)) x := by
  rcases h with ⟨hx, h0, h1⟩
  exact ⟨hx,
    by simpa [rowMarginal, columnMarginal, transposeCell] using h0,
    by simpa [rowMarginal, columnMarginal, transposeCell] using h1⟩

private theorem symmetricModel_transpose (h A K D : ℝ) :
    let ws : Cell → ℝ := fun z =>
      if z = (0, 0) then h * A else if z = (0, 1) then h * K
      else if z = (1, 0) then h * K else h * D
    ∀ z, ws (transposeCell z) = ws z := by
  intro ws z
  rcases z with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [ws, transposeCell]

/-- The symmetric-model response quotient equals the opposite root. -/
theorem bestResponse_quotient
    {h s t R K A D : ℝ} (hh : 0 < h) (hR : 0 < R) (hs : 0 < s)
    (hden : A + K * s ^ 2 = R * (1 + s ^ 3))
    (hnum : K + D * s ^ 2 = t * R * (1 + s ^ 3)) :
    (h * K + h * D * s ^ 2) / (h * A + h * K * s ^ 2) = t := by
  have hc : 0 < 1 + s ^ 3 := by positivity
  have hn : h * A + h * K * s ^ 2 ≠ 0 := by
    rw [show h * A + h * K * s ^ 2 = h * (A + K * s ^ 2) by ring, hden]
    positivity
  apply (div_eq_iff hn).2
  rw [show h * K + h * D * s ^ 2 = h * (K + D * s ^ 2) by ring, hnum]
  rw [show h * A + h * K * s ^ 2 = h * (A + K * s ^ 2) by ring, hden]
  ring

/-- The algebraic and transport conditions imply the two normal-form inputs. -/
theorem transposeNormalFormInputs_of_conditions :
    NormalFormConditions → TransposeNormalFormInputs := by
  rintro ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10,
    hC11, hC12, hC13, hC14, hC15, hC16, hC17, hC18, hC19, hC20, hC21⟩
  constructor
  · intro w hw q r s hq hr hs
    by_cases hqr : q = r
    · exact Or.inl hqr
    by_cases hqs : q = s
    · exact Or.inr (Or.inl hqs)
    by_cases hrs : r = s
    · exact Or.inr (Or.inr hrs)
    exfalso
    obtain ⟨x, hx⟩ := hC1 w q hw hq
    obtain ⟨y, hy⟩ := hC1 w r hw hr
    obtain ⟨z, hz⟩ := hC1 w s hw hs
    have hxy : x ≠ y := by
      intro h
      apply hqr
      apply hC5 w q r hw hq hr x hx
      simpa [h] using hy
    have hxz : x ≠ z := by
      intro h
      apply hqs
      apply hC5 w q s hw hq hs x hx
      simpa [h] using hz
    have hyz : y ≠ z := by
      intro h
      apply hrs
      apply hC5 w r s hw hr hs y hy
      simpa [h] using hz
    let P := feasibilityPolynomial w
    have hnonneg : ∀ u : ℝ, 0 < u → 0 ≤ P.eval u := by
      intro u hu
      rw [feasibilityPolynomial_eval]
      exact hC3 w hw u hu
    have hxroot : P.eval x = 0 := by
      rw [feasibilityPolynomial_eval]
      exact (hC4 w q hw hq x hx).1
    have hyroot : P.eval y = 0 := by
      rw [feasibilityPolynomial_eval]
      exact (hC4 w r hw hr y hy).1
    have hzroot : P.eval z = 0 := by
      rw [feasibilityPolynomial_eval]
      exact (hC4 w s hw hs z hz).1
    have hxdiv := hC7 P x hx.1 hnonneg hxroot
    have hydiv := hC7 P y hy.1 hnonneg hyroot
    have hzdiv := hC7 P z hz.1 hnonneg hzroot
    have hPne : P ≠ 0 := by
      intro hP
      have hp := (hC6 w hw).1
      have he : P.eval 0 = 0 := by rw [hP]; simp
      rw [feasibilityPolynomial_eval, feasibilityExpression] at he
      norm_num at he
      linarith
    exact hC8 P x y z hPne (feasibilityPolynomial_degree w)
      (feasibilityPolynomial_coeff_five w) hx.1 hy.1 hz.1 hxy hxz hyz hxdiv hydiv hzdiv
  · intro w hw q r hq hr hqr
    obtain ⟨s, hs⟩ := hC1 w q hw hq
    obtain ⟨t, ht⟩ := hC1 w r hw hr
    have hst : s ≠ t := by
      intro h
      apply hqr
      apply hC5 w q r hw hq hr s hs
      simpa [h] using ht
    let P := feasibilityPolynomial w
    have hnonneg : ∀ u : ℝ, 0 < u → 0 ≤ P.eval u := by
      intro u hu
      rw [feasibilityPolynomial_eval]
      exact hC3 w hw u hu
    have hsroot : P.eval s = 0 := by
      rw [feasibilityPolynomial_eval]
      exact (hC4 w q hw hq s hs).1
    have htroot : P.eval t = 0 := by
      rw [feasibilityPolynomial_eval]
      exact (hC4 w r hw hr t ht).1
    have hsdiv := hC7 P s hs.1 hnonneg hsroot
    have htdiv := hC7 P t ht.1 hnonneg htroot
    have hfactor := hC9 w hw s t hs.1 ht.1 hst P
      (feasibilityPolynomial_eval w) hsdiv htdiv
    obtain ⟨hm0, hm1, hm2, hm3⟩ :=
      hC10 (w (0, 0)) (w (0, 1)) (w (1, 0)) (w (1, 1)) s t hs.1 ht.1 hfactor
    have hwpos : ∀ z, 0 < w z := fun z => hw.1 z (by simp)
    have hnodes := hC14 w q r hw hq hr hqr
    obtain ⟨h, hh, hhcube, hwmodel⟩ :=
      hC16 w hwpos s t hs.1 ht.1 hst hm0 hm1 hm2 hm3 hnodes
    let R := s + t
    let T := s * t
    let K := R ^ 2 - T
    let A := R - T ^ 2
    let D := R * T - 1
    let ws : Cell → ℝ := fun z =>
      if z = (0, 0) then h * A else if z = (0, 1) then h * K
      else if z = (1, 0) then h * K else h * D
    rcases hwmodel with hwmodel | hwmodel
    · let g : Cell ≃ Cell := Equiv.refl _
      have hg : g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
          g = swapRowsCell.trans swapColumnsCell := Or.inl rfl
      have hgw : pushforward g w = ws := by
        rw [show pushforward g w = w by
          funext z
          rw [pushforward_apply_equiv]
          rfl]
        exact hwmodel
      refine ⟨g, hg, ?_⟩
      have hqs := rowCubeParameter_refl hs
      have hrt := rowCubeParameter_refl ht
      have hw' := hC20 w g hg hw
      have hq' := hC19 w q g hg hq
      have hr' := hC19 w r g hg hr
      have hsymm : ∀ z, pushforward g w (transposeCell z) = pushforward g w z := by
        rw [hgw]
        exact symmetricModel_transpose h A K D
      obtain ⟨y, hycol, hy⟩ := (hC4 _ _ hw' hq' s hqs).2
      obtain ⟨hden, hnum, -, -⟩ := hC17 s t hs.1 ht.1
      have hyt : y = t := hy.trans (by
        rw [hgw]
        exact bestResponse_quotient hh (by linarith [hs.1, ht.1]) hs.1 hden hnum)
      have hqTrow := transpose_columnCubeParameter (hyt ▸ hycol)
      have hqT := hC18 _ _ hsymm hq'
      exact hC5 _ _ _ hw' hr' hqT t hrt hqTrow
    · let g : Cell ≃ Cell := swapColumnsCell
      have hg : g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
          g = swapRowsCell.trans swapColumnsCell := Or.inr (Or.inr (Or.inl rfl))
      have hgw : pushforward g w = ws := by simpa [g] using hwmodel
      refine ⟨g, hg, ?_⟩
      have hqs := rowCubeParameter_swapColumns hs
      have hrt := rowCubeParameter_swapColumns ht
      have hw' := hC20 w g hg hw
      have hq' := hC19 w q g hg hq
      have hr' := hC19 w r g hg hr
      have hsymm : ∀ z, pushforward g w (transposeCell z) = pushforward g w z := by
        rw [hgw]
        exact symmetricModel_transpose h A K D
      obtain ⟨y, hycol, hy⟩ := (hC4 _ _ hw' hq' s hqs).2
      obtain ⟨hden, hnum, -, -⟩ := hC17 s t hs.1 ht.1
      have hyt : y = t := hy.trans (by
        rw [hgw]
        exact bestResponse_quotient hh (by linarith [hs.1, ht.1]) hs.1 hden hnum)
      have hqTrow := transpose_columnCubeParameter (hyt ▸ hycol)
      have hqT := hC18 _ _ hsymm hq'
      exact hC5 _ _ _ hw' hr' hqT t hrt hqTrow

end Binary

end

end StochasticToDeterministicLatents

namespace StochasticToDeterministicLatents

noncomputable section

open Finset

namespace Binary

/-! ## From contact geometry to an oriented optimizer -/

private theorem exists_seedSetup_and_clustering
    (p : Cell → ℝ) (hp : IsPMF p) (hfull : ∀ z, 0 < p z) :
    ∃ D : SeedSetup p, Nonempty (Clustering D) := by
  obtain ⟨D⟩ := exists_fullSupport_seedSetup hp hfull
  exact ⟨D, exists_clustering D⟩

private theorem clustering_card_eq_one_or_two
    (hclass : ContactClassification)
    {p : Cell → ℝ} (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) :
    Fintype.card K.κ = 1 ∨ Fintype.card K.κ = 2 := by
  have hle : Fintype.card K.κ ≤ 2 := by
    by_contra hn
    have hthree : 3 ≤ Fintype.card K.κ := by omega
    let e := Fintype.equivFin K.κ
    let a : K.κ := e.symm ⟨0, by omega⟩
    let b : K.κ := e.symm ⟨1, by omega⟩
    let c : K.κ := e.symm ⟨2, by omega⟩
    have hab : a ≠ b := by
      intro hab
      have h := congrArg e hab
      simp [a, b] at h
    have hac : a ≠ c := by
      intro hac
      have h := congrArg e hac
      simp [a, c] at h
    have hbc : b ≠ c := by
      intro hbc
      have h := congrArg e hbc
      simp [b, c] at h
    rcases clustering_three_indices_duplicate hclass hfull D K a b c with h | h | h
    · exact hab h
    · exact hac h
    · exact hbc h
  have hlabels : Nonempty D.L.ι := by
    by_contra hn
    let _ : IsEmpty D.L.ι := not_nonempty_iff.mp hn
    have htotal := D.L.prior_isPMF.total
    simp [stoch_to_det.mass] at htotal
  have hnonempty : Nonempty K.κ := ⟨K.cl (Classical.choice hlabels)⟩
  have hpos : 0 < Fintype.card K.κ := Fintype.card_pos_iff.mpr hnonempty
  omega

private theorem transpose_pair_for_two_classes
    (htransposeForm : TransposeNormalForm)
    {p : Cell → ℝ} (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) (c d : K.κ) (hcd : c ≠ d) :
    ∃ g : Cell ≃ Cell,
      (g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
       g = swapRowsCell.trans swapColumnsCell) ∧
      pushforward g (K.Q d) =
        fun z => pushforward g (K.Q c) (transposeCell.symm z) := by
  have hsupp : support p = (univ : Finset Cell) := support_eq_univ_of_pos hfull
  apply htransposeForm D.w (by simpa [hsupp] using D.feasible) (K.Q c) (K.Q d)
  · simpa [hsupp] using K.Q_isContact c
  · simpa [hsupp] using K.Q_isContact d
  · exact fun h => hcd (K.Q_injective h)

private theorem pushforward_contact_pos
    {p : Cell → ℝ} (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) (c : K.κ) (e : Cell ≃ Cell) :
    ∀ z, 0 < pushforward e (K.Q c) z := by
  have hsuppP : support p = (univ : Finset Cell) := support_eq_univ_of_pos hfull
  have hsuppQ : support (K.Q c) = support p :=
    contact_support_eq D.feasible D.conn (K.Q_isContact c)
  apply pushforward_pos (e := e)
  intro z
  have hz : z ∈ support (K.Q c) := by simp [hsuppQ, hsuppP]
  have hne : K.Q c z ≠ 0 := by
    simpa [support, stoch_to_det.support] using hz
  exact lt_of_le_of_ne ((K.Q_isContact c).1.nonneg z) (Ne.symm hne)

private theorem strict_offDiagonal_orientation
    {p : Cell → ℝ} (D : SeedSetup p) (K : Clustering D)
    (c d : K.κ) (hcd : c ≠ d) (g : Cell ≃ Cell)
    (htranspose : pushforward g (K.Q d) =
      fun z => pushforward g (K.Q c) (transposeCell.symm z)) :
    pushforward g (K.Q c) (1, 0) < pushforward g (K.Q c) (0, 1) ∨
      pushforward g (K.Q c) (0, 1) < pushforward g (K.Q c) (1, 0) := by
  let q := pushforward g (K.Q c)
  have hqne : q ≠ fun z => q (transposeCell.symm z) := by
    intro heq
    have hrel : pushforward g (K.Q d) = pushforward g (K.Q c) :=
      htranspose.trans heq.symm
    have horig : K.Q d = K.Q c := by
      have h := congrArg (pushforward g.symm) hrel
      simpa [pushforward_symm_pushforward] using h
    exact hcd (K.Q_injective horig.symm)
  have hoff : q (0, 1) ≠ q (1, 0) := by
    intro heq
    apply hqne
    funext z
    rcases z with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> simp [transposeCell, heq]
  rcases lt_or_gt_of_ne hoff with h | h
  · exact Or.inr h
  · exact Or.inl h

private theorem chart_index_pair
    (g : Cell ≃ Cell)
    (hg : g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
      g = swapRowsCell.trans swapColumnsCell) :
    ∃ jb jt : Fin 8,
      chartCellEquiv jb = g ∧ chartCellEquiv jt = g.trans transposeCell := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨0, 4, by rfl, by ext z <;> rfl⟩
  · refine ⟨1, 6, by rfl, ?_⟩
    apply Equiv.ext
    intro z
    rcases z with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;>
      simp [chartCellEquiv, swapRowsCell, swapColumnsCell, transposeCell, bitFlip]
  · refine ⟨2, 5, by rfl, ?_⟩
    apply Equiv.ext
    intro z
    rcases z with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;>
      simp [chartCellEquiv, swapRowsCell, swapColumnsCell, transposeCell, bitFlip]
  · refine ⟨3, 7, by rfl, ?_⟩
    apply Equiv.ext
    intro z
    rcases z with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;>
      simp [chartCellEquiv, swapRowsCell, swapColumnsCell, transposeCell, bitFlip]

private theorem exists_admissible_chart
    {p : Cell → ℝ} (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D)
    (hcard : Fintype.card K.κ = 2)
    (g : Cell ≃ Cell)
    (hg : g = Equiv.refl _ ∨ g = swapRowsCell ∨ g = swapColumnsCell ∨
      g = swapRowsCell.trans swapColumnsCell)
    (htranspose :
      let e := Fintype.equivFinOfCardEq hcard
      pushforward g (K.Q (e.symm 1)) =
        fun z => pushforward g (K.Q (e.symm 0)) (transposeCell.symm z)) :
    ∃ j, ChartAdmissible K j := by
  let e : K.κ ≃ Bit := Fintype.equivFinOfCardEq hcard
  let c : K.κ := e.symm 0
  let d : K.κ := e.symm 1
  have hcd : c ≠ d := by simp [c, d]
  have ht : pushforward g (K.Q d) =
      fun z => pushforward g (K.Q c) (transposeCell.symm z) := by
    simpa [e, c, d] using htranspose
  obtain ⟨jb, jt, hjb, hjt⟩ := chart_index_pair g hg
  have hpost (a : K.κ) : pushforward (chartCellEquiv jt) (K.Q a) =
      fun z => pushforward g (K.Q a) (transposeCell.symm z) := by
    rw [hjt]
    funext z
    simp only [pushforward_apply_equiv]
    rfl
  have hrev : pushforward g (K.Q c) =
      fun z => pushforward g (K.Q d) (transposeCell.symm z) := by
    funext z
    rw [ht]
    simp [transposeCell]
  have hsum : K.s c + K.s d = 1 := by
    have htotal := K.quotientLatent.prior_isPMF.total
    rw [stoch_to_det.mass] at htotal
    change (∑ a : K.κ, K.s a) = 1 at htotal
    calc
      K.s c + K.s d = ∑ i : Bit, K.s (e.symm i) := by
        simp [c, d, Fin.sum_univ_two]
      _ = ∑ a : K.κ, K.s a := Equiv.sum_comp e.symm K.s
      _ = 1 := htotal
  have hminor : K.s c ≤ 1 / 2 ∨ K.s d ≤ 1 / 2 := by
    by_cases hc : K.s c ≤ 1 / 2
    · exact Or.inl hc
    · exact Or.inr (by
        have hc' : 1 / 2 < K.s c := lt_of_not_ge hc
        linarith)
  have horient := strict_offDiagonal_orientation D K c d hcd g ht
  rcases hminor with hc | hd
  · let ec : K.κ ≃ Bit := e.trans bitFlip
    have he0 : ec.symm 0 = d := by simp [ec, e, bitFlip, d]
    have he1 : ec.symm 1 = c := by simp [ec, e, bitFlip, c]
    rcases horient with hq | hq
    · refine ⟨jt, ⟨⟨ec, ?_, ?_, ?_, ?_⟩⟩⟩
      · rw [he0, he1, hpost, hpost]
        simpa [transposeCell] using ht.symm
      · rw [he0, hpost]
        have h10 := congrFun ht (0, 1)
        have h01 := congrFun ht (1, 0)
        simp [transposeCell] at h10 h01 ⊢
        linarith
      · simpa [he1] using hc
      · intro z
        exact pushforward_contact_pos hfull D K d (chartCellEquiv jt) z
    · refine ⟨jb, ⟨⟨ec, ?_, ?_, ?_, ?_⟩⟩⟩
      · rw [he0, he1, hjb]
        exact hrev
      · rw [he0, hjb, ht]
        simpa [transposeCell] using hq
      · simpa [he1] using hc
      · intro z
        exact pushforward_contact_pos hfull D K d (chartCellEquiv jb) z
  · rcases horient with hq | hq
    · refine ⟨jb, ⟨⟨e, ?_, ?_, ?_, ?_⟩⟩⟩
      · simpa [c, d, hjb] using ht
      · simpa [c, hjb] using hq
      · simpa [d] using hd
      · intro z
        exact pushforward_contact_pos hfull D K c (chartCellEquiv jb) z
    · refine ⟨jt, ⟨⟨e, ?_, ?_, ?_, ?_⟩⟩⟩
      · change pushforward (chartCellEquiv jt) (K.Q d) =
          fun z => pushforward (chartCellEquiv jt) (K.Q c) (transposeCell.symm z)
        rw [hpost, hpost]
        simpa [transposeCell] using hrev.symm
      · change pushforward (chartCellEquiv jt) (K.Q c) (1, 0) <
          pushforward (chartCellEquiv jt) (K.Q c) (0, 1)
        rw [hpost]
        simpa [transposeCell] using hq
      · simpa [d] using hd
      · intro z
        exact pushforward_contact_pos hfull D K c (chartCellEquiv jt) z

/-- The two geometric inputs produce a selected optimizer in transpose normal form. -/
theorem selectedOptimizerNormalForm_of_inputs
    (h : TransposeNormalFormInputs) : SelectedOptimizerNormalForm := by
  intro p hp hfull
  obtain ⟨D, hK⟩ := exists_seedSetup_and_clustering p hp hfull
  obtain ⟨K⟩ := hK
  refine ⟨D, K, ?_⟩
  rcases clustering_card_eq_one_or_two h.1 hfull D K with hcard | hcard
  · exact Or.inl hcard
  · refine Or.inr ⟨hcard, ?_⟩
    let e : K.κ ≃ Bit := Fintype.equivFinOfCardEq hcard
    let c : K.κ := e.symm 0
    let d : K.κ := e.symm 1
    have hcd : c ≠ d := by simp [c, d]
    obtain ⟨g, hg, ht⟩ := transpose_pair_for_two_classes h.2 hfull D K c d hcd
    exact exists_admissible_chart hfull D K hcard g hg (by simpa [e, c, d] using ht)

/-! ## Discharging the normal-form conditions -/

/-- Every algebraic and transport condition used by the reconstruction holds. -/
theorem allNormalFormConditions : NormalFormConditions := by
  exact ⟨positiveCubeRootIdentities, contact_hasRowCubeParameter,
    twoThirdsPowerMaximum, feasibilityExpression_nonneg,
    contactParameter_bestResponse, contactParameter_injective,
    feasibilityEndpointCoefficients_positive, positiveRoot_square_dvd,
    threePositiveDoubleRoots_impossible, twoContactPolynomial_factorization,
    twoContact_momentIdentities, twoNode_hankel_identity, twoNode_recurrence_unique,
    positiveTwoCube_decomposition_unique, distinctContacts_haveDistinctKernelNodes,
    factor_hankel_normalForm, symmetricKernel_reconstruction,
    symmetric_bestResponse_swaps_roots, contact_transposeOf_symmetricKernel,
    contact_pushforwardAlongChart, feasible_pushforwardAlongChart,
    transposePair_canOrientOffDiagonal⟩

/-- The contact classification and transpose-pair reconstruction hold unconditionally. -/
theorem transposeNormalFormInputs_hold : TransposeNormalFormInputs :=
  transposeNormalFormInputs_of_conditions allNormalFormConditions

/-- Every full-support binary law has an attained optimizer whose duplicate quotient has
one class, or two classes admitting an oriented transpose chart.

This is the module's conclusion. Note what it does and does not give. The dichotomy is on
the duplicate quotient `K`, so reaching a latent with at most two component laws means
passing to `Clustering.quotientSeedSetup`. Nothing here shows the two-class branch ever
occurs, so `ChartCandidate` is not known to be inhabited. And this is the transpose normal
form, not the explicit chart parametrization: no closed form for the component masses is
delivered, and in particular the strict determinant inequality is not proved here. -/
theorem selectedOptimizerNormalForm : SelectedOptimizerNormalForm :=
  selectedOptimizerNormalForm_of_inputs transposeNormalFormInputs_hold

end Binary

end

end StochasticToDeterministicLatents
