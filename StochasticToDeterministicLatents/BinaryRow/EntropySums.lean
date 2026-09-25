import StochasticToDeterministicLatents.BinaryRow.ReplicaCells
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entropies of a two-label latent as finite sums

Generic: conditional entropy moves along a pushforward (`condEntropy_pushforward_comp`), and
`log 2 · H(f | g)` is a difference of `negMulLog` sums over the laws of `(f, g)` and of `g`
(`log_two_mul_condEntropy_eq_sum`).

On `Bit × Y`, for a latent `V` with labels identified with `Bit` by `e`, with no contact
assumption, write `πᵢ` for the prior and `mᵢ` for the row-one mass of component `i`. Then
`log 2 · H(X | W) = Σᵢ πᵢ h(mᵢ)` (`bitLatent_log_two_mul_condEntropy_row`),
`log 2 · I(W; X) = h(Σᵢ πᵢ mᵢ) - Σᵢ πᵢ h(mᵢ)` (`bitLatent_log_two_mul_mutualInfo_label_row`), and
`log 2 · H(W | X)` is a sum over `x` of `negMulLog` terms of the masses `πᵢ · rowMass (comp i) x`
(`bitLatent_log_two_mul_condEntropy_label`). For two contacts of one feasible kernel with row
parameters `s ≠ t`, `log 2 · H(W | X', X)` under the replica is the corresponding sum over the eight
cells `πᵢ · replicaCell κ mᵢ x x'` (`twoContact_log_two_mul_condEntropy_label_rows`).

Information quantities are in bits; each right side is `Real.log 2` times the bit-valued left side,
a sum of `negMulLog` or `binEntropy` terms in nats.

## Attribution

Original to this repository, on the entropy interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

/-! ## Generic helpers -/

/-- The law of the first coordinate of an equivalence `e : Ω ≃ A × K` at `a` is the sum over
the second coordinate. -/
private theorem aux_push_fst_equiv {Ω A K : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype K] (e : Ω ≃ A × K) (m : Ω → ℝ) (a : A) :
    pushforward (fun ω => (e ω).1) m a = ∑ k, m (e.symm (a, k)) := by
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, ← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- The law of the second coordinate of a law on a product is the sum over the first. -/
private theorem aux_push_snd_prod {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (q : A × B → ℝ) (b : B) :
    pushforward Prod.snd q b = ∑ a, q (a, b) := by
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

/-- The law of `g` is the second marginal of the law of `(f, g)`. -/
private theorem aux_push_pair_snd {Ω A B : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (m : Ω → ℝ) (f : Ω → A) (g : Ω → B) (b : B) :
    pushforward g m b = ∑ a, pushforward (fun ω => (f ω, g ω)) m (a, b) := by
  rw [← aux_push_snd_prod]
  unfold pushforward
  rw [stoch_to_det.push_push]
  rfl

/-- Two variables with the same level sets at `c` and `c'` have the same mass there. -/
private theorem aux_push_congr {Ω A B : Type*} [Fintype Ω] [DecidableEq A] [DecidableEq B]
    (m : Ω → ℝ) (u : Ω → A) (u' : Ω → B) (c : A) (c' : B) (h : ∀ ω, u ω = c ↔ u' ω = c') :
    pushforward u m c = pushforward u' m c' := by
  unfold pushforward stoch_to_det.push
  rw [Finset.filter_congr fun ω _ => h ω]

/-- A law on `Bit` has mass `1 - q 1` at `0`. -/
private theorem aux_bit_pmf_zero {q : Bit → ℝ} (hq : IsPMF q) : q 0 = 1 - q 1 := by
  have h := hq.total
  unfold stoch_to_det.mass at h
  rw [Fin.sum_univ_two] at h
  linarith

/-- `log 2 · H(f | g)` with the law of `g` written as the column sums of the law of `(f, g)`. -/
private theorem aux_log_two_mul_condEntropy_cols {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) :
    Real.log 2 * condEntropy f g m =
      ∑ b, ∑ a, Real.negMulLog (pushforward (fun ω => (f ω, g ω)) m (a, b))
        - ∑ b, Real.negMulLog (∑ a, pushforward (fun ω => (f ω, g ω)) m (a, b)) := by
  have h2 : Real.log 2 * condEntropy f g m =
      Real.log 2 * entropyOf (fun ω => (f ω, g ω)) m - Real.log 2 * entropyOf g m := by
    rw [← mul_sub]
    rfl
  rw [h2, log_two_mul_entropyOf hm, log_two_mul_entropyOf hm, Fintype.sum_prod_type,
    Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [aux_push_pair_snd m f g b]

/-- Swapping a pair does not change its entropy. -/
private theorem aux_entropyOf_pair_comm {Ω A B : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) :
    entropyOf (fun ω => (f ω, g ω)) m = entropyOf (fun ω => (g ω, f ω)) m := by
  symm
  simpa using entropyOf_equiv hm (fun ω => (f ω, g ω)) (Equiv.prodComm A B)

/-- `negMulLog (π (1 - r)) + negMulLog (π r) - negMulLog π = π h(r)`. -/
private theorem aux_negMulLog_split (π r : ℝ) :
    Real.negMulLog (π * (1 - r)) + Real.negMulLog (π * r) - Real.negMulLog π =
      π * Real.binEntropy r := by
  rw [Real.negMulLog_mul, Real.negMulLog_mul, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- Conditional entropy of variables on a law pushed forward along any map is that of the
composed variables. -/
theorem condEntropy_pushforward_comp {Ω Ω' A B : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (m : Ω → ℝ) (φ : Ω → Ω') (f : Ω' → A) (g : Ω' → B) :
    condEntropy f g (pushforward φ m) = condEntropy (fun ω => f (φ ω)) (fun ω => g (φ ω)) m := by
  have h2 := entropyOf_pushforward_comp m φ g
  have h3 := entropyOf_pushforward_comp m φ (fun z => (f z, g z))
  simp only [entropyOf] at h2 h3
  unfold condEntropy stoch_to_det.condH
  rw [h2, h3]

/-- `log 2 · H(f | g)` as `negMulLog` sums over the laws of `(f, g)` and of `g`. -/
theorem log_two_mul_condEntropy_eq_sum {Ω A B : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) :
    Real.log 2 * condEntropy f g m =
      ∑ c : A × B, Real.negMulLog (pushforward (fun ω => (f ω, g ω)) m c)
        - ∑ b, Real.negMulLog (pushforward g m b) := by
  have h2 : Real.log 2 * condEntropy f g m =
      Real.log 2 * entropyOf (fun ω => (f ω, g ω)) m - Real.log 2 * entropyOf g m := by
    rw [← mul_sub]
    rfl
  rw [h2, log_two_mul_entropyOf hm, log_two_mul_entropyOf hm]

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-! ## Latent helpers on `Bit × Y` -/

/-- Regroup `(W, (X, Y))` as `((W, X), Y)`. -/
private def aux_eWX {I A B : Type*} : I × (A × B) ≃ (I × A) × B where
  toFun a := ((a.1, a.2.1), a.2.2)
  invFun b := (b.1.1, (b.1.2, b.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq Y] in
/-- The row masses of a component sum to one. -/
private theorem aux_rowMass_zero {p : Bit × Y → ℝ} (V : Latent p) (v : V.ι) :
    rowMass (V.comp v) 0 = 1 - rowMass (V.comp v) 1 :=
  aux_bit_pmf_zero (rowMass_isPMF (V.comp_isPMF v))

omit [DecidableEq Y] in
/-- The law of `(W, X)` under a latent's joint law. -/
private theorem aux_law_WX {p : Bit × Y → ℝ} (V : Latent p) (v : V.ι) (x : Bit) :
    pushforward (fun a : V.ι × (Bit × Y) => (a.1, a.2.1)) V.joint (v, x) =
      V.prior v * rowMass (V.comp v) x := by
  refine (aux_push_fst_equiv aux_eWX V.joint (v, x)).trans ?_
  show ∑ y, V.prior v * V.comp v (x, y) = _
  rw [← Finset.mul_sum]
  rfl

omit [DecidableEq Y] in
/-- The law of `(X, W)` under a latent's joint law. -/
private theorem aux_law_XW {p : Bit × Y → ℝ} (V : Latent p) (x : Bit) (v : V.ι) :
    pushforward (fun a : V.ι × (Bit × Y) => (a.2.1, a.1)) V.joint (x, v) =
      V.prior v * rowMass (V.comp v) x := by
  rw [← aux_law_WX V v x]
  apply aux_push_congr
  intro a
  simp only [Prod.mk.injEq]
  tauto

omit [DecidableEq Y] in
/-- `log 2 · H(X | W) = Σᵢ πᵢ h(mᵢ)` for a `Bit`-labelled latent on `Bit × Y`. -/
theorem bitLatent_log_two_mul_condEntropy_row {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit) :
    Real.log 2 * condEntropy (fun a : V.ι × (Bit × Y) => a.2.1) (fun a => a.1) V.joint =
      ∑ i : Bit, V.prior (e.symm i) * Real.binEntropy (rowMass (V.comp (e.symm i)) 1) := by
  have h := aux_log_two_mul_condEntropy_cols V.joint_isPMF
    (fun a : V.ι × (Bit × Y) => a.2.1) (fun a => a.1)
  rw [h, ← Finset.sum_sub_distrib, ← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.sum_univ_two, aux_law_XW]
  rw [aux_rowMass_zero V (e.symm i), ← mul_add, sub_add_cancel, mul_one]
  exact aux_negMulLog_split _ _

omit [DecidableEq Y] in
/-- `log 2 · I(W; X) = h(Σᵢ πᵢ mᵢ) - Σᵢ πᵢ h(mᵢ)` for a `Bit`-labelled latent on `Bit × Y`. -/
theorem bitLatent_log_two_mul_mutualInfo_label_row {p : Bit × Y → ℝ} (V : Latent p)
    (e : V.ι ≃ Bit) :
    Real.log 2 * mutualInfo (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1) V.joint =
      Real.binEntropy (∑ i : Bit, V.prior (e.symm i) * rowMass (V.comp (e.symm i)) 1)
        - ∑ i : Bit, V.prior (e.symm i) * Real.binEntropy (rowMass (V.comp (e.symm i)) 1) := by
  have hJ := V.joint_isPMF
  have hc := aux_entropyOf_pair_comm hJ (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1)
  have hI : mutualInfo (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1) V.joint =
      entropyOf (fun a : V.ι × (Bit × Y) => a.2.1) V.joint
        - condEntropy (fun a : V.ι × (Bit × Y) => a.2.1) (fun a => a.1) V.joint := by
    simp only [entropyOf] at hc
    simp only [mutualInfo, condEntropy, entropyOf, stoch_to_det.MI, stoch_to_det.condH]
    rw [hc]
    ring
  rw [hI, mul_sub, log_two_mul_entropyOf hJ, bitLatent_log_two_mul_condEntropy_row V e]
  have hX : ∀ x, pushforward (fun a : V.ι × (Bit × Y) => a.2.1) V.joint x =
      ∑ i : Bit, V.prior (e.symm i) * rowMass (V.comp (e.symm i)) x := by
    intro x
    rw [aux_push_pair_snd V.joint (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1) x,
      ← e.symm.sum_comp]
    simp only [aux_law_WX]
  have h0 := aux_bit_pmf_zero (pushforward_isPMF (f := fun a : V.ι × (Bit × Y) => a.2.1) hJ)
  rw [Fin.sum_univ_two, h0, hX 1, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

omit [DecidableEq Y] in
/-- `log 2 · H(W | X)` for a `Bit`-labelled latent on `Bit × Y`, as a sum over rows `x` of
`negMulLog` of the masses `πᵢ · rowMass (comp i) x`. -/
theorem bitLatent_log_two_mul_condEntropy_label {p : Bit × Y → ℝ} (V : Latent p)
    (e : V.ι ≃ Bit) :
    Real.log 2 * condEntropy (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1) V.joint =
      ∑ x : Bit,
        (Real.negMulLog (V.prior (e.symm 0) * rowMass (V.comp (e.symm 0)) x)
          + Real.negMulLog (V.prior (e.symm 1) * rowMass (V.comp (e.symm 1)) x)
          - Real.negMulLog (V.prior (e.symm 0) * rowMass (V.comp (e.symm 0)) x
              + V.prior (e.symm 1) * rowMass (V.comp (e.symm 1)) x)) := by
  have h := aux_log_two_mul_condEntropy_cols V.joint_isPMF
    (fun a : V.ι × (Bit × Y) => a.1) (fun a => a.2.1)
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.symm.sum_comp, ← e.symm.sum_comp]
  simp only [Fin.sum_univ_two, aux_law_WX]

/-- `log 2 · H(W | X', X)` under the replica of a two-contact latent, as a sum over the eight cells
`πᵢ · replicaCell κ mᵢ x x'` with `κ = st/(s+t)²`. -/
theorem twoContact_log_two_mul_condEntropy_label_rows {p : Bit × Y → ℝ} (V : Latent p)
    (e : V.ι ≃ Bit) {w : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s ≠ t) :
    Real.log 2 * condEntropy (fun a : V.ι × (Bit × (Bit × Y)) => a.1) (fun a => (a.2.2.1, a.2.1))
        (replicaLaw V.joint) =
      ∑ x : Bit, ∑ x' : Bit,
        (Real.negMulLog (V.prior (e.symm 0) *
            replicaCell (s * t / (s + t) ^ 2) (rowMass (V.comp (e.symm 0)) 1) x x')
          + Real.negMulLog (V.prior (e.symm 1) *
            replicaCell (s * t / (s + t) ^ 2) (rowMass (V.comp (e.symm 1)) 1) x x')
          - Real.negMulLog
              (V.prior (e.symm 0) *
                  replicaCell (s * t / (s + t) ^ 2) (rowMass (V.comp (e.symm 0)) 1) x x'
                + V.prior (e.symm 1) *
                  replicaCell (s * t / (s + t) ^ 2) (rowMass (V.comp (e.symm 1)) 1) x x')) := by
  have hR := replicaLaw_isPMF V.joint_isPMF
  have h := aux_log_two_mul_condEntropy_cols hR
    (fun a : V.ι × (Bit × (Bit × Y)) => a.1) (fun a => (a.2.2.1, a.2.1))
  have hcell : ∀ i x x' : Bit,
      pushforward (fun a : V.ι × (Bit × (Bit × Y)) => (a.1, (a.2.2.1, a.2.1)))
          (replicaLaw V.joint) (e.symm i, (x', x)) =
        V.prior (e.symm i) *
          replicaCell (s * t / (s + t) ^ 2) (rowMass (V.comp (e.symm i)) 1) x x' := by
    intro i x x'
    rw [← twoContact_replica_rows V e hw h0 h1 hs ht hst i x x']
    apply aux_push_congr
    intro a
    simp only [Prod.mk.injEq]
    tauto
  rw [h, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  refine Finset.sum_comm.trans
    (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_)
  rw [← e.symm.sum_comp, ← e.symm.sum_comp]
  simp only [Fin.sum_univ_two, hcell]

end

end BinaryRow

end StochasticToDeterministicLatents
