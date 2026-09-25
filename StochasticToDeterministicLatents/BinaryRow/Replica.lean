import StochasticToDeterministicLatents.BinaryRow.Foundation

/-!
# The row replica

For a joint law `r` of a finite label `W` and the observed pair `(X, Y)` on any finite `α × β`,
the row replica (`replicaLaw`) draws a second row `X'` from the conditional law of `X` given
`(W, Y)`, independently of `X`. Its coordinates are `(W, (X, (X', Y)))`. This module proves that
the replica is a probability law (`replicaLaw_isPMF`) under which `(W, X, Y)` and `(W, X', Y)`
both have law `r` (`replicaLaw_pushforward_original`, `replicaLaw_pushforward_replica`), and `X`
and `X'` are conditionally independent given `(W, Y)`
(`replicaLaw_condMutualInfo_rows_eq_zero`). Hence

  `I(W; X' | X) + I(X; X' | Y) ≤ I(W; X | Y) + I(W; Y | X)` (`replica_bound_sharp`),

the left side under the replica and the right side under `r`, and
`I(X; Y | W) + I(W; X' | X) ≤ L.score` for every finite latent `L` (`latent_replica_bound`).
The chain is

  `I(W;X'|X) ≤ I(W;Y,X'|X) = I(W;Y|X) + I(W;X'|X,Y) = I(W;Y|X) + I(W;X|Y) - I(X;X'|Y)`,

done once on an abstract law in `condMutualInfo_add_le_of_condIndep`. All information quantities
are in bits; nothing here depends on the base. `condMutualInfo f g h m` is `I(f; g | h)` under
`m`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose entropy
functionals and latent structure these proofs use. The replica construction and its bound are
original to this repository.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The marginal mass `P(W = i, Y = y)` of label `i` and column `y` under a joint law `r` of a
label and the observed pair. -/
def labelColMass (r : ι × (α × β) → ℝ) (i : ι) (y : β) : ℝ :=
  ∑ x, r (i, (x, y))

/-- The row replica of a joint law `r` of a label `W` and the observed pair `(X, Y)`, with
coordinates `(W, (X, (X', Y)))`: given `(W, Y)`, the rows `X` and `X'` are independent, each with
the conditional law of `X`. The point `(i, (x, (x', y)))` has mass
`r(i,(x,y)) · r(i,(x',y)) / P(W = i, Y = y)`, and zero where that mass is zero. -/
def replicaLaw (r : ι × (α × β) → ℝ) : ι × (α × (α × β)) → ℝ := fun a =>
  if labelColMass r a.1 a.2.2.2 = 0 then 0
  else r (a.1, (a.2.1, a.2.2.2)) * r (a.1, (a.2.2.1, a.2.2.2)) / labelColMass r a.1 a.2.2.2

/-! ## Helpers: generic facts on any finite sample space -/

/-- The law of the first coordinate of an equivalence `e : Ω ≃ A × K` at `a` is the
sum over the second coordinate. -/
private theorem aux_push_fst_equiv {Ω A K : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype K]
    (e : Ω ≃ A × K) (m : Ω → ℝ) (a : A) :
    pushforward (fun ω => (e ω).1) m a = ∑ k, m (e.symm (a, k)) := by
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, ← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- Every point carries at most the mass of its fibre. -/
private theorem aux_le_push {Ω D : Type*} [Fintype Ω] [DecidableEq D] {m : Ω → ℝ}
    (hm : ∀ ω, 0 ≤ m ω) (u : Ω → D) (ω : Ω) : m ω ≤ stoch_to_det.push u m (u ω) := by
  unfold stoch_to_det.push
  exact Finset.single_le_sum (f := m) (fun b _ => hm b) (by simp)

/-- The entropy of a variable, in natural-log units, as an expectation of
`-log` of the law of the variable at the sample point. -/
private theorem aux_log_two_mul_Hvar {Ω D : Type*} [Fintype Ω] [Fintype D] [DecidableEq D]
    {m : Ω → ℝ} (hm : IsPMF m) (u : Ω → D) :
    Real.log 2 * stoch_to_det.Hvar u m =
      ∑ ω, m ω * (-Real.log (stoch_to_det.push u m (u ω))) := by
  have h := log_two_mul_entropyOf hm u
  have h2 := stoch_to_det.sum_push_mul u m (fun a => -Real.log (stoch_to_det.push u m a))
  rw [← h2]
  refine h.trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  show Real.negMulLog (stoch_to_det.push u m c) = _
  unfold Real.negMulLog
  ring

/-- Conditional mutual information vanishes for a conditionally product law, that is,
when at every point of positive mass `P(f,g,h) P(h) = P(f,h) P(g,h)`. -/
theorem condMutualInfo_eq_zero_of_factor {Ω A B C : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B) (h : Ω → C)
    (hfac : ∀ ω, 0 < m ω →
      pushforward (fun ω => (f ω, g ω, h ω)) m (f ω, g ω, h ω) * pushforward h m (h ω) =
        pushforward (fun ω => (f ω, h ω)) m (f ω, h ω) *
          pushforward (fun ω => (g ω, h ω)) m (g ω, h ω)) :
    condMutualInfo f g h m = 0 := by
  have h1 := aux_log_two_mul_Hvar hm (fun ω => (f ω, h ω))
  have h2 := aux_log_two_mul_Hvar hm (fun ω => (g ω, h ω))
  have h3 := aux_log_two_mul_Hvar hm (fun ω => (f ω, g ω, h ω))
  have h4 := aux_log_two_mul_Hvar hm h
  have hsplit : Real.log 2 * condMutualInfo f g h m =
      Real.log 2 * stoch_to_det.Hvar (fun ω => (f ω, h ω)) m
        + Real.log 2 * stoch_to_det.Hvar (fun ω => (g ω, h ω)) m
        - Real.log 2 * stoch_to_det.Hvar (fun ω => (f ω, g ω, h ω)) m
        - Real.log 2 * stoch_to_det.Hvar h m := by
    simp only [condMutualInfo, stoch_to_det.condMI]
    ring
  have hsum : Real.log 2 * condMutualInfo f g h m = 0 := by
    rw [hsplit, h1, h2, h3, h4, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rcases (hm.nonneg ω).eq_or_lt with h0 | hpos
    · rw [← h0]
      ring
    · have hfgh : 0 < stoch_to_det.push (fun ω => (f ω, g ω, h ω)) m (f ω, g ω, h ω) :=
        hpos.trans_le (aux_le_push hm.nonneg (fun ω => (f ω, g ω, h ω)) ω)
      have hh : 0 < stoch_to_det.push h m (h ω) := hpos.trans_le (aux_le_push hm.nonneg h ω)
      have hfh : 0 < stoch_to_det.push (fun ω => (f ω, h ω)) m (f ω, h ω) :=
        hpos.trans_le (aux_le_push hm.nonneg (fun ω => (f ω, h ω)) ω)
      have hgh : 0 < stoch_to_det.push (fun ω => (g ω, h ω)) m (g ω, h ω) :=
        hpos.trans_le (aux_le_push hm.nonneg (fun ω => (g ω, h ω)) ω)
      have hf : stoch_to_det.push (fun ω => (f ω, g ω, h ω)) m (f ω, g ω, h ω) *
            stoch_to_det.push h m (h ω) =
          stoch_to_det.push (fun ω => (f ω, h ω)) m (f ω, h ω) *
            stoch_to_det.push (fun ω => (g ω, h ω)) m (g ω, h ω) := hfac ω hpos
      have key : Real.log (stoch_to_det.push (fun ω => (f ω, g ω, h ω)) m (f ω, g ω, h ω)) +
            Real.log (stoch_to_det.push h m (h ω)) =
          Real.log (stoch_to_det.push (fun ω => (f ω, h ω)) m (f ω, h ω)) +
            Real.log (stoch_to_det.push (fun ω => (g ω, h ω)) m (g ω, h ω)) := by
        rw [← Real.log_mul hfgh.ne' hh.ne', ← Real.log_mul hfh.ne' hgh.ne', hf]
      linear_combination (m ω) * key
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  exact (mul_eq_zero.mp hsum).resolve_left hlog

/-- Swapping the pair in the second argument, `I(l; (x,y) | g) = I(l; (y,x) | g)`. -/
theorem condMutualInfo_swap_snd {Ω A B C D : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] {m : Ω → ℝ} (hm : IsPMF m)
    (l : Ω → A) (x : Ω → B) (y : Ω → C) (g : Ω → D) :
    condMutualInfo l (fun ω => (x ω, y ω)) g m = condMutualInfo l (fun ω => (y ω, x ω)) g m := by
  have h1 : entropyOf (fun ω => ((y ω, x ω), g ω)) m =
      entropyOf (fun ω => ((x ω, y ω), g ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => ((x ω, y ω), g ω))
      (Equiv.prodCongr (Equiv.prodComm B C) (Equiv.refl D))
  have h2 : entropyOf (fun ω => (l ω, (y ω, x ω), g ω)) m =
      entropyOf (fun ω => (l ω, (x ω, y ω), g ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => (l ω, (x ω, y ω), g ω))
      (Equiv.prodCongr (Equiv.refl A) (Equiv.prodCongr (Equiv.prodComm B C) (Equiv.refl D)))
  simp only [entropyOf] at h1 h2
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [h1, h2]

/-- Swapping the pair in the condition, `I(f; g | (x,y)) = I(f; g | (y,x))`. -/
private theorem aux_condMutualInfo_swap_cond {Ω A B C D : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → A) (g : Ω → B) (x : Ω → C) (y : Ω → D) :
    condMutualInfo f g (fun ω => (x ω, y ω)) m = condMutualInfo f g (fun ω => (y ω, x ω)) m := by
  have h1 : entropyOf (fun ω => (f ω, (y ω, x ω))) m =
      entropyOf (fun ω => (f ω, (x ω, y ω))) m := by
    simpa using entropyOf_equiv hm (fun ω => (f ω, (x ω, y ω)))
      (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm C D))
  have h2 : entropyOf (fun ω => (g ω, (y ω, x ω))) m =
      entropyOf (fun ω => (g ω, (x ω, y ω))) m := by
    simpa using entropyOf_equiv hm (fun ω => (g ω, (x ω, y ω)))
      (Equiv.prodCongr (Equiv.refl B) (Equiv.prodComm C D))
  have h3 : entropyOf (fun ω => (f ω, g ω, (y ω, x ω))) m =
      entropyOf (fun ω => (f ω, g ω, (x ω, y ω))) m := by
    simpa using entropyOf_equiv hm (fun ω => (f ω, g ω, (x ω, y ω)))
      (Equiv.prodCongr (Equiv.refl A) (Equiv.prodCongr (Equiv.refl B) (Equiv.prodComm C D)))
  have h4 : entropyOf (fun ω => (y ω, x ω)) m = entropyOf (fun ω => (x ω, y ω)) m := by
    simpa using entropyOf_equiv hm (fun ω => (x ω, y ω)) (Equiv.prodComm C D)
  simp only [entropyOf] at h1 h2 h3 h4
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [h1, h2, h3, h4]

/-- The replica chain. If `x` and `x'` are conditionally independent given `(w, y)`,
then `I(w; x' | x) + I(x; x' | y) ≤ I(w; x' | y) + I(w; y | x)`. -/
theorem condMutualInfo_add_le_of_condIndep {Ω I A A' B : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B]
    {m : Ω → ℝ} (hm : IsPMF m) (w : Ω → I) (x : Ω → A) (x' : Ω → A') (y : Ω → B)
    (hind : condMutualInfo x x' (fun ω => (w ω, y ω)) m = 0) :
    condMutualInfo w x' x m + condMutualInfo x x' y m ≤
      condMutualInfo w x' y m + condMutualInfo w y x m := by
  have c1 := condMutualInfo_chain_pair hm w y x' x
  have c2 := condMutualInfo_chain_pair hm w x' y x
  have s1 := condMutualInfo_swap_snd hm w x' y x
  have n1 := condMutualInfo_nonneg hm w y (fun ω => (x' ω, x ω))
  have s2 := aux_condMutualInfo_swap_cond hm w x' y x
  have cm1 := condMutualInfo_comm hm w x' (fun ω => (x ω, y ω))
  have c3 := condMutualInfo_chain_pair hm x' w x y
  have c4 := condMutualInfo_chain_pair hm x' x w y
  have s3 := condMutualInfo_swap_snd hm x' w x y
  have z : condMutualInfo x' x (fun ω => (w ω, y ω)) m = 0 := by
    rw [condMutualInfo_comm hm]
    exact hind
  have cm2 := condMutualInfo_comm hm x' w y
  have cm3 := condMutualInfo_comm hm x' x y
  linarith

/-! ## Helpers: coordinates of the replica -/

/-- Regroup the replica coordinates as `((W, X, Y), X')`. -/
private def aux_eOrig {I A B : Type*} : I × (A × (A × B)) ≃ (I × (A × B)) × A where
  toFun a := ((a.1, (a.2.1, a.2.2.2)), a.2.2.1)
  invFun b := (b.1.1, (b.1.2.1, (b.2, b.1.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup the replica coordinates as `((W, X', Y), X)`. -/
private def aux_eRep {I A B : Type*} : I × (A × (A × B)) ≃ (I × (A × B)) × A where
  toFun a := ((a.1, (a.2.2.1, a.2.2.2)), a.2.1)
  invFun b := (b.1.1, (b.2, (b.1.2.1, b.1.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup the replica coordinates as `((W, Y), (X, X'))`. -/
private def aux_eCond {I A B : Type*} : I × (A × (A × B)) ≃ (I × B) × (A × A) where
  toFun a := ((a.1, a.2.2.2), (a.2.1, a.2.2.1))
  invFun b := (b.1.1, (b.2.1, (b.2.2, b.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup the replica coordinates as `((X, (W, Y)), X')`. -/
private def aux_eFH {I A B : Type*} : I × (A × (A × B)) ≃ (A × (I × B)) × A where
  toFun a := ((a.2.1, (a.1, a.2.2.2)), a.2.2.1)
  invFun b := (b.1.2.1, (b.1.1, (b.2, b.1.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup the replica coordinates as `((X', (W, Y)), X)`. -/
private def aux_eGH {I A B : Type*} : I × (A × (A × B)) ≃ (A × (I × B)) × A where
  toFun a := ((a.2.2.1, (a.1, a.2.2.2)), a.2.1)
  invFun b := (b.1.2.1, (b.2, (b.1.1, b.1.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup the replica coordinates as `((X, (X', (W, Y))), ())`. -/
private def aux_eFGH {I A B : Type*} : I × (A × (A × B)) ≃ (A × (A × (I × B))) × Unit where
  toFun a := ((a.2.1, (a.2.2.1, (a.1, a.2.2.2))), ())
  invFun b := (b.1.2.2.1, (b.1.1, (b.1.2.1, b.1.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Helpers: the replica's masses -/

omit [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
/-- The label-column mass of a probability law is nonnegative. -/
theorem labelColMass_nonneg {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (y : β) :
    0 ≤ labelColMass r i y := by
  unfold labelColMass
  exact Finset.sum_nonneg fun x _ => hr.nonneg _

omit [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
private theorem aux_cell_eq_zero {r : ι × (α × β) → ℝ} (hr : IsPMF r) {i : ι} {y : β}
    (h : labelColMass r i y = 0) (x : α) : r (i, (x, y)) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hr.nonneg (i, (x, y)))).mp h x
    (Finset.mem_univ x)

omit [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
private theorem aux_replicaLaw_nonneg {r : ι × (α × β) → ℝ} (hr : IsPMF r)
    (a : ι × (α × (α × β))) : 0 ≤ replicaLaw r a := by
  unfold replicaLaw
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (hr.nonneg _) (hr.nonneg _))
      (labelColMass_nonneg hr _ _)

omit [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
private theorem aux_sum_replica {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (x : α) (y : β) :
    ∑ x', replicaLaw r (i, (x, (x', y))) = r (i, (x, y)) := by
  simp only [replicaLaw]
  by_cases h : labelColMass r i y = 0
  · simp only [if_pos h, Finset.sum_const_zero]
    exact (aux_cell_eq_zero hr h x).symm
  · simp only [if_neg h]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change r (i, (x, y)) * labelColMass r i y / labelColMass r i y = _
    field_simp

omit [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
private theorem aux_sum_original {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (x' : α) (y : β) :
    ∑ x, replicaLaw r (i, (x, (x', y))) = r (i, (x', y)) := by
  simp only [replicaLaw]
  by_cases h : labelColMass r i y = 0
  · simp only [if_pos h, Finset.sum_const_zero]
    exact (aux_cell_eq_zero hr h x').symm
  · simp only [if_neg h]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    change labelColMass r i y * r (i, (x', y)) / labelColMass r i y = _
    field_simp

private theorem aux_push_original {r : ι × (α × β) → ℝ} (hr : IsPMF r) :
    pushforward (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.2))) (replicaLaw r) = r := by
  funext c
  rcases c with ⟨i, x, y⟩
  exact (aux_push_fst_equiv aux_eOrig (replicaLaw r) (i, (x, y))).trans (aux_sum_replica hr i x y)

/-- The replica of a probability law is a probability law. -/
theorem replicaLaw_isPMF {r : ι × (α × β) → ℝ} (hr : IsPMF r) : IsPMF (replicaLaw r) := by
  refine ⟨aux_replicaLaw_nonneg hr, ?_⟩
  have hmass := stoch_to_det.mass_push
    (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.2))) (replicaLaw r)
  have h2 : stoch_to_det.push (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.2)))
      (replicaLaw r) = r := aux_push_original hr
  rw [h2] at hmass
  rw [← hmass]
  exact hr.total

omit [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
/-- Summing out the replica row `X'` recovers the joint law of `(W, X, Y)`. -/
theorem replicaLaw_sum_replica {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (x : α) (y : β) :
    ∑ x', replicaLaw r (i, (x, (x', y))) = r (i, (x, y)) := by
  exact aux_sum_replica hr i x y

omit [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
/-- Summing out the original row `X` gives the joint law of `(W, X', Y)`, which is `r` again. -/
theorem replicaLaw_sum_original {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (x' : α) (y : β) :
    ∑ x, replicaLaw r (i, (x, (x', y))) = r (i, (x', y)) := by
  exact aux_sum_original hr i x' y

/-- The law of `(W, (X, Y))` under the replica is `r`. -/
theorem replicaLaw_pushforward_original {r : ι × (α × β) → ℝ} (hr : IsPMF r) :
    pushforward (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.2))) (replicaLaw r) = r := by
  exact aux_push_original hr

/-- The law of `(W, (X', Y))` under the replica is `r`. -/
theorem replicaLaw_pushforward_replica {r : ι × (α × β) → ℝ} (hr : IsPMF r) :
    pushforward (fun a : ι × (α × (α × β)) => (a.1, (a.2.2.1, a.2.2.2))) (replicaLaw r) = r := by
  funext c
  rcases c with ⟨i, x', y⟩
  exact (aux_push_fst_equiv aux_eRep (replicaLaw r) (i, (x', y))).trans
    (aux_sum_original hr i x' y)

omit [DecidableEq α] in
private theorem aux_push_cond {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (y : β) :
    pushforward (fun a : ι × (α × (α × β)) => (a.1, a.2.2.2)) (replicaLaw r) (i, y) =
      labelColMass r i y := by
  refine (aux_push_fst_equiv aux_eCond (replicaLaw r) (i, y)).trans ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => aux_sum_replica hr i x y

private theorem aux_push_fh {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (x : α) (y : β) :
    pushforward (fun a : ι × (α × (α × β)) => (a.2.1, a.1, a.2.2.2)) (replicaLaw r) (x, i, y) =
      r (i, (x, y)) :=
  (aux_push_fst_equiv aux_eFH (replicaLaw r) (x, (i, y))).trans (aux_sum_replica hr i x y)

private theorem aux_push_gh {r : ι × (α × β) → ℝ} (hr : IsPMF r) (i : ι) (x' : α) (y : β) :
    pushforward (fun a : ι × (α × (α × β)) => (a.2.2.1, a.1, a.2.2.2)) (replicaLaw r)
        (x', i, y) = r (i, (x', y)) :=
  (aux_push_fst_equiv aux_eGH (replicaLaw r) (x', (i, y))).trans (aux_sum_original hr i x' y)

private theorem aux_push_fgh (r : ι × (α × β) → ℝ) (i : ι) (x x' : α) (y : β) :
    pushforward (fun a : ι × (α × (α × β)) => (a.2.1, a.2.2.1, a.1, a.2.2.2)) (replicaLaw r)
        (x, x', i, y) = replicaLaw r (i, (x, (x', y))) := by
  refine (aux_push_fst_equiv aux_eFGH (replicaLaw r) (x, (x', (i, y)))).trans ?_
  rw [Fintype.sum_unique]
  rfl

omit [Fintype β] [Fintype ι] [DecidableEq α] [DecidableEq β] [DecidableEq ι] in
private theorem aux_factor {r : ι × (α × β) → ℝ} {i : ι} {x x' : α} {y : β}
    (hpos : 0 < replicaLaw r (i, (x, (x', y)))) :
    replicaLaw r (i, (x, (x', y))) * labelColMass r i y = r (i, (x, y)) * r (i, (x', y)) := by
  have hl : labelColMass r i y ≠ 0 := by
    intro h0
    have h1 : replicaLaw r (i, (x, (x', y))) = 0 := by
      simp only [replicaLaw]
      rw [if_pos h0]
    linarith
  simp only [replicaLaw]
  rw [if_neg hl]
  field_simp

/-- The two rows of the replica are conditionally independent given the label and the column:
`I(X; X' | W, Y) = 0`. -/
theorem replicaLaw_condMutualInfo_rows_eq_zero {r : ι × (α × β) → ℝ} (hr : IsPMF r) :
    condMutualInfo (fun a : ι × (α × (α × β)) => a.2.1) (fun a => a.2.2.1)
      (fun a => (a.1, a.2.2.2)) (replicaLaw r) = 0 := by
  refine condMutualInfo_eq_zero_of_factor (replicaLaw_isPMF hr) _ _ _ ?_
  rintro ⟨i, x, x', y⟩ hpos
  show pushforward (fun a : ι × (α × (α × β)) => (a.2.1, a.2.2.1, a.1, a.2.2.2)) (replicaLaw r)
        (x, x', i, y) *
      pushforward (fun a : ι × (α × (α × β)) => (a.1, a.2.2.2)) (replicaLaw r) (i, y) =
    pushforward (fun a : ι × (α × (α × β)) => (a.2.1, a.1, a.2.2.2)) (replicaLaw r) (x, i, y) *
      pushforward (fun a : ι × (α × (α × β)) => (a.2.2.1, a.1, a.2.2.2)) (replicaLaw r)
        (x', i, y)
  rw [aux_push_fgh, aux_push_cond hr, aux_push_fh hr, aux_push_gh hr]
  exact aux_factor hpos

/-- The sharp replica inequality: `I(W; X' | X) + I(X; X' | Y) ≤ I(W; X | Y) + I(W; Y | X)`, the
left side computed under the replica and the right side under `r`. The second term on the left
is the slack of the chain. -/
theorem replica_bound_sharp {r : ι × (α × β) → ℝ} (hr : IsPMF r) :
    condMutualInfo (fun a : ι × (α × (α × β)) => a.1) (fun a => a.2.2.1) (fun a => a.2.1)
        (replicaLaw r)
      + condMutualInfo (fun a : ι × (α × (α × β)) => a.2.1) (fun a => a.2.2.1)
        (fun a => a.2.2.2) (replicaLaw r) ≤
      condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2) r
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1) r := by
  have hR : IsPMF (replicaLaw r) := replicaLaw_isPMF hr
  have hgen := condMutualInfo_add_le_of_condIndep hR (fun a : ι × (α × (α × β)) => a.1)
    (fun a => a.2.1)
    (fun a => a.2.2.1) (fun a => a.2.2.2) (replicaLaw_condMutualInfo_rows_eq_zero hr)
  have p1 : condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2) r =
      condMutualInfo (fun a : ι × (α × (α × β)) => a.1) (fun a => a.2.2.1) (fun a => a.2.2.2)
        (replicaLaw r) := by
    have h := condMutualInfo_pushforward_comp (replicaLaw r)
      (fun a : ι × (α × (α × β)) => (a.1, (a.2.2.1, a.2.2.2)))
      (fun b : ι × (α × β) => b.1) (fun b => b.2.1) (fun b => b.2.2)
    rw [replicaLaw_pushforward_replica hr] at h
    exact h
  have p2 : condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1) r =
      condMutualInfo (fun a : ι × (α × (α × β)) => a.1) (fun a => a.2.2.2) (fun a => a.2.1)
        (replicaLaw r) := by
    have h := condMutualInfo_pushforward_comp (replicaLaw r)
      (fun a : ι × (α × (α × β)) => (a.1, (a.2.1, a.2.2.2)))
      (fun b : ι × (α × β) => b.1) (fun b => b.2.2) (fun b => b.2.1)
    rw [replicaLaw_pushforward_original hr] at h
    exact h
  rw [p1, p2]
  exact hgen

/-- The replica inequality: `I(W; X' | X)` under the replica is at most
`I(W; X | Y) + I(W; Y | X)` under `r`. -/
theorem replica_bound {r : ι × (α × β) → ℝ} (hr : IsPMF r) :
    condMutualInfo (fun a : ι × (α × (α × β)) => a.1) (fun a => a.2.2.1) (fun a => a.2.1)
        (replicaLaw r) ≤
      condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2) r
        + condMutualInfo (fun a : ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1) r := by
  have h := replica_bound_sharp hr
  have hn := condMutualInfo_nonneg (replicaLaw_isPMF hr)
    (fun a : ι × (α × (α × β)) => a.2.1) (fun a => a.2.2.1) (fun a => a.2.2.2)
  linarith

/-- For every latent, `I(X; Y | W) + I(W; X' | X) ≤ L.score`, with `X'` the row replica of
`L.joint`; with an optimal latent the right side is `tau p`. -/
theorem latent_replica_bound {p : α × β → ℝ} (L : Latent p) :
    condMutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) L.joint
      + condMutualInfo (fun a : L.ι × (α × (α × β)) => a.1) (fun a => a.2.2.1) (fun a => a.2.1)
        (replicaLaw L.joint) ≤ L.score := by
  have h := replica_bound L.joint_isPMF
  have hs : L.score =
      condMutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) L.joint
        + condMutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.1) (fun a => a.2.2) L.joint
        + condMutualInfo (fun a : L.ι × (α × β) => a.1) (fun a => a.2.2) (fun a => a.2.1)
          L.joint := rfl
  rw [hs]
  linarith

end

end BinaryRow

end StochasticToDeterministicLatents
