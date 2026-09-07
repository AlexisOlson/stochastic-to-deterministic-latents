import StochasticToDeterministicLatents.Binary.FactorTwo.Defs
import StochasticToDeterministicLatents.Bridge

/-!
# The contact certificate and the optimum at a contact pair

The stochastic optimum is bounded above by exhibiting a latent and below by
exhibiting an affine majorant of `Phi`.  This module supplies both at the
diagonal contact pair of a binary law.

The majorant is the tangent certificate of `Phi` at a law `q`,

`tangentCert q z = -3 lg (q z) + 2 lg (mX q z.1) + 2 lg (mY q z.2)`,

whose value against `q` itself is `Phi q`.  That it majorizes `Phi` everywhere
is an analytic condition; it is reduced here to `NormBound` through a dual
kernel and the feasibility interface of `Bridge`.  `PositivityGate`, the sign
of four explicit rational expressions in the cells, is stated here and shown to
imply `NormBound` downstream.

Nothing in this module states the upstream duality vocabulary.  The majorant
property is carried as `Majorizes`, an explicit inequality over probability
laws, and the one duality fact consumed is
`phi_le_logCertificate_of_feasible`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

/-! ## Affine majorants of `Phi` -/

/-- `c` majorizes `Phi`: its pairing with every probability law is at least
`Phi` there.  This is the property the lower bound on `tau` consumes; it is
stated explicitly so that no duality vocabulary reaches the public tree. -/
def Majorizes (c : RealTable) : Prop :=
  ∀ q : RealTable, IsPMF q → Phi q ≤ ∑ z, c z * q z

/-- Weak duality, proved from the attained optimizer and the score
decomposition alone.  An affine majorant of `Phi` bounds `tau` below. -/
theorem tau_ge_of_majorizes {p : RealTable} (hp : IsPMF p) {c : RealTable}
    (hc : Majorizes c) : Psi p - ∑ z, c z * p z ≤ tau p := by
  obtain ⟨L, hL⟩ := exists_optimalLatent hp
  have hscore := latent_score_eq hp L
  have hprior : ∀ v, 0 ≤ L.prior v := fun v => L.prior_isPMF.nonneg v
  have hstep : ∀ v, L.prior v * Phi (L.comp v)
      ≤ L.prior v * ∑ z, c z * L.comp v z := fun v =>
    mul_le_mul_of_nonneg_left (hc (L.comp v) (L.comp_isPMF v)) (hprior v)
  have hpull : ∀ v, L.prior v * (∑ z, c z * L.comp v z)
      = ∑ z, c z * (L.prior v * L.comp v z) := by
    intro v
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hswap : (∑ v, L.prior v * ∑ z, c z * L.comp v z) = ∑ z, c z * p z := by
    rw [Finset.sum_congr rfl fun v _ => hpull v, Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => by
      rw [← Finset.mul_sum, L.mixture z]
  have hbound : (∑ v, L.prior v * Phi (L.comp v)) ≤ ∑ z, c z * p z := by
    calc (∑ v, L.prior v * Phi (L.comp v))
        ≤ ∑ v, L.prior v * ∑ z, c z * L.comp v z := Finset.sum_le_sum fun v _ => hstep v
      _ = ∑ z, c z * p z := hswap
  rw [hL] at hscore
  linarith

/-! ## The tangent certificate -/

/-- The tangent plane of `Phi` at `q`, in coordinates:
`c z = -3 lg (q z) + 2 lg (mX q z.1) + 2 lg (mY q z.2)`. -/
noncomputable def tangentCert (q : RealTable) : RealTable := fun z =>
  -3 * Real.logb 2 (q z) + 2 * Real.logb 2 (stoch_to_det.mX q z.1)
    + 2 * Real.logb 2 (stoch_to_det.mY q z.2)

private theorem sum_mul_logb_self {γ : Type*} [Fintype γ] {m : γ → ℝ} (hm : IsPMF m) :
    (∑ a, m a * Real.logb 2 (m a)) = -stoch_to_det.H m := by
  rw [stoch_to_det.H, hm.total, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : m a = 0
  · simp [ha]
  · rw [stoch_to_det.lg_eq_log_div, Real.logb, Real.log_div one_ne_zero ha]
    simp
    ring

/-- The tangent certificate pairs with its own base point to give `Phi`. -/
theorem tangentCert_self (q : RealTable) (hq : IsPMF q) :
    (∑ z, tangentCert q z * q z) = Phi q := by
  have hqX : IsPMF (stoch_to_det.mX q) := stoch_to_det.isPMF_push hq
  have hqY : IsPMF (stoch_to_det.mY q) := stoch_to_det.isPMF_push hq
  have hqsum : (∑ z, q z * Real.logb 2 (q z)) = -stoch_to_det.H q := sum_mul_logb_self hq
  have hxsum : (∑ z, q z * Real.logb 2 (stoch_to_det.mX q z.1))
      = -stoch_to_det.H (stoch_to_det.mX q) := by
    rw [← stoch_to_det.sum_push_mul Prod.fst q fun x => Real.logb 2 (stoch_to_det.mX q x)]
    exact sum_mul_logb_self hqX
  have hysum : (∑ z, q z * Real.logb 2 (stoch_to_det.mY q z.2))
      = -stoch_to_det.H (stoch_to_det.mY q) := by
    rw [← stoch_to_det.sum_push_mul Prod.snd q fun y => Real.logb 2 (stoch_to_det.mY q y)]
    exact sum_mul_logb_self hqY
  unfold tangentCert
  rw [show Phi q = 3 * stoch_to_det.H q - 2 * stoch_to_det.H (stoch_to_det.mX q)
      - 2 * stoch_to_det.H (stoch_to_det.mY q) from rfl]
  calc
    (∑ z, (-3 * Real.logb 2 (q z) + 2 * Real.logb 2 (stoch_to_det.mX q z.1)
        + 2 * Real.logb 2 (stoch_to_det.mY q z.2)) * q z)
        = -3 * (∑ z, q z * Real.logb 2 (q z))
          + 2 * (∑ z, q z * Real.logb 2 (stoch_to_det.mX q z.1))
          + 2 * (∑ z, q z * Real.logb 2 (stoch_to_det.mY q z.2)) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun z _ => by ring
    _ = 3 * stoch_to_det.H q - 2 * stoch_to_det.H (stoch_to_det.mX q)
          - 2 * stoch_to_det.H (stoch_to_det.mY q) := by
      rw [hqsum, hxsum, hysum]; ring

/-! ## Cell formulas for the two marginals

The row and column marginals of a binary law are sums of two cells.  These are
stated here because every later module in the lane needs them.
-/

theorem marginalX_zero (q : RealTable) :
    stoch_to_det.mX q 0 = q (0, 0) + q (0, 1) := by
  unfold stoch_to_det.mX stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem marginalX_one (q : RealTable) :
    stoch_to_det.mX q 1 = q (1, 0) + q (1, 1) := by
  unfold stoch_to_det.mX stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem marginalY_zero (q : RealTable) :
    stoch_to_det.mY q 0 = q (0, 0) + q (1, 0) := by
  unfold stoch_to_det.mY stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem marginalY_one (q : RealTable) :
    stoch_to_det.mY q 1 = q (0, 1) + q (1, 1) := by
  unfold stoch_to_det.mY stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

/-- Every row marginal of a fully supported binary law is positive. -/
theorem marginalX_pos {q : RealTable} (hq : FullSupport q) :
    ∀ x, 0 < stoch_to_det.mX q x := by
  intro x
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> simp
  rcases hx with rfl | rfl
  · rw [marginalX_zero]; exact add_pos (hq _) (hq _)
  · rw [marginalX_one]; exact add_pos (hq _) (hq _)

/-- Every column marginal of a fully supported binary law is positive. -/
theorem marginalY_pos {q : RealTable} (hq : FullSupport q) :
    ∀ y, 0 < stoch_to_det.mY q y := by
  intro y
  have hy : y = 0 ∨ y = 1 := by fin_cases y <;> simp
  rcases hy with rfl | rfl
  · rw [marginalY_zero]; exact add_pos (hq _) (hq _)
  · rw [marginalY_one]; exact add_pos (hq _) (hq _)

/-! ## The dual kernel and the positivity gate -/

/-- The dual kernel whose feasibility is equivalent to the tangent certificate
majorizing `Phi`. -/
private noncomputable def tangentKernel (q : RealTable) : RealTable := fun z =>
  q z / (stoch_to_det.mX q z.1 ^ ((2 : ℝ) / 3) * stoch_to_det.mY q z.2 ^ ((2 : ℝ) / 3))

private theorem tangentKernel_pos {q : RealTable} (hq : FullSupport q) :
    ∀ z, 0 < tangentKernel q z := fun z =>
  div_pos (hq z) (mul_pos (Real.rpow_pos_of_pos (marginalX_pos hq z.1) _)
    (Real.rpow_pos_of_pos (marginalY_pos hq z.2) _))

private theorem tangentCert_eq_logKernel {q : RealTable} (hq : FullSupport q) :
    tangentCert q = fun z => -3 * Real.logb 2 (tangentKernel q z) := by
  funext z
  have hx := marginalX_pos hq z.1
  have hy := marginalY_pos hq z.2
  unfold tangentCert tangentKernel
  rw [Real.logb_div (hq z).ne' (mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hx _))
    (ne_of_gt (Real.rpow_pos_of_pos hy _)))]
  rw [Real.logb_mul (ne_of_gt (Real.rpow_pos_of_pos hx _))
    (ne_of_gt (Real.rpow_pos_of_pos hy _))]
  rw [Real.logb_rpow_eq_mul_logb_of_pos hx, Real.logb_rpow_eq_mul_logb_of_pos hy]
  ring

/-- A feasible tangent kernel makes the tangent certificate a majorant. -/
private theorem majorizes_tangentCert_of_feasible {q : RealTable} (hq : FullSupport q)
    (hfeas : Feasible Finset.univ (tangentKernel q)) : Majorizes (tangentCert q) := by
  intro r hr
  have hsupp : stoch_to_det.Supported Finset.univ r := by
    intro z hz; simp at hz
  have h := phi_le_logCertificate_of_feasible
    (fun z _ => tangentKernel_pos hq z) hfeas hr hsupp
  rw [tangentCert_eq_logKernel hq]
  simpa using h

/-! ## Reduction of feasibility to a rational positivity gate

Feasibility of the tangent kernel is a statement about all pairs of row and
column laws. `NormBound` is that statement written out, and `PositivityGate`
is the sign condition on four explicit rational expressions in the cells that
implies it.  The implication itself is proved downstream.
-/

/-- Feasibility of the tangent kernel, written without the dual-kernel
vocabulary. -/
def NormBound (q : RealTable) : Prop :=
  ∀ u v : Bit → ℝ, IsPMF u → IsPMF v →
    ∑ z : Cell, q z * (u z.1 / stoch_to_det.mX q z.1) ^ ((2 : ℝ) / 3) *
      (v z.2 / stoch_to_det.mY q z.2) ^ ((2 : ℝ) / 3) ≤ 1

private theorem feasible_tangentKernel_iff_normBound {q : RealTable} (hq : FullSupport q) :
    Feasible Finset.univ (tangentKernel q) ↔ NormBound q := by
  have hterm : ∀ (u v : Bit → ℝ), IsPMF u → IsPMF v → ∀ z : Cell,
      tangentKernel q z * u z.1 ^ ((2 : ℝ) / 3) * v z.2 ^ ((2 : ℝ) / 3) =
        q z * (u z.1 / stoch_to_det.mX q z.1) ^ ((2 : ℝ) / 3) *
          (v z.2 / stoch_to_det.mY q z.2) ^ ((2 : ℝ) / 3) := by
    intro u v hu hv z
    rw [Real.div_rpow (hu.nonneg _) (le_of_lt (marginalX_pos hq _)),
      Real.div_rpow (hv.nonneg _) (le_of_lt (marginalY_pos hq _))]
    unfold tangentKernel
    field_simp
  constructor
  · intro h u v hu hv
    simpa [Lambda, stoch_to_det.Lambda, hterm u v hu hv] using h.2 u v hu hv
  · intro h
    refine ⟨fun z _ => tangentKernel_pos hq z, ?_⟩
    intro u v hu hv
    simpa [Lambda, stoch_to_det.Lambda, hterm u v hu hv] using h u v hu hv

/-! ### The rational gate

The gate expressions have no consumer in this module: the reduction of the gate
to `NormBound` and the verification of the gate on a chart are proved in two
modules that both import this one and neither of which imports the other, so
this is where they are shared.
-/

/-- First gate expression. -/
noncomputable def gateA (q : RealTable) : ℝ :=
  stoch_to_det.mY q 0 ^ 2 - q (0, 0) ^ 3 / stoch_to_det.mX q 0 ^ 2
    - q (1, 0) ^ 3 / stoch_to_det.mX q 1 ^ 2

/-- Second gate expression. -/
noncomputable def gateE (q : RealTable) : ℝ :=
  stoch_to_det.mY q 1 ^ 2 - q (0, 1) ^ 3 / stoch_to_det.mX q 0 ^ 2
    - q (1, 1) ^ 3 / stoch_to_det.mX q 1 ^ 2

/-- The determinant term of the gate. -/
noncomputable def gateV (q : RealTable) : ℝ :=
  determinant q ^ 2 / (stoch_to_det.mX q 0 * stoch_to_det.mX q 1)

/-- The column-marginal product of the gate. -/
noncomputable def gateM (q : RealTable) : ℝ :=
  stoch_to_det.mY q 0 * stoch_to_det.mY q 1

/-- The positivity gate: the rational sign condition from which the norm bound,
and hence the majorant property of the tangent certificate at `q`, follows. -/
def PositivityGate (q : RealTable) : Prop :=
  0 ≤ gateA q ∧ 0 ≤ gateE q ∧ gateV q ^ 3 ≤ gateA q * gateE q * gateM q

/-- Under the norm bound, the tangent certificate at `q` majorizes `Phi`.  The
gate is reduced to the norm bound in a later module; nothing here assumes that
reduction. -/
theorem majorizes_tangentCert_of_normBound {q : RealTable} (hq : FullSupport q)
    (hN : NormBound q) : Majorizes (tangentCert q) :=
  majorizes_tangentCert_of_feasible hq ((feasible_tangentKernel_iff_normBound hq).2 hN)

/-! ## The optimum at a contact pair

`tau` is squeezed between a latent built from the contact pair and the majorant
supplied by the tangent certificate.
-/

/-- The one-point latent, whose score is the constant-code value
`Psi p - Phi p`. -/
private noncomputable def trivialLatent {p : RealTable} (hp : IsPMF p) : Latent p where
  ι := Unit
  fin := inferInstance
  dec := inferInstance
  prior _ := 1
  comp _ := p
  prior_isPMF := ⟨fun _ => zero_le_one, by simp [stoch_to_det.mass]⟩
  comp_isPMF := fun _ => hp
  mixture := by intro z; simp

/-- The constant competitor bounds `tau` above by `Psi p - Phi p`, which is the
mutual information of `p`. -/
theorem tau_le_psi_sub_phi {p : RealTable} (hp : IsPMF p) : tau p ≤ Psi p - Phi p := by
  have h := tau_le_score (trivialLatent hp)
  have hs := latent_score_eq hp (trivialLatent hp)
  have hsum : (∑ v, (trivialLatent hp).prior v * Phi ((trivialLatent hp).comp v))
      = Phi p := by
    show (∑ _v : Unit, (1 : ℝ) * Phi p) = Phi p
    simp
  rw [hsum] at hs
  rw [hs] at h
  exact h

/-- The two-point latent supported on the contact pair. -/
private noncomputable def contactLatent {p : RealTable} {u : ℝ} (hp : IsPMF p)
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u) : Latent p where
  ι := Fin 2
  fin := inferInstance
  dec := inferInstance
  prior i := if i = 0 then mixingWeight p u else 1 - mixingWeight p u
  comp i := if i = 0 then contactAt p u else oppositeContactAt p u
  prior_isPMF := by
    refine ⟨fun i => ?_, ?_⟩
    · have hmix := contact_mixture hp hpos hu hnc
      fin_cases i <;> simp [hmix.2.2.1.le, sub_nonneg.mpr hmix.2.2.2.1.le]
    · simp [stoch_to_det.mass, Fin.sum_univ_two]
  comp_isPMF := by
    intro i
    have hmix := contact_mixture hp hpos hu hnc
    fin_cases i <;> simp [hmix.1, hmix.2.1]
  mixture := by
    intro z
    simpa [Fin.sum_univ_two] using (contact_mixture hp hpos hu hnc).2.2.2.2 z

/-- The upper bound: when the two contacts carry the same `Phi`, the contact
pair's latent scores `Psi p - Phi (contactAt p u)`. -/
theorem tau_le_contact {p : RealTable} {u : ℝ} (hp : IsPMF p)
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u)
    (hswap : Phi (contactAt p u) = Phi (oppositeContactAt p u)) :
    tau p ≤ Psi p - Phi (contactAt p u) := by
  have h := tau_le_score (contactLatent hp hpos hu hnc)
  have hs := latent_score_eq hp (contactLatent hp hpos hu hnc)
  have hsum : (∑ v, (contactLatent hp hpos hu hnc).prior v * Phi ((contactLatent hp hpos hu hnc).comp v))
      = Phi (contactAt p u) := by
    show (∑ v : Fin 2, (if v = 0 then mixingWeight p u else 1 - mixingWeight p u)
        * Phi (if v = 0 then contactAt p u else oppositeContactAt p u))
        = Phi (contactAt p u)
    rw [Fin.sum_univ_two]
    show mixingWeight p u * Phi (contactAt p u)
        + (1 - mixingWeight p u) * Phi (oppositeContactAt p u) = Phi (contactAt p u)
    rw [← hswap]
    ring
  rw [hsum] at hs
  rw [hs] at h
  exact h

end StochasticToDeterministicLatents.Binary
