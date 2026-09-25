import StochasticToDeterministicLatents.BinaryRow.Bernoulli
import StochasticToDeterministicLatents.BinaryRow.Posterior

/-!
# Component information as a Bernoulli average

For a law `q` on `Bit × Y`, `Real.log 2 * I(X;Y)` is the column-law average of the Bernoulli
divergence of the row-one posterior from the row-one mass (`log_two_mul_mutualInfo_bitRow`). For
every latent, `I(X;Y|W)` is the prior average of the components' `I(X;Y)`
(`condMutualInfo_eq_sum_prior`). For a contact of a two-contact pair with row parameters `s ≠ t`,
the posterior variance is `κ r (1 - r)` with `κ = st/(s+t)²` and `r` the row-one mass, so the
Ordentlich–Weinberger bound gives `κ · owL r · r (1 - r) ≤ log 2 · I(X;Y)`
(`rowTwoContact_mutualInfo_ge_owL`), and averaging over the labels bounds `log 2 · I(X;Y|W)` from
below (`twoContact_condMutualInfo_ge_owL`).

Information quantities are in bits and `klBer`, `owL` are in nats; each statement carries
`Real.log 2` on its information side.

## Attribution

Original to this repository, on the entropy interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0. The sum over the
fibres of the conditioning variable restates an inline step of the upstream proof that
conditional mutual information is nonnegative.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Binary

/-! ## Helpers -/

/-- One column of the Bernoulli-average identity, as scalar algebra: for cells `a, b ≥ 0` with
`b ≤ r` and `a ≤ 1 - r`, `(a + b) * klBer (b / (a + b)) r` equals
`negMulLog (a + b) - negMulLog a - negMulLog b - b log r - a log (1 - r)`. -/
private theorem aux_col_term {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hbr : b ≤ r) (har : a ≤ 1 - r) :
    (a + b) * klBer (b / (a + b)) r =
      Real.negMulLog (a + b) - Real.negMulLog a - Real.negMulLog b - b * Real.log r
        - a * Real.log (1 - r) := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hc | hc
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0
    subst hb0
    simp
  · have hc0 : a + b ≠ 0 := hc.ne'
    have h1 : 1 - b / (a + b) = a / (a + b) := by
      rw [← div_self hc0, ← sub_div]
      congr 1
      ring
    have hb' : (a + b) * (b / (a + b)) = b := by
      field_simp
    have ha' : (a + b) * (a / (a + b)) = a := by
      field_simp
    have hB : b * Real.log (b / (a + b) / r) =
        b * Real.log b - b * Real.log (a + b) - b * Real.log r := by
      rcases eq_or_ne b 0 with h0 | h0
      · simp [h0]
      · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm h0)
        have hr : r ≠ 0 := (lt_of_lt_of_le hbpos hbr).ne'
        rw [Real.log_div (div_ne_zero h0 hc0) hr, Real.log_div h0 hc0]
        ring
    have hA : a * Real.log (a / (a + b) / (1 - r)) =
        a * Real.log a - a * Real.log (a + b) - a * Real.log (1 - r) := by
      rcases eq_or_ne a 0 with h0 | h0
      · simp [h0]
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
        have hr : 1 - r ≠ 0 := (lt_of_lt_of_le hapos har).ne'
        rw [Real.log_div (div_ne_zero h0 hc0) hr, Real.log_div h0 hc0]
        ring
    unfold klBer
    rw [h1]
    calc
      (a + b) * (b / (a + b) * Real.log (b / (a + b) / r) +
          a / (a + b) * Real.log (a / (a + b) / (1 - r))) =
          ((a + b) * (b / (a + b))) * Real.log (b / (a + b) / r) +
            ((a + b) * (a / (a + b))) * Real.log (a / (a + b) / (1 - r)) := by ring
      _ = b * Real.log (b / (a + b) / r) + a * Real.log (a / (a + b) / (1 - r)) := by
        rw [hb', ha']
      _ = _ := by
        rw [hB, hA]
        simp only [Real.negMulLog]
        ring

/-- Pushing a law on a product forward along the identity pairing returns the law. -/
private theorem aux_pushforward_pair {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (q : A × B → ℝ) :
    pushforward (fun z : A × B => (z.1, z.2)) q = q := by
  funext z
  unfold pushforward stoch_to_det.push
  simp [Finset.sum_filter]

/-- Conditional mutual information as the sum over values of the conditioner of the mutual
information under the unnormalized fibre measures. -/
private theorem aux_condMI_eq_sum_fibers {Ω A B C : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    stoch_to_det.condMI f g h m =
      ∑ c, stoch_to_det.MI f g (fun a => if h a = c then m a else 0) := by
  have htrip : stoch_to_det.Hvar (fun a => (f a, g a, h a)) m =
      stoch_to_det.Hvar (fun a => ((f a, g a), h a)) m := by
    simpa using stoch_to_det.Hvar_equiv hm (fun a => ((f a, g a), h a)) (Equiv.prodAssoc A B C)
  unfold stoch_to_det.condMI
  rw [htrip, stoch_to_det.Hvar_pair_eq_sum_fibers hm f h,
    stoch_to_det.Hvar_pair_eq_sum_fibers hm g h,
    stoch_to_det.Hvar_pair_eq_sum_fibers hm (fun a => (f a, g a)) h]
  simp only [stoch_to_det.MI, stoch_to_det.Hvar]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Mutual information on a pushed-forward measure is mutual information of the composed
variables. -/
private theorem aux_MI_push {Ω Ω' A B : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω'] [Fintype A]
    [DecidableEq A] [Fintype B] [DecidableEq B] (m : Ω → ℝ) (φ : Ω → Ω') (f : Ω' → A)
    (g : Ω' → B) :
    stoch_to_det.MI f g (stoch_to_det.push φ m) =
      stoch_to_det.MI (fun ω => f (φ ω)) (fun ω => g (φ ω)) m := by
  unfold stoch_to_det.MI stoch_to_det.Hvar
  rw [stoch_to_det.push_push, stoch_to_det.push_push, stoch_to_det.push_push]
  rfl

/-- The fibre of a latent's joint law at a label is the scaled component, placed at that
label. -/
private theorem aux_fiber_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {p : α × β → ℝ} (L : Latent p) (v : L.ι) :
    (fun a : L.ι × (α × β) => if a.1 = v then L.joint a else 0) =
      stoch_to_det.push (fun z : α × β => (v, z)) (fun z => L.prior v * L.comp v z) := by
  funext a
  rcases a with ⟨u, z⟩
  unfold stoch_to_det.push
  rw [Finset.sum_filter]
  by_cases h : u = v
  · subst h
    simp [Latent.joint, stoch_to_det.Latent.joint]
  · simp [h, Ne.symm h]

/-- Combining two weighted lower bounds. -/
private theorem aux_combine {κ p0 p1 a0 a1 b0 b1 l m0 m1 : ℝ} (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (h0 : κ * a0 * b0 ≤ l * m0) (h1 : κ * a1 * b1 ≤ l * m1) :
    κ * (p0 * (a0 * b0) + p1 * (a1 * b1)) ≤ l * (p0 * m0) + l * (p1 * m1) := by
  have k0 := mul_le_mul_of_nonneg_left h0 hp0
  have k1 := mul_le_mul_of_nonneg_left h1 hp1
  calc
    κ * (p0 * (a0 * b0) + p1 * (a1 * b1)) = p0 * (κ * a0 * b0) + p1 * (κ * a1 * b1) := by
      ring
    _ ≤ p0 * (l * m0) + p1 * (l * m1) := add_le_add k0 k1
    _ = l * (p0 * m0) + l * (p1 * m1) := by ring

/-! ## Main statements -/

/-- On `Bit × Y`, `log 2 · I(X;Y)` is the column-law average of
`klBer (q(1,y) / colMass q y) (rowMass q 1)`, a zero-mass column contributing zero. -/
theorem log_two_mul_mutualInfo_bitRow {Y : Type} [Fintype Y] [DecidableEq Y]
    {q : Bit × Y → ℝ} (hq : IsPMF q) :
    Real.log 2 * mutualInfo Prod.fst Prod.snd q =
      ∑ y, colMass q y * klBer (q (1, y) / colMass q y) (rowMass q 1) := by
  have hX := log_two_mul_entropyOf hq (Prod.fst : Bit × Y → Bit)
  have hY := log_two_mul_entropyOf hq (Prod.snd : Bit × Y → Y)
  have hXY := log_two_mul_entropyOf hq (fun z : Bit × Y => (z.1, z.2))
  rw [pushforward_fst_eq_rowMass] at hX
  rw [pushforward_snd_eq_colMass] at hY
  rw [aux_pushforward_pair] at hXY
  have hMI : mutualInfo Prod.fst Prod.snd q =
      entropyOf Prod.fst q + entropyOf Prod.snd q - entropyOf (fun z : Bit × Y => (z.1, z.2)) q :=
    rfl
  have hr0 : rowMass q 0 = 1 - rowMass q 1 := by
    have h := (rowMass_isPMF hq).total
    simp only [stoch_to_det.mass, Fin.sum_univ_two] at h
    linarith
  have hle1 : ∀ y, q (1, y) ≤ rowMass q 1 := fun y =>
    Finset.single_le_sum (f := fun y => q (1, y)) (fun y _ => hq.nonneg (1, y))
      (Finset.mem_univ y)
  have hle0 : ∀ y, q (0, y) ≤ 1 - rowMass q 1 := fun y => by
    rw [← hr0]
    exact Finset.single_le_sum (f := fun y => q (0, y)) (fun y _ => hq.nonneg (0, y))
      (Finset.mem_univ y)
  have hterm : ∀ y, colMass q y * klBer (q (1, y) / colMass q y) (rowMass q 1) =
      Real.negMulLog (colMass q y) - Real.negMulLog (q (0, y)) - Real.negMulLog (q (1, y))
        - q (1, y) * Real.log (rowMass q 1) - q (0, y) * Real.log (1 - rowMass q 1) :=
    fun y => aux_col_term (a := q (0, y)) (b := q (1, y)) (r := rowMass q 1)
      (hq.nonneg _) (hq.nonneg _) (hle1 y) (hle0 y)
  have hs1 : ∑ y, q (1, y) = rowMass q 1 := rfl
  have hs0 : ∑ y, q (0, y) = 1 - rowMass q 1 := hr0
  rw [hMI, mul_sub, mul_add, hX, hY, hXY, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [hr0, Finset.sum_congr rfl fun y _ => hterm y]
  simp only [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hs1, hs0,
    show Real.negMulLog (rowMass q 1) = -rowMass q 1 * Real.log (rowMass q 1) from rfl,
    show Real.negMulLog (1 - rowMass q 1) = -(1 - rowMass q 1) * Real.log (1 - rowMass q 1)
      from rfl]
  ring

/-- For every latent on any finite `α × β`, `I(X;Y|W)` under the joint law is the prior average
of the components' mutual information. -/
theorem condMutualInfo_eq_sum_prior {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] {p : α × β → ℝ} (L : Latent p) :
    condMutualInfo (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1) L.joint =
      ∑ v, L.prior v * mutualInfo Prod.fst Prod.snd (L.comp v) := by
  have hJ : IsPMF L.joint := L.joint_isPMF
  show stoch_to_det.condMI (fun a : L.ι × (α × β) => a.2.1) (fun a => a.2.2) (fun a => a.1)
      L.joint = ∑ v, L.prior v * stoch_to_det.MI Prod.fst Prod.snd (L.comp v)
  rw [aux_condMI_eq_sum_fibers hJ]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [aux_fiber_eq L v, aux_MI_push]
  exact stoch_to_det.MI_smul (L.comp_isPMF v).isFinMeas Prod.fst Prod.snd
    (L.prior_isPMF.nonneg v)

/-- For a contact `q` of a feasible kernel and a second contact of different row parameter,
`st/(s+t)² · owL m · m (1 - m) ≤ log 2 · I_q(X;Y)` with `m = rowMass q 1`. -/
theorem rowTwoContact_mutualInfo_ge_owL {Y : Type} [Fintype Y] [DecidableEq Y]
    {w q r : Bit × Y → ℝ} (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) (hr : IsContact (univ : Finset (Bit × Y)) w r)
    {s t : ℝ} (hs : RowCubeParam q s) (ht : RowCubeParam r t) (hst : s ≠ t) :
    s * t / (s + t) ^ 2 * owL (rowMass q 1) * (rowMass q 1 * (1 - rowMass q 1)) ≤
      Real.log 2 * mutualInfo Prod.fst Prod.snd q := by
  have hqP : IsPMF q := hq.1
  have hcpos : ∀ y, 0 < colMass q y := rowContact_colMass_pos hw hq
  have hs0 : 0 < s := hs.1
  have hr0 : 0 < rowMass q 1 := by
    rw [hs.2.2]
    positivity
  have hr1 : rowMass q 1 < 1 := by
    rw [hs.2.2, div_lt_one (by positivity)]
    linarith
  have hR0 : ∀ y, 0 ≤ q (1, y) / colMass q y := fun y =>
    div_nonneg (hqP.nonneg _) (hcpos y).le
  have hR1 : ∀ y, q (1, y) / colMass q y ≤ 1 := fun y => by
    rw [div_le_one (hcpos y)]
    unfold colMass
    linarith [hqP.nonneg (0, y)]
  have hsum1 : ∑ y, colMass q y = 1 := (colMass_isPMF hqP).total
  have hmean := rowContact_posterior_mean hw hq
  have hvar := rowTwoContact_variance hw hq hr (ne_of_rowCubeParam_ne hs ht hst) hs ht
  have hpt : ∀ y, colMass q y * (owL (rowMass q 1) * (q (1, y) / colMass q y - rowMass q 1) ^ 2)
      = owL (rowMass q 1) * (colMass q y * (q (1, y) / colMass q y) ^ 2)
        - 2 * owL (rowMass q 1) * rowMass q 1 * (colMass q y * (q (1, y) / colMass q y))
        + owL (rowMass q 1) * rowMass q 1 ^ 2 * colMass q y := fun y => by ring
  have hexp : ∑ y, colMass q y * (owL (rowMass q 1) * (q (1, y) / colMass q y - rowMass q 1) ^ 2)
      = owL (rowMass q 1) *
        (∑ y, colMass q y * (q (1, y) / colMass q y) ^ 2 - rowMass q 1 ^ 2) := by
    rw [Finset.sum_congr rfl fun y _ => hpt y, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hmean, hsum1]
    ring
  rw [log_two_mul_mutualInfo_bitRow hqP]
  calc
    s * t / (s + t) ^ 2 * owL (rowMass q 1) * (rowMass q 1 * (1 - rowMass q 1)) =
        owL (rowMass q 1) *
          (∑ y, colMass q y * (q (1, y) / colMass q y) ^ 2 - rowMass q 1 ^ 2) := by
      rw [hvar]
      ring
    _ = ∑ y, colMass q y *
          (owL (rowMass q 1) * (q (1, y) / colMass q y - rowMass q 1) ^ 2) := hexp.symm
    _ ≤ ∑ y, colMass q y * klBer (q (1, y) / colMass q y) (rowMass q 1) :=
      Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (klBer_ge_owL_mul_sq (hR0 y) (hR1 y) hr0 hr1) (hcpos y).le

/-- For a `Bit`-labelled latent whose components are contacts of one feasible kernel with row
parameters `s ≠ t`, `log 2 · I(X;Y|W)` is at least `st/(s+t)²` times the prior average of
`owL m · m (1 - m)` over the components' row-one masses `m`. -/
theorem twoContact_condMutualInfo_ge_owL {Y : Type} [Fintype Y] [DecidableEq Y]
    {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit) {w : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (h0 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s ≠ t) :
    s * t / (s + t) ^ 2 * ∑ i : Bit, V.prior (e.symm i) *
        (owL (rowMass (V.comp (e.symm i)) 1) *
          (rowMass (V.comp (e.symm i)) 1 * (1 - rowMass (V.comp (e.symm i)) 1))) ≤
      Real.log 2 *
        condMutualInfo (fun a : V.ι × (Bit × Y) => a.2.1) (fun a => a.2.2) (fun a => a.1)
          V.joint := by
  have hp0 := V.prior_isPMF.nonneg (e.symm 0)
  have hp1 := V.prior_isPMF.nonneg (e.symm 1)
  have k0 := rowTwoContact_mutualInfo_ge_owL hw h0 h1 hs ht hst
  have k1 := rowTwoContact_mutualInfo_ge_owL hw h1 h0 ht hs (Ne.symm hst)
  have hk : t * s / (t + s) ^ 2 = s * t / (s + t) ^ 2 := by
    rw [mul_comm t s, add_comm t s]
  rw [hk] at k1
  rw [condMutualInfo_eq_sum_prior V]
  simp only [Fin.sum_univ_two]
  rw [Finset.mul_sum, ← Equiv.sum_comp e.symm]
  simp only [Fin.sum_univ_two]
  exact aux_combine hp0 hp1 k0 k1

end

end BinaryRow

end StochasticToDeterministicLatents
