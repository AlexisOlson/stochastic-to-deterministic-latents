import StochasticToDeterministicLatents.BinaryRow.ModerateBands
import StochasticToDeterministicLatents.BinaryRow.LargeSeparation
import StochasticToDeterministicLatents.BinaryRow.Optimizer
import StochasticToDeterministicLatents.BinaryRow.Purification
import StochasticToDeterministicLatents.SparseLimit

/-!
# The binary-row factor 27/4

For every probability law `p` on `Bit × Y` or on `Y × Bit`, with `Y` any finite type,
`T p ≤ 27/4 * tau p` (`T_le_twentySevenQuarters_mul_tau`, `T_le_twentySevenQuarters_mul_tau_col`).
On full support over `Bit × Y`, one of three codes meets the bound: the constant code, the row
code, or a purified code of a `tau`-optimal latent with positive weights and distinct
components, each relabelled injectively into the canonical code alphabet
(`exists_rowWitnessCode`, with `IsRowCode`, `IsOptimalPurifiedCode` and `IsRowWitnessCode`). An
injective relabelling keeps the score (`detScore_comp_injective`).
All information quantities are in bits; the constant is unit-free.

`T_le_mul_tau_of_forall_fullSupport` reduces the bound to full support, where the code clause
gives it through `T_le_detScore`. There `rowOptimizer_dichotomy` gives either
`tau p = I(X;Y)`, the score of the constant code (`detScore_constantCode_eq`), or an optimal
`Bit`-labelled latent `W` with positive weights whose two components are distinct contacts with
row parameters `s < t`, relabelled if needed. For `t/s ≤ 16` the constant code scores `I(X;Y)`
and the row code scores `H(X | Y)`, and the smaller is at most `27/4 · score`
(`twoContact_min_le_twentySevenQuarters`). For `t/s ≥ 16` a purified code of `W` scores at most
`score + 3 H(W | X, Y) ≤ score + 3 H(W | X) ≤ (1148/173) · score` (`IsPurifiedCode.score_le`,
`condEntropy_label_le`, `twoContact_condEntropy_label_le_score`). The column orientation
follows from `T_swap` and `tau_swap`.

The inequality on `T` holds for every law, zero cells included. The code clause is stated only
for full support over `Bit × Y`; it names no code for laws with a zero cell or for the column
orientation, does not say which of the three codes is used, and does not claim the optimal
latent is unique. The constant is not claimed to be least, and nothing here bounds laws whose
alphabets are both larger than two.

## Attribution

Original to this repository, on the latent interface of the upstream ancestor
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Binary

/-! ## Codes from labellings -/

section Recoding

variable {Ω A B C : Type*} [Fintype Ω]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- Entropy is unchanged when the values of a variable are recoded by an injection. -/
private theorem aux_Hvar_comp_injective {m : Ω → ℝ} (hm : IsPMF m) (F : Ω → A) (φ : A → B)
    (hφ : Function.Injective φ) :
    stoch_to_det.Hvar (fun ω => φ (F ω)) m = stoch_to_det.Hvar F m := by
  obtain ⟨ω0⟩ := nonempty_of_isPMF hm
  have : Nonempty A := ⟨F ω0⟩
  exact stoch_to_det.Hvar_eq_of_leftInverse hm F φ (Function.invFun φ)
    (Function.leftInverse_invFun hφ)

/-- Recoding the conditioning variable by an injection preserves conditional mutual
information. -/
private theorem aux_condMutualInfo_injective_right {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A)
    (g : Ω → B)
    (h : Ω → C) {D : Type*} [Fintype D] [DecidableEq D] (e : C → D)
    (he : Function.Injective e) :
    condMutualInfo f g (fun ω => e (h ω)) m = condMutualInfo f g h m := by
  have h1 : entropyOf (fun ω => (f ω, e (h ω))) m = entropyOf (fun ω => (f ω, h ω)) m :=
    aux_Hvar_comp_injective hm (fun ω => (f ω, h ω)) (Prod.map id e)
      (Function.injective_id.prodMap he)
  have h2 : entropyOf (fun ω => (g ω, e (h ω))) m = entropyOf (fun ω => (g ω, h ω)) m :=
    aux_Hvar_comp_injective hm (fun ω => (g ω, h ω)) (Prod.map id e)
      (Function.injective_id.prodMap he)
  have h3 : entropyOf (fun ω => (f ω, g ω, e (h ω))) m =
      entropyOf (fun ω => (f ω, g ω, h ω)) m :=
    aux_Hvar_comp_injective hm (fun ω => (f ω, g ω, h ω)) (Prod.map id (Prod.map id e))
      (Function.injective_id.prodMap (Function.injective_id.prodMap he))
  have h4 : entropyOf (fun ω => e (h ω)) m = entropyOf h m :=
    aux_Hvar_comp_injective hm h e he
  simp only [entropyOf] at h1 h2 h3 h4
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [h1, h2, h3, h4]

/-- Recoding the conditioned variable by an injection preserves conditional entropy. -/
private theorem aux_condEntropy_injective_left {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : Ω → B)
    {D : Type*} [Fintype D] [DecidableEq D] (e : A → D) (he : Function.Injective e) :
    condEntropy (fun ω => e (f ω)) g m = condEntropy f g m := by
  have h1 : entropyOf (fun ω => (e (f ω), g ω)) m = entropyOf (fun ω => (f ω, g ω)) m :=
    aux_Hvar_comp_injective hm (fun ω => (f ω, g ω)) (Prod.map e id)
      (he.prodMap Function.injective_id)
  simp only [entropyOf] at h1
  simp only [condEntropy, stoch_to_det.condH]
  rw [h1]

end Recoding

/-- The score of a labelling `f` into any finite type, recoded by an injection into the
canonical code alphabet, is `I(X;Y | f) + H(f | X) + H(f | Y)`: the recoding does not change
the score. -/
theorem detScore_comp_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] {p : α × β → ℝ} (hp : IsPMF p) {γ : Type*} [Fintype γ] [DecidableEq γ]
    (f : α × β → γ) (e : γ → Fin (Fintype.card (α × β))) (he : Function.Injective e) :
    detScore p (fun z => e (f z)) =
      condMutualInfo Prod.fst Prod.snd f p + condEntropy f Prod.fst p
        + condEntropy f Prod.snd p := by
  unfold detScore
  rw [aux_condMutualInfo_injective_right hp Prod.fst Prod.snd f e he,
    aux_condEntropy_injective_left hp f Prod.fst e he,
    aux_condEntropy_injective_left hp f Prod.snd e he]

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-! ## The witness codes -/

/-- The row code `g(x, y) = x`, relabelled by an injection of `Bit` into the canonical code
alphabet: `g` has the classes of `X`. -/
def IsRowCode (g : Code Bit Y) : Prop :=
  ∃ e : Bit → Fin (Fintype.card (Bit × Y)), Function.Injective e ∧ ∀ z, g z = e z.1

/-- A purified code of some latent of `p` whose score is `tau p`, whose weights are positive
and whose components are distinct, relabelled by an injection of its labels into the
canonical code alphabet. -/
def IsOptimalPurifiedCode (p : Bit × Y → ℝ) (g : Code Bit Y) : Prop :=
  ∃ (V : Latent p) (f : Bit × Y → V.ι) (e : V.ι → Fin (Fintype.card (Bit × Y))),
    V.score = tau p ∧ (∀ v, 0 < V.prior v) ∧ Function.Injective V.comp ∧
      IsPurifiedCode V f ∧ Function.Injective e ∧ ∀ z, g z = e (f z)

/-- The three codes named on full support: the constant code, the row code, or a purified
code of a `tau`-optimal latent with positive weights and distinct components. -/
def IsRowWitnessCode (p : Bit × Y → ℝ) (g : Code Bit Y) : Prop :=
  g = StochasticToDeterministicLatents.constantCode ∨ IsRowCode g ∨ IsOptimalPurifiedCode p g

omit [DecidableEq Y] in
/-- `Bit` embeds in the canonical code alphabet of `Bit × Y` when `Y` is nonempty. -/
private theorem aux_exists_bit_injection [Nonempty Y] :
    ∃ e : Bit → Fin (Fintype.card (Bit × Y)), Function.Injective e := by
  have h : Fintype.card Bit ≤ Fintype.card (Fin (Fintype.card (Bit × Y))) :=
    calc
      Fintype.card Bit ≤ Fintype.card Bit * Fintype.card Y :=
        Nat.le_mul_of_pos_right _ (Fintype.card_pos (α := Y))
      _ = Fintype.card (Bit × Y) := (Fintype.card_prod Bit Y).symm
      _ = Fintype.card (Fin (Fintype.card (Bit × Y))) := (Fintype.card_fin _).symm
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le h
  exact ⟨φ, φ.injective⟩

/-- The row code `g = e(X)` scores `H(X | Y)`. -/
private theorem aux_detScore_row {p : Bit × Y → ℝ} (hp : IsPMF p)
    (e : Bit → Fin (Fintype.card (Bit × Y))) (he : Function.Injective e) :
    detScore p (fun z => e z.1) = condEntropy Prod.fst Prod.snd p := by
  have h := detScore_comp_injective hp (Prod.fst : Bit × Y → Bit) e he
  have h1 : condMutualInfo (Prod.fst : Bit × Y → Bit) Prod.snd Prod.fst p = 0 :=
    condMutualInfo_given_self_eq_zero hp _ _
  have h2 : condEntropy (Prod.fst : Bit × Y → Bit) Prod.fst p = 0 :=
    condEntropy_function_eq_zero hp Prod.fst id
  rw [h1, h2, zero_add, zero_add] at h
  exact h

omit [DecidableEq Y] in
/-- A latent labelled by `Bit` whose two components differ has distinct components. -/
private theorem aux_comp_injective_of_ne {p : Bit × Y → ℝ} (V : Latent p) (e : V.ι ≃ Bit)
    (hne : V.comp (e.symm 0) ≠ V.comp (e.symm 1)) : Function.Injective V.comp := by
  intro u v huv
  by_contra huv'
  apply hne
  have key : ∀ a b : Bit, a ≠ b → V.comp (e.symm a) = V.comp (e.symm b) →
      V.comp (e.symm 0) = V.comp (e.symm 1) := by
    intro a b hab h
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact h
    · exact h.symm
    · exact absurd rfl hab
  refine key (e u) (e v) (e.injective.ne huv') ?_
  rw [e.symm_apply_apply, e.symm_apply_apply]
  exact huv

/-- Scalar step for large separation: `D ≤ S + 3 H₁`, `H₁ ≤ H₂`, `(173/325) H₂ ≤ S` and
`0 ≤ S` give `D ≤ (27/4) S`, since `1 + 3 · 325/173 = 1148/173 ≤ 27/4`. -/
private theorem aux_scalar_large {D S H₁ H₂ : ℝ} (hD : D ≤ S + 3 * H₁) (hc : H₁ ≤ H₂)
    (hl : 173 / 325 * H₂ ≤ S) (hS : 0 ≤ S) : D ≤ 27 / 4 * S := by
  linarith

/-- The two-contact case with row parameters `s < t`, for an optimal latent: a witness code. -/
private theorem aux_exists_of_twoContact {p : Bit × Y → ℝ} (hp : IsPMF p) (V : Latent p)
    (e : V.ι ≃ Bit)
    {w : Bit × Y → ℝ} (hw : Feasible (Finset.univ : Finset (Bit × Y)) w)
    (h0 : IsContact (Finset.univ : Finset (Bit × Y)) w (V.comp (e.symm 0)))
    (h1 : IsContact (Finset.univ : Finset (Bit × Y)) w (V.comp (e.symm 1)))
    {s t : ℝ} (hs : RowCubeParam (V.comp (e.symm 0)) s) (ht : RowCubeParam (V.comp (e.symm 1)) t)
    (hst : s < t) (hpos : ∀ v, 0 < V.prior v) (hV : V.score = tau p)
    (hcomp : Function.Injective V.comp)
    (eb : Bit → Fin (Fintype.card (Bit × Y))) (heb : Function.Injective eb) :
    ∃ g : Code Bit Y, IsRowWitnessCode p g ∧ detScore p g ≤ 27 / 4 * tau p := by
  rcases le_total (t / s) 16 with hk | hk
  · have hm := twoContact_min_le_twentySevenQuarters V e hw h0 h1 hs ht hst hpos hk
    rw [hV] at hm
    rcases le_total (mutualInfo Prod.fst Prod.snd p) (condEntropy Prod.fst Prod.snd p) with
      hle | hle
    · refine ⟨StochasticToDeterministicLatents.constantCode, Or.inl rfl, ?_⟩
      rw [detScore_constantCode_eq hp]
      exact (min_eq_left hle).symm.le.trans hm
    · refine ⟨fun z => eb z.1, Or.inr (Or.inl ⟨eb, heb, fun _ => rfl⟩), ?_⟩
      rw [aux_detScore_row hp eb heb]
      exact (min_eq_right hle).symm.le.trans hm
  · have hl := twoContact_condEntropy_label_le_score V e hw h0 h1 hs ht hst hpos hk
    obtain ⟨f, hf⟩ := exists_isPurifiedCode V
    have hinj : Function.Injective (fun u : V.ι => eb (e u)) := heb.comp e.injective
    refine ⟨fun z => eb (e (f z)),
      Or.inr (Or.inr ⟨V, f, fun u => eb (e u), hV, hpos, hcomp, hf, hinj, fun _ => rfl⟩), ?_⟩
    rw [← hV]
    refine (detScore_comp_injective hp f (fun u : V.ι => eb (e u)) hinj).trans_le ?_
    exact aux_scalar_large (hf.score_le hp) (condEntropy_label_le V) hl V.score_nonneg

/-- On full support over `Bit × Y`, the constant code, the row code, or a purified code of a
`tau`-optimal latent with positive weights and distinct components has deterministic score at
most `27/4 · tau p`, in bits. -/
theorem exists_rowWitnessCode (p : Bit × Y → ℝ) (hp : IsPMF p) (hpos : ∀ z, 0 < p z) :
    ∃ g : Code Bit Y, IsRowWitnessCode p g ∧ detScore p g ≤ 27 / 4 * tau p := by
  obtain ⟨z0⟩ := nonempty_of_isPMF hp
  have : Nonempty Y := ⟨z0.2⟩
  obtain ⟨eb, heb⟩ := aux_exists_bit_injection (Y := Y)
  rcases rowOptimizer_dichotomy hp hpos with hI | ⟨w, V, e, hw, hV, hprior, hc, hne⟩
  · refine ⟨StochasticToDeterministicLatents.constantCode, Or.inl rfl, ?_⟩
    have h1 : detScore p StochasticToDeterministicLatents.constantCode = tau p :=
      (detScore_constantCode_eq hp).trans hI.symm
    have h2 : 0 ≤ tau p := tau_nonneg p
    rw [h1]
    linarith
  · have hcomp : Function.Injective V.comp :=
      aux_comp_injective_of_ne V e hne
    obtain ⟨x, hx⟩ := rowContact_hasCubeParam hw (hc (e.symm 0))
    obtain ⟨y, hy⟩ := rowContact_hasCubeParam hw (hc (e.symm 1))
    have hxy : x ≠ y := rowContact_param_ne hw (hc _) (hc _) hne hx hy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact aux_exists_of_twoContact hp V e hw (hc _) (hc _) hx hy h hprior hV hcomp eb heb
    · let e' : V.ι ≃ Bit := e.trans (Equiv.swap (0 : Bit) 1)
      have he0 : e'.symm 0 = e.symm 1 := by simp [e']
      have he1 : e'.symm 1 = e.symm 0 := by simp [e']
      have hy' : RowCubeParam (V.comp (e'.symm 0)) y := by rw [he0]; exact hy
      have hx' : RowCubeParam (V.comp (e'.symm 1)) x := by rw [he1]; exact hx
      exact aux_exists_of_twoContact hp V e' hw (hc _) (hc _) hy' hx' h hprior hV hcomp eb heb

/-! ## The bound for every law -/

/-- The binary-row factor: for every law `p` on `Bit × Y`, `T p ≤ (27/4) · tau p`. -/
theorem T_le_twentySevenQuarters_mul_tau (p : Bit × Y → ℝ) (hp : IsPMF p) :
    T p ≤ 27 / 4 * tau p := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · obtain ⟨z, -⟩ := univ_nonempty_of_isPMF hp
    exact (IsEmpty.false z.2).elim
  · refine T_le_mul_tau_of_forall_fullSupport (by norm_num) (fun q hq hqpos => ?_) p hp
    obtain ⟨g, -, hg⟩ := exists_rowWitnessCode q hq hqpos
    exact (T_le_detScore q g).trans hg

/-- The binary-column factor: for every law `p` on `Y × Bit`, `T p ≤ (27/4) · tau p`. -/
theorem T_le_twentySevenQuarters_mul_tau_col (p : Y × Bit → ℝ) (hp : IsPMF p) :
    T p ≤ 27 / 4 * tau p := by
  have h := T_le_twentySevenQuarters_mul_tau (fun z : Bit × Y => p z.swap) (isPMF_swap hp)
  rw [T_swap hp, tau_swap hp] at h
  exact h

end

end BinaryRow

end StochasticToDeterministicLatents
