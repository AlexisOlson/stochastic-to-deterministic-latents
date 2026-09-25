import StochasticToDeterministicLatents.BinaryRow.Contact
import StochasticToDeterministicLatents.BinaryRow.Shannon

/-!
# The two-label optimizer on `Bit × Y`

For a law on `Bit × Y` with every cell positive, at most two distinct component laws occur in an
optimal latent. Among any three contacts of one feasible kernel two coincide
(`rowContact_three_dup`): each contact's row parameter is a double root of the row
feasibility polynomial, which is a nonzero sextic (`rowFeasibilityPolynomial_coeff_three`) with
no degree-five term. Hence the duplicate quotient of an optimal latent has one or two classes
(`rowClustering_card_eq_one_or_two`), and `rowOptimizer_dichotomy` states the two cases: either
the stochastic optimum is the mutual information `I(X;Y)`, or it is attained by a latent labelled
by `Bit` whose two component laws are distinct contacts of one feasible kernel, with positive
prior weights. `exists_optimalLatent_bit` is the weaker statement that some optimal latent is
labelled by `Bit`; its components may coincide.

The generic section proves, for any finite product alphabet, that the full cell set is connected
and that a law with every cell positive admits a seed setup.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0, whose seed setup,
clustering, and `Phi`/`Ixy` identity these proofs use. The contact count and the card bound follow
the `Bit × Bit` proofs of `Binary/TransposeNormalForm.lean` with sums over `Y`.
-/

open scoped BigOperators

namespace StochasticToDeterministicLatents

namespace BinaryRow

noncomputable section

open Finset Polynomial Binary

/-! ## Full support on a product alphabet -/

section Generic

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- The full cell set of a product alphabet is connected. -/
theorem isConnected_univ_prod : IsConnected (univ : Finset (α × β)) := by
  intro z _ w _
  let mid : α × β := (z.1, w.2)
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      ⟨Finset.mem_univ z, Finset.mem_univ mid, Or.inl rfl⟩)
    (Relation.ReflTransGen.single
      ⟨Finset.mem_univ mid, Finset.mem_univ w, Or.inr rfl⟩)

omit [DecidableEq α] [DecidableEq β] in
/-- A law with every cell positive has full support. -/
theorem support_eq_univ_of_forall_pos {p : α × β → ℝ} (hpos : ∀ z, 0 < p z) :
    support p = univ := by
  ext z
  simp [support, stoch_to_det.support, (hpos z).ne']

/-- A full-support law admits a seed setup. -/
theorem exists_seedSetup_of_forall_pos {p : α × β → ℝ} (hp : IsPMF p)
    (hpos : ∀ z, 0 < p z) : Nonempty (SeedSetup p) := by
  apply exists_seedSetup hp
  rw [support_eq_univ_of_forall_pos hpos]
  exact isConnected_univ_prod

/-- A nonempty finite type in which any three elements contain a repeat has one or two
elements. -/
theorem card_eq_one_or_two_of_three_dup {κ : Type*} [Fintype κ] [Nonempty κ]
    (h : ∀ a b c : κ, a = b ∨ a = c ∨ b = c) :
    Fintype.card κ = 1 ∨ Fintype.card κ = 2 := by
  have hle : Fintype.card κ ≤ 2 := by
    by_contra hn
    have hthree : 3 ≤ Fintype.card κ := by omega
    let e := Fintype.equivFin κ
    let a : κ := e.symm ⟨0, by omega⟩
    let b : κ := e.symm ⟨1, by omega⟩
    let c : κ := e.symm ⟨2, by omega⟩
    have hab : a ≠ b := by
      intro hab
      have h' := congrArg e hab
      simp [a, b] at h'
    have hac : a ≠ c := by
      intro hac
      have h' := congrArg e hac
      simp [a, c] at h'
    have hbc : b ≠ c := by
      intro hbc
      have h' := congrArg e hbc
      simp [b, c] at h'
    rcases h a b c with h' | h' | h'
    · exact hab h'
    · exact hac h'
    · exact hbc h'
  have hpos : 0 < Fintype.card κ := Fintype.card_pos
  omega

/-- The mutual information of the two coordinates is the upstream `Ixy`. -/
private theorem mutualInfo_eq_Ixy (p : α × β → ℝ) :
    mutualInfo (fun z : α × β => z.1) (fun z : α × β => z.2) p = stoch_to_det.Ixy p := by
  have hId : stoch_to_det.Hvar (fun z : α × β => (z.1, z.2)) p = stoch_to_det.H p := by
    unfold stoch_to_det.Hvar
    apply congrArg stoch_to_det.H
    funext z
    rw [stoch_to_det.push]
    apply Finset.sum_eq_single z
    · intro b hb hne
      exact (hne (Finset.mem_filter.mp hb).2).elim
    · intro hnot
      exact (hnot (by simp)).elim
  show stoch_to_det.Hvar (fun z : α × β => z.1) p + stoch_to_det.Hvar (fun z : α × β => z.2) p -
      stoch_to_det.Hvar (fun z : α × β => (z.1, z.2)) p = stoch_to_det.Ixy p
  rw [hId]
  rfl

/-- A latent all of whose components equal the observed law scores `Ixy`. -/
private theorem score_eq_Ixy_of_comp_eq {p : α × β → ℝ} (hp : IsPMF p) (V : Latent p)
    (hc : ∀ v, V.comp v = p) : V.score = stoch_to_det.Ixy p := by
  have hV := latent_score_eq hp V
  have hprior : ∑ v, V.prior v = 1 := by
    simpa [stoch_to_det.mass] using V.prior_isPMF.total
  have hsum : ∑ v, V.prior v * Phi (V.comp v) = Phi p := by
    simp only [hc, ← Finset.sum_mul, hprior, one_mul]
  rw [hV, hsum]
  change stoch_to_det.Psi p - stoch_to_det.Phi p = stoch_to_det.Ixy p
  rw [stoch_to_det.Phi_eq_Psi_sub_Ixy]
  ring

omit [DecidableEq α] [DecidableEq β] in
/-- A latent with one label has that label's component equal to the observed law. -/
private theorem comp_eq_of_subsingleton {p : α × β → ℝ} (V : Latent p) [Subsingleton V.ι]
    (v : V.ι) : V.comp v = p := by
  have hprior : V.prior v = 1 := by
    have h : ∑ u, V.prior u = 1 := by
      simpa [stoch_to_det.mass] using V.prior_isPMF.total
    rwa [Fintype.sum_subsingleton _ v] at h
  funext z
  have h := V.mixture z
  rw [Fintype.sum_subsingleton _ v, hprior, one_mul] at h
  exact h

/-- A latent with one label scores the mutual information `I(X;Y)`. -/
theorem score_eq_mutualInfo_of_subsingleton {p : α × β → ℝ} (hp : IsPMF p)
    (V : Latent p) [Subsingleton V.ι] :
    V.score = mutualInfo (fun z : α × β => z.1) (fun z : α × β => z.2) p := by
  rw [mutualInfo_eq_Ixy]
  exact score_eq_Ixy_of_comp_eq hp V (comp_eq_of_subsingleton V)

/-- If the duplicate quotient has one class, the stochastic optimum is `I(X;Y)`. -/
theorem oneClass_tau_eq_mutualInfo {p : α × β → ℝ} (hp : IsPMF p)
    (D : SeedSetup p) (K : Clustering D) (h1 : Fintype.card K.κ = 1) :
    tau p = mutualInfo (fun z : α × β => z.1) (fun z : α × β => z.2) p := by
  have : Subsingleton K.κ := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have : Subsingleton (Clustering.quotientLatent K).ι := by
    change Subsingleton K.κ
    infer_instance
  rw [← (K.quotientLatent_score_eq.trans D.optimal)]
  exact score_eq_mutualInfo_of_subsingleton hp _

/-- The latent labelled by `Bit` with uniform prior and both components the observed law. -/
private def uniformBitLatent {p : α × β → ℝ} (hp : IsPMF p) : Latent p where
  ι := Bit
  fin := inferInstance
  dec := inferInstance
  prior := fun _ => 1 / 2
  comp := fun _ => p
  prior_isPMF := ⟨fun _ => by norm_num, by
    simp only [stoch_to_det.mass, Fin.sum_univ_two]
    norm_num⟩
  comp_isPMF := fun _ => hp
  mixture := by
    intro z
    simp only [Fin.sum_univ_two]
    ring

/-- The uniform `Bit` latent scores `Ixy`. -/
private theorem uniformBitLatent_score {p : α × β → ℝ} (hp : IsPMF p) :
    (uniformBitLatent hp).score = stoch_to_det.Ixy p :=
  score_eq_Ixy_of_comp_eq hp _ (fun _ => rfl)

end Generic

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-! ## The row feasibility polynomial is nonzero -/

/-- A cubed column coefficient has no degree-three term. -/
private theorem cube_coeff_three (a b : ℝ) :
    ((C a + C b * X ^ 2) ^ 3 : Polynomial ℝ).coeff 3 = 0 := by
  rw [show (C a + C b * X ^ 2) ^ 3 =
      C (a ^ 3) + C (3 * a ^ 2 * b) * X ^ 2 +
        C (3 * a * b ^ 2) * X ^ 4 + C (b ^ 3) * X ^ 6 by
    simp only [C_mul, C_pow, C_ofNat]
    ring]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
  norm_num

/-- The base term has degree-three coefficient two. -/
private theorem base_coeff_three :
    (((1 : Polynomial ℝ) + X ^ 3) ^ 2).coeff 3 = 2 := by
  rw [show ((1 : Polynomial ℝ) + X ^ 3) ^ 2 =
      C 1 + C 2 * X ^ 3 + C 1 * X ^ 6 by
    simp only [map_one, C_ofNat]
    ring]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
  norm_num

omit [DecidableEq Y] in
/-- Every cubed column coefficient has only even-degree terms, so the degree-three coefficient
of the row feasibility polynomial is that of `(1 + X³)²`. -/
theorem rowFeasibilityPolynomial_coeff_three (w : Bit × Y → ℝ) :
    (rowFeasibilityPolynomial w).coeff 3 = 2 := by
  simp only [rowFeasibilityPolynomial, coeff_sub, finsetSum_coeff, base_coeff_three,
    cube_coeff_three, sum_const_zero, sub_zero]

omit [DecidableEq Y] in
/-- The row feasibility polynomial is never zero. -/
theorem rowFeasibilityPolynomial_ne_zero (w : Bit × Y → ℝ) :
    rowFeasibilityPolynomial w ≠ 0 := by
  intro h
  have h3 := rowFeasibilityPolynomial_coeff_three w
  rw [h, coeff_zero] at h3
  norm_num at h3

/-! ## Three contacts of one feasible kernel contain a duplicate -/

/-- Distinct contacts of one feasible kernel have distinct row parameters. -/
theorem rowContact_param_ne {w q r : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q)
    (hr : IsContact (univ : Finset (Bit × Y)) w r) (hqr : q ≠ r)
    {x y : ℝ} (hx : RowCubeParam q x) (hy : RowCubeParam r y) : x ≠ y := by
  intro h
  apply hqr
  apply rowContact_injective hw hq hr hx
  rw [h]
  exact hy

/-- A contact's row parameter is a double root of the row feasibility polynomial. -/
theorem rowContact_param_square_dvd [Nonempty Y] {w q : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w)
    (hq : IsContact (univ : Finset (Bit × Y)) w q) {x : ℝ} (hx : RowCubeParam q x) :
    (Polynomial.X - Polynomial.C x) ^ 2 ∣ rowFeasibilityPolynomial w := by
  have hnonneg : ∀ u : ℝ, 0 < u → 0 ≤ (rowFeasibilityPolynomial w).eval u := by
    intro u hu
    rw [rowFeasibilityPolynomial_eval]
    exact rowFeasibility_nonneg hw hu
  have hroot : (rowFeasibilityPolynomial w).eval x = 0 := by
    rw [rowFeasibilityPolynomial_eval]
    exact (rowContact_root hw hq hx).1
  exact positiveRoot_square_dvd _ x hx.1 hnonneg hroot

/-- Among three contacts of one feasible kernel on `Bit × Y`, two are equal. -/
theorem rowContact_three_dup {w : Bit × Y → ℝ}
    (hw : Feasible (univ : Finset (Bit × Y)) w) {q r s : Bit × Y → ℝ}
    (hq : IsContact (univ : Finset (Bit × Y)) w q)
    (hr : IsContact (univ : Finset (Bit × Y)) w r)
    (hs : IsContact (univ : Finset (Bit × Y)) w s) :
    q = r ∨ q = s ∨ r = s := by
  by_cases hqr : q = r
  · exact Or.inl hqr
  by_cases hqs : q = s
  · exact Or.inr (Or.inl hqs)
  by_cases hrs : r = s
  · exact Or.inr (Or.inr hrs)
  exfalso
  have : Nonempty Y := by
    obtain ⟨y, -⟩ := univ_nonempty_of_isPMF (colMass_isPMF hq.1)
    exact ⟨y⟩
  obtain ⟨x, hx⟩ := rowContact_hasCubeParam hw hq
  obtain ⟨y, hy⟩ := rowContact_hasCubeParam hw hr
  obtain ⟨z, hz⟩ := rowContact_hasCubeParam hw hs
  exact threePositiveDoubleRoots_impossible (rowFeasibilityPolynomial w) x y z
    (rowFeasibilityPolynomial_ne_zero w) (rowFeasibilityPolynomial_natDegree_le w)
    (rowFeasibilityPolynomial_coeff_five w) hx.1 hy.1 hz.1
    (rowContact_param_ne hw hq hr hqr hx hy) (rowContact_param_ne hw hq hs hqs hx hz)
    (rowContact_param_ne hw hr hs hrs hy hz)
    (rowContact_param_square_dvd hw hq hx) (rowContact_param_square_dvd hw hr hy)
    (rowContact_param_square_dvd hw hs hz)

/-! ## At most two distinct optimal components -/

/-- On a full-support law the setup's kernel is feasible on the full cell set. -/
private theorem feasible_univ {p : Bit × Y → ℝ} (hpos : ∀ z, 0 < p z) (D : SeedSetup p) :
    Feasible (univ : Finset (Bit × Y)) D.w := by
  rw [← support_eq_univ_of_forall_pos hpos]
  exact D.feasible

/-- On a full-support law every cluster law is a contact on the full cell set. -/
private theorem contact_univ {p : Bit × Y → ℝ} (hpos : ∀ z, 0 < p z) (D : SeedSetup p)
    (K : Clustering D) (c : K.κ) :
    IsContact (univ : Finset (Bit × Y)) D.w (K.Q c) := by
  rw [← support_eq_univ_of_forall_pos hpos]
  exact K.Q_isContact c

/-- Any three cluster indices contain a repeat. -/
private theorem clustering_three_dup {p : Bit × Y → ℝ} (hpos : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) (a b c : K.κ) :
    a = b ∨ a = c ∨ b = c := by
  rcases rowContact_three_dup (feasible_univ hpos D) (contact_univ hpos D K a)
      (contact_univ hpos D K b) (contact_univ hpos D K c) with h | h | h
  · exact Or.inl (K.Q_injective h)
  · exact Or.inr (Or.inl (K.Q_injective h))
  · exact Or.inr (Or.inr (K.Q_injective h))

/-- For a full-support law on `Bit × Y`, a clustering of a seed setup has one or two classes. -/
theorem rowClustering_card_eq_one_or_two {p : Bit × Y → ℝ} (hpos : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) :
    Fintype.card K.κ = 1 ∨ Fintype.card K.κ = 2 := by
  have : Nonempty K.κ := ⟨K.cl (Classical.arbitrary D.L.ι)⟩
  exact card_eq_one_or_two_of_three_dup (clustering_three_dup hpos D K)

/-! ## The optimizer dichotomy -/

/-- With two clusters, the quotient latent relabelled by `Bit` is an optimizer whose two
components are distinct contacts of the setup's kernel. -/
private theorem bitOptimizer_of_card_two {p : Bit × Y → ℝ} (hpos : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) (h2 : Fintype.card K.κ = 2) :
    ∃ (w : Bit × Y → ℝ) (V : Latent p) (e : V.ι ≃ Bit),
        Feasible (univ : Finset (Bit × Y)) w ∧ V.score = tau p ∧
        (∀ v, 0 < V.prior v) ∧ (∀ v, IsContact (univ : Finset (Bit × Y)) w (V.comp v)) ∧
        V.comp (e.symm 0) ≠ V.comp (e.symm 1) := by
  let e : K.κ ≃ Bit := (Fintype.equivFin K.κ).trans (finCongr h2)
  refine ⟨D.w, Clustering.quotientLatent K, e, feasible_univ hpos D,
    K.quotientLatent_score_eq.trans D.optimal, K.s_pos, contact_univ hpos D K, ?_⟩
  intro h
  have h' : K.Q (e.symm 0) = K.Q (e.symm 1) := h
  have h01 := e.symm.injective (K.Q_injective h')
  exact absurd h01 (by decide)

/-- A full-support law on `Bit × Y` has an optimal latent labelled by `Bit`. -/
theorem exists_optimalLatent_bit {p : Bit × Y → ℝ} (hp : IsPMF p) (hpos : ∀ z, 0 < p z) :
    ∃ (V : Latent p) (_ : V.ι ≃ Bit), V.score = tau p := by
  obtain ⟨D⟩ := exists_seedSetup_of_forall_pos hp hpos
  obtain ⟨K⟩ := exists_clustering D
  rcases rowClustering_card_eq_one_or_two hpos D K with h1 | h2
  · refine ⟨uniformBitLatent hp, Equiv.refl _, ?_⟩
    rw [uniformBitLatent_score hp, oneClass_tau_eq_mutualInfo hp D K h1,
      mutualInfo_eq_Ixy]
  · obtain ⟨-, V, e, -, hs, -⟩ := bitOptimizer_of_card_two hpos D K h2
    exact ⟨V, e, hs⟩

/-- For a full-support law on `Bit × Y`, either the stochastic optimum equals the mutual
information `I(X;Y)`, or it is attained by a latent labelled by `Bit` whose two component laws
are distinct contacts of one feasible kernel, with positive prior weights. -/
theorem rowOptimizer_dichotomy {p : Bit × Y → ℝ} (hp : IsPMF p) (hpos : ∀ z, 0 < p z) :
    tau p = mutualInfo (fun z : Bit × Y => z.1) (fun z : Bit × Y => z.2) p ∨
      ∃ (w : Bit × Y → ℝ) (V : Latent p) (e : V.ι ≃ Bit),
        Feasible (univ : Finset (Bit × Y)) w ∧ V.score = tau p ∧
        (∀ v, 0 < V.prior v) ∧ (∀ v, IsContact (univ : Finset (Bit × Y)) w (V.comp v)) ∧
        V.comp (e.symm 0) ≠ V.comp (e.symm 1) := by
  obtain ⟨D⟩ := exists_seedSetup_of_forall_pos hp hpos
  obtain ⟨K⟩ := exists_clustering D
  rcases rowClustering_card_eq_one_or_two hpos D K with h1 | h2
  · exact Or.inl (oneClass_tau_eq_mutualInfo hp D K h1)
  · exact Or.inr (bitOptimizer_of_card_two hpos D K h2)

end

end BinaryRow

end StochasticToDeterministicLatents
