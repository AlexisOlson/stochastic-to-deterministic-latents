import StochasticToDeterministicLatents.Bridge

/-!
# Transfer from strictly positive laws to sparse laws

A nonnegative multiplicative bound for the deterministic optimum in terms of
the stochastic optimum extends from strictly positive probability laws to the
closed probability simplex.  The deterministic optimum is the minimum of
finitely many continuous score extensions.  For the stochastic optimum, an
attained optimal latent is smoothed by adjoining a uniform component whose
weight tends to zero.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents

open Filter Finset

noncomputable section

variable {α β : Type*}
  [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
  [Nonempty α] [Nonempty β]

private abbrev AmbientCode (α β : Type*) [Fintype α] [Fintype β] :=
  α × β → Fin (Fintype.card (α × β))

private def baseCode : AmbientCode α β :=
  constantCode

omit [Nonempty α] [Nonempty β] in
private theorem code_univ_nonempty :
    (Finset.univ : Finset (AmbientCode α β)).Nonempty :=
  ⟨baseCode, Finset.mem_univ _⟩

/-! ## Continuous deterministic extension -/

private noncomputable def extendedDetScore
    (p : α × β → ℝ) (g : AmbientCode α β) : ℝ :=
  continuousEntropy (pushforward (fun z => (z.1, g z)) p) +
      continuousEntropy (pushforward (fun z => (z.2, g z)) p) -
      continuousEntropy (pushforward (fun z => (z.1, z.2, g z)) p) -
      continuousEntropy (pushforward g p) +
    (continuousEntropy (pushforward (fun z => (g z, z.1)) p) -
      continuousEntropy (pushforward (fun z => z.1) p)) +
    (continuousEntropy (pushforward (fun z => (g z, z.2)) p) -
      continuousEntropy (pushforward (fun z => z.2) p))

omit [Nonempty α] [Nonempty β] in
private theorem continuous_extendedDetScore (g : AmbientCode α β) :
    Continuous (fun p : α × β → ℝ => extendedDetScore p g) := by
  unfold extendedDetScore
  have hXg : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward (fun z => (z.1, g z)) p)) :=
    continuous_continuousEntropy.comp
      (continuous_pushforward (fun z => (z.1, g z)))
  have hYg : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward (fun z => (z.2, g z)) p)) :=
    continuous_continuousEntropy.comp
      (continuous_pushforward (fun z => (z.2, g z)))
  have hXYg : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward (fun z => (z.1, z.2, g z)) p)) :=
    continuous_continuousEntropy.comp
      (continuous_pushforward (fun z => (z.1, z.2, g z)))
  have hg : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward g p)) :=
    continuous_continuousEntropy.comp (continuous_pushforward g)
  have hgX : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward (fun z => (g z, z.1)) p)) :=
    continuous_continuousEntropy.comp
      (continuous_pushforward (fun z => (g z, z.1)))
  have hX : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward (fun z => z.1) p)) :=
    continuous_continuousEntropy.comp
      (continuous_pushforward (fun z : α × β => z.1))
  have hgY : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward (fun z => (g z, z.2)) p)) :=
    continuous_continuousEntropy.comp
      (continuous_pushforward (fun z => (g z, z.2)))
  have hY : Continuous (fun p : α × β → ℝ =>
      continuousEntropy (pushforward (fun z => z.2) p)) :=
    continuous_continuousEntropy.comp
      (continuous_pushforward (fun z : α × β => z.2))
  exact ((((hXg.add hYg).sub hXYg).sub hg).add
    (hgX.sub hX)).add (hgY.sub hY)

omit [Nonempty α] [Nonempty β] in
private theorem extendedDetScore_eq_detScore
    {p : α × β → ℝ} (hp : IsPMF p) (g : AmbientCode α β) :
    extendedDetScore p g = detScore p g := by
  have hXg :
      entropy (pushforward (fun z : α × β => (z.1, g z)) p) =
        continuousEntropy (pushforward (fun z : α × β => (z.1, g z)) p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  have hYg :
      entropy (pushforward (fun z : α × β => (z.2, g z)) p) =
        continuousEntropy (pushforward (fun z : α × β => (z.2, g z)) p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  have hXYg :
      entropy (pushforward (fun z : α × β => (z.1, z.2, g z)) p) =
        continuousEntropy
          (pushforward (fun z : α × β => (z.1, z.2, g z)) p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  have hg : entropy (pushforward g p) = continuousEntropy (pushforward g p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  have hgX :
      entropy (pushforward (fun z : α × β => (g z, z.1)) p) =
        continuousEntropy (pushforward (fun z : α × β => (g z, z.1)) p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  have hX :
      entropy (pushforward (fun z : α × β => z.1) p) =
        continuousEntropy (pushforward (fun z : α × β => z.1) p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  have hgY :
      entropy (pushforward (fun z : α × β => (g z, z.2)) p) =
        continuousEntropy (pushforward (fun z : α × β => (g z, z.2)) p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  have hY :
      entropy (pushforward (fun z : α × β => z.2) p) =
        continuousEntropy (pushforward (fun z : α × β => z.2) p) :=
    entropy_eq_continuousEntropy (pushforward_isPMF hp)
  unfold extendedDetScore detScore
  change _ =
    (entropy (pushforward (fun z : α × β => (z.1, g z)) p) +
        entropy (pushforward (fun z : α × β => (z.2, g z)) p) -
        entropy (pushforward (fun z : α × β => (z.1, z.2, g z)) p) -
        entropy (pushforward g p)) +
      (entropy (pushforward (fun z : α × β => (g z, z.1)) p) -
        entropy (pushforward (fun z : α × β => z.1) p)) +
      (entropy (pushforward (fun z : α × β => (g z, z.2)) p) -
        entropy (pushforward (fun z : α × β => z.2) p))
  rw [hXg, hYg, hXYg, hg, hgX, hX, hgY, hY]

private noncomputable def extendedT (p : α × β → ℝ) : ℝ :=
  (Finset.univ : Finset (AmbientCode α β)).inf' code_univ_nonempty
    (fun g => extendedDetScore p g)

omit [Nonempty α] [Nonempty β] in
private theorem continuous_extendedT :
    Continuous (extendedT : (α × β → ℝ) → ℝ) := by
  unfold extendedT
  apply Continuous.finset_inf'_apply code_univ_nonempty
  intro g _hg
  exact continuous_extendedDetScore g

omit [Nonempty α] [Nonempty β] in
private theorem extendedT_eq_T {p : α × β → ℝ} (hp : IsPMF p) :
    extendedT p = T p := by
  obtain ⟨g₀, hg₀⟩ := exists_optimalCode p
  apply le_antisymm
  · calc
      extendedT p ≤ extendedDetScore p g₀ := by
        exact Finset.inf'_le (f := fun g => extendedDetScore p g)
          (Finset.mem_univ g₀)
      _ = detScore p g₀ := extendedDetScore_eq_detScore hp g₀
      _ = T p := hg₀
  · apply Finset.le_inf' code_univ_nonempty
    intro g _hg
    calc
      T p ≤ detScore p g := T_le_detScore p g
      _ = extendedDetScore p g := (extendedDetScore_eq_detScore hp g).symm

/-! ## Explicit strictly positive smoothing -/

private noncomputable def uniformProductLaw : α × β → ℝ :=
  fun _ => (Fintype.card (α × β) : ℝ)⁻¹

omit [DecidableEq α] [DecidableEq β] in
private theorem uniformProductLaw_isPMF :
    IsPMF (uniformProductLaw : α × β → ℝ) := by
  have hcard : (Fintype.card (α × β) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (α × β) ≠ 0)
  constructor
  · intro z
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · unfold stoch_to_det.mass uniformProductLaw
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard

omit [DecidableEq α] [DecidableEq β] in
private theorem uniformProductLaw_pos (z : α × β) :
    0 < (uniformProductLaw : α × β → ℝ) z := by
  unfold uniformProductLaw
  positivity

private def smoothedLaw (p u : α × β → ℝ) (t : ℝ) : α × β → ℝ :=
  fun z => (1 - t) * p z + t * u z

omit [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β] in
private theorem smoothedLaw_isPMF
    {p u : α × β → ℝ} (hp : IsPMF p) (hu : IsPMF u)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsPMF (smoothedLaw p u t) := by
  constructor
  · intro z
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1) (hp.nonneg z))
      (mul_nonneg ht0 (hu.nonneg z))
  · have hp_sum : (∑ z, p z) = 1 := by
      simpa [stoch_to_det.mass] using hp.total
    have hu_sum : (∑ z, u z) = 1 := by
      simpa [stoch_to_det.mass] using hu.total
    unfold stoch_to_det.mass smoothedLaw
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hp_sum, hu_sum]
    ring

omit [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β] in
private theorem smoothedLaw_pos
    {p u : α × β → ℝ} (hp : IsPMF p)
    (hu_pos : ∀ z, 0 < u z) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (z : α × β) :
    0 < smoothedLaw p u t z := by
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr ht1) (hp.nonneg z))
    (mul_pos ht0 (hu_pos z))

private def smoothedPrior {p : α × β → ℝ} (V : Latent p)
    (t : ℝ) : Option V.ι → ℝ
  | none => t
  | some v => (1 - t) * V.prior v

private def smoothedComponent {p u : α × β → ℝ} (V : Latent p) :
    Option V.ι → (α × β → ℝ)
  | none => u
  | some v => V.comp v

private noncomputable def smoothedLatent
    {p u : α × β → ℝ} (V : Latent p) (hu : IsPMF u) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Latent (smoothedLaw p u t) where
  ι := Option V.ι
  fin := inferInstance
  dec := inferInstance
  prior := smoothedPrior V t
  comp := smoothedComponent V
  prior_isPMF := by
    constructor
    · intro w
      cases w with
      | none => exact ht0
      | some v =>
          exact mul_nonneg (sub_nonneg.mpr ht1) (V.prior_isPMF.nonneg v)
    · have hprior : (∑ v, V.prior v) = 1 := by
        simpa [stoch_to_det.mass] using V.prior_isPMF.total
      unfold stoch_to_det.mass
      rw [Fintype.sum_option]
      change t + (∑ v, (1 - t) * V.prior v) = 1
      rw [← Finset.mul_sum, hprior]
      ring
  comp_isPMF := by
    intro w
    cases w with
    | none => exact hu
    | some v => exact V.comp_isPMF v
  mixture := by
    intro z
    rw [Fintype.sum_option]
    change t * u z + (∑ v, ((1 - t) * V.prior v) * V.comp v z) =
      smoothedLaw p u t z
    calc
      _ = t * u z + (1 - t) * (∑ v, V.prior v * V.comp v z) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = t * u z + (1 - t) * p z := by rw [V.mixture z]
      _ = smoothedLaw p u t z := by unfold smoothedLaw; ring

/-! ## One-sided continuity of the stochastic optimum -/

private noncomputable def extendedPsi (q : α × β → ℝ) : ℝ :=
  2 * continuousEntropy q -
    continuousEntropy (pushforward Prod.fst q) -
    continuousEntropy (pushforward Prod.snd q)

omit [Nonempty α] [Nonempty β] in
private theorem continuous_extendedPsi :
    Continuous (extendedPsi : (α × β → ℝ) → ℝ) := by
  unfold extendedPsi
  have hq : Continuous (fun q : α × β → ℝ => continuousEntropy q) :=
    continuous_continuousEntropy
  have hqX : Continuous (fun q : α × β → ℝ =>
      continuousEntropy (pushforward Prod.fst q)) :=
    continuous_continuousEntropy.comp (continuous_pushforward Prod.fst)
  have hqY : Continuous (fun q : α × β → ℝ =>
      continuousEntropy (pushforward Prod.snd q)) :=
    continuous_continuousEntropy.comp (continuous_pushforward Prod.snd)
  exact ((continuous_const.mul hq).sub hqX).sub hqY

omit [Nonempty α] [Nonempty β] in
private theorem extendedPsi_eq_Psi {q : α × β → ℝ} (hq : IsPMF q) :
    extendedPsi q = Psi q := by
  have hqX : IsPMF (pushforward Prod.fst q) := pushforward_isPMF hq
  have hqY : IsPMF (pushforward Prod.snd q) := pushforward_isPMF hq
  unfold extendedPsi
  change
    2 * continuousEntropy q -
        continuousEntropy (pushforward Prod.fst q) -
        continuousEntropy (pushforward Prod.snd q) =
      2 * entropy q - entropy (pushforward Prod.fst q) -
        entropy (pushforward Prod.snd q)
  rw [entropy_eq_continuousEntropy hq,
    entropy_eq_continuousEntropy hqX,
    entropy_eq_continuousEntropy hqY]

private noncomputable def smoothedScore
    {p : α × β → ℝ} (V : Latent p) (u : α × β → ℝ) (t : ℝ) : ℝ :=
  extendedPsi (smoothedLaw p u t) -
    (t * Phi u + (1 - t) * (∑ v, V.prior v * Phi (V.comp v)))

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β] in
private theorem continuous_smoothedLaw (p u : α × β → ℝ) :
    Continuous (smoothedLaw p u) := by
  unfold smoothedLaw
  apply continuous_pi
  intro z
  fun_prop

omit [Nonempty α] [Nonempty β] in
private theorem continuous_smoothedScore
    {p : α × β → ℝ} (V : Latent p) (u : α × β → ℝ) :
    Continuous (smoothedScore V u) := by
  unfold smoothedScore
  have hsmooth : Continuous (fun t : ℝ =>
      extendedPsi (smoothedLaw p u t)) :=
    continuous_extendedPsi.comp (continuous_smoothedLaw p u)
  fun_prop

omit [Nonempty α] [Nonempty β] in
private theorem smoothedLatent_score_eq
    {p u : α × β → ℝ} (V : Latent p)
    (hp : IsPMF p) (hu : IsPMF u) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (smoothedLatent V hu t ht0 ht1).score = smoothedScore V u t := by
  have hsum :
      (∑ w : Option V.ι,
        (smoothedLatent V hu t ht0 ht1).prior w *
          Phi ((smoothedLatent V hu t ht0 ht1).comp w)) =
        t * Phi u + (1 - t) * (∑ v, V.prior v * Phi (V.comp v)) := by
    simp only [smoothedLatent, smoothedPrior, smoothedComponent,
      Fintype.sum_option]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    ring
  rw [latent_score_eq (smoothedLaw_isPMF hp hu ht0 ht1)]
  rw [← extendedPsi_eq_Psi (smoothedLaw_isPMF hp hu ht0 ht1)]
  unfold smoothedScore
  exact congrArg (fun x : ℝ => extendedPsi (smoothedLaw p u t) - x) hsum

omit [Nonempty α] [Nonempty β] in
private theorem smoothedScore_zero
    {p : α × β → ℝ} (V : Latent p) (hp : IsPMF p)
    (u : α × β → ℝ) :
    smoothedScore V u 0 = V.score := by
  rw [latent_score_eq hp]
  unfold smoothedScore
  have hsmooth0 : smoothedLaw p u 0 = p := by
    funext z
    simp [smoothedLaw]
  rw [hsmooth0, extendedPsi_eq_Psi hp]
  ring

private def smoothingWeight (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem smoothingWeight_pos (n : ℕ) : 0 < smoothingWeight n := by
  unfold smoothingWeight
  positivity

private theorem smoothingWeight_le_one (n : ℕ) : smoothingWeight n ≤ 1 := by
  unfold smoothingWeight
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdenom : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  exact inv_le_one_of_one_le₀ hdenom

private theorem tendsto_smoothingWeight :
    Tendsto smoothingWeight atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0)
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A nonnegative multiplicative `T`/`tau` bound proved for strictly positive
laws extends to every law on the same finite nonempty alphabets. -/
theorem T_le_mul_tau_of_forall_fullSupport
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    {C : ℝ} (hC : 0 ≤ C)
    (hfull : ∀ p : α × β → ℝ, IsPMF p → (∀ z, 0 < p z) → T p ≤ C * tau p)
    (p : α × β → ℝ) (hp : IsPMF p) :
    T p ≤ C * tau p := by
  let u : α × β → ℝ := uniformProductLaw
  have hu : IsPMF u := uniformProductLaw_isPMF
  have hu_pos : ∀ z, 0 < u z := uniformProductLaw_pos
  obtain ⟨V, hV⟩ := exists_optimalLatent hp
  let pn : ℕ → (α × β → ℝ) := fun n => smoothedLaw p u (smoothingWeight n)
  have hpn (n : ℕ) : IsPMF (pn n) :=
    smoothedLaw_isPMF hp hu (smoothingWeight_pos n).le
      (smoothingWeight_le_one n)
  have hpn_pos (n : ℕ) : ∀ z, 0 < pn n z := by
    intro z
    exact smoothedLaw_pos hp hu_pos (smoothingWeight_pos n)
      (smoothingWeight_le_one n) z
  let W : (n : ℕ) → Latent (pn n) := fun n =>
    smoothedLatent V hu (smoothingWeight n) (smoothingWeight_pos n).le
      (smoothingWeight_le_one n)
  have hineq (n : ℕ) :
      extendedT (pn n) ≤ C * smoothedScore V u (smoothingWeight n) := by
    have hbase := hfull (pn n) (hpn n) (hpn_pos n)
    have htau : tau (pn n) ≤ (W n).score := tau_le_score (W n)
    have hscaled := mul_le_mul_of_nonneg_left htau hC
    rw [extendedT_eq_T (hpn n)]
    rw [smoothedLatent_score_eq V hp hu
      (smoothingWeight_pos n).le (smoothingWeight_le_one n)] at hscaled
    exact hbase.trans hscaled
  have hpn_tendsto : Tendsto pn atTop (nhds p) := by
    change Tendsto (fun n => smoothedLaw p u (smoothingWeight n)) atTop (nhds p)
    have h := (continuous_smoothedLaw p u).continuousAt.tendsto.comp
      tendsto_smoothingWeight
    change Tendsto (fun n => smoothedLaw p u (smoothingWeight n)) atTop
      (nhds (smoothedLaw p u 0)) at h
    have hsmooth0 : smoothedLaw p u 0 = p := by
      funext z
      simp [smoothedLaw]
    rw [hsmooth0] at h
    exact h
  have hleft : Tendsto (fun n => extendedT (pn n)) atTop (nhds (T p)) := by
    have hT := continuous_extendedT.continuousAt.tendsto.comp hpn_tendsto
    rw [extendedT_eq_T hp] at hT
    change Tendsto (extendedT ∘ pn) atTop (nhds (T p))
    exact hT
  have hright : Tendsto
      (fun n => C * smoothedScore V u (smoothingWeight n))
      atTop (nhds (C * tau p)) := by
    have hscore := continuous_smoothedScore V u |>.continuousAt.tendsto.comp
      tendsto_smoothingWeight
    have hscaled : Tendsto
        (fun n : ℕ => C * smoothedScore V u (smoothingWeight n))
        atTop (nhds (C * smoothedScore V u 0)) :=
      tendsto_const_nhds.mul hscore
    simpa [smoothedScore_zero V hp u, hV] using hscaled
  exact le_of_tendsto_of_tendsto' hleft hright hineq

end

end StochasticToDeterministicLatents
