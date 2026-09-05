import StochasticToDeterministicLatents.Binary.FactorNine.SeamEndpoints
import StochasticToDeterministicLatents.Binary.NormalForm
import StochasticToDeterministicLatents.SparseLimit

/-!
# The binary factor-nine theorem

For a full-support binary law, the selected optimal latent has either one
component or a presented contact chart. The one-component code costs zero;
the two scalar phase bounds control the chart-selected code by eight times
the latent score. Catalog recovery transports this witness to the observable
law. Pricing then gives factor nine for the law-only selector. Smoothing
extends the bound on `T` to every binary law, and finite attainment supplies
a deterministic code there.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

noncomputable section

/-- An optimal latent and a law-defined catalog code with cost at most eight times `tau`. -/
def SmallCatalogFactorEightWitness : Prop :=
  ∀ (p : RealTable), IsPMF p → (∀ z, 0 < p z) →
    ∃ L : Latent p, ∃ g : BinaryCode,
      L.score = tau p ∧ g ∈ catalog p ∧ w3Cost L g ≤ 8 * tau p

private theorem w3Cost_constantCode_eq_zero_of_subsingleton
    {p : RealTable} (L : Latent p) [Subsingleton L.ι] :
    w3Cost L constantCode = 0 := by
  have hlabel : Nonempty L.ι := by
    by_contra h
    let _ : IsEmpty L.ι := not_nonempty_iff.mp h
    have htotal := L.prior_isPMF.total
    simp [mass, stoch_to_det.mass] at htotal
  let i0 : L.ι := Classical.choice hlabel
  let g0 : Fin (Fintype.card Cell) := ⟨0, by decide⟩
  have hcode : constantCode = fun _ => g0 := by rfl
  have hLg : entropyOf (fun a : L.ι × Cell => (a.1, g0)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.1) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.1) (fun x => (x, g0)) Prod.fst (by intro; rfl)
  have hZg : entropyOf (fun a : L.ι × Cell => (a.2, g0)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.2) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.2) (fun x => (x, g0)) Prod.fst (by intro; rfl)
  have hLZg : entropyOf (fun a : L.ι × Cell => (a.1, a.2, g0)) L.joint =
      entropyOf (fun a : L.ι × Cell => (a.1, a.2)) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => (a.1, a.2))
      (fun x => (x.1, x.2, g0)) (fun y => (y.1, y.2.1)) (by intro; rfl)
  have hL : (fun w : L.ι × Cell => w.1) = fun _ => i0 := by
    funext w
    exact Subsingleton.elim _ _
  have hpair : (fun w : L.ι × Cell => (w.1, w.2)) = fun w => (i0, w.2) := by
    funext w
    exact congrArg (fun i => (i, w.2)) (Subsingleton.elim _ _)
  have hLZ : entropyOf (fun a : L.ι × Cell => (a.1, a.2)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.2) L.joint := by
    rw [hpair]
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.2) (fun x => (i0, x)) Prod.snd (by intro; rfl)
  have hgL : entropyOf (fun a : L.ι × Cell => (g0, a.1)) L.joint =
      entropyOf (fun a : L.ι × Cell => a.1) L.joint := by
    simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun a : L.ι × Cell => a.1) (fun x => (g0, x)) Prod.snd (by intro; rfl)
  have hsum : ∑ w, L.joint w = 1 := by
    simpa [mass, stoch_to_det.mass] using L.joint_isPMF.total
  have hunit : entropyOf (fun _ : L.ι × Cell => ()) L.joint = 0 := by
    simp [entropyOf, entropy, pushforward, stoch_to_det.Hvar, stoch_to_det.H,
      stoch_to_det.push, stoch_to_det.mass, hsum]
  have hconstL : entropyOf (fun _ : L.ι × Cell => i0) L.joint = 0 := by
    apply le_antisymm
    · exact (stoch_to_det.Hvar_comp_le L.joint_isPMF
        (fun _ : L.ι × Cell => ()) (fun _ => i0)).trans_eq hunit
    · unfold entropyOf stoch_to_det.Hvar
      exact stoch_to_det.H_nonneg_of_isPMF
        (stoch_to_det.isPMF_push L.joint_isPMF)
  have hconstG : entropyOf (fun _ : L.ι × Cell => g0) L.joint = 0 := by
    apply le_antisymm
    · exact (stoch_to_det.Hvar_comp_le L.joint_isPMF
        (fun _ : L.ι × Cell => ()) (fun _ => g0)).trans_eq hunit
    · unfold entropyOf stoch_to_det.Hvar
      exact stoch_to_det.H_nonneg_of_isPMF
        (stoch_to_det.isPMF_push L.joint_isPMF)
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, g0)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.1) L.joint at hLg
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.2, g0)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.2) L.joint at hZg
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, a.2, g0)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, a.2)) L.joint at hLZg
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (a.1, a.2)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.2) L.joint at hLZ
  change stoch_to_det.Hvar (fun a : L.ι × Cell => (g0, a.1)) L.joint =
    stoch_to_det.Hvar (fun a : L.ι × Cell => a.1) L.joint at hgL
  change stoch_to_det.Hvar (fun _ : L.ι × Cell => i0) L.joint = 0 at hconstL
  change stoch_to_det.Hvar (fun _ : L.ι × Cell => g0) L.joint = 0 at hconstG
  unfold w3Cost condMutualInfo condEntropy
  unfold stoch_to_det.condMI stoch_to_det.condH
  rw [hcode]
  simp only
  rw [hLg, hZg, hLZg, hLZ, hgL, hL, hconstL, hconstG]
  ring

private theorem exists_catalogCode_w3Cost_le_eight_of_card_eq_one
    {p : RealTable} (D : SeedSetup p) (K : Clustering D)
    (hcard : Fintype.card K.κ = 1)
    (hscore : K.quotientSeedSetup.L.score = tau p) :
    ∃ L : Latent p, ∃ g : BinaryCode,
      L.score = tau p ∧ g ∈ catalog p ∧ w3Cost L g ≤ 8 * tau p := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
  let : Subsingleton K.κ := ⟨fun a b => (hi a).trans (hi b).symm⟩
  let : Subsingleton K.quotientSeedSetup.L.ι := by
    change Subsingleton K.κ
    infer_instance
  refine ⟨K.quotientSeedSetup.L, constantCode, hscore, constantCode_mem_catalog p, ?_⟩
  rw [w3Cost_constantCode_eq_zero_of_subsingleton]
  have htau : 0 ≤ tau p := hscore ▸ K.quotientSeedSetup.L.score_nonneg
  positivity

private theorem smallCatalogFactorEightWitness : SmallCatalogFactorEightWitness := by
  intro p hp hpos
  obtain ⟨D, K, _hinj, hscore, hcases⟩ :=
    selectedOptimizer_zeroOrContactPresentation p hp hpos
  rcases hcases with hOne | hTwo
  · exact exists_catalogCode_w3Cost_le_eight_of_card_eq_one D K hOne.1 hscore
  · obtain ⟨_hcard, M, P, _hkernel, hMscore, _hcost, _hw3, _hpi, hroot⟩ := hTwo
    obtain ⟨x, hx0, hx1, hratio, hmass, heq⟩ := hroot
    have h8 := ContactChart.strictFactorEight M.chart x hx0 hx1 hratio hmass heq
    obtain ⟨g, hg, _hw3rec, _hraw, hphase⟩ :=
      exists_catalogCode_of_contactPresentation hp hpos D K M P
    refine ⟨K.quotientSeedSetup.L, g, hscore, hg, ?_⟩
    calc
      w3Cost K.quotientSeedSetup.L g =
          w3Cost M.chart.toTransposeChart.latent
            (phaseSelector M.chart.toTransposeChart) := hphase
      _ ≤ 8 * M.chart.toTransposeChart.latent.score := h8
      _ = 8 * tau p := by rw [hMscore, hscore]

/-- Every full-support binary law has an optimal latent satisfying factor eight. -/
theorem exists_optimalLatent_w3_le_eight_of_fullSupport
    (p : RealTable) (hp : IsPMF p) (hpos : ∀ z, 0 < p z) :
    ∃ L : Latent p, L.score = tau p ∧ w3 L ≤ 8 * tau p := by
  obtain ⟨L, g, hscore, _hg, hcost⟩ := smallCatalogFactorEightWitness p hp hpos
  exact ⟨L, hscore, (w3_le_w3Cost L g).trans hcost⟩

/-- The law-only selector has deterministic score at most nine times `tau` on full support. -/
theorem detScore_selector_le_nine_mul_tau_of_fullSupport
    (p : RealTable) (hp : IsPMF p) (hpos : ∀ z, 0 < p z) :
    detScore p (selector p) ≤ 9 * tau p := by
  obtain ⟨L, g, hscore, hg, hcost⟩ := smallCatalogFactorEightWitness p hp hpos
  calc
    detScore p (selector p) ≤ detScore p g := detScore_selector_le_of_mem p g hg
    _ ≤ L.score + w3Cost L g := detScore_le_latentScore_add_w3Cost L g
    _ = tau p + w3Cost L g := by rw [hscore]
    _ ≤ tau p + 8 * tau p := by linarith
    _ = 9 * tau p := by ring

/-- The certificate-free factor-nine theorem for every binary probability law. -/
theorem T_le_nine_mul_tau (p : RealTable) (hp : IsPMF p) :
    T p ≤ 9 * tau p := by
  apply T_le_mul_tau_of_forall_fullSupport (by norm_num : (0 : ℝ) ≤ 9) ?_ p hp
  intro q hq hpos
  obtain ⟨L, hscore, hw3⟩ := exists_optimalLatent_w3_le_eight_of_fullSupport q hq hpos
  simpa only [show (1 : ℝ) + 8 = 9 by norm_num] using
    T_le_one_add_mul_tau_of_w3 L hscore 8 hw3

/-- Every binary law has a deterministic code with score at most nine times `tau`. -/
theorem exists_code_detScore_le_nine_mul_tau
    (p : RealTable) (hp : IsPMF p) :
    ∃ g : BinaryCode, T p ≤ detScore p g ∧ detScore p g ≤ 9 * tau p := by
  obtain ⟨g, hg⟩ := exists_optimalCode p
  exact ⟨g, hg.ge, hg.trans_le (T_le_nine_mul_tau p hp)⟩

end

end StochasticToDeterministicLatents.Binary
