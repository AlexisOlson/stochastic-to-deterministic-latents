import StochasticToDeterministicLatents.Latent
import StochasticToDeterministicLatents.Deterministic

/-!
# Pricing a deterministic replacement

Let `L` be a finite stochastic latent for `(X,Y)`, and let `g` be a
deterministic code of `(X,Y)`.  The extra cost relevant to determinization is

`I(L ; (X,Y) | g) + 3 H(g | L)`.

This module gives that expression a name, proves an exact score identity, and
then drops an explicitly nonnegative remainder to obtain the pricing
inequality.  The last theorem packages the argument without choosing a
numerical constant.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-! ## Cost -/

/-- The pointwise determinization cost
`I(L ; (X,Y) | g) + 3 H(g | L)`, in bits. -/
noncomputable def w3Cost {p : α × β → ℝ} (L : Latent p)
    (g : Code α β) : ℝ :=
  condMutualInfo
      (fun w : L.ι × (α × β) => w.1)
      (fun w => w.2)
      (fun w => g w.2)
      L.joint
    + 3 * condEntropy
      (fun w : L.ι × (α × β) => g w.2)
      (fun w => w.1)
      L.joint

/-- The best pointwise determinization cost over the canonical finite code
space.  The infimum is attained; see `exists_optimalW3Code`. -/
noncomputable def w3 {p : α × β → ℝ} (L : Latent p) : ℝ :=
  ⨅ g : Code α β, w3Cost L g

/-- The four conditional-mutual-information terms subtracted in the exact
score identity.  Their nonnegativity is recorded after that identity. -/
noncomputable def scoreRebate {p : α × β → ℝ} (L : Latent p)
    (g : Code α β) : ℝ :=
  condMutualInfo
      (fun w : L.ι × (α × β) => w.1)
      (fun w => w.2.2)
      (fun w => (w.2.1, g w.2))
      L.joint
    + condMutualInfo
      (fun w : L.ι × (α × β) => w.1)
      (fun w => w.2.1)
      (fun w => (w.2.2, g w.2))
      L.joint
    + condMutualInfo
      (fun w : L.ι × (α × β) => g w.2)
      (fun w => w.2.1)
      (fun w => w.1)
      L.joint
    + condMutualInfo
      (fun w : L.ι × (α × β) => g w.2)
      (fun w => w.2.2)
      (fun w => w.1)
      L.joint

/-! ## The finite cost landscape -/

private theorem exists_minimalW3Code {p : α × β → ℝ} (L : Latent p) :
    ∃ g : Code α β, ∀ h : Code α β, w3Cost L g ≤ w3Cost L h := by
  classical
  let g₀ : Code α β := constantCode
  have hcodes : (Finset.univ : Finset (Code α β)).Nonempty :=
    ⟨g₀, Finset.mem_univ _⟩
  obtain ⟨g, _hg, hminimal⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset (Code α β)) (fun h => w3Cost L h) hcodes
  exact ⟨g, fun h => hminimal h (Finset.mem_univ _)⟩

/-- `w3` is at most the cost of every supplied canonical code. -/
theorem w3_le_w3Cost {p : α × β → ℝ} (L : Latent p) (g : Code α β) :
    w3 L ≤ w3Cost L g := by
  obtain ⟨g₀, hminimal⟩ := exists_minimalW3Code L
  unfold w3
  have hb : BddBelow (Set.range fun h : Code α β => w3Cost L h) :=
    ⟨w3Cost L g₀, by
      rintro _ ⟨h, rfl⟩
      exact hminimal h⟩
  exact ciInf_le hb g

/-- The finite infimum defining `w3` is attained by a canonical code. -/
theorem exists_optimalW3Code {p : α × β → ℝ} (L : Latent p) :
    ∃ g : Code α β, w3Cost L g = w3 L := by
  obtain ⟨g, hminimal⟩ := exists_minimalW3Code L
  let _ : Nonempty (Code α β) := ⟨constantCode⟩
  refine ⟨g, le_antisymm ?_ (w3_le_w3Cost L g)⟩
  unfold w3
  exact le_ciInf hminimal

/-! ## Exact score accounting -/

/- The proof has three private layers: transport from the latent joint law to
the observable law, entropy invariance under finite relabeling, and algebraic
changes of score coordinates. -/

/- First, any observable statistic has the same entropy whether evaluated on
`p` or lifted to the `(L,X,Y)` joint law. -/

private theorem latentPushSndJoint {p : α × β → ℝ} (L : Latent p) :
    pushforward (fun w : L.ι × (α × β) => w.2) L.joint = p := by
  funext z
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simpa [Latent.joint, stoch_to_det.Latent.joint] using L.mixture z

private theorem latentEntropyOfLift
    {p : α × β → ℝ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Latent p) (f : α × β → κ) :
    entropyOf (fun w : L.ι × (α × β) => f w.2) L.joint = entropyOf f p := by
  unfold entropyOf stoch_to_det.Hvar
  congr 1
  calc
    stoch_to_det.push (fun w : L.ι × (α × β) => f w.2) L.joint =
        stoch_to_det.push f
          (stoch_to_det.push (fun w : L.ι × (α × β) => w.2) L.joint) := by
      symm
      simpa [Function.comp_def] using
        (stoch_to_det.push_push (fun w : L.ι × (α × β) => w.2) f L.joint)
    _ = stoch_to_det.push f p :=
      congrArg (stoch_to_det.push f) (latentPushSndJoint L)

private theorem latentCondEntropyLift
    {p : α × β → ℝ}
    {κ δ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    (L : Latent p) (f : α × β → κ) (g : α × β → δ) :
    condEntropy (fun w : L.ι × (α × β) => f w.2)
        (fun w => g w.2) L.joint = condEntropy f g p := by
  show entropyOf (fun w : L.ι × (α × β) => (f w.2, g w.2)) L.joint
      - entropyOf (fun w : L.ι × (α × β) => g w.2) L.joint
    = entropyOf (fun z => (f z, g z)) p - entropyOf g p
  rw [latentEntropyOfLift L (fun z => (f z, g z)), latentEntropyOfLift L g]

private theorem latentCondMutualInfoLift
    {p : α × β → ℝ}
    {κ δ ε : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    (L : Latent p) (f : α × β → κ) (g : α × β → δ)
    (h : α × β → ε) :
    condMutualInfo (fun w : L.ι × (α × β) => f w.2)
        (fun w => g w.2) (fun w => h w.2) L.joint = condMutualInfo f g h p := by
  show entropyOf (fun w : L.ι × (α × β) => (f w.2, h w.2)) L.joint
      + entropyOf (fun w : L.ι × (α × β) => (g w.2, h w.2)) L.joint
      - entropyOf (fun w : L.ι × (α × β) => (f w.2, g w.2, h w.2)) L.joint
      - entropyOf (fun w : L.ι × (α × β) => h w.2) L.joint
    = entropyOf (fun z => (f z, h z)) p + entropyOf (fun z => (g z, h z)) p
      - entropyOf (fun z => (f z, g z, h z)) p - entropyOf h p
  rw [latentEntropyOfLift L (fun z => (f z, h z)),
    latentEntropyOfLift L (fun z => (g z, h z)),
    latentEntropyOfLift L (fun z => (f z, g z, h z)), latentEntropyOfLift L h]

/- Next, expand both scores in a common set of information coordinates. -/

private noncomputable def threeTermScore
    {Ω ι κ δ : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    (v : Ω → ι) (x : Ω → κ) (y : Ω → δ) (m : Ω → ℝ) : ℝ :=
  stoch_to_det.condMI x y v m
    + stoch_to_det.condMI v x y m
    + stoch_to_det.condMI v y x m

private theorem pairEntropy_comm
    {Ω κ δ : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → κ) (g : Ω → δ) :
    entropyOf (fun ω => (f ω, g ω)) m =
      entropyOf (fun ω => (g ω, f ω)) m := by
  symm
  simpa using entropyOf_equiv hm (fun ω => (f ω, g ω)) (Equiv.prodComm κ δ)

private theorem tripleEntropy_swapLast
    {Ω κ δ ε : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → κ) (g : Ω → δ) (h : Ω → ε) :
    entropyOf (fun ω => (f ω, (g ω, h ω))) m =
      entropyOf (fun ω => (f ω, (h ω, g ω))) m := by
  symm
  simpa using entropyOf_equiv hm (fun ω => (f ω, (g ω, h ω)))
    (Equiv.prodCongr (Equiv.refl κ) (Equiv.prodComm δ ε))

private theorem tripleEntropy_rotate
    {Ω κ δ ε : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → κ) (g : Ω → δ) (h : Ω → ε) :
    entropyOf (fun ω => (f ω, (g ω, h ω))) m =
      entropyOf (fun ω => (h ω, (f ω, g ω))) m := by
  let e : κ × (δ × ε) ≃ ε × (κ × δ) :=
    { toFun := fun a => (a.2.2, (a.1, a.2.1))
      invFun := fun a => (a.2.1, (a.2.2, a.1))
      left_inv := by intro a; rcases a with ⟨a, b, c⟩; rfl
      right_inv := by intro a; rcases a with ⟨c, a, b⟩; rfl }
  symm
  simpa [e] using entropyOf_equiv hm (fun ω => (f ω, (g ω, h ω))) e

private theorem tripleEntropy_reverse
    {Ω κ δ ε : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → κ) (g : Ω → δ) (h : Ω → ε) :
    entropyOf (fun ω => (f ω, (g ω, h ω))) m =
      entropyOf (fun ω => (h ω, (g ω, f ω))) m := by
  let e : κ × (δ × ε) ≃ ε × (δ × κ) :=
    { toFun := fun a => (a.2.2, (a.2.1, a.1))
      invFun := fun a => (a.2.2, (a.2.1, a.1))
      left_inv := by intro a; rcases a with ⟨a, b, c⟩; rfl
      right_inv := by intro a; rcases a with ⟨c, b, a⟩; rfl }
  symm
  simpa [e] using entropyOf_equiv hm (fun ω => (f ω, (g ω, h ω))) e

private theorem threeTermScore_in_pairCoordinates
    {Ω ι κ δ : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m)
    (v : Ω → ι) (x : Ω → κ) (y : Ω → δ) :
    threeTermScore v x y m - mutualInfo x y m =
      3 * mutualInfo v (fun ω => (x ω, y ω)) m
        - 2 * mutualInfo v x m - 2 * mutualInfo v y m := by
  have hxv := pairEntropy_comm hm x v
  have hyv := pairEntropy_comm hm y v
  have hyx := pairEntropy_comm hm y x
  have hxyv := tripleEntropy_rotate hm x y v
  have hvyx := tripleEntropy_swapLast hm v y x
  simp only [entropyOf] at hxv hyv hyx hxyv hvyx
  simp only [threeTermScore, mutualInfo, stoch_to_det.MI, stoch_to_det.condMI]
  rw [hxv, hyv, hyx, hxyv, hvyx]
  ring

private theorem mutualInfo_difference_in_conditionals
    {Ω ι κ δ : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m)
    (g : Ω → ι) (l : Ω → κ) (x : Ω → δ) :
    mutualInfo g x m - mutualInfo l x m =
      condMutualInfo g x l m - condMutualInfo l x g m := by
  have hgl := pairEntropy_comm hm g l
  have hxl := pairEntropy_comm hm x l
  have hxg := pairEntropy_comm hm x g
  have htrip := tripleEntropy_reverse hm g x l
  simp only [entropyOf] at hgl hxl hxg htrip
  simp only [mutualInfo, condMutualInfo, stoch_to_det.MI, stoch_to_det.condMI]
  rw [hgl, hxl, hxg, htrip]
  ring

private theorem entropyOf_encodedGraph
    {Ω κ δ : Type*} [Fintype Ω]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m) (z : Ω → κ) (u : κ → δ) :
    entropyOf (fun ω => (u (z ω), z ω)) m = entropyOf z m := by
  let enc : κ → δ × κ := fun a => (u a, a)
  have h := stoch_to_det.Hvar_eq_of_leftInverse hm z enc Prod.snd (by intro a; rfl)
  simpa [enc, Function.comp_def] using h

private theorem entropyOf_encodedGraph_right
    {Ω ι κ δ : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m)
    (l : Ω → ι) (z : Ω → κ) (u : κ → δ) :
    entropyOf (fun ω => (l ω, (z ω, u (z ω)))) m =
      entropyOf (fun ω => (l ω, z ω)) m := by
  let enc : ι × κ → ι × (κ × δ) := fun a => (a.1, (a.2, u a.2))
  let dec : ι × (κ × δ) → ι × κ := fun a => (a.1, a.2.1)
  have hleft : Function.LeftInverse dec enc := by
    intro a
    rcases a with ⟨a, z⟩
    rfl
  have h := stoch_to_det.Hvar_eq_of_leftInverse hm
    (fun ω => (l ω, z ω)) enc dec hleft
  simpa [enc, Function.comp_def] using h

private theorem deterministicMutualInfo_difference
    {Ω ι κ δ : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m)
    (l : Ω → ι) (z : Ω → κ) (u : κ → δ) :
    mutualInfo (fun ω => u (z ω)) z m - mutualInfo l z m =
      condEntropy (fun ω => u (z ω)) l m -
        condMutualInfo l z (fun ω => u (z ω)) m := by
  have hgz := entropyOf_encodedGraph hm z u
  have hzg :
      entropyOf (fun ω => (z ω, u (z ω))) m = entropyOf z m := by
    rw [pairEntropy_comm hm z (fun ω => u (z ω)), hgz]
  have hlzg := entropyOf_encodedGraph_right hm l z u
  have hgl := pairEntropy_comm hm (fun ω => u (z ω)) l
  simp only [entropyOf] at hgz hzg hlzg hgl
  simp only [mutualInfo, condEntropy, condMutualInfo,
    stoch_to_det.MI, stoch_to_det.condH, stoch_to_det.condMI]
  rw [hgz, hzg, hlzg, hgl]
  ring

private theorem condMutualInfo_chain_pair
    {Ω ι κ δ ε : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (l : Ω → ι) (x : Ω → κ) (y : Ω → δ) (g : Ω → ε) :
    condMutualInfo l (fun ω => (x ω, y ω)) g m =
      condMutualInfo l x g m
        + condMutualInfo l y (fun ω => (x ω, g ω)) m := by
  let e : δ × (κ × ε) ≃ (κ × δ) × ε :=
    { toFun := fun a => ((a.2.1, a.1), a.2.2)
      invFun := fun a => (a.1.2, (a.1.1, a.2))
      left_inv := by intro a; rcases a with ⟨y, x, g⟩; rfl
      right_inv := by intro a; rcases a with ⟨⟨x, y⟩, g⟩; rfl }
  have hyxg :
      entropyOf (fun ω => (y ω, (x ω, g ω))) m =
        entropyOf (fun ω => ((x ω, y ω), g ω)) m := by
    symm
    simpa [e] using entropyOf_equiv hm (fun ω => (y ω, (x ω, g ω))) e
  have hlyxg :
      entropyOf (fun ω => (l ω, (y ω, (x ω, g ω)))) m =
        entropyOf (fun ω => (l ω, ((x ω, y ω), g ω))) m := by
    symm
    simpa [e] using entropyOf_equiv hm (fun ω => (l ω, (y ω, (x ω, g ω))))
      (Equiv.prodCongr (Equiv.refl ι) e)
  simp only [entropyOf] at hyxg hlyxg
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [hyxg, hlyxg]
  ring

private theorem condMutualInfo_relabel
    {Ω ι κ κ' ε : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ']
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (l : Ω → ι) (x : Ω → κ) (g : Ω → ε) (e : κ ≃ κ') :
    condMutualInfo l (fun ω => e (x ω)) g m = condMutualInfo l x g m := by
  have hxg := entropyOf_equiv hm (fun ω => (x ω, g ω))
    (Equiv.prodCongr e (Equiv.refl ε))
  have hlxg := entropyOf_equiv hm (fun ω => (l ω, (x ω, g ω)))
    (Equiv.prodCongr (Equiv.refl ι)
      (Equiv.prodCongr e (Equiv.refl ε)))
  have hxg' :
      entropyOf (fun ω => (e (x ω), g ω)) m =
        entropyOf (fun ω => (x ω, g ω)) m := by
    simpa using hxg
  have hlxg' :
      entropyOf (fun ω => (l ω, (e (x ω), g ω))) m =
        entropyOf (fun ω => (l ω, (x ω, g ω))) m := by
    simpa using hlxg
  simp only [entropyOf] at hxg' hlxg'
  simp only [condMutualInfo, stoch_to_det.condMI]
  rw [hxg', hlxg']

private theorem condEntropy_deterministic_pair_zero
    {Ω ι κ δ : Type*} [Fintype Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    {m : Ω → ℝ} (hm : IsPMF m)
    (x : Ω → κ) (y : Ω → δ) (u : κ × δ → ι) :
    condEntropy (fun ω => u (x ω, y ω))
      (fun ω => (x ω, y ω)) m = 0 := by
  have hgraph := entropyOf_encodedGraph hm (fun ω => (x ω, y ω)) u
  simp only [entropyOf] at hgraph
  simp only [condEntropy, stoch_to_det.condH]
  rw [hgraph]
  ring

private theorem detScore_eq_threeTermScore
    {p : α × β → ℝ} (L : Latent p) (g : Code α β) :
    detScore p g =
      threeTermScore
        (fun w : L.ι × (α × β) => g w.2)
        (fun w => w.2.1) (fun w => w.2.2) L.joint := by
  have hbase :
      detScore p g =
        condMutualInfo
            (fun w : L.ι × (α × β) => w.2.1)
            (fun w => w.2.2) (fun w => g w.2) L.joint
          + condEntropy (fun w => g w.2) (fun w => w.2.1) L.joint
          + condEntropy (fun w => g w.2) (fun w => w.2.2) L.joint := by
    unfold detScore
    rw [latentCondMutualInfoLift L (fun z : α × β => z.1) (fun z => z.2) g,
      latentCondEntropyLift L g (fun z : α × β => z.1),
      latentCondEntropyLift L g (fun z : α × β => z.2)]
  have hzero :
      stoch_to_det.condH (fun w : L.ι × (α × β) => g w.2)
        (fun w => (w.2.1, w.2.2)) L.joint = 0 :=
    condEntropy_deterministic_pair_zero L.joint_isPMF
      (fun w : L.ι × (α × β) => w.2.1) (fun w => w.2.2) g
  have hzero' :
      stoch_to_det.condH (fun w : L.ι × (α × β) => g w.2)
        (fun w => (w.2.2, w.2.1)) L.joint = 0 :=
    condEntropy_deterministic_pair_zero L.joint_isPMF
      (fun w : L.ι × (α × β) => w.2.2) (fun w => w.2.1)
      (fun z : β × α => g (z.2, z.1))
  have hx := stoch_to_det.condMI_eq_condH_sub_pair L.joint_isPMF
    (fun w : L.ι × (α × β) => g w.2)
    (fun w => w.2.1) (fun w => w.2.2)
  have hy := stoch_to_det.condMI_eq_condH_sub_pair L.joint_isPMF
    (fun w : L.ι × (α × β) => g w.2)
    (fun w => w.2.2) (fun w => w.2.1)
  rw [hzero, sub_zero] at hx
  rw [hzero', sub_zero] at hy
  rw [hbase]
  unfold threeTermScore condMutualInfo condEntropy
  rw [hx, hy]
  ring

/-- Exact deterministic-score identity.  It holds for every latent and code;
no stochastic-optimality hypothesis is used. -/
theorem detScore_eq_latentScore_add_w3Cost_sub_rebate
    {p : α × β → ℝ} (L : Latent p) (g : Code α β) :
    detScore p g = L.score + w3Cost L g - 2 * scoreRebate L g := by
  let l : L.ι × (α × β) → L.ι := fun w => w.1
  let x : L.ι × (α × β) → α := fun w => w.2.1
  let y : L.ι × (α × β) → β := fun w => w.2.2
  let z : L.ι × (α × β) → α × β := fun w => w.2
  let encoded : L.ι × (α × β) → Fin (Fintype.card (α × β)) := fun w => g w.2
  have hdet : detScore p g = threeTermScore encoded x y L.joint := by
    simpa [encoded, x, y] using detScore_eq_threeTermScore L g
  have hlatent : L.score = threeTermScore l x y L.joint := by
    rfl
  have hscore_encoded := threeTermScore_in_pairCoordinates L.joint_isPMF encoded x y
  have hscore_l := threeTermScore_in_pairCoordinates L.joint_isPMF l x y
  have hscore :
      threeTermScore encoded x y L.joint - threeTermScore l x y L.joint =
        3 * (mutualInfo encoded z L.joint - mutualInfo l z L.joint)
          - 2 * (mutualInfo encoded x L.joint - mutualInfo l x L.joint)
          - 2 * (mutualInfo encoded y L.joint - mutualInfo l y L.joint) := by
    dsimp [z] at hscore_encoded hscore_l ⊢
    linarith
  have hz := deterministicMutualInfo_difference L.joint_isPMF l z g
  have hx := mutualInfo_difference_in_conditionals L.joint_isPMF encoded l x
  have hy := mutualInfo_difference_in_conditionals L.joint_isPMF encoded l y
  have hchain_x := condMutualInfo_chain_pair L.joint_isPMF l x y encoded
  have hchain_rev := condMutualInfo_chain_pair L.joint_isPMF l y x encoded
  have hswap_pair := condMutualInfo_relabel L.joint_isPMF l
    (fun w => (y w, x w)) encoded (Equiv.prodComm β α)
  have hchain_y :
      condMutualInfo l z encoded L.joint =
        condMutualInfo l y encoded L.joint
          + condMutualInfo l x (fun w => (y w, encoded w)) L.joint := by
    dsimp [z]
    calc
      condMutualInfo l (fun w => (x w, y w)) encoded L.joint =
          condMutualInfo l (fun w => (y w, x w)) encoded L.joint := hswap_pair
      _ = condMutualInfo l y encoded L.joint
          + condMutualInfo l x (fun w => (y w, encoded w)) L.joint := hchain_rev
  rw [hdet, hlatent]
  unfold w3Cost scoreRebate
  dsimp [l, x, y, z, encoded] at hscore hz hx hy hchain_x hchain_y ⊢
  linarith

/-! ## From the identity to an inequality -/

/-- The rebate in the exact identity is nonnegative. -/
theorem scoreRebate_nonneg {p : α × β → ℝ} (L : Latent p)
    (g : Code α β) : 0 ≤ scoreRebate L g := by
  have h₁ := condMutualInfo_nonneg L.joint_isPMF
    (fun w : L.ι × (α × β) => w.1)
    (fun w => w.2.2) (fun w => (w.2.1, g w.2))
  have h₂ := condMutualInfo_nonneg L.joint_isPMF
    (fun w : L.ι × (α × β) => w.1)
    (fun w => w.2.1) (fun w => (w.2.2, g w.2))
  have h₃ := condMutualInfo_nonneg L.joint_isPMF
    (fun w : L.ι × (α × β) => g w.2)
    (fun w => w.2.1) (fun w => w.1)
  have h₄ := condMutualInfo_nonneg L.joint_isPMF
    (fun w : L.ι × (α × β) => g w.2)
    (fun w => w.2.2) (fun w => w.1)
  unfold scoreRebate
  exact add_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) h₄

/-- Dropping the nonnegative rebate gives the pointwise pricing inequality. -/
theorem detScore_le_latentScore_add_w3Cost
    {p : α × β → ℝ} (L : Latent p) (g : Code α β) :
    detScore p g ≤ L.score + w3Cost L g := by
  rw [detScore_eq_latentScore_add_w3Cost_sub_rebate L g]
  have hrebate := scoreRebate_nonneg L g
  linarith

/-! ## Parametric pricing -/

/-- Parametric `w3` pricing.  If `L` attains the stochastic optimum and its
best determinization cost is at most `c * tau p`, then the deterministic
optimum is at most `(1 + c) * tau p`.

The latent itself witnesses that `p` is a probability law, so no separate
`IsPMF p` hypothesis is needed.  No sign hypothesis on `c` is needed beyond
the displayed cost bound. -/
theorem T_le_one_add_mul_tau_of_w3 {p : α × β → ℝ}
    (L : Latent p) (hL_optimal : L.score = tau p)
    (c : ℝ) (hw3 : w3 L ≤ c * tau p) :
    T p ≤ (1 + c) * tau p := by
  obtain ⟨g, hg⟩ := exists_optimalW3Code L
  calc
    T p ≤ detScore p g := T_le_detScore p g
    _ ≤ L.score + w3Cost L g := detScore_le_latentScore_add_w3Cost L g
    _ = tau p + w3 L := by rw [hL_optimal, hg]
    _ ≤ tau p + c * tau p := by linarith
    _ = (1 + c) * tau p := by ring

end StochasticToDeterministicLatents
