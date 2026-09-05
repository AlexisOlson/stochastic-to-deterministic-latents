import StochasticToDeterministicLatents.Pricing
import StochasticToDeterministicLatents.Binary.Table

/-!
# The binary transpose chart and two-code switch

This module fixes a five-scalar chart for a binary law obtained by mixing a
positive table with its transpose.  It also isolates the code-independent
observable information, the reward of a binary deterministic code, and the
exact switch between the constant code and the singleton at `cell10`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

noncomputable section

/-! ## The transpose chart -/

/-- A binary real table specified by its four row-major entries. -/
def tableOfEntries (a b c d : ℝ) : RealTable
  | (0, 0) => a
  | (0, 1) => b
  | (1, 0) => c
  | (1, 1) => d

/-- The transpose of `tableOfEntries a b c d`. -/
def transposeTableOfEntries (a b c d : ℝ) : RealTable :=
  tableOfEntries a c b d

/-- A prior on two labels with mass `pi` assigned to label `1`. -/
def twoPointPrior (pi : ℝ) : Bit → ℝ
  | 0 => 1 - pi
  | 1 => pi

/-- The `pi`-mixture of a binary table and its transpose. -/
def transposeMixtureLaw (a b c d pi : ℝ) : RealTable :=
  fun z =>
    (1 - pi) * tableOfEntries a b c d z
      + pi * transposeTableOfEntries a b c d z

/--
The scalar chart for a positive binary component table, its transpose, and a
minority-label prior.  The order condition is deliberately non-strict.
-/
structure TransposeChart where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  pi : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  d_pos : 0 < d
  total : a + b + c + d = 1
  order : c ≤ b
  pi_pos : 0 < pi
  pi_le_half : pi ≤ 1 / 2

namespace TransposeChart

/-- The first component law of a transpose chart. -/
def firstComponent (D : TransposeChart) : RealTable :=
  tableOfEntries D.a D.b D.c D.d

/-- The transposed second component law of a transpose chart. -/
def secondComponent (D : TransposeChart) : RealTable :=
  transposeTableOfEntries D.a D.b D.c D.d

/-- The two-label prior of a transpose chart. -/
def prior (D : TransposeChart) : Bit → ℝ :=
  twoPointPrior D.pi

/-- The observable mixture law reconstructed from a transpose chart. -/
def law (D : TransposeChart) : RealTable :=
  transposeMixtureLaw D.a D.b D.c D.d D.pi

theorem pi_lt_one (D : TransposeChart) : D.pi < 1 := by
  exact lt_of_le_of_lt D.pi_le_half (by norm_num)

theorem prior_zero (D : TransposeChart) : D.prior 0 = 1 - D.pi :=
  rfl

theorem prior_one (D : TransposeChart) : D.prior 1 = D.pi :=
  rfl

theorem prior_zero_pos (D : TransposeChart) : 0 < D.prior 0 := by
  rw [prior_zero]
  linarith [D.pi_le_half]

theorem prior_one_pos (D : TransposeChart) : 0 < D.prior 1 :=
  D.pi_pos

theorem firstComponent_isPMF (D : TransposeChart) : IsPMF D.firstComponent := by
  refine ⟨?_, ?_⟩
  · intro z
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [firstComponent, tableOfEntries, D.a_pos.le, D.b_pos.le,
        D.c_pos.le, D.d_pos.le]
  · change (∑ z : Cell, tableOfEntries D.a D.b D.c D.d z) = 1
    simp [tableOfEntries, Fintype.sum_prod_type, Fin.sum_univ_two]
    linarith [D.total]

theorem secondComponent_isPMF (D : TransposeChart) : IsPMF D.secondComponent := by
  refine ⟨?_, ?_⟩
  · intro z
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [secondComponent, transposeTableOfEntries, tableOfEntries,
        D.a_pos.le, D.b_pos.le, D.c_pos.le, D.d_pos.le]
  · change (∑ z : Cell, transposeTableOfEntries D.a D.b D.c D.d z) = 1
    simp [transposeTableOfEntries, tableOfEntries,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    linarith [D.total]

theorem prior_isPMF (D : TransposeChart) : IsPMF D.prior := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact D.prior_zero_pos.le
    · exact D.prior_one_pos.le
  · change (∑ i : Bit, twoPointPrior D.pi i) = 1
    simp [twoPointPrior, Fin.sum_univ_two]

theorem law_isPMF (D : TransposeChart) : IsPMF D.law := by
  refine ⟨?_, ?_⟩
  · intro z
    exact add_nonneg
      (mul_nonneg D.prior_zero_pos.le (D.firstComponent_isPMF.nonneg z))
      (mul_nonneg D.prior_one_pos.le (D.secondComponent_isPMF.nonneg z))
  · change
      (∑ z : Cell,
        ((1 - D.pi) * tableOfEntries D.a D.b D.c D.d z
          + D.pi * transposeTableOfEntries D.a D.b D.c D.d z)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hfirst : ∑ z, tableOfEntries D.a D.b D.c D.d z = 1 := by
      simpa [firstComponent, stoch_to_det.mass] using D.firstComponent_isPMF.total
    have hsecond : ∑ z, transposeTableOfEntries D.a D.b D.c D.d z = 1 := by
      simpa [secondComponent, stoch_to_det.mass] using D.secondComponent_isPMF.total
    rw [hfirst, hsecond]
    ring

/-- The binary latent represented by a transpose chart. -/
def latent (D : TransposeChart) : Latent D.law where
  ι := Bit
  fin := inferInstance
  dec := inferInstance
  prior := D.prior
  comp := fun i => if i = 0 then D.firstComponent else D.secondComponent
  prior_isPMF := D.prior_isPMF
  comp_isPMF := by
    intro i
    fin_cases i
    · simpa using D.firstComponent_isPMF
    · simpa using D.secondComponent_isPMF
  mixture := by
    intro z
    simp [law, transposeMixtureLaw, prior, twoPointPrior,
      firstComponent, secondComponent]

end TransposeChart

/-! ## Information reward -/

/-- `I(L;(X,Y))`, the code-independent term in each candidate cost, in bits. -/
noncomputable def observableInfo {p : RealTable} (L : Latent p) : ℝ :=
  mutualInfo (fun w : L.ι × Cell => w.1) (fun w => w.2) L.joint

/-- The binary-code reward `H(g) - 4 H(g|L)`, in bits. -/
noncomputable def codeReward {p : RealTable} (L : Latent p)
    (g : BinaryCode) : ℝ :=
  entropyOf g p
    - 4 * condEntropy (fun w : L.ι × Cell => g w.2) (fun w => w.1) L.joint

private theorem entropyOf_observableLift
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : RealTable} (L : Latent p) (f : Cell → γ) :
    entropyOf (fun w : L.ι × Cell => f w.2) L.joint = entropyOf f p := by
  unfold entropyOf stoch_to_det.Hvar
  congr 1
  calc
    stoch_to_det.push (fun w : L.ι × Cell => f w.2) L.joint =
        stoch_to_det.push f
          (stoch_to_det.push (fun w : L.ι × Cell => w.2) L.joint) := by
      symm
      simpa [Function.comp_def] using
        (stoch_to_det.push_push (fun w : L.ι × Cell => w.2) f L.joint)
    _ = stoch_to_det.push f p := by
      congr 1
      funext z
      unfold stoch_to_det.push
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      simpa [Latent.joint, stoch_to_det.Latent.joint] using L.mixture z

private theorem entropyOf_graphOfFunction
    {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (g : A → B) :
    entropyOf (fun w => (f w, g (f w))) m = entropyOf f m := by
  let enc : A → A × B := fun a => (a, g a)
  have h := stoch_to_det.Hvar_eq_of_leftInverse hm f enc Prod.fst (by intro a; rfl)
  simpa [enc, Function.comp_def] using h

/-- Exact reduction of binary determinization cost to observable information
minus code reward. -/
theorem w3Cost_eq_observableInfo_sub_codeReward {p : RealTable}
    (L : Latent p) (g : BinaryCode) :
    w3Cost L g = observableInfo L - codeReward L g := by
  have hobservableCode :
      entropyOf (fun w : L.ι × Cell => (w.2, g w.2)) L.joint =
        entropyOf (fun w : L.ι × Cell => w.2) L.joint := by
    simpa using entropyOf_graphOfFunction L.joint_isPMF
      (fun w : L.ι × Cell => w.2) g
  have hlatentObservableCode :
      entropyOf (fun w : L.ι × Cell => (w.1, w.2, g w.2)) L.joint =
        entropyOf (fun w : L.ι × Cell => (w.1, w.2)) L.joint := by
    let enc : L.ι × Cell → L.ι × (Cell × Fin (Fintype.card Cell)) :=
      fun w => (w.1, (w.2, g w.2))
    let dec : L.ι × (Cell × Fin (Fintype.card Cell)) → L.ι × Cell :=
      fun w => (w.1, w.2.1)
    have h := stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
      (fun w : L.ι × Cell => (w.1, w.2)) enc dec (by intro w; rfl)
    simpa [enc, dec, Function.comp_def] using h
  have hcodeLift := entropyOf_observableLift L g
  have hcodeLatent :
      entropyOf (fun w : L.ι × Cell => (g w.2, w.1)) L.joint =
        entropyOf (fun w : L.ι × Cell => (w.1, g w.2)) L.joint := by
    simpa using (stoch_to_det.Hvar_equiv L.joint_isPMF
      (fun w : L.ι × Cell => (g w.2, w.1))
      (Equiv.prodComm (Fin (Fintype.card Cell)) L.ι)).symm
  have hobservableCode' :
      stoch_to_det.Hvar (fun w : L.ι × Cell => (w.2, g w.2)) L.joint =
        stoch_to_det.Hvar (fun w : L.ι × Cell => w.2) L.joint :=
    hobservableCode
  have hlatentObservableCode' :
      stoch_to_det.Hvar (fun w : L.ι × Cell => (w.1, w.2, g w.2)) L.joint =
        stoch_to_det.Hvar (fun w : L.ι × Cell => (w.1, w.2)) L.joint :=
    hlatentObservableCode
  have hcodeLift' :
      stoch_to_det.Hvar (fun w : L.ι × Cell => g w.2) L.joint =
        stoch_to_det.Hvar g p :=
    hcodeLift
  have hcodeLatent' :
      stoch_to_det.Hvar (fun w : L.ι × Cell => (g w.2, w.1)) L.joint =
        stoch_to_det.Hvar (fun w : L.ι × Cell => (w.1, g w.2)) L.joint :=
    hcodeLatent
  unfold w3Cost observableInfo codeReward
  unfold condMutualInfo mutualInfo condEntropy
  unfold stoch_to_det.condMI stoch_to_det.MI stoch_to_det.condH
  rw [hobservableCode', hlatentObservableCode', hcodeLift', hcodeLatent']
  ring

/-! ## The exact two-code switch -/

/-- Choose the singleton at `cell10` exactly when its reward is nonnegative;
an exact zero-reward tie goes to the singleton. -/
noncomputable def phaseSelector (D : TransposeChart) : BinaryCode :=
  if 0 ≤ codeReward D.latent (singletonCode cell10) then
    singletonCode cell10
  else
    constantCode

private theorem observableLaw_isPMF {p : RealTable} (L : Latent p) : IsPMF p := by
  refine ⟨?_, ?_⟩
  · intro z
    rw [← L.mixture z]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (L.prior_isPMF.nonneg i) ((L.comp_isPMF i).nonneg z)
  · change (∑ z, p z) = 1
    simp_rw [← L.mixture]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hcomponent : ∀ i, ∑ z, L.comp i z = 1 := fun i => by
      simpa [stoch_to_det.mass] using (L.comp_isPMF i).total
    simp_rw [hcomponent, mul_one]
    simpa [stoch_to_det.mass] using L.prior_isPMF.total

private theorem entropyOf_constantCode
    {p : RealTable} (hp : IsPMF p) : entropyOf constantCode p = 0 := by
  change stoch_to_det.Hvar constantCode p = 0
  have hsum : ∑ z, p z = 1 := by
    simpa [stoch_to_det.mass] using hp.total
  have hunit : stoch_to_det.Hvar (fun _ : Cell => ()) p = 0 := by
    simp [stoch_to_det.Hvar, stoch_to_det.H, stoch_to_det.push,
      stoch_to_det.mass, hsum]
  apply le_antisymm
  · have hle := stoch_to_det.Hvar_comp_le hp (fun _ : Cell => ())
      (fun _ : Unit => constantCode cell00)
    have hfunction :
        (fun _ : Unit => constantCode cell00) ∘ (fun _ : Cell => ()) =
          constantCode := by
      funext z
      apply Fin.ext
      simp [constantCode, StochasticToDeterministicLatents.constantCode]
    rw [hfunction, hunit] at hle
    exact hle
  · unfold stoch_to_det.Hvar
    exact stoch_to_det.H_nonneg_of_isPMF (stoch_to_det.isPMF_push hp)

private theorem condEntropy_constantCode {p : RealTable} (L : Latent p) :
    condEntropy (fun w : L.ι × Cell => constantCode w.2)
      (fun w => w.1) L.joint = 0 := by
  change stoch_to_det.condH (fun w : L.ι × Cell => constantCode w.2)
    (fun w => w.1) L.joint = 0
  have hpair :
      stoch_to_det.Hvar (fun w : L.ι × Cell => (constantCode w.2, w.1)) L.joint =
        stoch_to_det.Hvar (fun w : L.ι × Cell => w.1) L.joint := by
    have hright :
        stoch_to_det.Hvar (fun w : L.ι × Cell => (w.1, constantCode w.2)) L.joint =
          stoch_to_det.Hvar (fun w : L.ι × Cell => w.1) L.joint := by
      simpa [constantCode, StochasticToDeterministicLatents.constantCode] using
        entropyOf_graphOfFunction L.joint_isPMF
          (fun w : L.ι × Cell => w.1)
          (fun _ : L.ι => constantCode cell00)
    have hswap :
        stoch_to_det.Hvar (fun w : L.ι × Cell => (constantCode w.2, w.1)) L.joint =
          stoch_to_det.Hvar (fun w : L.ι × Cell => (w.1, constantCode w.2)) L.joint := by
      simpa using (stoch_to_det.Hvar_equiv L.joint_isPMF
        (fun w : L.ι × Cell => (constantCode w.2, w.1))
        (Equiv.prodComm _ _)).symm
    exact hswap.trans hright
  unfold stoch_to_det.condH
  rw [hpair]
  ring

/-- The constant binary code has zero reward. -/
theorem codeReward_constantCode {p : RealTable} (L : Latent p) :
    codeReward L constantCode = 0 := by
  unfold codeReward
  rw [entropyOf_constantCode (observableLaw_isPMF L), condEntropy_constantCode L]
  ring

/-- The constant binary code has cost exactly equal to the observable
information term. -/
theorem w3Cost_constantCode {p : RealTable} (L : Latent p) :
    w3Cost L constantCode = observableInfo L := by
  rw [w3Cost_eq_observableInfo_sub_codeReward, codeReward_constantCode]
  ring

/-- A nonnegative singleton reward selects the singleton at `cell10`, including
the equality case. -/
theorem phaseSelector_eq_singletonCode_of_codeReward_nonneg
    (D : TransposeChart)
    (h : 0 ≤ codeReward D.latent (singletonCode cell10)) :
    phaseSelector D = singletonCode cell10 := by
  simp [phaseSelector, h]

/-- A negative singleton reward selects the constant code. -/
theorem phaseSelector_eq_constantCode_of_codeReward_neg
    (D : TransposeChart)
    (h : codeReward D.latent (singletonCode cell10) < 0) :
    phaseSelector D = constantCode := by
  simp [phaseSelector, not_le.mpr h]

/-- The phase-selected cost is observable information minus the positive part
of the singleton reward. -/
theorem w3Cost_phaseSelector_eq_observableInfo_sub_max (D : TransposeChart) :
    w3Cost D.latent (phaseSelector D) =
      observableInfo D.latent - max 0 (codeReward D.latent (singletonCode cell10)) := by
  by_cases h : 0 ≤ codeReward D.latent (singletonCode cell10)
  · rw [phaseSelector_eq_singletonCode_of_codeReward_nonneg D h,
      w3Cost_eq_observableInfo_sub_codeReward, max_eq_right h]
  · have hnegative : codeReward D.latent (singletonCode cell10) < 0 :=
      lt_of_not_ge h
    rw [phaseSelector_eq_constantCode_of_codeReward_neg D hnegative,
      w3Cost_constantCode, max_eq_left (le_of_lt hnegative)]
    ring

end

end StochasticToDeterministicLatents.Binary
