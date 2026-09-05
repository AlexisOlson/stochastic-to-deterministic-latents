import StochasticToDeterministicLatents.Binary.Selector
import StochasticToDeterministicLatents.Binary.ContactChart
import StochasticToDeterministicLatents.Binary.TransposeNormalForm

/-!
# Binary catalog recovery

On a full-support binary contact presentation, the two-code chart witness has
an equal-cost representative in the law-only catalog.  The proof first shows
that the tied active-endpoint set is equivariant under every binary-table
symmetry, then transports the constant/singleton witness back to the original
law.  A final adapter keeps the quotient optimizer itself fixed.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

noncomputable section

/-! ## Explicit form of the public catalog and selector -/

/-- The public catalog written with its off-support default made explicit.
Both sides are the public `catalog`; the equality is `canonicalizeRealCode`
agreeing with `constantCode` off support.  It is stated so that the catalog's
two arms can be read without unfolding `canonicalizeRealCode`, and it makes no
comparison with any construction outside this repository. -/
theorem catalog_eq_zeroSupportForm (p : RealTable) :
    catalog p =
      match activeCell? p with
      | none => [constantCode]
      | some z =>
          [constantCode, fun w =>
            if p w = 0 then constantCode w
            else canonicalizeRealCode p (singletonCode z) w] := by
  cases hactive : activeCell? p with
  | none => simp [catalog, hactive]
  | some z =>
      simp only [catalog, hactive]
      congr 2
      funext w
      by_cases hw : p w = 0
      · simp [hw, canonicalizeRealCode_of_eq_zero]
      · simp [hw]

/-- The public selector written with its private score comparison unfolded.
This exhibits the public catalog order and the left-biased final score tie
without unfolding `pickLowerScore`; it compares the selector with nothing
outside this repository. -/
theorem selector_eq_zeroSupportForm (p : RealTable) :
    selector p =
      match activeCell? p with
      | none => constantCode
      | some z =>
          let g : BinaryCode := fun w =>
            if p w = 0 then constantCode w
            else canonicalizeRealCode p (singletonCode z) w
          if detScore p constantCode ≤ detScore p g then constantCode else g := by
  cases hactive : activeCell? p with
  | none => simp [selector, hactive]
  | some z =>
      have hg :
          canonicalizeRealCode p (singletonCode z) =
            (fun w =>
              if p w = 0 then constantCode w
              else canonicalizeRealCode p (singletonCode z) w) := by
        funext w
        by_cases hw : p w = 0
        · simp [hw, canonicalizeRealCode_of_eq_zero]
        · simp [hw]
      simp only [selector, hactive]
      rw [← hg]
      rfl

/-! ## Full-support singleton canonicalization -/

/-- Output-label relabeling needed only for the first row-major singleton. -/
def singletonCanonicalLabelRelabeling (z : Cell) : Fin 4 ≃ Fin 4 :=
  if z = cell00 then Equiv.swap 0 1 else Equiv.refl (Fin 4)

private theorem fullSupport_filter_eq_rowMajorCells
    {p : RealTable} (hpos : ∀ z, 0 < p z) :
    rowMajorCells.filter (realSupported p) = rowMajorCells := by
  simp [realSupported, rowMajorCells,
    (hpos cell00).ne', (hpos cell01).ne',
    (hpos cell10).ne', (hpos cell11).ne']

/-- On full support, singleton canonicalization is only an output-label
relabeling. -/
theorem canonicalizeRealCode_singleton_of_pos
    {p : RealTable} (hpos : ∀ z, 0 < p z) (z : Cell) :
    canonicalizeRealCode p (singletonCode z) =
      relabelCodeLabels (singletonCanonicalLabelRelabeling z) (singletonCode z) := by
  have hsupp := fullSupport_filter_eq_rowMajorCells hpos
  funext w
  change
    (if realSupported p w then
      let cells := rowMajorCells.filter (realSupported p)
      let values := cells.map (singletonCode z)
      let representatives := values.eraseDups
      let labels := values.map fun value => representatives.idxOf value
      ⟨labels.getD (cells.idxOf w) 0 % Fintype.card Cell,
        Nat.mod_lt _ (by decide)⟩
    else constantCode w) =
      relabelCodeLabels (singletonCanonicalLabelRelabeling z) (singletonCode z) w
  rw [hsupp]
  rcases z with ⟨zi, zj⟩
  rcases w with ⟨wi, wj⟩
  fin_cases zi <;> fin_cases zj <;>
    fin_cases wi <;> fin_cases wj <;>
    simp [realSupported, rowMajorCells, singletonCanonicalLabelRelabeling,
      singletonCode, relabelCodeLabels, cell00, cell01, cell10, cell11,
      (hpos _).ne'] <;>
    norm_num [List.idxOf, List.eraseDups] <;> rfl

/-- Full-support singleton canonicalization preserves determinization cost for
the same latent. -/
theorem w3Cost_canonicalizeRealCode_singleton_of_pos
    {p : RealTable} (hpos : ∀ z, 0 < p z)
    (L : Latent p) (z : Cell) :
    w3Cost L (canonicalizeRealCode p (singletonCode z)) =
      w3Cost L (singletonCode z) := by
  rw [canonicalizeRealCode_singleton_of_pos hpos z]
  exact w3Cost_relabelCodeLabels L
    (singletonCanonicalLabelRelabeling z) (singletonCode z)

@[simp] theorem constantCode_mem_catalog (p : RealTable) :
    constantCode ∈ catalog p := by
  cases h : activeCell? p <;> simp [catalog, h]

/-- The support-canonicalized active singleton is the literal second catalog
arm. -/
theorem canonicalized_activeSingleton_mem_catalog
    {p : RealTable} {z : Cell} (hz : activeCell? p = some z) :
    canonicalizeRealCode p (singletonCode z) ∈ catalog p := by
  simp [catalog, hz]

/-! ## Equivariant active endpoints -/

/-- Symmetry-equivariant active endpoint set; an endpoint-mass tie retains
both endpoints. -/
def activeEndpointOrbit (p : RealTable) : Finset Cell :=
  if diagonalProduct p = offDiagonalProduct p then
    ∅
  else if offDiagonalProduct p < diagonalProduct p then
    if p cell00 = p cell11 then {cell00, cell11}
    else {lowerMassEndpoint p cell00 cell11}
  else if p cell01 = p cell10 then {cell01, cell10}
  else {lowerMassEndpoint p cell01 cell10}

/-- The row-major active endpoint belongs to the equivariant endpoint set. -/
theorem activeCell_mem_activeEndpointOrbit
    {p : RealTable} {z : Cell} (hz : activeCell? p = some z) :
    z ∈ activeEndpointOrbit p := by
  unfold activeCell? at hz
  unfold activeEndpointOrbit
  split_ifs at hz ⊢ <;> simp_all [lowerMassEndpoint]

/-- A nonempty active-endpoint set has the row-major representative selected
by `activeCell?`. -/
theorem exists_activeCell_of_activeEndpointOrbit_nonempty
    {p : RealTable} (h : (activeEndpointOrbit p).Nonempty) :
    ∃ z, activeCell? p = some z := by
  unfold activeEndpointOrbit at h
  unfold activeCell?
  split_ifs at h ⊢ <;> simp_all [lowerMassEndpoint]

/-- The active endpoint set of a relabeled table is the image of the original
active endpoint set: the set is equivariant, not invariant, under every table
symmetry. -/
def ActiveEndpointOrbitTransport : Prop :=
  ∀ (r : TableSymmetry) (p : RealTable),
    activeEndpointOrbit (pushforward r.equiv p) =
      (activeEndpointOrbit p).image r.equiv

private abbrev IsLowerEndpoint
    (p : RealTable) (a b z : Cell) : Prop :=
  (z = a ∧ p a ≤ p b) ∨ (z = b ∧ p b ≤ p a)

private theorem isLowerEndpoint_comm
    (p : RealTable) (a b z : Cell) :
    IsLowerEndpoint p a b z ↔ IsLowerEndpoint p b a z := by
  unfold IsLowerEndpoint
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

private theorem isLowerEndpoint_pushforward
    (e : Cell ≃ Cell) (p : RealTable) (a b z : Cell) :
    IsLowerEndpoint (pushforward e p) (e a) (e b) (e z) ↔
      IsLowerEndpoint p a b z := by
  simp [IsLowerEndpoint, pushforward_apply_equiv]

private theorem mem_tiedEndpointSet_iff
    (p : RealTable) (a b z : Cell) :
    z ∈ (if p a = p b then ({a, b} : Finset Cell)
         else {lowerMassEndpoint p a b}) ↔
      IsLowerEndpoint p a b z := by
  rcases lt_trichotomy (p a) (p b) with h | h | h
  · have hne : p a ≠ p b := ne_of_lt h
    have hnba : ¬p b ≤ p a := not_le_of_gt h
    simp [IsLowerEndpoint, lowerMassEndpoint, hne, h.le, hnba]
  · simp [IsLowerEndpoint, h]
  · have hne : p a ≠ p b := ne_of_gt h
    have hnab : ¬p a ≤ p b := not_le_of_gt h
    simp [IsLowerEndpoint, lowerMassEndpoint, hne, hnab, h.le]

private theorem mem_activeEndpointOrbit_iff
    (p : RealTable) (z : Cell) :
    z ∈ activeEndpointOrbit p ↔
      (offDiagonalProduct p < diagonalProduct p ∧
        IsLowerEndpoint p cell00 cell11 z) ∨
      (diagonalProduct p < offDiagonalProduct p ∧
        IsLowerEndpoint p cell01 cell10 z) := by
  unfold activeEndpointOrbit
  by_cases hEq : diagonalProduct p = offDiagonalProduct p
  · simp [hEq]
  · by_cases hMain : offDiagonalProduct p < diagonalProduct p
    · simp only [if_neg hEq, if_pos hMain]
      rw [mem_tiedEndpointSet_iff]
      have hNotOff : ¬diagonalProduct p < offDiagonalProduct p :=
        not_lt_of_ge hMain.le
      simp [hMain, hNotOff]
    · have hOff : diagonalProduct p < offDiagonalProduct p :=
        lt_of_le_of_ne (le_of_not_gt hMain) hEq
      simp only [if_neg hEq, if_neg hMain]
      rw [mem_tiedEndpointSet_iff]
      simp [hMain, hOff]

private theorem diagonalProduct_swapRows (p : RealTable) :
    diagonalProduct (pushforward swapRowsCell p) = offDiagonalProduct p := by
  unfold diagonalProduct offDiagonalProduct
  rw [pushforward_apply_equiv, pushforward_apply_equiv]
  simp [swapRowsCell, bitFlip, cell00, cell01, cell10, cell11]
  ring

private theorem offDiagonalProduct_swapRows (p : RealTable) :
    offDiagonalProduct (pushforward swapRowsCell p) = diagonalProduct p := by
  unfold diagonalProduct offDiagonalProduct
  rw [pushforward_apply_equiv, pushforward_apply_equiv]
  simp [swapRowsCell, bitFlip, cell00, cell01, cell10, cell11]
  ring

private theorem diagonalProduct_swapColumns (p : RealTable) :
    diagonalProduct (pushforward swapColumnsCell p) = offDiagonalProduct p := by
  unfold diagonalProduct offDiagonalProduct
  rw [pushforward_apply_equiv, pushforward_apply_equiv]
  simp [swapColumnsCell, bitFlip, cell00, cell01, cell10, cell11]

private theorem offDiagonalProduct_swapColumns (p : RealTable) :
    offDiagonalProduct (pushforward swapColumnsCell p) = diagonalProduct p := by
  unfold diagonalProduct offDiagonalProduct
  rw [pushforward_apply_equiv, pushforward_apply_equiv]
  simp [swapColumnsCell, bitFlip, cell00, cell01, cell10, cell11]

private theorem diagonalProduct_transpose (p : RealTable) :
    diagonalProduct (pushforward transposeCell p) = diagonalProduct p := by
  unfold diagonalProduct
  rw [pushforward_apply_equiv, pushforward_apply_equiv]
  simp [transposeCell, cell00, cell11]

private theorem offDiagonalProduct_transpose (p : RealTable) :
    offDiagonalProduct (pushforward transposeCell p) = offDiagonalProduct p := by
  unfold offDiagonalProduct
  rw [pushforward_apply_equiv, pushforward_apply_equiv]
  simp [transposeCell, cell01, cell10]
  ring

private theorem isLowerEndpoint_swapRows_main
    (p : RealTable) (z : Cell) :
    IsLowerEndpoint (pushforward swapRowsCell p) cell00 cell11 z ↔
      IsLowerEndpoint p cell01 cell10 (swapRowsCell.symm z) := by
  have h := isLowerEndpoint_pushforward swapRowsCell p
    cell10 cell01 (swapRowsCell.symm z)
  rw [swapRowsCell.apply_symm_apply] at h
  have hs := isLowerEndpoint_comm p cell10 cell01 (swapRowsCell.symm z)
  simpa [swapRowsCell, bitFlip, cell00, cell01, cell10, cell11]
    using h.trans hs

private theorem isLowerEndpoint_swapRows_off
    (p : RealTable) (z : Cell) :
    IsLowerEndpoint (pushforward swapRowsCell p) cell01 cell10 z ↔
      IsLowerEndpoint p cell00 cell11 (swapRowsCell.symm z) := by
  have h := isLowerEndpoint_pushforward swapRowsCell p
    cell11 cell00 (swapRowsCell.symm z)
  rw [swapRowsCell.apply_symm_apply] at h
  have hs := isLowerEndpoint_comm p cell11 cell00 (swapRowsCell.symm z)
  simpa [swapRowsCell, bitFlip, cell00, cell01, cell10, cell11]
    using h.trans hs

private theorem isLowerEndpoint_swapColumns_main
    (p : RealTable) (z : Cell) :
    IsLowerEndpoint (pushforward swapColumnsCell p) cell00 cell11 z ↔
      IsLowerEndpoint p cell01 cell10 (swapColumnsCell.symm z) := by
  have h := isLowerEndpoint_pushforward swapColumnsCell p
    cell01 cell10 (swapColumnsCell.symm z)
  rw [swapColumnsCell.apply_symm_apply] at h
  simpa [swapColumnsCell, bitFlip, cell00, cell01, cell10, cell11] using h

private theorem isLowerEndpoint_swapColumns_off
    (p : RealTable) (z : Cell) :
    IsLowerEndpoint (pushforward swapColumnsCell p) cell01 cell10 z ↔
      IsLowerEndpoint p cell00 cell11 (swapColumnsCell.symm z) := by
  have h := isLowerEndpoint_pushforward swapColumnsCell p
    cell00 cell11 (swapColumnsCell.symm z)
  rw [swapColumnsCell.apply_symm_apply] at h
  simpa [swapColumnsCell, bitFlip, cell00, cell01, cell10, cell11] using h

private theorem isLowerEndpoint_transpose_main
    (p : RealTable) (z : Cell) :
    IsLowerEndpoint (pushforward transposeCell p) cell00 cell11 z ↔
      IsLowerEndpoint p cell00 cell11 (transposeCell.symm z) := by
  simpa [transposeCell, cell00, cell11]
    using isLowerEndpoint_pushforward transposeCell p
      cell00 cell11 (transposeCell.symm z)

private theorem isLowerEndpoint_transpose_off
    (p : RealTable) (z : Cell) :
    IsLowerEndpoint (pushforward transposeCell p) cell01 cell10 z ↔
      IsLowerEndpoint p cell01 cell10 (transposeCell.symm z) := by
  have h := isLowerEndpoint_pushforward transposeCell p
    cell10 cell01 (transposeCell.symm z)
  have hs := isLowerEndpoint_comm p cell10 cell01 (transposeCell.symm z)
  simpa [transposeCell, cell01, cell10] using h.trans hs

private theorem mem_activeEndpointOrbit_swapRows (p : RealTable) (z : Cell) :
    z ∈ activeEndpointOrbit (pushforward swapRowsCell p) ↔
      swapRowsCell.symm z ∈ activeEndpointOrbit p := by
  rw [mem_activeEndpointOrbit_iff, mem_activeEndpointOrbit_iff,
    diagonalProduct_swapRows, offDiagonalProduct_swapRows,
    isLowerEndpoint_swapRows_main, isLowerEndpoint_swapRows_off]
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

private theorem mem_activeEndpointOrbit_swapColumns (p : RealTable) (z : Cell) :
    z ∈ activeEndpointOrbit (pushforward swapColumnsCell p) ↔
      swapColumnsCell.symm z ∈ activeEndpointOrbit p := by
  rw [mem_activeEndpointOrbit_iff, mem_activeEndpointOrbit_iff,
    diagonalProduct_swapColumns, offDiagonalProduct_swapColumns,
    isLowerEndpoint_swapColumns_main, isLowerEndpoint_swapColumns_off]
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

private theorem mem_activeEndpointOrbit_transpose (p : RealTable) (z : Cell) :
    z ∈ activeEndpointOrbit (pushforward transposeCell p) ↔
      transposeCell.symm z ∈ activeEndpointOrbit p := by
  rw [mem_activeEndpointOrbit_iff, mem_activeEndpointOrbit_iff,
    diagonalProduct_transpose, offDiagonalProduct_transpose,
    isLowerEndpoint_transpose_main, isLowerEndpoint_transpose_off]

private theorem pushforward_refl (p : RealTable) :
    pushforward (Equiv.refl Cell) p = p := by
  funext z
  rw [pushforward_apply_equiv]
  rfl

private theorem mem_activeEndpointOrbit_refl (p : RealTable) (z : Cell) :
    z ∈ activeEndpointOrbit (pushforward (Equiv.refl Cell) p) ↔
      (Equiv.refl Cell).symm z ∈ activeEndpointOrbit p := by
  rw [pushforward_refl]
  rfl

private theorem mem_image_equiv_iff
    (e : Cell ≃ Cell) (s : Finset Cell) (z : Cell) :
    z ∈ s.image e ↔ e.symm z ∈ s := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hz
    exact ⟨e.symm z, hz, e.apply_symm_apply z⟩

private theorem activeEndpointOrbit_refl (p : RealTable) :
    activeEndpointOrbit (pushforward (Equiv.refl Cell) p) =
      (activeEndpointOrbit p).image (Equiv.refl Cell) := by
  apply Finset.ext
  intro z
  rw [mem_image_equiv_iff]
  exact mem_activeEndpointOrbit_refl p z

private theorem activeEndpointOrbit_swapRows (p : RealTable) :
    activeEndpointOrbit (pushforward swapRowsCell p) =
      (activeEndpointOrbit p).image swapRowsCell := by
  apply Finset.ext
  intro z
  rw [mem_image_equiv_iff]
  exact mem_activeEndpointOrbit_swapRows p z

private theorem activeEndpointOrbit_swapColumns (p : RealTable) :
    activeEndpointOrbit (pushforward swapColumnsCell p) =
      (activeEndpointOrbit p).image swapColumnsCell := by
  apply Finset.ext
  intro z
  rw [mem_image_equiv_iff]
  exact mem_activeEndpointOrbit_swapColumns p z

private theorem activeEndpointOrbit_transpose (p : RealTable) :
    activeEndpointOrbit (pushforward transposeCell p) =
      (activeEndpointOrbit p).image transposeCell := by
  apply Finset.ext
  intro z
  rw [mem_image_equiv_iff]
  exact mem_activeEndpointOrbit_transpose p z

/-- The active endpoint orbit commutes with every binary-table symmetry. -/
theorem activeEndpointOrbit_pushforward : ActiveEndpointOrbitTransport := by
  intro r
  induction r with
  | refl =>
      intro p
      simpa [TableSymmetry.equiv] using activeEndpointOrbit_refl p
  | swapRows =>
      intro p
      simpa [TableSymmetry.equiv] using activeEndpointOrbit_swapRows p
  | swapColumns =>
      intro p
      simpa [TableSymmetry.equiv] using activeEndpointOrbit_swapColumns p
  | transpose =>
      intro p
      simpa [TableSymmetry.equiv] using activeEndpointOrbit_transpose p
  | comp first second ihFirst ihSecond =>
      intro p
      rw [TableSymmetry.equiv, pushforward_trans, ihSecond, ihFirst]
      simp only [Finset.image_image]
      rfl

/-! ## Transpose-chart endpoint geometry -/

private theorem transposeChart_law_cells (D : TransposeChart) :
    D.law cell00 = D.a ∧
    D.law cell01 = (1 - D.pi) * D.b + D.pi * D.c ∧
    D.law cell10 = (1 - D.pi) * D.c + D.pi * D.b ∧
    D.law cell11 = D.d := by
  constructor
  · simp [TransposeChart.law, transposeMixtureLaw, tableOfEntries,
      transposeTableOfEntries, cell00]
    ring
  · constructor
    · simp [TransposeChart.law, transposeMixtureLaw, tableOfEntries,
        transposeTableOfEntries, cell01]
    · constructor
      · simp [TransposeChart.law, transposeMixtureLaw, tableOfEntries,
          transposeTableOfEntries, cell10]
      · simp [TransposeChart.law, transposeMixtureLaw, tableOfEntries,
          transposeTableOfEntries, cell11]
        ring

private theorem transposeChart_diagonalProduct (D : TransposeChart) :
    diagonalProduct D.law = D.a * D.d := by
  rcases transposeChart_law_cells D with ⟨h00, _, _, h11⟩
  simp [diagonalProduct, h00, h11]

private theorem transposeChart_offDiagonalProduct (D : TransposeChart) :
    offDiagonalProduct D.law =
      D.b * D.c + D.pi * (1 - D.pi) * (D.b - D.c) ^ 2 := by
  rcases transposeChart_law_cells D with ⟨_, h01, h10, _⟩
  rw [offDiagonalProduct, h01, h10]
  ring

private theorem transposeChart_law01_sub_law10 (D : TransposeChart) :
    D.law cell01 - D.law cell10 =
      (1 - 2 * D.pi) * (D.b - D.c) := by
  rcases transposeChart_law_cells D with ⟨_, h01, h10, _⟩
  rw [h01, h10]
  ring

private theorem transposeChart_offDiagonalProduct_gt
    (D : TransposeChart) (hbc : D.c < D.b)
    (hdet : D.a * D.d < D.b * D.c) :
    diagonalProduct D.law < offDiagonalProduct D.law := by
  rw [transposeChart_diagonalProduct, transposeChart_offDiagonalProduct]
  have hpi1 : 0 < 1 - D.pi := by linarith [D.pi_lt_one]
  have hsq : 0 < (D.b - D.c) ^ 2 := sq_pos_of_pos (sub_pos.mpr hbc)
  have hadd : 0 < D.pi * (1 - D.pi) * (D.b - D.c) ^ 2 :=
    mul_pos (mul_pos D.pi_pos hpi1) hsq
  linarith

private theorem transposeChart_activeOrbit_of_pi_lt_half
    (D : TransposeChart) (hpi : D.pi < 1 / 2)
    (hbc : D.c < D.b) (hdet : D.a * D.d < D.b * D.c) :
    activeEndpointOrbit D.law = {cell10} := by
  have hprod := transposeChart_offDiagonalProduct_gt D hbc hdet
  have hmass : D.law cell10 < D.law cell01 := by
    rw [← sub_pos]
    rw [transposeChart_law01_sub_law10]
    exact mul_pos (by linarith) (sub_pos.mpr hbc)
  simp [activeEndpointOrbit, hprod.ne, not_lt_of_ge hprod.le,
    hmass.ne', lowerMassEndpoint, not_le_of_gt hmass]

private theorem transposeChart_activeOrbit_of_pi_eq_half
    (D : TransposeChart) (hpi : D.pi = 1 / 2)
    (hbc : D.c < D.b) (hdet : D.a * D.d < D.b * D.c) :
    activeEndpointOrbit D.law = {cell01, cell10} := by
  have hprod := transposeChart_offDiagonalProduct_gt D hbc hdet
  have hmass : D.law cell01 = D.law cell10 := by
    have hdiff := transposeChart_law01_sub_law10 D
    rw [hpi] at hdiff
    norm_num at hdiff
    linarith
  simp [activeEndpointOrbit, hprod.ne, not_lt_of_ge hprod.le, hmass]

/-! ## Half-prior transpose symmetry -/

/-- At prior `1 / 2`, observable transpose equals latent-label flip on the
joint law. -/
theorem halfPrior_transpose_joint_eq_reindex
    (D : TransposeChart) (hpi : D.pi = 1 / 2) :
    (Latent.relabel transposeCell D.latent).joint =
      (Latent.reindex D.latent bitFlip).joint := by
  funext w
  rcases w with ⟨i, z⟩
  rcases z with ⟨x, y⟩
  change
    D.latent.prior i * pushforward transposeCell (D.latent.comp i) (x, y) =
      D.latent.prior (bitFlip i) * D.latent.comp (bitFlip i) (x, y)
  rw [pushforward_apply_equiv]
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    simp [TransposeChart.latent, TransposeChart.prior, twoPointPrior,
      TransposeChart.firstComponent, TransposeChart.secondComponent,
      tableOfEntries, transposeTableOfEntries, transposeCell, bitFlip, hpi]
  all_goals norm_num

/-- The two off-diagonal singleton arms have equal cost at prior `1 / 2`. -/
theorem halfPrior_singleton10_w3Cost_eq_singleton01
    (D : TransposeChart) (hpi : D.pi = 1 / 2) :
    w3Cost D.latent (singletonCode cell10) =
      w3Cost D.latent (singletonCode cell01) := by
  have htransport :
      w3Cost (Latent.relabel transposeCell D.latent) (singletonCode cell01) =
        w3Cost D.latent (singletonCode cell10) := by
    simpa [transportCode_singletonCode, cell10, cell01, transposeCell] using
      w3Cost_relabel transposeCell D.latent (singletonCode cell10)
  have hjoint := halfPrior_transpose_joint_eq_reindex D hpi
  have hJointCost :
      w3Cost (Latent.relabel transposeCell D.latent) (singletonCode cell01) =
        w3Cost (Latent.reindex D.latent bitFlip) (singletonCode cell01) := by
    unfold w3Cost
    rw [hjoint]
    rfl
  calc
    w3Cost D.latent (singletonCode cell10) =
        w3Cost (Latent.relabel transposeCell D.latent)
          (singletonCode cell01) := htransport.symm
    _ = w3Cost (Latent.reindex D.latent bitFlip)
          (singletonCode cell01) := hJointCost
    _ = w3Cost D.latent (singletonCode cell01) :=
      w3Cost_reindex D.latent bitFlip (singletonCode cell01)

/-! ## Joint presentations -/

/-- A latent-label presentation of a chart preserves every fixed-code cost. -/
theorem w3Cost_eq_of_jointPresentation
    {p : RealTable} (L : Latent p) (D : TransposeChart)
    (u : L.ι ≃ D.latent.ι)
    (hjoint : L.joint = (Latent.reindex D.latent u).joint)
    (g : BinaryCode) :
    w3Cost L g = w3Cost D.latent g := by
  have hJointCost :
      w3Cost L g = w3Cost (Latent.reindex D.latent u) g := by
    unfold w3Cost
    rw [hjoint]
    rfl
  exact hJointCost.trans (w3Cost_reindex D.latent u g)

/-- A latent-label presentation of a chart preserves optimal determinization
cost. -/
theorem w3_eq_of_jointPresentation
    {p : RealTable} (L : Latent p) (D : TransposeChart)
    (u : L.ι ≃ D.latent.ι)
    (hjoint : L.joint = (Latent.reindex D.latent u).joint) :
    w3 L = w3 D.latent := by
  apply le_antisymm
  · obtain ⟨g, hg⟩ := exists_optimalW3Code D.latent
    calc
      w3 L ≤ w3Cost L g := w3_le_w3Cost L g
      _ = w3Cost D.latent g := w3Cost_eq_of_jointPresentation L D u hjoint g
      _ = w3 D.latent := hg
  · obtain ⟨g, hg⟩ := exists_optimalW3Code L
    calc
      w3 D.latent ≤ w3Cost D.latent g := w3_le_w3Cost D.latent g
      _ = w3Cost L g := (w3Cost_eq_of_jointPresentation L D u hjoint g).symm
      _ = w3 L := hg

/-! ## Same-witness catalog recovery -/

/-- Pulling a presented transpose chart back to a full-support law produces a
catalog code with exactly the chart-selected cost, without changing the seed
setup witness. -/
theorem exists_catalogCode_of_transposeChartPresentation
    {p : RealTable} (hp : IsPMF p) (hpos : ∀ z, 0 < p z)
    (r : TableSymmetry)
    (S : SeedSetup (pushforward r.equiv p))
    (D : TransposeChart)
    (hLaw : pushforward r.equiv p = D.law)
    (u : S.L.ι ≃ D.latent.ι)
    (hjoint : S.L.joint = (Latent.reindex D.latent u).joint)
    (hbc : D.c < D.b)
    (hdet : D.a * D.d < D.b * D.c) :
    ∃ (S₀ : SeedSetup p) (g : BinaryCode),
      S₀ = SeedSetup.pullback r S hp hpos ∧
      S₀.L = Latent.pullback r.equiv S.L ∧
      S₀.w = pushforward r.equiv.symm S.w ∧
      g ∈ catalog p ∧
      w3 S₀.L = w3 D.latent ∧
      w3Cost S₀.L g =
        w3Cost S₀.L (transportCode r.equiv.symm (phaseSelector D)) ∧
      w3Cost S₀.L g = w3Cost D.latent (phaseSelector D) := by
  let S₀ := SeedSetup.pullback r S hp hpos
  have hW3 : w3 S₀.L = w3 D.latent := by
    calc
      w3 S₀.L = w3 S.L := w3_pullback r.equiv S.L
      _ = w3 D.latent := w3_eq_of_jointPresentation S.L D u hjoint
  by_cases hphase : 0 ≤ codeReward D.latent (singletonCode cell10)
  · have hphaseEq : phaseSelector D = singletonCode cell10 :=
      phaseSelector_eq_singletonCode_of_codeReward_nonneg D hphase
    have hpiCases : D.pi < 1 / 2 ∨ D.pi = 1 / 2 :=
      lt_or_eq_of_le D.pi_le_half
    have hOrbitLaw :
        activeEndpointOrbit D.law =
          (activeEndpointOrbit p).image r.equiv := by
      rw [← hLaw]
      exact activeEndpointOrbit_pushforward r p
    have hChartNonempty : (activeEndpointOrbit D.law).Nonempty := by
      rcases hpiCases with hpi | hpi
      · rw [transposeChart_activeOrbit_of_pi_lt_half D hpi hbc hdet]
        simp
      · rw [transposeChart_activeOrbit_of_pi_eq_half D hpi hbc hdet]
        simp
    have hOriginalNonempty : (activeEndpointOrbit p).Nonempty := by
      rw [hOrbitLaw] at hChartNonempty
      simpa using hChartNonempty
    obtain ⟨z, hzActive⟩ :=
      exists_activeCell_of_activeEndpointOrbit_nonempty hOriginalNonempty
    have hzOrbit := activeCell_mem_activeEndpointOrbit hzActive
    have hzImage : r.equiv z ∈ activeEndpointOrbit D.law := by
      rw [hOrbitLaw]
      exact Finset.mem_image.mpr ⟨z, hzOrbit, rfl⟩
    let g := canonicalizeRealCode p (singletonCode z)
    have hgMem : g ∈ catalog p :=
      canonicalized_activeSingleton_mem_catalog hzActive
    have hCanon :
        w3Cost S₀.L g = w3Cost S₀.L (singletonCode z) :=
      w3Cost_canonicalizeRealCode_singleton_of_pos hpos S₀.L z
    have hPull :
        w3Cost S₀.L (singletonCode z) =
          w3Cost S.L (singletonCode (r.equiv z)) := by
      change w3Cost (Latent.pullback r.equiv S.L) (singletonCode z) = _
      rw [w3Cost_pullback, transportCode_singletonCode]
    have hPresent :
        w3Cost S.L (singletonCode (r.equiv z)) =
          w3Cost D.latent (singletonCode (r.equiv z)) :=
      w3Cost_eq_of_jointPresentation S.L D u hjoint _
    have hChartCost :
        w3Cost D.latent (singletonCode (r.equiv z)) =
          w3Cost D.latent (singletonCode cell10) := by
      rcases hpiCases with hpi | hpi
      · have hOrbitStrict :=
          transposeChart_activeOrbit_of_pi_lt_half D hpi hbc hdet
        rw [hOrbitStrict] at hzImage
        have hz : r.equiv z = cell10 := by simpa using hzImage
        simp [hz]
      · have hOrbitHalf :=
          transposeChart_activeOrbit_of_pi_eq_half D hpi hbc hdet
        rw [hOrbitHalf] at hzImage
        have hz : r.equiv z = cell01 ∨ r.equiv z = cell10 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hzImage
        rcases hz with hz | hz
        · simpa [hz] using
            (halfPrior_singleton10_w3Cost_eq_singleton01 D hpi).symm
        · simp [hz]
    have hPhaseCost :
        w3Cost S₀.L g = w3Cost D.latent (phaseSelector D) := by
      rw [hCanon, hPull, hPresent, hChartCost, hphaseEq]
    have hRawCost :
        w3Cost S₀.L g =
          w3Cost S₀.L (transportCode r.equiv.symm (phaseSelector D)) := by
      calc
        w3Cost S₀.L g = w3Cost D.latent (phaseSelector D) := hPhaseCost
        _ = w3Cost S.L (phaseSelector D) :=
          (w3Cost_eq_of_jointPresentation S.L D u hjoint _).symm
        _ = w3Cost S₀.L
            (transportCode r.equiv.symm (phaseSelector D)) := by
          change w3Cost S.L (phaseSelector D) =
            w3Cost (Latent.pullback r.equiv S.L)
              (transportCode r.equiv.symm (phaseSelector D))
          exact (w3Cost_pullback_inverse r.equiv S.L _).symm
    exact ⟨S₀, g, rfl, rfl, rfl, hgMem, hW3, hRawCost, hPhaseCost⟩
  · have hnegative : codeReward D.latent (singletonCode cell10) < 0 :=
      lt_of_not_ge hphase
    have hphaseEq : phaseSelector D = constantCode :=
      phaseSelector_eq_constantCode_of_codeReward_neg D hnegative
    let g := constantCode
    have hgMem : g ∈ catalog p := constantCode_mem_catalog p
    have hPull : w3Cost S₀.L g = w3Cost S.L constantCode := by
      change w3Cost (Latent.pullback r.equiv S.L) constantCode = _
      rw [w3Cost_pullback, transportCode_constantCode]
    have hPresent : w3Cost S.L constantCode = w3Cost D.latent constantCode :=
      w3Cost_eq_of_jointPresentation S.L D u hjoint constantCode
    have hPhaseCost :
        w3Cost S₀.L g = w3Cost D.latent (phaseSelector D) := by
      rw [hPull, hPresent, hphaseEq]
    have hRawCost :
        w3Cost S₀.L g =
          w3Cost S₀.L (transportCode r.equiv.symm (phaseSelector D)) := by
      calc
        w3Cost S₀.L g = w3Cost D.latent (phaseSelector D) := hPhaseCost
        _ = w3Cost S.L (phaseSelector D) :=
          (w3Cost_eq_of_jointPresentation S.L D u hjoint _).symm
        _ = w3Cost S₀.L
            (transportCode r.equiv.symm (phaseSelector D)) := by
          change w3Cost S.L (phaseSelector D) =
            w3Cost (Latent.pullback r.equiv S.L)
              (transportCode r.equiv.symm (phaseSelector D))
          exact (w3Cost_pullback_inverse r.equiv S.L _).symm
    exact ⟨S₀, g, rfl, rfl, rfl, hgMem, hW3, hRawCost, hPhaseCost⟩

/-! ## Quotient presentation adapter -/

/-- The duplicate quotient, relabeled by a contact presentation's table
symmetry. -/
def orientedQuotientSetup
    {p : RealTable} (hpos : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D)
    (M : ContactPresentation p) :
    SeedSetup (pushforward M.relabel.equiv p) :=
  SeedSetup.relabel K.quotientSeedSetup hpos M.relabel

/-- Componentwise presentation of the oriented quotient by the contact chart,
including the latent-label orientation. -/
structure QuotientPresentation
    {p : RealTable} (hpos : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D)
    (M : ContactPresentation p) where
  labelEquiv :
    (orientedQuotientSetup hpos D K M).L.ι ≃
      M.chart.toTransposeChart.latent.ι
  prior_eq : ∀ v,
    (orientedQuotientSetup hpos D K M).L.prior v =
      M.chart.toTransposeChart.latent.prior (labelEquiv v)
  component_eq : ∀ v z,
    (orientedQuotientSetup hpos D K M).L.comp v z =
      M.chart.toTransposeChart.latent.comp (labelEquiv v) z

/-- The componentwise quotient presentation identifies the two joint laws. -/
theorem QuotientPresentation.joint_eq_reindex
    {p : RealTable} {hpos : ∀ z, 0 < p z}
    {D : SeedSetup p} {K : Clustering D}
    {M : ContactPresentation p}
    (P : QuotientPresentation hpos D K M) :
    (orientedQuotientSetup hpos D K M).L.joint =
      (Latent.reindex M.chart.toTransposeChart.latent P.labelEquiv).joint := by
  funext w
  rcases w with ⟨v, z⟩
  change
    (orientedQuotientSetup hpos D K M).L.prior v *
        (orientedQuotientSetup hpos D K M).L.comp v z =
      M.chart.toTransposeChart.latent.prior (P.labelEquiv v) *
        M.chart.toTransposeChart.latent.comp (P.labelEquiv v) z
  rw [P.prior_eq, P.component_eq]

/-- Strict contact coordinates imply the strict diagonal-product gap used by
catalog recovery. -/
theorem ContactChart.diagonalProduct_lt_offDiagonalProduct
    (C : ContactChart) :
    C.toTransposeChart.a * C.toTransposeChart.d <
      C.toTransposeChart.b * C.toTransposeChart.c := by
  rw [C.a_eq, C.b_eq, C.c_eq, C.d_eq]
  have hnorm0 : C.norm ≠ 0 := ne_of_gt C.norm_pos
  have hnorm2 : 0 < C.norm ^ 2 := sq_pos_of_pos C.norm_pos
  calc
    (C.lowMass / C.norm) * (C.highMass / C.norm) =
        (C.lowMass * C.highMass) / C.norm ^ 2 := by
          field_simp [hnorm0]
    _ < C.ratio / C.norm ^ 2 :=
      (div_lt_div_iff_of_pos_right hnorm2).2 C.contactGap
    _ = (1 / C.norm) * (C.ratio / C.norm) := by
      field_simp [hnorm0]

/-- The duplicate quotient latent has a catalog code whose determinization cost
equals the chart-selected cost, and its optimal determinization cost equals the
chart's.  Only the code is chosen; the latent in the conclusion is
`K.quotientSeedSetup.L` itself.  The catalog code is not claimed to attain
`w3`, and the inverse-transported phase selector appears only inside a cost
equality and is not claimed to lie in the catalog. -/
theorem exists_catalogCode_of_contactPresentation
    {p : RealTable} (hp : IsPMF p) (hpos : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D)
    (M : ContactPresentation p)
    (P : QuotientPresentation hpos D K M) :
    ∃ g ∈ catalog p,
      w3 K.quotientSeedSetup.L = w3 M.chart.toTransposeChart.latent ∧
      w3Cost K.quotientSeedSetup.L g =
        w3Cost K.quotientSeedSetup.L
          (transportCode M.relabel.equiv.symm
            (phaseSelector M.chart.toTransposeChart)) ∧
      w3Cost K.quotientSeedSetup.L g =
        w3Cost M.chart.toTransposeChart.latent
          (phaseSelector M.chart.toTransposeChart) := by
  let Q : SeedSetup p := K.quotientSeedSetup
  let S : SeedSetup (pushforward M.relabel.equiv p) :=
    orientedQuotientSetup hpos D K M
  have hPjoint :
      S.L.joint =
        (Latent.reindex M.chart.toTransposeChart.latent P.labelEquiv).joint := by
    simpa [S] using P.joint_eq_reindex
  obtain ⟨S₀, g, hS₀, _hS₀L, _hS₀w, hmem, hW3, hraw, hphase⟩ :=
    exists_catalogCode_of_transposeChartPresentation
      hp hpos M.relabel S M.chart.toTransposeChart
      M.oriented_law P.labelEquiv hPjoint
      M.chart.strictOrder M.chart.diagonalProduct_lt_offDiagonalProduct
  subst S₀
  have hround :
      (SeedSetup.pullback M.relabel S hp hpos).L.joint = Q.L.joint := by
    simpa [S, Q, orientedQuotientSetup, SeedSetup.pullback, SeedSetup.relabel]
      using Latent.pullback_relabel_joint M.relabel.equiv Q.L
  have hcost (g : BinaryCode) :
      w3Cost (SeedSetup.pullback M.relabel S hp hpos).L g =
        w3Cost Q.L g := by
    unfold w3Cost
    rw [hround]
    rfl
  have hW3round :
      w3 (SeedSetup.pullback M.relabel S hp hpos).L = w3 Q.L := by
    calc
      w3 (SeedSetup.pullback M.relabel S hp hpos).L = w3 S.L :=
        w3_pullback M.relabel.equiv S.L
      _ = w3 Q.L := by
        simpa [S, Q, orientedQuotientSetup, SeedSetup.relabel] using
          w3_relabel M.relabel.equiv Q.L
  refine ⟨g, hmem, ?_, ?_, ?_⟩
  · exact hW3round.symm.trans hW3
  · exact (hcost g).symm.trans (hraw.trans (hcost _))
  · exact (hcost g).symm.trans hphase

end

end StochasticToDeterministicLatents.Binary
