import StochasticToDeterministicLatents.Binary.Table

/-!
# The mathematical binary selector

For a binary table `[[p00, p01], [p10, p11]]`, the selector compares the two
checkerboard products. Equality returns the constant code. Otherwise it
isolates the lower-mass endpoint of the larger-product matching, with
row-major priority on a mass tie, then chooses the lower-score code from
that singleton and the constant code. The constant code wins a score tie.

The rule uses exact real comparisons and is `noncomputable`. This module
proves its two-candidate interface. `Binary.FactorNine` proves its
full-support bound; the executable count/rational refinement remains a
separate obligation in `Binary.CountSelector`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-! ## Structural choice -/

/-- Product of the main-diagonal entries. -/
noncomputable def diagonalProduct (p : RealTable) : ℝ :=
  p cell00 * p cell11

/-- Product of the off-diagonal entries. -/
noncomputable def offDiagonalProduct (p : RealTable) : ℝ :=
  p cell01 * p cell10

/-- The usual `2 x 2` determinant. -/
noncomputable def determinant (p : RealTable) : ℝ :=
  diagonalProduct p - offDiagonalProduct p

/-- The lower-mass endpoint, with the first endpoint winning equality. -/
noncomputable def lowerMassEndpoint
    (p : RealTable) (first second : Cell) : Cell :=
  if p first ≤ p second then first else second

/--
The active singleton cell.  Determinant zero returns `none`.  Positive
determinant selects the main diagonal; negative determinant selects the off
diagonal.  The endpoint order in each branch is row-major.
-/
noncomputable def activeCell? (p : RealTable) : Option Cell :=
  if diagonalProduct p = offDiagonalProduct p then
    none
  else if offDiagonalProduct p < diagonalProduct p then
    some (lowerMassEndpoint p cell00 cell11)
  else
    some (lowerMassEndpoint p cell01 cell10)

theorem activeCell?_eq_none_iff (p : RealTable) :
    activeCell? p = none ↔ diagonalProduct p = offDiagonalProduct p := by
  by_cases hdet : diagonalProduct p = offDiagonalProduct p
  · simp [activeCell?, hdet]
  · by_cases horient : offDiagonalProduct p < diagonalProduct p
    · simp [activeCell?, hdet, horient]
    · simp [activeCell?, hdet, horient]

/-- Determinant zero collapses the candidate list to the constant code. -/
theorem activeCell?_eq_none_of_determinant_eq_zero
    (p : RealTable) (hdet : determinant p = 0) :
    activeCell? p = none := by
  apply (activeCell?_eq_none_iff p).2
  exact sub_eq_zero.mp hdet

/-- The ordered one- or two-code candidate list determined by a real table. -/
noncomputable def catalog (p : RealTable) : List BinaryCode :=
  match activeCell? p with
  | none => [constantCode]
  | some z => [constantCode, canonicalizeRealCode p (singletonCode z)]

/-- Compare two codes by their exact real deterministic scores, retaining the
left code on equality.  This is internal comparison machinery for `selector`. -/
private noncomputable def pickLowerScore
    (p : RealTable) (g h : BinaryCode) : BinaryCode :=
  if detScore p g ≤ detScore p h then g else h

/--
The law-only selector on arbitrary exact real tables.

Although this definition depends only on `p`, it is classical rather than an
oracle-free executable procedure: determinant, endpoint-mass, and final-score
ties all require exact real comparison.
-/
noncomputable def selector (p : RealTable) : BinaryCode :=
  match activeCell? p with
  | none => constantCode
  | some z =>
      pickLowerScore p constantCode
        (canonicalizeRealCode p (singletonCode z))

/-- Determinant-zero tables return the constant code before any score
comparison is made. -/
theorem selector_eq_constantCode_of_determinant_eq_zero
    (p : RealTable) (hdet : determinant p = 0) :
    selector p = constantCode := by
  simp [selector, activeCell?_eq_none_of_determinant_eq_zero p hdet]

private theorem detScore_pickLowerScore_le_left
    (p : RealTable) (g h : BinaryCode) :
    detScore p (pickLowerScore p g h) ≤ detScore p g := by
  by_cases hscore : detScore p g ≤ detScore p h
  · simp [pickLowerScore, hscore]
  · simp [pickLowerScore, hscore, (lt_of_not_ge hscore).le]

private theorem detScore_pickLowerScore_le_right
    (p : RealTable) (g h : BinaryCode) :
    detScore p (pickLowerScore p g h) ≤ detScore p h := by
  by_cases hscore : detScore p g ≤ detScore p h
  · simp [pickLowerScore, hscore]
  · simp [pickLowerScore, hscore, (lt_of_not_ge hscore).le]

/-- The real selector returns one of the explicitly listed catalog codes. -/
theorem selector_mem_catalog (p : RealTable) : selector p ∈ catalog p := by
  cases hactive : activeCell? p with
  | none => simp [selector, catalog, hactive]
  | some z =>
      by_cases hscore :
          detScore p constantCode ≤
            detScore p (canonicalizeRealCode p (singletonCode z))
      · simp [selector, catalog, pickLowerScore, hactive, hscore]
      · simp [selector, catalog, pickLowerScore, hactive, hscore]

/-- The real selector has no larger score than either member of its catalog. -/
theorem detScore_selector_le_of_mem
    (p : RealTable) (g : BinaryCode) (hg : g ∈ catalog p) :
    detScore p (selector p) ≤ detScore p g := by
  cases hactive : activeCell? p with
  | none =>
      simp [selector, catalog, hactive] at hg ⊢
      simpa [hg]
  | some z =>
      simp [catalog, hactive] at hg
      rcases hg with hg | hg
      · subst g
        simpa [selector, hactive] using
          detScore_pickLowerScore_le_left p constantCode
            (canonicalizeRealCode p (singletonCode z))
      · subst g
        simpa [selector, hactive] using
          detScore_pickLowerScore_le_right p constantCode
            (canonicalizeRealCode p (singletonCode z))

/-- An exact final score tie is resolved toward the constant code. -/
theorem selector_eq_constantCode_of_score_tie
    (p : RealTable) (z : Cell)
    (hactive : activeCell? p = some z)
    (htie : detScore p constantCode =
      detScore p (canonicalizeRealCode p (singletonCode z))) :
    selector p = constantCode := by
  simp [selector, pickLowerScore, hactive, htie.le]

end StochasticToDeterministicLatents.Binary
