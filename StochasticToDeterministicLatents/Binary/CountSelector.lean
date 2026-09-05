import StochasticToDeterministicLatents.Binary.Table
import Mathlib.Data.NNRat.BigOperators

/-!
# Executable binary selectors

The mathematical rule in `Binary.Selector` asks exact questions about real
numbers.  This module gives it a finite data model instead: natural counts,
with exact nonnegative rational tables handled by denominator clearing.

The structural choices are executable and follow the same fixed contract:
equal checkerboard products return the constant code; otherwise the larger
product chooses a checkerboard, and its lower-count endpoint is isolated,
with row-major priority on equality.  Support canonicalization happens before
label compression, so every zero-count cell receives label zero.  The final
integer-key comparison retains the constant code on equality.

The elementary score identity connecting these natural-number keys to the
real deterministic score is a deferred proof obligation.  Consequently this
module supplies an executable draft and structural lemmas, not yet a proved
refinement theorem for `Binary.selector`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open scoped BigOperators

/-! ## Exact finite inputs -/

/-- A raw table of nonnegative natural counts.  Positive `total` is the
validity condition for a represented probability law.  The selector is
totalized at zero total and returns the constant code there. -/
structure CountTable where
  count : Cell → ℕ

namespace CountTable

/-- Total count in the table. -/
def total (q : CountTable) : ℕ := ∑ z, q.count z

/-- The represented real table.  It is a probability law when `0 < q.total`. -/
noncomputable def realTable (q : CountTable) : RealTable :=
  fun z => (q.count z : ℝ) / (q.total : ℝ)

/-- Executable positive-support test. -/
def supported (q : CountTable) (z : Cell) : Bool :=
  decide (q.count z ≠ 0)

/-- Canonicalize a code after restricting it to positive-count cells. -/
def canonicalizeCode (q : CountTable) (code : BinaryCode) : BinaryCode :=
  canonicalizeWithSupport q.supported code

@[simp] theorem canonicalizeCode_of_count_eq_zero
    (q : CountTable) (code : BinaryCode) (z : Cell)
    (hz : q.count z = 0) :
    q.canonicalizeCode code z = constantCode z := by
  simp [canonicalizeCode, supported, canonicalizeWithSupport, hz]

/-! ## Structural choice -/

/-- Main-diagonal count product. -/
def diagonalProduct (q : CountTable) : ℕ :=
  q.count cell00 * q.count cell11

/-- Off-diagonal count product. -/
def offDiagonalProduct (q : CountTable) : ℕ :=
  q.count cell01 * q.count cell10

/-- Lower-count endpoint, with the first endpoint winning equality. -/
def lowerMassEndpoint
    (q : CountTable) (first second : Cell) : Cell :=
  if q.count first ≤ q.count second then first else second

/-- Executable determinant-orientation and endpoint selection. -/
def activeCell? (q : CountTable) : Option Cell :=
  if q.diagonalProduct = q.offDiagonalProduct then
    none
  else if q.offDiagonalProduct < q.diagonalProduct then
    some (q.lowerMassEndpoint cell00 cell11)
  else
    some (q.lowerMassEndpoint cell01 cell10)

@[simp] theorem activeCell?_eq_none_iff (q : CountTable) :
    q.activeCell? = none ↔ q.diagonalProduct = q.offDiagonalProduct := by
  by_cases hdet : q.diagonalProduct = q.offDiagonalProduct
  · simp [activeCell?, hdet]
  · by_cases horient : q.offDiagonalProduct < q.diagonalProduct
    · simp [activeCell?, hdet, horient]
    · simp [activeCell?, hdet, horient]

/-- The ordered one- or two-code candidate list. -/
def catalog (q : CountTable) : List BinaryCode :=
  match q.activeCell? with
  | none => [constantCode]
  | some z => [constantCode, q.canonicalizeCode (singletonCode z)]

/-! ## Exact final comparison -/

/-- Count in the selected cell's row. -/
def rowCount (q : CountTable) (z : Cell) : ℕ :=
  q.count (z.1, 0) + q.count (z.1, 1)

/-- Count in the selected cell's column. -/
def columnCount (q : CountTable) (z : Cell) : ℕ :=
  q.count (0, z.2) + q.count (1, z.2)

/-- Numerator in the singleton-minus-constant logarithmic score key. -/
def singletonScoreNumerator (q : CountTable) (z : Cell) : ℕ :=
  let row := q.rowCount z
  let column := q.columnCount z
  let complement := q.total - q.count z
  row ^ (2 * row) * column ^ (2 * column) *
    complement ^ complement

/-- Denominator in the singleton-minus-constant logarithmic score key. -/
def singletonScoreDenominator (q : CountTable) (z : Cell) : ℕ :=
  let selected := q.count z
  let row := q.rowCount z
  let column := q.columnCount z
  let rowRemainder := row - selected
  let columnRemainder := column - selected
  q.total ^ q.total *
    rowRemainder ^ (2 * rowRemainder) *
    columnRemainder ^ (2 * columnRemainder) *
    selected ^ (3 * selected)

/--
The executable law-only selector for natural count tables.

For positive total, the deferred score-key identity says that the sign of
`D_p(singleton) - D_p(constant)` is the sign of the logarithm of
`singletonScoreNumerator / singletonScoreDenominator`.  Thus a smaller
numerator selects the singleton; equality and a larger numerator select the
constant.  Natural powers supply the required convention `0^0 = 1`.
-/
def selector (q : CountTable) : BinaryCode :=
  match q.activeCell? with
  | none => constantCode
  | some z =>
      let singleton := q.canonicalizeCode (singletonCode z)
      if q.singletonScoreDenominator z ≤ q.singletonScoreNumerator z then
        constantCode
      else
        singleton

/-- Equal checkerboard products return the constant code without consulting
the score key. -/
theorem selector_eq_constantCode_of_products_eq
    (q : CountTable) (hprod : q.diagonalProduct = q.offDiagonalProduct) :
    q.selector = constantCode := by
  have hnone : q.activeCell? = none :=
    (activeCell?_eq_none_iff q).2 hprod
  simp [selector, hnone]

/-- The executable selector returns one of its listed candidates.  This is a
structural fact only; score minimality awaits the score-key bridge. -/
theorem selector_mem_catalog (q : CountTable) : q.selector ∈ q.catalog := by
  cases hactive : q.activeCell? with
  | none => simp [selector, catalog, hactive]
  | some z =>
      by_cases hkey :
          q.singletonScoreDenominator z ≤ q.singletonScoreNumerator z
      · simp [selector, catalog, hactive, hkey]
      · simp [selector, catalog, hactive, hkey]

end CountTable

/-! ## Exact rational inputs -/

/-- A normalized table of exact nonnegative rational masses. -/
structure RationalTable where
  mass : Cell → ℚ≥0
  total_eq_one : ∑ z, mass z = 1

namespace RationalTable

/-- A simple executable common denominator for the four entries. -/
def commonDenominator (q : RationalTable) : ℕ :=
  ∏ z, (q.mass z).den

/-- The natural count obtained by clearing one entry's denominator. -/
def clearedCount (q : RationalTable) (z : Cell) : ℕ :=
  (q.mass z).num * (q.commonDenominator / (q.mass z).den)

/-- Clear all four denominators.  Preservation of the represented law and of
the selector decisions is part of the deferred integration proof. -/
def toCountTable (q : RationalTable) : CountTable where
  count := q.clearedCount

/-- The represented real-valued law. -/
noncomputable def realTable (q : RationalTable) : RealTable :=
  fun z => (q.mass z : ℝ)

/-- Clear denominators and run the finite count selector. -/
def selector (q : RationalTable) : BinaryCode :=
  q.toCountTable.selector

end RationalTable

end StochasticToDeterministicLatents.Binary
