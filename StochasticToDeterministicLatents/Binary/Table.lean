import StochasticToDeterministicLatents.Deterministic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD

/-!
# Binary tables and canonical codes

This module fixes a reader-facing representation of a `2 x 2` table.  It also
contains the two deterministic codes used by the binary law-only selector:
the constant code and a singleton-versus-complement code.

Code labels have no intrinsic meaning.  `canonicalizeWithSupport` therefore
renumbers the fibers that occur on a supplied support in row-major
first-occurrence order, after removing unsupported cells, and assigns label
zero to every unsupported cell.  Removing unsupported cells first is
important on sparse laws: two codes that differ only away from positive mass
should not become different canonical partitions.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-- One binary coordinate. -/
abbrev Bit := Fin 2

/-- A cell of a binary `2 x 2` table. -/
abbrev Cell := Bit × Bit

/-- A real-valued binary table.  Probability-law hypotheses are stated
separately, so the same small type can also be used for intermediate tables. -/
abbrev RealTable := Cell → ℝ

/-- The canonical four-label deterministic-code type on a binary table. -/
abbrev BinaryCode := Code Bit Bit

def cell00 : Cell := (0, 0)
def cell01 : Cell := (0, 1)
def cell10 : Cell := (1, 0)
def cell11 : Cell := (1, 1)

/-- The fixed coordinate priority used for every structural tie. -/
def rowMajorCells : List Cell := [cell00, cell01, cell10, cell11]

/-- The constant binary code. -/
def constantCode : BinaryCode :=
  StochasticToDeterministicLatents.constantCode

/-- The singleton-versus-complement code that gives the distinguished cell
label `1` and every other cell label `0`. -/
def singletonCode (distinguished : Cell) : BinaryCode :=
  fun z => if z = distinguished then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- Renumber a list of labels by the order in which their fibers first occur. -/
private def compressedLabels {κ : Type*} [DecidableEq κ] (values : List κ) : List ℕ :=
  let representatives := values.eraseDups
  values.map fun value => representatives.idxOf value

/-- Cells retained by a Boolean support test, in row-major order. -/
private def supportCellsFor (supported : Cell → Bool) : List Cell :=
  rowMajorCells.filter supported

/--
Canonicalize a code on a supplied support.

The induced partition is first restricted to supported cells, then its labels
are compressed by row-major first occurrence.  Unsupported cells receive
label zero.  The final modulus only totalizes the four-label output; for a
four-cell table every compressed label is already smaller than four.
-/
def canonicalizeWithSupport
    (supported : Cell → Bool) (g : BinaryCode) : BinaryCode :=
  fun z =>
    if supported z then
      let cells := supportCellsFor supported
      let labels := compressedLabels (cells.map g)
      ⟨labels.getD (cells.idxOf z) 0 % Fintype.card Cell, by
        exact Nat.mod_lt _ (by decide)⟩
    else
      constantCode z

@[simp] theorem canonicalizeWithSupport_of_false
    (supported : Cell → Bool) (g : BinaryCode) (z : Cell)
    (hz : supported z = false) :
    canonicalizeWithSupport supported g z = constantCode z := by
  simp [canonicalizeWithSupport, hz]

/-- Equality of the fiber relations induced on the positive support of a real
table.  This ignores both output-label names and values on zero-mass cells. -/
def supportPartitionEquivalent
    (p : RealTable) (g h : BinaryCode) : Prop :=
  ∀ z w, p z ≠ 0 → p w ≠ 0 → (g z = g w ↔ h z = h w)

/-! ## Real support -/

/-- Exact support test for an arbitrary real table.  This is classical and
noncomputable: equality of arbitrary exact real numbers is not an executable
oracle-free operation. -/
noncomputable def realSupported (p : RealTable) (z : Cell) : Bool :=
  decide (p z ≠ 0)

/-- Canonicalize a code on the nonzero support of an arbitrary real table. -/
noncomputable def canonicalizeRealCode
    (p : RealTable) (g : BinaryCode) : BinaryCode :=
  canonicalizeWithSupport (realSupported p) g

@[simp] theorem canonicalizeRealCode_of_eq_zero
    (p : RealTable) (g : BinaryCode) (z : Cell) (hz : p z = 0) :
    canonicalizeRealCode p g z = constantCode z := by
  simp [canonicalizeRealCode, realSupported, canonicalizeWithSupport, hz]

end StochasticToDeterministicLatents.Binary
