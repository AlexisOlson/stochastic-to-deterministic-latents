import StochasticToDeterministicLatents.Binary.FactorTwo.ChordScalars

/-!
# The isolating code's score along the chord

The second competitor on the diagonal chord is the code that gives the last
cell its own label and every other cell a common one.  Its deterministic score
is an explicit sum of `xLogX` terms in the moving coordinate, and so is the
margin it leaves against the chord's budget.

The code's labels live in `Fin (Fintype.card Cell)`, so two of the four labels
carry no mass; they contribute nothing because `xLogX 0 = 0`.  Three
pushforwards have to be computed.  The fourth, the cell together with its
label, is the law itself: the label is a function of the cell, so the pair has
a left inverse and the entropy is unchanged.  The two reversed pairs are
equivalences of the computed ones.

Everything here is in natural-log units, with the explicit factor of
`Real.log 2` the library requires of a scalar ledger.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

variable {p : RealTable} {u t : ℝ}

/-! ## The three pushforwards -/

/-- The isolating code's own pushforward: the last cell keeps its mass, the
other three are merged, and the remaining two labels are empty. -/
private theorem push_singletonCode_apply (q : RealTable)
    (i : Fin (Fintype.card Cell)) :
    pushforward (singletonCode cell11) q i
      = if i = 1 then q (1, 1)
        else if i = 0 then q (0, 0) + q (0, 1) + q (1, 0) else 0 := by
  fin_cases i <;>
    (unfold pushforward stoch_to_det.push
     rw [Finset.sum_filter, Fintype.sum_prod_type]
     simp [Fin.sum_univ_two, singletonCode, cell11, Fin.ext_iff])

/-- The row index together with the label.  The label tests are on values, so
that no equation between labels has to be simplified. -/
private theorem push_row_apply (q : RealTable) (x : Fin 2)
    (i : Fin (Fintype.card Cell)) :
    pushforward (fun z : Cell => (z.1, singletonCode cell11 z)) q (x, i)
      = if i.val = 1 then (if x.val = 1 then q (1, 1) else 0)
        else if i.val = 0 then (if x.val = 0 then q (0, 0) + q (0, 1) else q (1, 0))
        else 0 := by
  fin_cases x <;> fin_cases i <;>
    (unfold pushforward stoch_to_det.push
     rw [Finset.sum_filter, Fintype.sum_prod_type]
     simp +decide [Fin.sum_univ_two, singletonCode, cell11, Prod.ext_iff])

/-- The column index together with the label. -/
private theorem push_column_apply (q : RealTable) (y : Fin 2)
    (i : Fin (Fintype.card Cell)) :
    pushforward (fun z : Cell => (z.2, singletonCode cell11 z)) q (y, i)
      = if i.val = 1 then (if y.val = 1 then q (1, 1) else 0)
        else if i.val = 0 then (if y.val = 0 then q (0, 0) + q (1, 0) else q (0, 1))
        else 0 := by
  fin_cases y <;> fin_cases i <;>
    (unfold pushforward stoch_to_det.push
     rw [Finset.sum_filter, Fintype.sum_prod_type]
     simp +decide [Fin.sum_univ_two, singletonCode, cell11, Prod.ext_iff])

/-- An unoccupied label has value neither zero nor one. -/
private theorem val_ne_zero {i : Fin (Fintype.card Cell)} (h : i ≠ 0) : i.val ≠ 0 := by
  intro hv
  exact h (Fin.eq_of_val_eq (by rw [hv]; decide))

private theorem val_ne_one {i : Fin (Fintype.card Cell)} (h : i ≠ 1) : i.val ≠ 1 := by
  intro hv
  exact h (Fin.eq_of_val_eq (by rw [hv]; decide))

/-! ## The four entropies -/

/-- A sum over the label type reduces to its two occupied labels. -/
private theorem sum_labels {f : Fin (Fintype.card Cell) → ℝ}
    (h : ∀ i, i ≠ 0 → i ≠ 1 → f i = 0) : ∑ i, f i = f 0 + f 1 :=
  Fintype.sum_eq_add (0 : Fin (Fintype.card Cell)) 1 (by decide)
    fun c hc => h c hc.1 hc.2

private theorem log_two_mul_entropyOf_singletonCode (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * entropyOf (singletonCode cell11) (chordAt p t)
      = -(xLogX (t + entryB p + entryC p) + xLogX (diagonalMass p - t)) := by
  have hq := isPMF_chordAt h ht
  have hz : ∀ i : Fin (Fintype.card Cell), i ≠ 0 → i ≠ 1 →
      xLogX (pushforward (singletonCode cell11) (chordAt p t) i) = 0 := by
    intro i h0 h1
    rw [push_singletonCode_apply, if_neg h1, if_neg h0, xLogX_zero]
  have h0 : pushforward (singletonCode cell11) (chordAt p t) 0
      = t + entryB p + entryC p := by
    rw [push_singletonCode_apply]
    simp [chordAt, entryB, entryC]
  have h1 : pushforward (singletonCode cell11) (chordAt p t) 1
      = diagonalMass p - t := by
    rw [push_singletonCode_apply]
    simp [chordAt]
  show Real.log 2 * entropy (pushforward (singletonCode cell11) (chordAt p t)) = _
  rw [log_two_mul_entropy (pushforward_isPMF hq), sum_labels hz, h0, h1]

private theorem log_two_mul_entropyOf_row (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * entropyOf (fun z : Cell => (z.1, singletonCode cell11 z)) (chordAt p t)
      = -(xLogX (t + entryB p) + xLogX (entryC p) + xLogX (diagonalMass p - t)) := by
  have hq := isPMF_chordAt h ht
  have hz : ∀ x : Fin 2, ∀ i : Fin (Fintype.card Cell), i ≠ 0 → i ≠ 1 →
      xLogX (pushforward (fun z : Cell => (z.1, singletonCode cell11 z))
        (chordAt p t) (x, i)) = 0 := by
    intro x i h0 h1
    rw [push_row_apply, if_neg (val_ne_one h1), if_neg (val_ne_zero h0), xLogX_zero]
  have e00 : pushforward (fun z : Cell => (z.1, singletonCode cell11 z))
      (chordAt p t) (0, 0) = t + entryB p := by
    rw [push_row_apply]
    simp +decide [chordAt, entryB]
  have e01 : pushforward (fun z : Cell => (z.1, singletonCode cell11 z))
      (chordAt p t) (0, 1) = 0 := by
    rw [push_row_apply]
    simp +decide
  have e10 : pushforward (fun z : Cell => (z.1, singletonCode cell11 z))
      (chordAt p t) (1, 0) = entryC p := by
    rw [push_row_apply]
    simp +decide [chordAt, entryC]
  have e11 : pushforward (fun z : Cell => (z.1, singletonCode cell11 z))
      (chordAt p t) (1, 1) = diagonalMass p - t := by
    rw [push_row_apply]
    simp +decide [chordAt]
  show Real.log 2 * entropy (pushforward
    (fun z : Cell => (z.1, singletonCode cell11 z)) (chordAt p t)) = _
  rw [log_two_mul_entropy (pushforward_isPMF hq), Fintype.sum_prod_type,
    Fin.sum_univ_two, sum_labels (hz 0), sum_labels (hz 1), e00, e01, e10, e11,
    xLogX_zero]
  ring

private theorem log_two_mul_entropyOf_column (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * entropyOf (fun z : Cell => (z.2, singletonCode cell11 z)) (chordAt p t)
      = -(xLogX (t + entryC p) + xLogX (entryB p) + xLogX (diagonalMass p - t)) := by
  have hq := isPMF_chordAt h ht
  have hz : ∀ y : Fin 2, ∀ i : Fin (Fintype.card Cell), i ≠ 0 → i ≠ 1 →
      xLogX (pushforward (fun z : Cell => (z.2, singletonCode cell11 z))
        (chordAt p t) (y, i)) = 0 := by
    intro y i h0 h1
    rw [push_column_apply, if_neg (val_ne_one h1), if_neg (val_ne_zero h0), xLogX_zero]
  have e00 : pushforward (fun z : Cell => (z.2, singletonCode cell11 z))
      (chordAt p t) (0, 0) = t + entryC p := by
    rw [push_column_apply]
    simp +decide [chordAt, entryC]
  have e01 : pushforward (fun z : Cell => (z.2, singletonCode cell11 z))
      (chordAt p t) (0, 1) = 0 := by
    rw [push_column_apply]
    simp +decide
  have e10 : pushforward (fun z : Cell => (z.2, singletonCode cell11 z))
      (chordAt p t) (1, 0) = entryB p := by
    rw [push_column_apply]
    simp +decide [chordAt, entryB]
  have e11 : pushforward (fun z : Cell => (z.2, singletonCode cell11 z))
      (chordAt p t) (1, 1) = diagonalMass p - t := by
    rw [push_column_apply]
    simp +decide [chordAt]
  show Real.log 2 * entropy (pushforward
    (fun z : Cell => (z.2, singletonCode cell11 z)) (chordAt p t)) = _
  rw [log_two_mul_entropy (pushforward_isPMF hq), Fintype.sum_prod_type,
    Fin.sum_univ_two, sum_labels (hz 0), sum_labels (hz 1), e00, e01, e10, e11,
    xLogX_zero]
  ring

/-- The cell together with its label carries the law's own entropy: the label
is a function of the cell, so the pair has a left inverse. -/
private theorem entropyOf_cell_singletonCode {q : RealTable} (hq : IsPMF q) :
    stoch_to_det.Hvar (fun z : Cell => (z.1, z.2, singletonCode cell11 z)) q
      = entropy q := by
  have hid : stoch_to_det.Hvar (fun z : Cell => z) q = entropy q := by
    show entropy (pushforward (fun z : Cell => z) q) = entropy q
    congr 1
    funext z
    unfold pushforward stoch_to_det.push
    rw [Finset.sum_filter]
    simp
  rw [← hid]
  exact stoch_to_det.Hvar_eq_of_leftInverse hq (fun z : Cell => z)
    (fun z : Cell => (z.1, z.2, singletonCode cell11 z))
    (fun w : Fin 2 × Fin 2 × Fin (Fintype.card Cell) => (w.1, w.2.1))
    (by intro z; rfl)

/-! ## The score and the margin -/

/-- The isolating code's deterministic score along the chord, in natural-log
units. -/
theorem log_two_mul_detScore_singletonCode_chordAt (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * detScore (chordAt p t) (singletonCode cell11)
      = xLogX t - xLogX (entryB p) - xLogX (entryC p)
        - 2 * xLogX (diagonalMass p - t)
        - xLogX (t + entryB p) - xLogX (t + entryC p)
        + xLogX (entryC p + (diagonalMass p - t))
        + xLogX (entryB p + (diagonalMass p - t))
        + xLogX (t + entryB p + entryC p) := by
  have hq := isPMF_chordAt h ht
  have hrow : stoch_to_det.Hvar
      (fun a : Cell => (singletonCode cell11 a, a.1)) (chordAt p t)
      = stoch_to_det.Hvar
        (fun a : Cell => (a.1, singletonCode cell11 a)) (chordAt p t) := by
    have hswap := stoch_to_det.Hvar_equiv hq
      (fun z : Cell => (z.1, singletonCode cell11 z))
      (Equiv.prodComm (Fin 2) (Fin (Fintype.card Cell)))
    simpa using hswap
  have hcol : stoch_to_det.Hvar
      (fun a : Cell => (singletonCode cell11 a, a.2)) (chordAt p t)
      = stoch_to_det.Hvar
        (fun a : Cell => (a.2, singletonCode cell11 a)) (chordAt p t) := by
    have hswap := stoch_to_det.Hvar_equiv hq
      (fun z : Cell => (z.2, singletonCode cell11 z))
      (Equiv.prodComm (Fin 2) (Fin (Fintype.card Cell)))
    simpa using hswap
  have hA : Real.log 2 * stoch_to_det.Hvar
      (fun a : Cell => (a.1, singletonCode cell11 a)) (chordAt p t)
      = -(xLogX (t + entryB p) + xLogX (entryC p) + xLogX (diagonalMass p - t)) :=
    log_two_mul_entropyOf_row h ht
  have hB : Real.log 2 * stoch_to_det.Hvar
      (fun a : Cell => (a.2, singletonCode cell11 a)) (chordAt p t)
      = -(xLogX (t + entryC p) + xLogX (entryB p) + xLogX (diagonalMass p - t)) :=
    log_two_mul_entropyOf_column h ht
  have hD : Real.log 2 * stoch_to_det.Hvar (singletonCode cell11) (chordAt p t)
      = -(xLogX (t + entryB p + entryC p) + xLogX (diagonalMass p - t)) :=
    log_two_mul_entropyOf_singletonCode h ht
  have hC : Real.log 2 * stoch_to_det.Hvar
      (fun a : Cell => (a.1, a.2, singletonCode cell11 a)) (chordAt p t)
      = -(xLogX t + xLogX (entryB p) + xLogX (entryC p)
            + xLogX (diagonalMass p - t)) := by
    rw [entropyOf_cell_singletonCode hq]
    exact log_two_mul_entropy_chordAt h ht
  have hX : Real.log 2 * stoch_to_det.Hvar Prod.fst (chordAt p t)
      = -(xLogX (t + entryB p) + xLogX (entryC p + (diagonalMass p - t))) :=
    log_two_mul_entropy_marginalX_chordAt h ht
  have hY : Real.log 2 * stoch_to_det.Hvar Prod.snd (chordAt p t)
      = -(xLogX (t + entryC p) + xLogX (entryB p + (diagonalMass p - t))) :=
    log_two_mul_entropy_marginalY_chordAt h ht
  have hscore : Real.log 2 * detScore (chordAt p t) (singletonCode cell11)
      = 2 * (Real.log 2 * stoch_to_det.Hvar
            (fun a : Cell => (a.1, singletonCode cell11 a)) (chordAt p t))
        + 2 * (Real.log 2 * stoch_to_det.Hvar
            (fun a : Cell => (a.2, singletonCode cell11 a)) (chordAt p t))
        - Real.log 2 * stoch_to_det.Hvar
            (fun a : Cell => (a.1, a.2, singletonCode cell11 a)) (chordAt p t)
        - Real.log 2 * stoch_to_det.Hvar (singletonCode cell11) (chordAt p t)
        - Real.log 2 * stoch_to_det.Hvar Prod.fst (chordAt p t)
        - Real.log 2 * stoch_to_det.Hvar Prod.snd (chordAt p t) := by
    unfold detScore condMutualInfo condEntropy stoch_to_det.condMI stoch_to_det.condH
    rw [hrow, hcol]
    ring
  rw [hscore, hA, hB, hC, hD, hX, hY]
  ring

private theorem log_two_mul_psi (q : RealTable) :
    Real.log 2 * Psi q = 2 * (Real.log 2 * entropy q)
      - (Real.log 2 * entropy (stoch_to_det.mX q))
      - (Real.log 2 * entropy (stoch_to_det.mY q)) := by
  show Real.log 2 * stoch_to_det.Psi q = _
  rw [stoch_to_det.Psi]
  ring

/-- The isolating code's margin along the chord, in natural-log units. -/
theorem log_two_mul_singletonMargin (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * singletonMargin p u t
      = -2 * (Real.log 2 * Phi (contactAt p u))
        - 5 * xLogX t - 3 * xLogX (entryB p) - 3 * xLogX (entryC p)
        - 2 * xLogX (diagonalMass p - t)
        + 3 * xLogX (t + entryB p) + 3 * xLogX (t + entryC p)
        + xLogX (entryC p + (diagonalMass p - t))
        + xLogX (entryB p + (diagonalMass p - t))
        - xLogX (t + entryB p + entryC p) := by
  have hm : Real.log 2 * singletonMargin p u t
      = 2 * (Real.log 2 * Psi (chordAt p t))
        - 2 * (Real.log 2 * Phi (contactAt p u))
        - Real.log 2 * detScore (chordAt p t) (singletonCode cell11) := by
    rw [singletonMargin, chordBudget]
    ring
  rw [hm, log_two_mul_psi, log_two_mul_detScore_singletonCode_chordAt h ht,
    log_two_mul_entropy_chordAt h ht, log_two_mul_entropy_marginalX_chordAt h ht,
    log_two_mul_entropy_marginalY_chordAt h ht]
  ring

end StochasticToDeterministicLatents.Binary
