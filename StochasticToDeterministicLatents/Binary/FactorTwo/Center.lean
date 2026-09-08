import StochasticToDeterministicLatents.Binary.FactorTwo.Margins

/-!
# The chord centre

The centre of the chord is the law `chordAt p (chordMidpoint p)`, whose two
diagonal cells are equal.  This module records what the two margins are there.

At the centre both marginals coincide, so the row and column entropies of
[`Margins.lean`](Margins.lean) become one number, and the four cells are fixed
by two: the off-diagonal mass `v` and the imbalance `z = (b - c) / v`.  The
scalar forms below are those two functions written in `(v, z)`, and
`log_two_mul_constantMargin_center` and `log_two_mul_singletonMargin_center`
identify them with the margins at the midpoint.  Everything is in natural-log
units, as in `Margins`.

`centerConstantScalar` is the first line of the page's display (4.2) as it
stands.  `centerSingletonScalar` is the second line with its two `gamma` terms
written out: `gamma(v z) = log 2 - centerMarginalEntropy v z` and
`log 2 - gamma(v) = -xLogX ((1 - v) / 2) - xLogX ((1 + v) / 2)`, which turns
`3 J - 3 R + 2 k - gamma(v) + gamma(v z)` into the form below.  No declaration
here states those two identities; they are the arithmetic between the page's
display and this file.

The centre is where the gate hypotheses of [`Gates.lean`](Gates.lean) are
evaluated: `T_le_two_mul_tau_of_centerGate` asks for a nonnegative constant
margin at `chordMidpoint p`, and both cut gates ask for a nonnegative
isolating margin there.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-! ## The centre is a chord domain -/

/-- The centre of the chord carries the same chord domain, with the same top
root.  It is the chord point of `chordDomain_chordAt` at the midpoint. -/
theorem chordDomain_center (h : ChordDomain p u) :
    ChordDomain (chordAt p (chordMidpoint p)) u :=
  chordDomain_chordAt h ⟨le_rfl, chordMidpoint_lt_chordTop h⟩

/-! ## The two scalar forms -/

/-- The centre law's entropy, in natural-log units, in terms of the
off-diagonal mass `v` and the imbalance `z`. -/
noncomputable def centerLogEntropy (v z : ℝ) : ℝ :=
  -(2 * xLogX ((1 - v) / 2) + xLogX (v * (1 + z) / 2) + xLogX (v * (1 - z) / 2))

/-- The centre law's marginal entropy.  Both marginals are
`((1 + v z) / 2, (1 - v z) / 2)`, so one number serves for the row and the
column. -/
noncomputable def centerMarginalEntropy (v z : ℝ) : ℝ :=
  -(xLogX ((1 + v * z) / 2) + xLogX ((1 - v * z) / 2))

/-- The constant code's margin at the centre.  `k` is the contact's `Phi` in
natural-log units, as in `constantScalar`. -/
noncomputable def centerConstantScalar (v z k : ℝ) : ℝ :=
  5 * centerLogEntropy v z - 6 * centerMarginalEntropy v z - 2 * k

/-- The isolating code's margin at the centre. -/
noncomputable def centerSingletonScalar (v z k : ℝ) : ℝ :=
  3 * centerLogEntropy v z - 4 * centerMarginalEntropy v z - 2 * k
    - xLogX ((1 - v) / 2) - xLogX ((1 + v) / 2)

/-! ## The two bridges

Both proofs are the same rewrite: the midpoint and the two arguments of the
marginal entropy are read back as cells, so that the two sides differ by
nothing but association.
-/

/-- The seven substitutions that carry the centre's `(v, z)` arguments back to
the cells of `p`: the midpoint and its complement, then the five arguments the
two scalar forms take. -/
private theorem center_substitutions (h : ChordDomain p u) :
    chordMidpoint p = (1 - offDiagonalMass p) / 2
      ∧ diagonalMass p - chordMidpoint p = (1 - offDiagonalMass p) / 2
      ∧ offDiagonalMass p * (1 + (entryB p - entryC p) / offDiagonalMass p) / 2
          = entryB p
      ∧ offDiagonalMass p * (1 - (entryB p - entryC p) / offDiagonalMass p) / 2
          = entryC p
      ∧ (1 + offDiagonalMass p * ((entryB p - entryC p) / offDiagonalMass p)) / 2
          = (1 - offDiagonalMass p) / 2 + entryB p
      ∧ (1 - offDiagonalMass p * ((entryB p - entryC p) / offDiagonalMass p)) / 2
          = (1 - offDiagonalMass p) / 2 + entryC p
      ∧ (1 + offDiagonalMass p) / 2
          = (1 - offDiagonalMass p) / 2 + entryB p + entryC p := by
  have hbc : offDiagonalMass p = entryB p + entryC p := rfl
  have hne : entryB p + entryC p ≠ 0 := by
    rw [← hbc]; exact (offDiagonalMass_pos h.fullSupport).ne'
  have hsum := diagonalMass_add_offDiagonalMass h.isPMF
  have hmid : chordMidpoint p = (1 - offDiagonalMass p) / 2 := by
    rw [chordMidpoint]; linarith
  refine ⟨hmid, by rw [hmid]; linarith, ?_, ?_, ?_, ?_, by rw [hbc]; ring⟩ <;>
    · rw [hbc]
      field_simp
      ring

/-- The constant margin at the centre is its scalar form. -/
theorem log_two_mul_constantMargin_center (h : ChordDomain p u) :
    Real.log 2 * constantMargin p u (chordMidpoint p)
      = centerConstantScalar (offDiagonalMass p)
          ((entryB p - entryC p) / offDiagonalMass p)
          (Real.log 2 * Phi (contactAt p u)) := by
  obtain ⟨hmid, hs, eB, eC, eX, eY, -⟩ := center_substitutions h
  rw [log_two_mul_constantMargin_eq h ⟨le_rfl, (chordMidpoint_lt_chordTop h).le⟩]
  unfold constantScalar chordLogEntropy rowLogEntropy columnLogEntropy
    centerConstantScalar centerLogEntropy centerMarginalEntropy
  rw [hs, hmid, eB, eC, eX, eY]
  ring

/-- The isolating margin at the centre is its scalar form. -/
theorem log_two_mul_singletonMargin_center (h : ChordDomain p u) :
    Real.log 2 * singletonMargin p u (chordMidpoint p)
      = centerSingletonScalar (offDiagonalMass p)
          ((entryB p - entryC p) / offDiagonalMass p)
          (Real.log 2 * Phi (contactAt p u)) := by
  obtain ⟨hmid, hs, eB, eC, eX, eY, eZ⟩ := center_substitutions h
  rw [log_two_mul_singletonMargin_eq h ⟨le_rfl, (chordMidpoint_lt_chordTop h).le⟩]
  unfold singletonScalar chordLogEntropy rowLogEntropy columnLogEntropy
    singletonLogCost centerSingletonScalar centerLogEntropy centerMarginalEntropy
  rw [hs, hmid, eB, eC, eX, eY, eZ]
  ring

end StochasticToDeterministicLatents.Binary
