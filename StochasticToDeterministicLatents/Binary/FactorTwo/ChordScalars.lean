import StochasticToDeterministicLatents.Binary.FactorTwo.Chord
import StochasticToDeterministicLatents.Binary.ContactChart

/-!
# The chord's entropies, written out

Everything downstream of the chord is calculus in one variable, so the
entropies along the chord have to be visible as scalar expressions.  This
module writes them out.

The library's information quantities are in bits; `xLogX` is in natural-log
units.  Every statement here therefore carries an explicit factor of
`Real.log 2`, which is the conversion the library requires a scalar ledger to
keep.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

variable {p : RealTable} {u t : ℝ}

/-! ## Entropy as a sum of `xLogX` -/

/-- The entropy of a probability law, in natural-log units, is minus the sum of
`xLogX` over its values. -/
theorem log_two_mul_entropy {γ : Type*} [Fintype γ] {m : γ → ℝ} (hm : IsPMF m) :
    Real.log 2 * entropy m = -∑ i, xLogX (m i) := by
  have h := stoch_to_det.H_eq_negMulLog hm.isFiniteMeasure
  have hmass : stoch_to_det.mass m = 1 := hm.total
  rw [hmass, Real.log_one, mul_zero, zero_add] at h
  rw [h, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.negMulLog, xLogX]
    ring

/-! ## The three entropies along the chord

The law, its row marginal and its column marginal, each as four or two
`xLogX` terms in the moving coordinate `t`. -/

theorem log_two_mul_entropy_chordAt (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * entropy (chordAt p t)
      = -(xLogX t + xLogX (entryB p) + xLogX (entryC p)
            + xLogX (diagonalMass p - t)) := by
  have h00 : chordAt p t (0, 0) = t := by simp [chordAt]
  have h01 : chordAt p t (0, 1) = entryB p := by simp [chordAt, entryB]
  have h10 : chordAt p t (1, 0) = entryC p := by simp [chordAt, entryC]
  have h11 : chordAt p t (1, 1) = diagonalMass p - t := by simp [chordAt]
  rw [log_two_mul_entropy (isPMF_chordAt h ht), sum_cells, h00, h01, h10, h11]

theorem log_two_mul_entropy_marginalX_chordAt (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * entropy (stoch_to_det.mX (chordAt p t))
      = -(xLogX (t + entryB p) + xLogX (entryC p + (diagonalMass p - t))) := by
  have hq := isPMF_chordAt h ht
  have h0 : stoch_to_det.mX (chordAt p t) 0 = t + entryB p := by
    rw [marginalX_zero]
    simp [chordAt, entryB]
  have h1 : stoch_to_det.mX (chordAt p t) 1 = entryC p + (diagonalMass p - t) := by
    rw [marginalX_one]
    simp [chordAt, entryC]
  have hmX : IsPMF (stoch_to_det.mX (chordAt p t)) := pushforward_isPMF (f := Prod.fst) hq
  rw [log_two_mul_entropy hmX, Fin.sum_univ_two, h0, h1]

theorem log_two_mul_entropy_marginalY_chordAt (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * entropy (stoch_to_det.mY (chordAt p t))
      = -(xLogX (t + entryC p) + xLogX (entryB p + (diagonalMass p - t))) := by
  have hq := isPMF_chordAt h ht
  have h0 : stoch_to_det.mY (chordAt p t) 0 = t + entryC p := by
    rw [marginalY_zero]
    simp [chordAt, entryC]
  have h1 : stoch_to_det.mY (chordAt p t) 1 = entryB p + (diagonalMass p - t) := by
    rw [marginalY_one]
    simp [chordAt, entryB]
  have hmY : IsPMF (stoch_to_det.mY (chordAt p t)) := pushforward_isPMF (f := Prod.snd) hq
  rw [log_two_mul_entropy hmY, Fin.sum_univ_two, h0, h1]

/-! ## The constant margin, written out

`Psi q + Phi q = 5 H(q) - 3 H(q_X) - 3 H(q_Y)`, so the constant margin is a
sum of eight `xLogX` terms in `t` and the value of `Phi` at the fixed
contact. -/

private theorem log_two_mul_psi_add_phi (q : RealTable) :
    Real.log 2 * (Psi q + Phi q)
      = 5 * (Real.log 2 * entropy q)
        - 3 * (Real.log 2 * entropy (stoch_to_det.mX q))
        - 3 * (Real.log 2 * entropy (stoch_to_det.mY q)) := by
  show Real.log 2 * (stoch_to_det.Psi q + stoch_to_det.Phi q) = _
  rw [stoch_to_det.Psi, stoch_to_det.Phi]
  ring

theorem constantMargin_eq_psi_add_phi :
    constantMargin p u t
      = Psi (chordAt p t) + Phi (chordAt p t) - 2 * Phi (contactAt p u) := by
  rw [constantMargin, chordBudget]
  ring

/-- The constant margin along the chord, in natural-log units. -/
theorem log_two_mul_constantMargin (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * constantMargin p u t
      = -5 * (xLogX t + xLogX (entryB p) + xLogX (entryC p)
                + xLogX (diagonalMass p - t))
        + 3 * (xLogX (t + entryB p) + xLogX (entryC p + (diagonalMass p - t)))
        + 3 * (xLogX (t + entryC p) + xLogX (entryB p + (diagonalMass p - t)))
        - 2 * (Real.log 2 * Phi (contactAt p u)) := by
  rw [constantMargin_eq_psi_add_phi, mul_sub, log_two_mul_psi_add_phi,
    log_two_mul_entropy_chordAt h ht, log_two_mul_entropy_marginalX_chordAt h ht,
    log_two_mul_entropy_marginalY_chordAt h ht]
  ring

end StochasticToDeterministicLatents.Binary
