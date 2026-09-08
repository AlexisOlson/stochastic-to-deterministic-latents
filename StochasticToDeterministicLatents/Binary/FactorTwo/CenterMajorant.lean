import StochasticToDeterministicLatents.Binary.FactorTwo.CertValues
import StochasticToDeterministicLatents.Binary.FactorTwo.Chord

/-!
# A contact plane, evaluated at the centre of a chord

The tangent certificate at a contact law majorizes `Phi` everywhere, so its
pairing with any law bounds `Phi` there from above.  This module says what that
bound becomes at the midpoint of a chord, and it says it for **two independent
laws**: the plane may come from one contact and be evaluated at another law's
midpoint.  That is what lets a handful of fixed reference laws bound `Phi`
across a whole family.

The mechanism is that a contact plane does not distinguish the two diagonal
cells.  `CertValues` gives its two diagonal values as the same
`certDiagonal`, and the chord moves mass only between those two cells while
holding their sum fixed, so a pairing against such a plane is constant along
the chord.  The contact is one point of the chord and the midpoint is another,
so the value at the contact -- which is `Phi` there -- is the value at the
midpoint.

Nothing here is quantitative: it converts a majorant into a bound at a
specified point, and supplies no number.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-! ## The plane at a chord domain's contact -/

/-- The tangent certificate at the contact of a chord domain majorizes `Phi`.
This is the same route `tau_eq_contact` takes: the positivity gate at the
contact gives the norm bound, and the norm bound gives the majorant. -/
private theorem majorizes_contact (h : ChordDomain p u) :
    Majorizes (tangentCert (contactAt p u)) := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hpos := contactAt_pos h.fullSupport hu h.nonconstant
  exact majorizes_tangentCert_of_normBound hpos
    (normBound_of_positivityGate hpos
      (isPMF_contactAt h.isPMF h.fullSupport hu h.nonconstant)
      (positivityGate_contactAt h.isPMF h.fullSupport hu h.nonconstant h.topRoot.2.1))

/-- **A contact plane is blind to the two diagonal cells.**  Both of its
diagonal values are `certDiagonal` of the diagonal mass and the top root, so
they agree. -/
private theorem tangentCert_contact_diagonal (h : ChordDomain p u) :
    tangentCert (contactAt p u) (0, 0) = tangentCert (contactAt p u) (1, 1) := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  obtain ⟨h00, h11, -, -⟩ := tangentCert_contact_values
    (isPMF_contactAt h.isPMF h.fullSupport hu h.nonconstant)
    (contactAt_pos h.fullSupport hu h.nonconstant) hu
    (chordTop_mul_chordBottom h)
    (by rw [← chordAt_chordTop, cubic_chordAt]; exact h.topRoot.2.1)
  rw [h00, h11]

/-! ## Constancy along the chord -/

/-- The chord's four cells.  `Chord.lean` establishes the same four values
inline where it needs them; they are collected here because this module needs
them at two different points of the chord. -/
private theorem chordAt_cells (p : RealTable) (t : ℝ) :
    chordAt p t (0, 0) = t ∧ chordAt p t (0, 1) = p (0, 1)
      ∧ chordAt p t (1, 0) = p (1, 0)
      ∧ chordAt p t (1, 1) = diagonalMass p - t :=
  ⟨by simp [chordAt], by simp [chordAt], by simp [chordAt], by simp [chordAt]⟩

/-- A plane that does not distinguish the two diagonal cells pairs the same
against every point of the chord.  Stated between the two points that are
wanted: the contact at the top and the midpoint. -/
private theorem sum_contact_eq_sum_chordMidpoint {c : RealTable} (hc : c (0, 0) = c (1, 1))
    (p : RealTable) (u : ℝ) :
    ∑ z, c z * contactAt p u z = ∑ z, c z * chordAt p (chordMidpoint p) z := by
  obtain ⟨t00, t01, t10, t11⟩ := chordAt_cells p (chordTop p u)
  obtain ⟨m00, m01, m10, m11⟩ := chordAt_cells p (chordMidpoint p)
  rw [← chordAt_chordTop, sum_cells, sum_cells, t00, t01, t10, t11,
    m00, m01, m10, m11, hc]
  ring

/-! ## The bound at the centre -/

/-- **The plane of one chord domain, evaluated at another's centre.**  `Phi` at
the first law's contact is at most the pairing of the second law's contact
plane with the first law's chord midpoint.  Taking `p' = p` gives the bound
from a law's own plane; taking `p'` to be an explicit reference law gives the
bound from a fixed plane, which is how a finite family of planes covers a
range of `p`. -/
theorem phi_contact_le_chordMidpoint_pairing (h : ChordDomain p u)
    {p' : RealTable} {u' : ℝ} (h' : ChordDomain p' u') :
    Phi (contactAt p u)
      ≤ ∑ z, tangentCert (contactAt p' u') z * chordAt p (chordMidpoint p) z := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  rw [← sum_contact_eq_sum_chordMidpoint (tangentCert_contact_diagonal h') p u]
  exact majorizes_contact h' (contactAt p u)
    (isPMF_contactAt h.isPMF h.fullSupport hu h.nonconstant)

end StochasticToDeterministicLatents.Binary
