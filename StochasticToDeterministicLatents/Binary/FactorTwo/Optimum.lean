import StochasticToDeterministicLatents.Binary.FactorTwo.NormBound
import StochasticToDeterministicLatents.Binary.FactorTwo.RationalTest

/-!
# The stochastic optimum of a fully supported binary law

The preceding modules supply the two sides of a squeeze.  `Contact` bounds
`tau` above by a latent built from the diagonal contact pair and below by any
affine majorant of `Phi`; `RationalTest` verifies the positivity gate at the
contact and at a constant optimum; `NormBound` turns the gate into the norm
bound, which makes the tangent certificate a majorant.  This module closes the
squeeze and reads off `tau` exactly.

The answer has two branches, selected by whether the top root of the cubic has
reached the geometric mean of the diagonal.  Below it the optimum is the
contact pair and `tau p = Psi p - Phi (contactAt p u)`; at it the optimum is
constant and `tau p = Psi p - Phi p`.  Both are `Psi` minus the value of `Phi`
at the law where the certificate touches, so the two branches differ only in
which law that is.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

variable {p : RealTable} {u : ℝ}

/-! ## The certificate pairs with `p` through the mixture -/

/-- `Touch` pairs the certificate at one contact with the other contact.  Since
`p` is the mixture of the two and both carry the same `Phi`, the certificate
pairs with `p` itself to the same value. -/
private theorem tangentCert_contact_pairing_law (hp : IsPMF p) (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    (∑ z, tangentCert (contactAt p u) z * p z) = Phi (contactAt p u) := by
  obtain ⟨hq, -, -, -, hmix⟩ := contact_mixture hp hpos hu hnc
  have hself := tangentCert_self (contactAt p u) hq
  have hpair := tangentCert_contact_pairing hp hpos hu hnc hroot
  have hswap := phi_oppositeContactAt hp hpos hu hnc
  calc (∑ z, tangentCert (contactAt p u) z * p z)
      = ∑ z, (mixingWeight p u * (tangentCert (contactAt p u) z * contactAt p u z)
          + (1 - mixingWeight p u)
            * (tangentCert (contactAt p u) z * oppositeContactAt p u z)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← hmix z]
        ring
    _ = mixingWeight p u * (∑ z, tangentCert (contactAt p u) z * contactAt p u z)
        + (1 - mixingWeight p u)
          * ∑ z, tangentCert (contactAt p u) z * oppositeContactAt p u z := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = Phi (contactAt p u) := by
        rw [hself, hpair, ← hswap]
        ring

/-! ## The two branches -/

/-- Below the geometric mean of the diagonal the optimum is the contact pair. -/
theorem tau_eq_contact (hp : IsPMF p) (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) (hroot : cubic p u = 0) :
    tau p = Psi p - Phi (contactAt p u) := by
  refine le_antisymm
    (tau_le_contact hp hpos hu hnc (phi_oppositeContactAt hp hpos hu hnc)) ?_
  have hqpos : FullSupport (contactAt p u) := contactAt_pos hpos hu hnc
  have hmaj := majorizes_tangentCert_of_normBound hqpos
    (normBound_of_positivityGate hqpos (isPMF_contactAt hp hpos hu hnc)
      (positivityGate_contactAt hp hpos hu hnc hroot))
  have h := tau_ge_of_majorizes hp hmaj
  rwa [tangentCert_contact_pairing_law hp hpos hu hnc hroot] at h

/-- At the geometric mean of the diagonal the optimum is constant. -/
theorem tau_eq_self (hp : IsPMF p) (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u)
    (hnc : ¬ Nonconstant p u) : tau p = Psi p - Phi p := by
  refine le_antisymm (tau_le_psi_sub_phi hp) ?_
  have hmaj := majorizes_tangentCert_of_normBound hpos
    (normBound_of_positivityGate hpos hp
      (positivityGate_of_constant hp hpos hdet htop hnc))
  have h := tau_ge_of_majorizes hp hmaj
  rwa [tangentCert_self p hp] at h

/-! ## The dichotomy -/

private theorem offDiagonalMass_nonneg (hpos : FullSupport p) :
    0 ≤ offDiagonalMass p :=
  (offDiagonalMass_pos hpos).le

/-- The stochastic optimum of a fully supported binary law with nonnegative
determinant, in both branches, at the top root of its cubic. -/
theorem tau_eq_at_topRoot (hp : IsPMF p) (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) :
    IsTopRoot p (cubicRoot p) ∧
      ((Nonconstant p (cubicRoot p)
          ∧ tau p = Psi p - Phi (contactAt p (cubicRoot p)))
        ∨ (¬ Nonconstant p (cubicRoot p) ∧ tau p = Psi p - Phi p)) := by
  obtain ⟨u, ⟨hu, hroot⟩, -⟩ := exists_unique_pos_root (offDiagonalMass_nonneg hpos)
    (offDiagonalProduct_pos hpos) (diagonalMass_pos hpos)
  have htop : IsTopRoot p u :=
    isTopRoot_of_pos_root (offDiagonalProduct_pos hpos).le
      (diagonalMass_pos hpos).le hu hroot
  have hroot' : cubicRoot p = u := cubicRoot_eq htop
  rw [hroot']
  refine ⟨htop, ?_⟩
  by_cases hnc : Nonconstant p u
  · exact Or.inl ⟨hnc, tau_eq_contact hp hpos hu hnc hroot⟩
  · exact Or.inr ⟨hnc, tau_eq_self hp hpos hdet htop hnc⟩

end StochasticToDeterministicLatents.Binary
