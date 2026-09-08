import StochasticToDeterministicLatents.Binary.FactorTwo.Contact

/-!
# The tangent certificate touches at both contacts

The tangent certificate of `Phi` at the upper contact `contactAt p u` pairs
with the lower contact to give `Phi` there too, when `u` is a root of the
cubic.  Together with the majorant property this pins `tau p` at a contact
pair: the certificate is tight at both components of the mixture, so the bound
of `tau_le_contact` is met from below as well.

Two facts carry the argument.  The diagonal swap is a relabelling of the four
cells, so `Phi` is invariant under it and the two contacts carry the same
`Phi`.  And at a root of the cubic the logarithmic difference of the two
contacts vanishes, which reduces to an algebraic identity in the cells.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

/-! ## The diagonal swap is a relabelling -/

/-- The diagonal swap as an equivalence of the four cells. -/
private def diagonalSwap : Cell ≃ Cell := Equiv.swap ((0, 0) : Cell) (1, 1)

/-- Reversal of the binary alphabet. -/
private def bitSwap : Bit ≃ Bit := Equiv.swap 0 1

private theorem swapDiagonal_eq_push (q : RealTable) :
    swapDiagonal q = stoch_to_det.push diagonalSwap q := by
  classical
  funext z
  have hpoint : swapDiagonal q z = q (diagonalSwap.symm z) := by
    fin_cases z <;> rfl
  rw [hpoint]
  unfold stoch_to_det.push
  symm
  apply Finset.sum_eq_single (diagonalSwap.symm z)
  · intro b hb hne
    have hb' : diagonalSwap b = z := (Finset.mem_filter.mp hb).2
    exact (hne (by simpa using congrArg diagonalSwap.symm hb')).elim
  · simp

private theorem fst_comp_diagonalSwap :
    Prod.fst ∘ diagonalSwap = bitSwap ∘ Prod.snd := by
  funext z
  fin_cases z <;> rfl

private theorem snd_comp_diagonalSwap :
    Prod.snd ∘ diagonalSwap = bitSwap ∘ Prod.fst := by
  funext z
  fin_cases z <;> rfl

private theorem marginalX_swapDiagonal (q : RealTable) :
    stoch_to_det.mX (swapDiagonal q)
      = stoch_to_det.push bitSwap (stoch_to_det.mY q) := by
  rw [swapDiagonal_eq_push]
  change stoch_to_det.push Prod.fst (stoch_to_det.push diagonalSwap q)
    = stoch_to_det.push bitSwap (stoch_to_det.push Prod.snd q)
  rw [stoch_to_det.push_push, fst_comp_diagonalSwap, ← stoch_to_det.push_push]

private theorem marginalY_swapDiagonal (q : RealTable) :
    stoch_to_det.mY (swapDiagonal q)
      = stoch_to_det.push bitSwap (stoch_to_det.mX q) := by
  rw [swapDiagonal_eq_push]
  change stoch_to_det.push Prod.snd (stoch_to_det.push diagonalSwap q)
    = stoch_to_det.push bitSwap (stoch_to_det.push Prod.fst q)
  rw [stoch_to_det.push_push, snd_comp_diagonalSwap, ← stoch_to_det.push_push]

/-- `Phi` is invariant under the diagonal swap, which only relabels cells. -/
private theorem phi_swapDiagonal (q : RealTable) (hq : IsPMF q) :
    Phi (swapDiagonal q) = Phi q := by
  have hX : entropy (stoch_to_det.mX (swapDiagonal q))
      = entropy (stoch_to_det.mY q) := by
    rw [marginalX_swapDiagonal]
    exact stoch_to_det.H_push_equiv bitSwap (stoch_to_det.mY q)
      (stoch_to_det.isPMF_push hq)
  have hY : entropy (stoch_to_det.mY (swapDiagonal q))
      = entropy (stoch_to_det.mX q) := by
    rw [marginalY_swapDiagonal]
    exact stoch_to_det.H_push_equiv bitSwap (stoch_to_det.mX q)
      (stoch_to_det.isPMF_push hq)
  have hH : entropy (swapDiagonal q) = entropy q := by
    rw [swapDiagonal_eq_push]
    exact stoch_to_det.H_push_equiv diagonalSwap q hq
  show 3 * entropy (swapDiagonal q)
      - 2 * entropy (stoch_to_det.mX (swapDiagonal q))
      - 2 * entropy (stoch_to_det.mY (swapDiagonal q))
    = 3 * entropy q - 2 * entropy (stoch_to_det.mX q)
      - 2 * entropy (stoch_to_det.mY q)
  rw [hH, hX, hY]
  ring

private theorem oppositeContactAt_eq_swapDiagonal (p : RealTable) (u : ℝ) :
    oppositeContactAt p u = swapDiagonal (contactAt p u) := by
  funext z
  fin_cases z <;> simp [oppositeContactAt, contactAt, swapDiagonal]

/-- The two contacts carry the same `Phi`: they differ by a relabelling of the
diagonal.  This is the hypothesis `tau_le_contact` takes. -/
theorem phi_oppositeContactAt {p : RealTable} {u : ℝ} (hp : IsPMF p)
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u) :
    Phi (contactAt p u) = Phi (oppositeContactAt p u) := by
  rw [oppositeContactAt_eq_swapDiagonal,
    phi_swapDiagonal _ (isPMF_contactAt hp hpos hu hnc)]

/-! ## The two diagonal cells of a contact -/

/-- The larger diagonal cell `(s + r)/2` of the contact pair. -/
noncomputable def upperContactCell (p : RealTable) (u : ℝ) : ℝ :=
  (diagonalMass p + contactRadius p u) / 2

/-- The smaller diagonal cell `(s - r)/2` of the contact pair. -/
noncomputable def lowerContactCell (p : RealTable) (u : ℝ) : ℝ :=
  (diagonalMass p - contactRadius p u) / 2

@[simp] theorem contactAt_apply_zero (p : RealTable) (u : ℝ) :
    contactAt p u (0, 0) = upperContactCell p u := rfl

@[simp] theorem contactAt_apply_one (p : RealTable) (u : ℝ) :
    contactAt p u (1, 1) = lowerContactCell p u := by
  simp [contactAt, lowerContactCell]

@[simp] theorem oppositeContactAt_apply_zero (p : RealTable) (u : ℝ) :
    oppositeContactAt p u (0, 0) = lowerContactCell p u := rfl

@[simp] theorem oppositeContactAt_apply_one (p : RealTable) (u : ℝ) :
    oppositeContactAt p u (1, 1) = upperContactCell p u := by
  simp [oppositeContactAt, upperContactCell]

theorem upperContactCell_pos {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : 0 < upperContactCell p u := by
  have hs : 0 < diagonalMass p := add_pos (hpos (0, 0)) (hpos (1, 1))
  exact div_pos (add_pos hs (contactRadius_pos hpos hu hnc)) (by norm_num)

theorem lowerContactCell_pos {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) : 0 < lowerContactCell p u :=
  diagonalMass_sub_contactRadius_pos hpos hu hnc

/-! ## The quadratic in the off-diagonal data -/

/-- The monic quadratic `x^2 + v x + w` whose coefficients are the off-diagonal
mass and product. -/
noncomputable def offDiagonalQuadratic (p : RealTable) (x : ℝ) : ℝ :=
  x ^ 2 + offDiagonalMass p * x + offDiagonalProduct p

/-- The quadratic factors through the two off-diagonal cells. -/
theorem offDiagonalQuadratic_factor (p : RealTable) (x : ℝ) :
    (x + entryB p) * (x + entryC p) = offDiagonalQuadratic p x := by
  rw [offDiagonalQuadratic, offDiagonalMass, offDiagonalProduct_eq]
  ring

/-! ## The cubic seen from the contact pair -/

private theorem contactCell_mul {p : RealTable} {u : ℝ} (hpos : FullSupport p)
    (hu : 0 < u) (hnc : Nonconstant p u) :
    upperContactCell p u * lowerContactCell p u = u ^ 2 := by
  have hr := contactRadius_sq hpos hu hnc
  rw [upperContactCell, lowerContactCell]
  nlinarith

private theorem contactCell_poly {p : RealTable} {u : ℝ}
    (hAD : upperContactCell p u * lowerContactCell p u = u ^ 2) :
    u ^ 3 * offDiagonalQuadratic p (lowerContactCell p u)
        - lowerContactCell p u ^ 3 * offDiagonalQuadratic p (upperContactCell p u)
      = -(lowerContactCell p u * (u - lowerContactCell p u)) * cubic p u := by
  have hs : diagonalMass p = upperContactCell p u + lowerContactCell p u := by
    rw [upperContactCell, lowerContactCell]; ring
  rw [cubic, offDiagonalQuadratic, offDiagonalQuadratic, hs]
  linear_combination
    (-lowerContactCell p u * (u ^ 2 + upperContactCell p u * lowerContactCell p u)
      - lowerContactCell p u ^ 2 * offDiagonalMass p
      - offDiagonalProduct p * (u - lowerContactCell p u)) * hAD

private theorem contactCell_cubic_eq {p : RealTable} {u : ℝ}
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u)
    (hroot : cubic p u = 0) :
    u ^ 3 * offDiagonalQuadratic p (lowerContactCell p u)
      = lowerContactCell p u ^ 3 * offDiagonalQuadratic p (upperContactCell p u) := by
  have h := contactCell_poly (contactCell_mul hpos hu hnc)
  rw [hroot] at h
  linarith

/-- At a root of the cubic the two contacts satisfy a cube-square identity,
which is what makes the tangent certificate touch at both. -/
theorem contactCell_cube_quadratic_sq {p : RealTable} {u : ℝ}
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u)
    (hroot : cubic p u = 0) :
    upperContactCell p u ^ 3 * offDiagonalQuadratic p (lowerContactCell p u) ^ 2
      = lowerContactCell p u ^ 3
        * offDiagonalQuadratic p (upperContactCell p u) ^ 2 := by
  set A := upperContactCell p u with hA
  set D := lowerContactCell p u with hD
  set Q := offDiagonalQuadratic p D
  set P := offDiagonalQuadratic p A
  have hAD : A * D = u ^ 2 := contactCell_mul hpos hu hnc
  have hc : u ^ 3 * Q = D ^ 3 * P := contactCell_cubic_eq hpos hu hnc hroot
  have hsquared : u ^ 6 * Q ^ 2 = D ^ 6 * P ^ 2 := by
    calc u ^ 6 * Q ^ 2 = (u ^ 3 * Q) ^ 2 := by ring
      _ = (D ^ 3 * P) ^ 2 := by rw [hc]
      _ = D ^ 6 * P ^ 2 := by ring
  have hDpos : 0 < D := lowerContactCell_pos hpos hu hnc
  have hcancel : D ^ 3 * (A ^ 3 * Q ^ 2) = D ^ 3 * (D ^ 3 * P ^ 2) := by
    have hpow : D ^ 3 * A ^ 3 = u ^ 6 := by
      calc D ^ 3 * A ^ 3 = (A * D) ^ 3 := by ring
        _ = (u ^ 2) ^ 3 := by rw [hAD]
        _ = u ^ 6 := by ring
    calc D ^ 3 * (A ^ 3 * Q ^ 2) = (D ^ 3 * A ^ 3) * Q ^ 2 := by ring
      _ = u ^ 6 * Q ^ 2 := by rw [hpow]
      _ = D ^ 6 * P ^ 2 := hsquared
      _ = D ^ 3 * (D ^ 3 * P ^ 2) := by ring
  exact mul_left_cancel₀ (pow_ne_zero 3 hDpos.ne') hcancel

/-! ## The certificate difference between the two contacts -/

private theorem contactAt_apply_zero_one (p : RealTable) (u : ℝ) :
    contactAt p u (0, 1) = entryB p := by
  simp [contactAt, entryB]

private theorem contactAt_apply_one_zero (p : RealTable) (u : ℝ) :
    contactAt p u (1, 0) = entryC p := by
  simp [contactAt, entryC]

private theorem oppositeContactAt_apply_zero_one (p : RealTable) (u : ℝ) :
    oppositeContactAt p u (0, 1) = entryB p := by
  simp [oppositeContactAt, entryB]

private theorem oppositeContactAt_apply_one_zero (p : RealTable) (u : ℝ) :
    oppositeContactAt p u (1, 0) = entryC p := by
  simp [oppositeContactAt, entryC]

/-- The logarithmic difference between the two contacts vanishes at a root of
the cubic.  This is the cube-square identity read through the logarithm. -/
private theorem contact_log_identity {p : RealTable} {u : ℝ}
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u)
    (hroot : cubic p u = 0) :
    -3 * Real.logb 2 (upperContactCell p u / lowerContactCell p u)
      + 2 * Real.logb 2 ((upperContactCell p u + entryB p)
        / (lowerContactCell p u + entryB p))
      + 2 * Real.logb 2 ((upperContactCell p u + entryC p)
        / (lowerContactCell p u + entryC p)) = 0 := by
  set A := upperContactCell p u with hAdef
  set D := lowerContactCell p u with hDdef
  have hA : 0 < A := upperContactCell_pos hpos hu hnc
  have hD : 0 < D := lowerContactCell_pos hpos hu hnc
  have hb : 0 < entryB p := hpos (0, 1)
  have hc : 0 < entryC p := hpos (1, 0)
  have hsq := contactCell_cube_quadratic_sq hpos hu hnc hroot
  rw [← offDiagonalQuadratic_factor p D, ← offDiagonalQuadratic_factor p A] at hsq
  have hlog := congrArg Real.log hsq
  rw [Real.log_mul (pow_ne_zero 3 hA.ne')
      (pow_ne_zero 2 (mul_pos (add_pos hD hb) (add_pos hD hc)).ne'),
    Real.log_mul (pow_ne_zero 3 hD.ne')
      (pow_ne_zero 2 (mul_pos (add_pos hA hb) (add_pos hA hc)).ne')] at hlog
  simp_rw [Real.log_pow] at hlog
  rw [Real.log_mul (add_pos hD hb).ne' (add_pos hD hc).ne',
    Real.log_mul (add_pos hA hb).ne' (add_pos hA hc).ne'] at hlog
  rw [Real.logb_div hA.ne' hD.ne',
    Real.logb_div (add_pos hA hb).ne' (add_pos hD hb).ne',
    Real.logb_div (add_pos hA hc).ne' (add_pos hD hc).ne']
  unfold Real.logb
  have hnum : -(3 * (Real.log A - Real.log D))
      + 2 * (Real.log (A + entryB p) - Real.log (D + entryB p))
      + 2 * (Real.log (A + entryC p) - Real.log (D + entryC p)) = 0 := by
    norm_num at hlog ⊢
    linarith
  field_simp
  simpa using hnum

private theorem certDiff_zero_zero {p : RealTable} {u : ℝ}
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u) :
    tangentCert (contactAt p u) (0, 0) - tangentCert (oppositeContactAt p u) (0, 0)
      = -3 * Real.logb 2 (upperContactCell p u / lowerContactCell p u)
        + 2 * Real.logb 2 ((upperContactCell p u + entryB p)
          / (lowerContactCell p u + entryB p))
        + 2 * Real.logb 2 ((upperContactCell p u + entryC p)
          / (lowerContactCell p u + entryC p)) := by
  have hA : 0 < upperContactCell p u := upperContactCell_pos hpos hu hnc
  have hD : 0 < lowerContactCell p u := lowerContactCell_pos hpos hu hnc
  have hb : 0 < entryB p := hpos (0, 1)
  have hc : 0 < entryC p := hpos (1, 0)
  unfold tangentCert
  rw [marginalX_zero, marginalY_zero, marginalX_zero, marginalY_zero]
  simp only [contactAt_apply_zero, contactAt_apply_zero_one, contactAt_apply_one_zero,
    oppositeContactAt_apply_zero, oppositeContactAt_apply_zero_one,
    oppositeContactAt_apply_one_zero]
  rw [Real.logb_div hA.ne' hD.ne',
    Real.logb_div (add_pos hA hb).ne' (add_pos hD hb).ne',
    Real.logb_div (add_pos hA hc).ne' (add_pos hD hc).ne']
  ring

private theorem certDiff_zero_one {p : RealTable} {u : ℝ} :
    tangentCert (contactAt p u) (0, 1)
      - tangentCert (oppositeContactAt p u) (0, 1) = 0 := by
  unfold tangentCert
  rw [marginalX_zero, marginalY_one, marginalX_zero, marginalY_one]
  simp only [contactAt_apply_zero, contactAt_apply_one, contactAt_apply_zero_one,
    oppositeContactAt_apply_zero, oppositeContactAt_apply_one,
    oppositeContactAt_apply_zero_one]
  ring_nf

private theorem certDiff_one_zero {p : RealTable} {u : ℝ} :
    tangentCert (contactAt p u) (1, 0)
      - tangentCert (oppositeContactAt p u) (1, 0) = 0 := by
  unfold tangentCert
  rw [marginalX_one, marginalY_zero, marginalX_one, marginalY_zero]
  simp only [contactAt_apply_zero, contactAt_apply_one, contactAt_apply_one_zero,
    oppositeContactAt_apply_zero, oppositeContactAt_apply_one,
    oppositeContactAt_apply_one_zero]
  ring_nf

private theorem certDiff_one_one {p : RealTable} {u : ℝ}
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u) :
    tangentCert (contactAt p u) (1, 1) - tangentCert (oppositeContactAt p u) (1, 1)
      = -(-3 * Real.logb 2 (upperContactCell p u / lowerContactCell p u)
        + 2 * Real.logb 2 ((upperContactCell p u + entryB p)
          / (lowerContactCell p u + entryB p))
        + 2 * Real.logb 2 ((upperContactCell p u + entryC p)
          / (lowerContactCell p u + entryC p))) := by
  have hA : 0 < upperContactCell p u := upperContactCell_pos hpos hu hnc
  have hD : 0 < lowerContactCell p u := lowerContactCell_pos hpos hu hnc
  have hb : 0 < entryB p := hpos (0, 1)
  have hc : 0 < entryC p := hpos (1, 0)
  unfold tangentCert
  rw [marginalX_one, marginalY_one, marginalX_one, marginalY_one]
  simp only [contactAt_apply_one, contactAt_apply_zero_one, contactAt_apply_one_zero,
    oppositeContactAt_apply_one, oppositeContactAt_apply_zero_one,
    oppositeContactAt_apply_one_zero]
  rw [Real.logb_div hA.ne' hD.ne',
    Real.logb_div (add_pos hA hb).ne' (add_pos hD hb).ne',
    Real.logb_div (add_pos hA hc).ne' (add_pos hD hc).ne']
  ring_nf

/-- The tangent certificate at the upper contact pairs with the lower contact
to give `Phi` there.  With `tangentCert_self` this makes the certificate tight
at both components of the contact mixture. -/
theorem tangentCert_contact_pairing {p : RealTable} {u : ℝ} (hp : IsPMF p)
    (hpos : FullSupport p) (hu : 0 < u) (hnc : Nonconstant p u)
    (hroot : cubic p u = 0) :
    (∑ z, tangentCert (contactAt p u) z * oppositeContactAt p u z)
      = Phi (oppositeContactAt p u) := by
  have hmix := contact_mixture hp hpos hu hnc
  have hself := tangentCert_self (oppositeContactAt p u) hmix.2.1
  have hzero := contact_log_identity hpos hu hnc hroot
  have hdiff : (∑ z, (tangentCert (contactAt p u) z
      - tangentCert (oppositeContactAt p u) z) * oppositeContactAt p u z) = 0 := by
    rw [sum_cells]
    rw [certDiff_zero_zero hpos hu hnc, certDiff_zero_one, certDiff_one_zero,
      certDiff_one_one hpos hu hnc]
    simp only [oppositeContactAt_apply_zero, oppositeContactAt_apply_one,
      oppositeContactAt_apply_zero_one, oppositeContactAt_apply_one_zero]
    rw [hzero]
    ring
  calc (∑ z, tangentCert (contactAt p u) z * oppositeContactAt p u z)
      = (∑ z, (tangentCert (contactAt p u) z
          - tangentCert (oppositeContactAt p u) z) * oppositeContactAt p u z)
        + ∑ z, tangentCert (oppositeContactAt p u) z * oppositeContactAt p u z := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
    _ = Phi (oppositeContactAt p u) := by rw [hdiff, hself]; ring

end StochasticToDeterministicLatents.Binary
