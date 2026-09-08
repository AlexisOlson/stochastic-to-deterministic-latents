/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Renamed, restated over the
public interfaces of this library, and re-proved where the argument differs.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRayEnds
import StochasticToDeterministicLatents.Binary.FactorTwo.ChordScalars

/-!
# The ray's law at the critical radius

At the critical radius the diagonal product `entryA * entryD` is exactly the
square of the ray's root, so the geometric mean of the diagonal *is* that
root.  **No `ChordDomain` holds there, at any top root.**  Such a domain's
`nonconstant` field (`Chord.lean:213`) would put its own root strictly below
that geometric mean, hence strictly below the ray's root; its `topRoot`
field then makes the cubic strictly positive at every larger point, and
`rayLaw_cubic` says the cubic vanishes at the ray's root.  So everything
that takes one -- `rayConstantScalar_eq` and
`log_two_mul_phi_contact_chart` among them -- is unavailable.  The route that
would have supplied one is closed for the matching reason: `chordDomain_rayLaw`
asks for the chart's interior condition `0 < 1 - r - 3 omega`, and that
condition degenerates to an equality at this radius.  What survives is the
contact itself: the two diagonal contacts coalesce, the ray's root is still
the cubic's root, and `log_two_mul_phi_contact`, which asks only for a fully
supported probability law, a positive root, and the two cubic conditions,
still gives `Phi`.

The consequence is the page's identification at that end of the ray: the
constant code's margin there is `Real.log 2` times the law's own mutual
information `Psi - Phi`.

**Two conventions meet in this module.**  `entropy`, `Psi`, `Phi` and the
mutual information are in bits; `centerLogEntropy`, `centerMarginalEntropy`,
`chartHeight` and `rayConstantScalar` are in natural-log units.  Every
statement below therefore carries an explicit `Real.log 2`, as in
`ChordScalars`.

**What is not proved here.**  The page states that the mutual information at
the critical radius is *positive*, and gives a reason: the law there is not a
product law.  This module proves only that it is **nonnegative**, through
`psi_sub_phi_nonneg`.  `psi_sub_phi_pos` now supplies the
strict inequality for any full-support law of nonvanishing determinant, but
nothing here shows that the law at the critical radius has one, so the
endpoint below is still stated in its nonnegative form.  The endpoint
comparison that consumes it uses only the nonnegativity, so nothing waits
on the strict inequality.
-/

namespace StochasticToDeterministicLatents.Binary

variable {z r : ℝ}

/-! ## The law's entries, in the ray's coordinates

Everything below reads the ray law's four cells and its two aggregates in
terms of the root, so they are collected once. -/

private theorem rayLaw_entries (z r : ℝ) :
    entryA (rayLaw z r) = (1 - rayMass z r) / 2
      ∧ entryB (rayLaw z r) = (1 + z) * r / 2 * rayRoot z r
      ∧ entryC (rayLaw z r) = (1 - z) * r / 2 * rayRoot z r
      ∧ entryD (rayLaw z r) = (1 - rayMass z r) / 2 := by
  have hmass : rayMass z r = r * rayRoot z r := rfl
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show rayMass z r * (1 + z) / 2 = _
    rw [hmass]
    ring
  · show rayMass z r * (1 - z) / 2 = _
    rw [hmass]
    ring

private theorem rayLaw_aggregates (z r : ℝ) :
    diagonalMass (rayLaw z r) = 1 - rayMass z r
      ∧ offDiagonalMass (rayLaw z r) = rayMass z r
      ∧ offDiagonalProduct (rayLaw z r)
        = rayProductCoeff z * r ^ 2 * rayRoot z r ^ 2 := by
  have hmass : rayMass z r = r * rayRoot z r := rfl
  refine ⟨?_, ?_, ?_⟩
  · show (1 - rayMass z r) / 2 + (1 - rayMass z r) / 2 = _
    ring
  · show rayMass z r * (1 + z) / 2 + rayMass z r * (1 - z) / 2 = _
    ring
  · rw [offDiagonalProduct_eq]
    show rayMass z r * (1 + z) / 2 * (rayMass z r * (1 - z) / 2) = _
    rw [hmass]
    unfold rayProductCoeff
    ring

/-! ## The ray's root is a root of the cubic, at every radius -/

/-- **The cubic vanishes at the ray's root** on the whole closed interval, the
critical radius included.  `chartRoot_cubic` does not serve at that radius: it
takes a `ChartDomain`, whose interior condition degenerates there. -/
private theorem rayLaw_cubic (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    cubic (rayLaw z r) (rayRoot z r) = 0 := by
  have hn := rayNorm_pos hz hr
  have hmass : rayMass z r = r * rayRoot z r := rfl
  obtain ⟨hS, hV, hW⟩ := rayLaw_aggregates z r
  have hU : rayRoot z r * ((1 - r) * (1 - rayProductCoeff z * r ^ 2))
      = rayProductCoeff z * r ^ 2 := by
    show chartRoot r (rayProductCoeff z * r ^ 2) * _ = _
    unfold chartRoot
    unfold chartNorm at hn
    exact div_mul_cancel₀ _ hn.ne'
  have e : cubic (rayLaw z r) (rayRoot z r)
      = rayRoot z r ^ 2
        * (rayRoot z r * ((1 - r) * (1 - rayProductCoeff z * r ^ 2))
          - rayProductCoeff z * r ^ 2) := by
    unfold cubic
    rw [hV, hW, hS, hmass]
    ring
  rw [e, hU]
  ring

/-! ## The contact coalesces at the critical radius -/

/-- The diagonal product at the critical radius is the root's square: the two
contacts of the law there are the same law. -/
private theorem rayLaw_boundary_diagonal (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    entryA (rayLaw z (criticalRadius z)) * entryD (rayLaw z (criticalRadius z))
      = rayRoot z (criticalRadius z) ^ 2 := by
  obtain ⟨hA, -, -, hD⟩ := rayLaw_entries z (criticalRadius z)
  obtain ⟨hv, hu⟩ := ray_boundary_values hz
  rw [hA, hD, hv, hu]
  ring

/-- **The two diagonal contacts meet at the critical radius.**  The contact
radius is zero there and the upper contact is the law itself.  This is the
page's `rho = 0` and `q^+ = p^o`, and it is what makes the identification
below an identification of the law's own mutual information. -/
theorem rayLaw_coalesces (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    contactRadius (rayLaw z (criticalRadius z)) (rayRoot z (criticalRadius z))
        = 0
      ∧ contactAt (rayLaw z (criticalRadius z)) (rayRoot z (criticalRadius z))
        = rayLaw z (criticalRadius z) := by
  obtain ⟨hv, hu⟩ := ray_boundary_values hz
  obtain ⟨hS, -, -⟩ := rayLaw_aggregates z (criticalRadius z)
  have hs : diagonalMass (rayLaw z (criticalRadius z)) = 1 - criticalMass z := by
    rw [hS, hv]
  have hrad : contactRadius (rayLaw z (criticalRadius z))
      (rayRoot z (criticalRadius z)) = 0 := by
    unfold contactRadius
    rw [hs, hu]
    rw [show (1 - criticalMass z) ^ 2 - 4 * ((1 - criticalMass z) / 2) ^ 2 = 0 by
      ring]
    exact Real.sqrt_zero
  refine ⟨hrad, ?_⟩
  funext a
  rcases a with ⟨x, y⟩
  fin_cases x <;> fin_cases y
  · show (diagonalMass (rayLaw z (criticalRadius z))
      + contactRadius (rayLaw z (criticalRadius z))
        (rayRoot z (criticalRadius z))) / 2 = _
    rw [hs, hrad]
    show _ = (1 - rayMass z (criticalRadius z)) / 2
    rw [hv]
    ring
  · simp [contactAt]
  · simp [contactAt]
  · show (diagonalMass (rayLaw z (criticalRadius z))
      - contactRadius (rayLaw z (criticalRadius z))
        (rayRoot z (criticalRadius z))) / 2 = _
    rw [hs, hrad]
    show _ = (1 - rayMass z (criticalRadius z)) / 2
    rw [hv]
    ring

/-! ## The three entropies along the ray -/

/-- The ray law's entropy and its two marginal entropies, in natural-log
units, are the centre's two scalar ledgers at the ray's off-diagonal mass. -/
private theorem log_two_mul_entropy_rayLaw (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    Real.log 2 * entropy (rayLaw z r) = centerLogEntropy (rayMass z r) z
      ∧ Real.log 2 * entropy (stoch_to_det.mX (rayLaw z r))
        = centerMarginalEntropy (rayMass z r) z
      ∧ Real.log 2 * entropy (stoch_to_det.mY (rayLaw z r))
        = centerMarginalEntropy (rayMass z r) z := by
  have hp := (rayLaw_isPMF hz hr).1
  have hpX : IsPMF (stoch_to_det.mX (rayLaw z r)) :=
    pushforward_isPMF (f := Prod.fst) hp
  have hpY : IsPMF (stoch_to_det.mY (rayLaw z r)) :=
    pushforward_isPMF (f := Prod.snd) hp
  refine ⟨?_, ?_, ?_⟩
  · rw [log_two_mul_entropy hp, sum_cells]
    show -(xLogX ((1 - rayMass z r) / 2) + xLogX (rayMass z r * (1 + z) / 2)
      + xLogX (rayMass z r * (1 - z) / 2) + xLogX ((1 - rayMass z r) / 2)) = _
    unfold centerLogEntropy
    ring
  · have h0 : stoch_to_det.mX (rayLaw z r) 0 = (1 + rayMass z r * z) / 2 := by
      rw [marginalX_zero]
      show (1 - rayMass z r) / 2 + rayMass z r * (1 + z) / 2 = _
      ring
    have h1 : stoch_to_det.mX (rayLaw z r) 1 = (1 - rayMass z r * z) / 2 := by
      rw [marginalX_one]
      show rayMass z r * (1 - z) / 2 + (1 - rayMass z r) / 2 = _
      ring
    rw [log_two_mul_entropy hpX, Fin.sum_univ_two, h0, h1]
    unfold centerMarginalEntropy
    ring
  · have h0 : stoch_to_det.mY (rayLaw z r) 0 = (1 - rayMass z r * z) / 2 := by
      rw [marginalY_zero]
      show (1 - rayMass z r) / 2 + rayMass z r * (1 - z) / 2 = _
      ring
    have h1 : stoch_to_det.mY (rayLaw z r) 1 = (1 + rayMass z r * z) / 2 := by
      rw [marginalY_one]
      show rayMass z r * (1 + z) / 2 + (1 - rayMass z r) / 2 = _
      ring
    rw [log_two_mul_entropy hpY, Fin.sum_univ_two, h0, h1]
    unfold centerMarginalEntropy
    ring

/-- `Phi` along the ray.  The private material's `lowerPhi` is `-Phi`, so this
statement is the negation of the one it was adapted from. -/
private theorem log_two_mul_phi_rayLaw (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    Real.log 2 * Phi (rayLaw z r)
      = 3 * centerLogEntropy (rayMass z r) z
        - 4 * centerMarginalEntropy (rayMass z r) z := by
  obtain ⟨h1, h2, h3⟩ := log_two_mul_entropy_rayLaw hz hr
  show Real.log 2 * stoch_to_det.Phi (rayLaw z r) = _
  rw [stoch_to_det.Phi]
  linear_combination 3 * h1 - 2 * h2 - 2 * h3

/-- `Psi` along the ray. -/
private theorem log_two_mul_psi_rayLaw (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) :
    Real.log 2 * Psi (rayLaw z r)
      = 2 * centerLogEntropy (rayMass z r) z
        - 2 * centerMarginalEntropy (rayMass z r) z := by
  obtain ⟨h1, h2, h3⟩ := log_two_mul_entropy_rayLaw hz hr
  show Real.log 2 * stoch_to_det.Psi (rayLaw z r) = _
  rw [stoch_to_det.Psi]
  linear_combination 2 * h1 - h2 - h3

/-! ## The height, where the two contacts have already met -/

/-- The chart's height along the ray is minus `Real.log 2 * Phi` of the law
there, wherever the law's diagonal product is the root's square.  On a chord
domain this is `log_two_mul_phi_contact_chart`; the hypothesis here is the
weaker one `log_two_mul_phi_contact` actually asks for, and it holds at the
critical radius, where no chord domain does. -/
private theorem rayHeight_eq_neg_phi (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) (criticalRadius z)) (hr0 : 0 < r)
    (hd : entryA (rayLaw z r) * entryD (rayLaw z r) = rayRoot z r ^ 2) :
    chartHeight ((1 + z) * r / 2) ((1 - z) * r / 2)
      = -(Real.log 2 * Phi (rayLaw z r)) := by
  have hr1 : r < 1 := lt_of_le_of_lt hr.2 (criticalRadius_spec hz).2.1
  have hn := rayNorm_pos hz hr
  have hq := (rayLaw_isPMF hz hr).1
  have hpos := (rayLaw_isPMF hz hr).2 hr0
  obtain ⟨hA, hB, hC, hD⟩ := rayLaw_entries z r
  obtain ⟨hS, -, -⟩ := rayLaw_aggregates z r
  have hU0 : 0 < rayRoot z r := by
    show 0 < chartRoot r (rayProductCoeff z * r ^ 2)
    unfold chartRoot
    refine div_pos (mul_pos ?_ (pow_pos hr0 2)) hn
    unfold rayProductCoeff
    nlinarith [hz.1, hz.2]
  have hx : 0 < (1 + z) * r / 2 :=
    div_pos (mul_pos (by linarith [hz.1]) hr0) (by norm_num)
  have hy : 0 < (1 - z) * r / 2 :=
    div_pos (mul_pos (sub_pos.mpr hz.2) hr0) (by norm_num)
  have hxy : (1 + z) * r / 2 + (1 - z) * r / 2 = r := by ring
  have hprod : (1 + z) * r / 2 * ((1 - z) * r / 2)
      = rayProductCoeff z * r ^ 2 := by
    unfold rayProductCoeff
    ring
  obtain ⟨-, hLb, hLc⟩ := chart_certValues hx hy (by rw [hxy]; exact hr1)
  have hUeq : chartRoot ((1 + z) * r / 2 + (1 - z) * r / 2)
      ((1 + z) * r / 2 * ((1 - z) * r / 2)) = rayRoot z r := by
    rw [hxy, hprod]
    rfl
  rw [hUeq] at hLb hLc
  have hsum : 1 - (1 + z) * r / 2 - (1 - z) * r / 2 = 1 - r := by ring
  have hd0 : 1 - (1 + z) * r / 2 - (1 - z) * r / 2 ≠ 0 := by
    rw [hsum]
    exact sub_ne_zero.mpr hr1.ne'
  have hx1 : (1 + z) * r / 2 < 1 := by linarith [hxy, hy, hr1]
  have hy1 : (1 - z) * r / 2 < 1 := by linarith [hxy, hx, hr1]
  have hx10 : 1 - (1 + z) * r / 2 ≠ 0 := sub_ne_zero.mpr hx1.ne'
  have hy10 : 1 - (1 - z) * r / 2 ≠ 0 := sub_ne_zero.mpr hy1.ne'
  rw [log_two_mul_phi_contact hq hpos hU0 hd (rayLaw_cubic hz hr), hS, hB, hC,
    hLb, hLc, rayHeight_eq,
    Real.log_div (mul_ne_zero (mul_pos hx hU0).ne' (pow_ne_zero 2 hd0))
      (pow_ne_zero 2 hx10),
    Real.log_div (mul_ne_zero (mul_pos hy hU0).ne' (pow_ne_zero 2 hd0))
      (pow_ne_zero 2 hy10),
    Real.log_mul (mul_pos hx hU0).ne' (pow_ne_zero 2 hd0),
    Real.log_mul (mul_pos hy hU0).ne' (pow_ne_zero 2 hd0),
    Real.log_pow, Real.log_pow, Real.log_pow, hsum]
  unfold xLogX
  rw [show rayMass z r = r * rayRoot z r from rfl]
  ring

/-! ## The constant code's margin at the critical radius -/

/-- **The identification in part (2) of the page's Lemma 4.4.**  At the
critical radius the constant code's margin is `Real.log 2` times the law's
mutual information `Psi - Phi`.  The margin is in natural-log units and the
mutual information in bits, which is what the factor carries. -/
theorem rayConstantScalar_boundary_eq (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    rayConstantScalar z (criticalRadius z)
      = Real.log 2 * (Psi (rayLaw z (criticalRadius z))
        - Phi (rayLaw z (criticalRadius z))) := by
  have hrc := criticalRadius_spec hz
  have hr : criticalRadius z ∈ Set.Icc (0 : ℝ) (criticalRadius z) :=
    ⟨hrc.1.le, le_rfl⟩
  have h1 := log_two_mul_phi_rayLaw hz hr
  have h2 := log_two_mul_psi_rayLaw hz hr
  have hh := rayHeight_eq_neg_phi hz hr hrc.1 (rayLaw_boundary_diagonal hz)
  unfold rayConstantScalar centerConstantScalar
  rw [hh, mul_sub]
  linarith [h1, h2]

/-- **The page's inequality there, weakened.**  The margin at the critical
radius is nonnegative, because a mutual information is.  The page claims it
is *positive*, from the law there not being a product law.  The general
fact is available as `psi_sub_phi_pos`; **what is missing is its hypothesis
here**, since nothing in this tree computes the determinant of the law at
the critical radius. -/
theorem rayConstantScalar_boundary_nonneg (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    0 ≤ rayConstantScalar z (criticalRadius z) := by
  rw [rayConstantScalar_boundary_eq hz]
  refine mul_nonneg (Real.log_nonneg (by norm_num)) ?_
  exact psi_sub_phi_nonneg
    (rayLaw_isPMF hz ⟨(criticalRadius_spec hz).1.le, le_rfl⟩).1

end StochasticToDeterministicLatents.Binary
