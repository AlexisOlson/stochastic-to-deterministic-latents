import StochasticToDeterministicLatents.Binary.FactorTwo.Optimum

/-!
# The diagonal chord through a binary law

Sliding mass along the diagonal, with the off-diagonal and the total diagonal
mass held fixed, leaves the cubic -- and therefore the contact pair -- exactly
where it was.  So a whole segment of laws shares one stochastic optimum, and a
deterministic competitor may be tested anywhere along it.

The segment runs from the midpoint of the diagonal to the upper contact.  Its
two ends and its midpoint are ordered, the law itself lies on it whenever the
diagonal is ordered, and at each of its points the two named competitors --
the constant code and the code isolating the last cell -- are measured against
one budget: twice `Psi` at the point, less twice `Phi` at the common contact.
At the law itself that budget is twice the stochastic optimum, so if either
margin is nonnegative everywhere on the segment, then `T p ≤ 2 * tau p`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Real

variable {p : RealTable} {u t : ℝ}

/-! ## The constant competitor

`Psi q - Phi q` is the mutual information of `q`, which is the score of the
constant code.  Upstream bounds `T` by it; the public optimum agrees with the
upstream one on probability laws. -/

/-- The constant competitor bounds `T` above by `Psi p - Phi p`, exactly as
`tau_le_psi_sub_phi` bounds `tau`. -/
theorem T_le_psi_sub_phi (hp : IsPMF p) : T p ≤ Psi p - Phi p := by
  have h := stoch_to_det.T_le_Ixy hp
  have he := stoch_to_det.Phi_eq_Psi_sub_Ixy p
  rw [T_eq_upstream hp]
  linarith

/-! ## The chord -/

/-- The diagonal chord through `p`: the first diagonal entry is moved to `t`
and the second takes the rest of the diagonal mass, leaving the off-diagonal
alone. -/
noncomputable def chordAt (p : RealTable) (t : ℝ) : RealTable := fun z =>
  if z = (0, 0) then t
  else if z = (1, 1) then diagonalMass p - t
  else p z

/-- The midpoint of the diagonal, where the chord's two ends balance. -/
noncomputable def chordMidpoint (p : RealTable) : ℝ := diagonalMass p / 2

/-- The upper end of the chord: the first diagonal entry of the contact. -/
noncomputable def chordTop (p : RealTable) (u : ℝ) : ℝ := entryA (contactAt p u)

/-- The lower end of the chord: the second diagonal entry of the contact. -/
noncomputable def chordBottom (p : RealTable) (u : ℝ) : ℝ := entryD (contactAt p u)

theorem chordTop_eq : chordTop p u = (diagonalMass p + contactRadius p u) / 2 := by
  simp [chordTop, entryA, contactAt]

theorem chordBottom_eq : chordBottom p u = (diagonalMass p - contactRadius p u) / 2 := by
  simp [chordBottom, entryD, contactAt]

@[simp] theorem entryA_chordAt : entryA (chordAt p t) = t := by
  simp [entryA, chordAt]

@[simp] theorem entryB_chordAt : entryB (chordAt p t) = entryB p := by
  simp [entryB, chordAt]

@[simp] theorem entryC_chordAt : entryC (chordAt p t) = entryC p := by
  simp [entryC, chordAt]

@[simp] theorem entryD_chordAt : entryD (chordAt p t) = diagonalMass p - t := by
  simp [entryD, chordAt]

@[simp] theorem diagonalMass_chordAt : diagonalMass (chordAt p t) = diagonalMass p := by
  rw [diagonalMass, entryA_chordAt, entryD_chordAt]
  ring

@[simp] theorem offDiagonalMass_chordAt :
    offDiagonalMass (chordAt p t) = offDiagonalMass p := by
  rw [offDiagonalMass, entryB_chordAt, entryC_chordAt, offDiagonalMass]

@[simp] theorem offDiagonalProduct_chordAt :
    offDiagonalProduct (chordAt p t) = offDiagonalProduct p := by
  rw [offDiagonalProduct_eq, entryB_chordAt, entryC_chordAt, offDiagonalProduct_eq]

/-- The whole chord carries the same cubic: this is why it carries the same
stochastic optimum. -/
theorem cubic_chordAt (x : ℝ) : cubic (chordAt p t) x = cubic p x := by
  simp only [cubic, offDiagonalMass_chordAt, offDiagonalProduct_chordAt,
    diagonalMass_chordAt]

theorem isTopRoot_chordAt (h : IsTopRoot p u) : IsTopRoot (chordAt p t) u := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [cubic_chordAt]
    exact h.2.1
  · intro x hx
    rw [cubic_chordAt]
    exact h.2.2 x hx

@[simp] theorem contactRadius_chordAt :
    contactRadius (chordAt p t) u = contactRadius p u := by
  rw [contactRadius, diagonalMass_chordAt, contactRadius]

/-- **The contact pair is the same at every point of the chord.** Every other
statement in this module rests on it. -/
theorem contactAt_chordAt : contactAt (chordAt p t) u = contactAt p u := by
  funext z
  rcases z with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    simp [contactAt, chordAt, diagonalMass_chordAt, contactRadius_chordAt]

theorem determinant_chordAt :
    determinant (chordAt p t) = t * (diagonalMass p - t) - offDiagonalProduct p := by
  rw [determinant_eq, entryA_chordAt, entryB_chordAt, entryC_chordAt, entryD_chordAt,
    ← offDiagonalProduct_eq]

/-- The law itself sits on its own chord. -/
theorem chordAt_entryA : chordAt p (entryA p) = p := by
  funext z
  rcases z with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;> simp [chordAt, diagonalMass, entryA, entryD]

/-- The upper end of the chord is the contact. -/
theorem chordAt_chordTop : chordAt p (chordTop p u) = contactAt p u := by
  funext z
  rcases z with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    simp [chordAt, chordTop, contactAt, entryA, diagonalMass]
  ring

/-! ## Positivity and the sum of the two masses -/

private theorem chordMidpoint_pos (hpos : FullSupport p) : 0 < chordMidpoint p := by
  rw [chordMidpoint]
  linarith [diagonalMass_pos hpos]

/-- The two masses of a probability law exhaust it. -/
theorem diagonalMass_add_offDiagonalMass (hp : IsPMF p) :
    diagonalMass p + offDiagonalMass p = 1 := by
  have ht : (∑ z, p z) = 1 := by simpa [stoch_to_det.mass] using hp.total
  rw [sum_cells] at ht
  rw [diagonalMass, offDiagonalMass, entryA, entryB, entryC, entryD]
  linarith

/-- The cubic at the off-diagonal mass is minus the off-diagonal product. -/
private theorem cubic_offDiagonalMass (hp : IsPMF p) :
    cubic p (offDiagonalMass p) = -offDiagonalProduct p := by
  have hs : diagonalMass p = 1 - offDiagonalMass p := by
    linarith [diagonalMass_add_offDiagonalMass hp]
  rw [cubic, hs]
  ring

/-! ## The determinant is strict where the optimum is not constant

This is what lets the oriented region be taken at a nonnegative determinant
while every chord statement asks for a strictly positive one. -/

/-- A fully supported law with a non-constant top root has a nonzero
determinant. -/
private theorem determinant_ne_zero_of_nonconstant (hp : IsPMF p) (hpos : FullSupport p)
    (htop : IsTopRoot p u) (hnc : Nonconstant p u) : determinant p ≠ 0 := by
  intro hdet
  have hw : 0 < offDiagonalProduct p := offDiagonalProduct_pos hpos
  have hprod : diagonalProduct p = offDiagonalProduct p := by
    rw [determinant] at hdet
    linarith
  have hnn : 0 ≤ diagonalProduct p := hprod ▸ hw.le
  have hsq : √(diagonalProduct p) ^ 2 = offDiagonalProduct p := by
    rw [Real.sq_sqrt hnn, hprod]
  have hcube : √(diagonalProduct p) ^ 3
      = offDiagonalProduct p * √(diagonalProduct p) := by
    have : √(diagonalProduct p) ^ 3 = √(diagonalProduct p) ^ 2 * √(diagonalProduct p) := by
      ring
    rw [this, hsq]
  have hone := diagonalMass_add_offDiagonalMass hp
  have hval : cubic p √(diagonalProduct p) = -offDiagonalProduct p := by
    rw [cubic, hcube, hsq]
    nlinarith [hone]
  have hgt := htop.2.2 √(diagonalProduct p) hnc
  rw [hval] at hgt
  linarith

/-- With a nonnegative determinant, the same hypotheses make it positive. -/
theorem determinant_pos_of_nonconstant (hp : IsPMF p) (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) (htop : IsTopRoot p u) (hnc : Nonconstant p u) :
    0 < determinant p :=
  lt_of_le_of_ne hdet (Ne.symm (determinant_ne_zero_of_nonconstant hp hpos htop hnc))

/-! ## The chord domain -/

/-- The hypotheses every chord statement carries: an oriented, fully supported
law with a strictly positive determinant, at a non-constant top root. -/
structure ChordDomain (p : RealTable) (u : ℝ) : Prop where
  /-- The law is a probability law. -/
  isPMF : IsPMF p
  /-- Every cell carries positive mass. -/
  fullSupport : FullSupport p
  /-- The determinant is strictly positive. -/
  det_pos : 0 < determinant p
  /-- `u` is the top root of the cubic. -/
  topRoot : IsTopRoot p u
  /-- The top root falls below the geometric mean of the diagonal. -/
  nonconstant : Nonconstant p u
  /-- The diagonal is ordered. -/
  diagonal_le : entryD p ≤ entryA p
  /-- The off-diagonal is ordered. -/
  offDiagonal_le : entryC p ≤ entryB p

/-! ## The geometry of the chord -/

theorem offDiagonalMass_lt_topRoot (hp : IsPMF p) (hpos : FullSupport p)
    (htop : IsTopRoot p u) : offDiagonalMass p < u := by
  by_contra hn
  have hw : 0 < offDiagonalProduct p := offDiagonalProduct_pos hpos
  have hval := cubic_offDiagonalMass hp
  rcases (le_of_not_gt hn).eq_or_lt with heq | hlt
  · have hz := htop.2.1
    rw [heq, hval] at hz
    linarith
  · have hc := htop.2.2 (offDiagonalMass p) hlt
    rw [hval] at hc
    linarith

theorem topRoot_pos (hp : IsPMF p) (hpos : FullSupport p) (htop : IsTopRoot p u) :
    0 < u :=
  lt_trans (offDiagonalMass_pos hpos) (offDiagonalMass_lt_topRoot hp hpos htop)

private theorem two_mul_topRoot_lt_diagonalMass (hpos : FullSupport p)
    (hnc : Nonconstant p u) (hu : 0 ≤ u) : 2 * u < diagonalMass p := by
  obtain ⟨ha, -, -, hd⟩ := cell_pos hpos
  have had : 0 ≤ diagonalProduct p := by
    rw [diagonalProduct_eq]
    exact (mul_pos ha hd).le
  have hsqrt := Real.sq_sqrt had
  rw [Nonconstant] at hnc
  rw [diagonalMass, diagonalProduct_eq] at *
  nlinarith [sq_nonneg (entryA p - entryD p), sq_nonneg (u + √(entryA p * entryD p))]

theorem topRoot_lt_chordMidpoint (h : ChordDomain p u) : u < chordMidpoint p := by
  rw [chordMidpoint]
  linarith [two_mul_topRoot_lt_diagonalMass h.fullSupport h.nonconstant h.topRoot.1]

theorem chordBottom_pos (h : ChordDomain p u) : 0 < chordBottom p u := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  rw [chordBottom_eq]
  exact diagonalMass_sub_contactRadius_pos h.fullSupport hu h.nonconstant

theorem chordTop_add_chordBottom : chordTop p u + chordBottom p u = diagonalMass p := by
  rw [chordTop_eq, chordBottom_eq]
  ring

theorem chordBottom_lt_chordMidpoint (h : ChordDomain p u) :
    chordBottom p u < chordMidpoint p := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hr := contactRadius_pos h.fullSupport hu h.nonconstant
  rw [chordBottom_eq, chordMidpoint]
  linarith

theorem chordMidpoint_lt_chordTop (h : ChordDomain p u) :
    chordMidpoint p < chordTop p u := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hr := contactRadius_pos h.fullSupport hu h.nonconstant
  rw [chordTop_eq, chordMidpoint]
  linarith

theorem chordTop_mul_chordBottom (h : ChordDomain p u) :
    chordTop p u * chordBottom p u = u ^ 2 := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hrs := contactRadius_sq h.fullSupport hu h.nonconstant
  rw [chordTop_eq, chordBottom_eq]
  nlinarith [hrs]

/-- The law itself sits between the midpoint and the upper end, which is why
testing a competitor along the chord tests it at `p`. -/
private theorem entryA_mem_chord (h : ChordDomain p u) :
    entryA p ∈ Set.Icc (chordMidpoint p) (chordTop p u) := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have habs := abs_sub_lt_contactRadius h.fullSupport hu h.nonconstant
  rw [abs_lt] at habs
  constructor
  · rw [chordMidpoint, diagonalMass]
    linarith [h.diagonal_le]
  · rw [chordTop_eq, diagonalMass]
    linarith [habs.2]

theorem isPMF_chordAt (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) : IsPMF (chordAt p t) := by
  have hlower : 0 < t := lt_of_lt_of_le (chordMidpoint_pos h.fullSupport) ht.1
  have hupper : 0 < diagonalMass p - t := by
    have hsum := chordTop_add_chordBottom (p := p) (u := u)
    linarith [ht.2, chordBottom_pos h]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y⟩
    fin_cases x <;> fin_cases y
    · simpa [chordAt] using hlower.le
    · simpa [chordAt] using (h.fullSupport (0, 1)).le
    · simpa [chordAt] using (h.fullSupport (1, 0)).le
    · simpa [chordAt] using hupper.le
  · have hone := diagonalMass_add_offDiagonalMass h.isPMF
    have h00 : chordAt p t (0, 0) = t := by simp [chordAt]
    have h01 : chordAt p t (0, 1) = p (0, 1) := by simp [chordAt]
    have h10 : chordAt p t (1, 0) = p (1, 0) := by simp [chordAt]
    have h11 : chordAt p t (1, 1) = diagonalMass p - t := by simp [chordAt]
    rw [offDiagonalMass, entryB, entryC] at hone
    change (∑ z, chordAt p t z) = 1
    rw [sum_cells, h00, h01, h10, h11]
    linarith

theorem fullSupport_chordAt (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) : FullSupport (chordAt p t) := by
  have hupper : 0 < diagonalMass p - t := by
    have hsum := chordTop_add_chordBottom (p := p) (u := u)
    linarith [ht.2, chordBottom_pos h]
  rintro ⟨x, y⟩
  fin_cases x <;> fin_cases y
  · simpa [chordAt] using lt_of_lt_of_le (chordMidpoint_pos h.fullSupport) ht.1
  · simpa [chordAt] using h.fullSupport (0, 1)
  · simpa [chordAt] using h.fullSupport (1, 0)
  · simpa [chordAt] using hupper

/-! ## The two margins -/

/-- The budget both margins are measured against: twice `Psi` at the point of
the chord, less twice `Phi` at the common contact.  At `t = entryA p` it is
twice the stochastic optimum of `p`, which is the only value the reduction
uses; away from that point it is the smooth function the later modules
differentiate. -/
noncomputable def chordBudget (p : RealTable) (u t : ℝ) : ℝ :=
  2 * (Psi (chordAt p t) - Phi (contactAt p u))

/-- The margin of the constant code against the chord budget.
`Psi q - Phi q` is the mutual information of `q`, which is the constant code's
score. -/
noncomputable def constantMargin (p : RealTable) (u t : ℝ) : ℝ :=
  chordBudget p u t - (Psi (chordAt p t) - Phi (chordAt p t))

/-- The same margin for the code that isolates the last cell. -/
noncomputable def singletonMargin (p : RealTable) (u t : ℝ) : ℝ :=
  chordBudget p u t - detScore (chordAt p t) (singletonCode cell11)

/-- Mutual information, written in the public vocabulary, is nonnegative. -/
theorem psi_sub_phi_nonneg {q : RealTable} (hq : IsPMF q) : 0 ≤ Psi q - Phi q :=
  le_trans (tau_nonneg q) (tau_le_psi_sub_phi hq)

/-- At the upper end the chord reaches the contact, so the constant margin
there is the contact's own mutual information, and nonnegative. -/
theorem constantMargin_chordTop (h : ChordDomain p u) :
    constantMargin p u (chordTop p u) = Psi (contactAt p u) - Phi (contactAt p u)
      ∧ 0 ≤ Psi (contactAt p u) - Phi (contactAt p u) := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  refine ⟨?_, psi_sub_phi_nonneg (isPMF_contactAt h.isPMF h.fullSupport hu h.nonconstant)⟩
  rw [constantMargin, chordBudget, chordAt_chordTop]
  ring

private theorem tau_eq_chord (h : ChordDomain p u) :
    tau p = Psi p - Phi (contactAt p u) :=
  tau_eq_contact h.isPMF h.fullSupport (topRoot_pos h.isPMF h.fullSupport h.topRoot)
    h.nonconstant h.topRoot.2.1

theorem chordBudget_entryA (h : ChordDomain p u) :
    chordBudget p u (entryA p) = 2 * tau p := by
  rw [chordBudget, chordAt_entryA, tau_eq_chord h]

private theorem constantMargin_entryA (h : ChordDomain p u) :
    constantMargin p u (entryA p) = 2 * tau p - (Psi p - Phi p) := by
  rw [constantMargin, chordBudget_entryA h, chordAt_entryA]

private theorem singletonMargin_entryA (h : ChordDomain p u) :
    singletonMargin p u (entryA p)
      = 2 * tau p - detScore p (singletonCode cell11) := by
  rw [singletonMargin, chordBudget_entryA h, chordAt_entryA]

/-! ## The chord point is itself a chord domain -/

/-- The top root exceeds the geometric mean of the off-diagonal.  This is what
keeps the determinant positive at every point of the chord, not only at `p`. -/
private theorem offDiagonalProduct_lt_sq_topRoot (h : ChordDomain p u) :
    offDiagonalProduct p < u ^ 2 := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hw : 0 < offDiagonalProduct p := by
    rw [offDiagonalProduct_eq]
    exact mul_pos (cell_pos h.fullSupport).2.1 (cell_pos h.fullSupport).2.2.1
  have hs := diagonalMass_pos h.fullSupport
  have hv := offDiagonalMass_pos h.fullSupport
  have hroot := h.topRoot.2.1
  rw [cubic] at hroot
  have key : u * (u ^ 2 - offDiagonalProduct p)
      = offDiagonalMass p * u ^ 2 + offDiagonalProduct p * diagonalMass p := by
    linear_combination hroot
  have hpos : 0 < offDiagonalMass p * u ^ 2 + offDiagonalProduct p * diagonalMass p := by
    positivity
  nlinarith [key, hpos, hu]

/-- Every point of the chord below the upper contact carries the same chord
domain, with the same top root.  The upper contact is excluded: there the
diagonal product falls to `u ^ 2` and the law is constant-optimal. -/
theorem chordDomain_chordAt (h : ChordDomain p u)
    (ht : t ∈ Set.Ico (chordMidpoint p) (chordTop p u)) : ChordDomain (chordAt p t) u := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hsum := chordTop_add_chordBottom (p := p) (u := u)
  have hTB := chordTop_mul_chordBottom h
  have hDmid := chordBottom_lt_chordMidpoint h
  have hmem : t ∈ Set.Icc (chordMidpoint p) (chordTop p u) := ⟨ht.1, ht.2.le⟩
  have hmid : chordMidpoint p ≤ t := ht.1
  rw [chordMidpoint] at hmid hDmid
  have hBt : chordBottom p u < t := by linarith
  have hkey : 0 < (chordTop p u - t) * (t - chordBottom p u) :=
    mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hBt)
  have hexp : (chordTop p u - t) * (t - chordBottom p u)
      = t * (diagonalMass p - t) - u ^ 2 := by
    rw [← hsum, ← hTB]
    ring
  have hprod : u ^ 2 < t * (diagonalMass p - t) := by linarith [hexp ▸ hkey]
  refine ⟨isPMF_chordAt h hmem, fullSupport_chordAt h hmem, ?_,
    isTopRoot_chordAt h.topRoot, ?_, ?_, ?_⟩
  · rw [determinant_chordAt]
    linarith [offDiagonalProduct_lt_sq_topRoot h]
  · rw [Nonconstant, diagonalProduct_eq, entryA_chordAt, entryD_chordAt]
    have hlt := Real.sqrt_lt_sqrt (sq_nonneg u) hprod
    rwa [Real.sqrt_sq hu.le] at hlt
  · rw [entryA_chordAt, entryD_chordAt]
    linarith
  · rw [entryB_chordAt, entryC_chordAt]
    exact h.offDiagonal_le

/-- The chord budget at any point below the upper contact is twice that
point's own stochastic optimum.  This is what makes `constantMargin` and
`singletonMargin` the margins their names claim. -/
private theorem chordBudget_eq_two_mul_tau (h : ChordDomain p u)
    (ht : t ∈ Set.Ico (chordMidpoint p) (chordTop p u)) :
    chordBudget p u t = 2 * tau (chordAt p t) := by
  rw [chordBudget, tau_eq_chord (chordDomain_chordAt h ht), contactAt_chordAt]

/-- The constant code's margin is `2 tau - I` at the chord point. -/
theorem constantMargin_eq_two_mul_tau_sub (h : ChordDomain p u)
    (ht : t ∈ Set.Ico (chordMidpoint p) (chordTop p u)) :
    constantMargin p u t
      = 2 * tau (chordAt p t) - (Psi (chordAt p t) - Phi (chordAt p t)) := by
  rw [constantMargin, chordBudget_eq_two_mul_tau h ht]

/-- The isolating code's margin is `2 tau - S` at the chord point. -/
theorem singletonMargin_eq_two_mul_tau_sub (h : ChordDomain p u)
    (ht : t ∈ Set.Ico (chordMidpoint p) (chordTop p u)) :
    singletonMargin p u t
      = 2 * tau (chordAt p t) - detScore (chordAt p t) (singletonCode cell11) := by
  rw [singletonMargin, chordBudget_eq_two_mul_tau h ht]

/-- If one of the two margins is nonnegative everywhere on the chord, then the
deterministic optimum is at most twice the stochastic one. -/
theorem T_le_two_tau_of_chordMargin (h : ChordDomain p u)
    (hmargin : ∀ t ∈ Set.Icc (chordMidpoint p) (chordTop p u),
      0 ≤ constantMargin p u t ∨ 0 ≤ singletonMargin p u t) :
    T p ≤ 2 * tau p := by
  rcases hmargin (entryA p) (entryA_mem_chord h) with h0 | hD
  · rw [constantMargin_entryA h] at h0
    linarith [T_le_psi_sub_phi h.isPMF]
  · rw [singletonMargin_entryA h] at hD
    linarith [T_le_detScore p (singletonCode cell11)]

end StochasticToDeterministicLatents.Binary
