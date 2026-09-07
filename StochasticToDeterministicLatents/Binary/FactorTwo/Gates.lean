import StochasticToDeterministicLatents.Binary.FactorTwo.Margins
import StochasticToDeterministicLatents.Binary.FactorTwo.Orientation

/-!
# The three gates, and the factor-two bound from them

The chord reduction of `Chord.lean` asks for one of the two margins to be
nonnegative at every point of the segment.  This module supplies three
sufficient conditions, each checkable at one or two points:

* the constant margin is nonnegative at the midpoint of the diagonal -- then it
  is nonnegative on the whole segment, because its curvature changes sign at
  most once and its slope vanishes at the midpoint;
* the isolating margin is nonnegative at both ends -- then it is nonnegative
  throughout, because it is concave;
* the isolating margin is nonnegative at the midpoint and at some interior
  point where the constant margin is also nonnegative -- then the two together
  cover the segment.

Nothing here proves that a gate holds.  Given one of them at every chord
domain, together with the orientation of `Orientation.lean` and the constant
branch of the stochastic optimum, the binary factor-two bound follows for every
probability law; what remains is entirely one-dimensional, an inequality
between explicit scalar functions at named points.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

variable {p : RealTable} {u t : ℝ}

private theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two

/-! ## The segment -/

private theorem chordTop_lt_diagonalMass (h : ChordDomain p u) :
    chordTop p u < diagonalMass p := by
  have hb := chordBottom_pos h
  have he := chordTop_add_chordBottom (p := p) (u := u)
  linarith

private theorem args_pos_Ioo (h : ChordDomain p u)
    (ht : t ∈ Set.Ioo (chordMidpoint p) (chordTop p u)) :
    0 < t ∧ 0 < diagonalMass p - t ∧ 0 < entryB p ∧ 0 < entryC p :=
  chordArguments_pos h ⟨ht.1.le, ht.2.le⟩

private theorem constantMargin_chordTop_nonneg (h : ChordDomain p u) :
    0 ≤ constantMargin p u (chordTop p u) := by
  obtain ⟨heq, hnn⟩ := constantMargin_chordTop h
  rw [heq]
  exact hnn

/-! ## The isolating margin is concave -/

private theorem singletonScalar_concaveOn (h : ChordDomain p u) :
    ConcaveOn ℝ (Set.Icc (chordMidpoint p) (chordTop p u))
      (singletonScalar (diagonalMass p) (entryB p) (entryC p)
        (Real.log 2 * Phi (contactAt p u))) := by
  refine concaveOn_Icc_of_hasDerivAt2_nonpos (chordMidpoint p) (chordTop p u) _
    (singletonSlope (diagonalMass p) (entryB p) (entryC p))
    (singletonCurvature (diagonalMass p) (entryB p) (entryC p))
    (continuous_singletonScalar _ _ _ _).continuousOn ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := args_pos_Ioo h hx
    exact hasDerivAt_singletonScalar _ _ _ _ _ h1 h2 h3 h4
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := args_pos_Ioo h hx
    exact hasDerivAt_singletonSlope _ _ _ _ h1 h2 h3 h4
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := args_pos_Ioo h hx
    unfold singletonCurvature
    exact (singletonCurvature_neg x (diagonalMass p - x) (entryB p) (entryC p)
      h1 h2 h3 h4).le

/-- The isolating code's margin is concave along the chord. -/
theorem singletonMargin_concaveOn (h : ChordDomain p u) :
    ConcaveOn ℝ (Set.Icc (chordMidpoint p) (chordTop p u)) (singletonMargin p u) := by
  refine ((singletonScalar_concaveOn h).smul
    (inv_nonneg.mpr log_two_pos.le)).congr ?_
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← log_two_mul_singletonMargin_eq h hx, ← mul_assoc,
    inv_mul_cancel₀ log_two_pos.ne', one_mul]

/-! ## The constant margin has no interior minimum -/

private theorem constantCurvature_nonneg (h : ChordDomain p u)
    (ht : t ∈ Set.Ioo (chordMidpoint p) (chordTop p u))
    (hn : 0 ≤ constantCurvatureNumerator (diagonalMass p) (entryB p) (entryC p)
      (t * (diagonalMass p - t))) :
    0 ≤ constantCurvature (diagonalMass p) (entryB p) (entryC p) t := by
  obtain ⟨h1, h2, h3, h4⟩ := args_pos_Ioo h ht
  have hs := diagonalMass_pos h.fullSupport
  unfold constantCurvature
  rw [constantCurvature_eq_numerator_div t (diagonalMass p) (entryB p) (entryC p)
    h1 h2 h3 h4]
  have hden : 0 < (t * (diagonalMass p - t))
      * (t * (diagonalMass p - t) + entryB p * (diagonalMass p + entryB p))
      * (t * (diagonalMass p - t) + entryC p * (diagonalMass p + entryC p)) := by
    positivity
  exact div_nonneg hn hden.le

private theorem constantCurvature_nonpos (h : ChordDomain p u)
    (ht : t ∈ Set.Ioo (chordMidpoint p) (chordTop p u))
    (hn : constantCurvatureNumerator (diagonalMass p) (entryB p) (entryC p)
      (t * (diagonalMass p - t)) ≤ 0) :
    constantCurvature (diagonalMass p) (entryB p) (entryC p) t ≤ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := args_pos_Ioo h ht
  have hs := diagonalMass_pos h.fullSupport
  unfold constantCurvature
  rw [constantCurvature_eq_numerator_div t (diagonalMass p) (entryB p) (entryC p)
    h1 h2 h3 h4]
  have hden : 0 < (t * (diagonalMass p - t))
      * (t * (diagonalMass p - t) + entryB p * (diagonalMass p + entryB p))
      * (t * (diagonalMass p - t) + entryC p * (diagonalMass p + entryC p)) := by
    positivity
  exact div_nonpos_of_nonpos_of_nonneg hn hden.le

private theorem constantScalar_min_le (h : ChordDomain p u) :
    ∀ x y z, x ∈ Set.Icc (chordMidpoint p) (chordTop p u) →
      z ∈ Set.Icc (chordMidpoint p) (chordTop p u) → x ≤ y → y ≤ z →
      min (constantScalar (diagonalMass p) (entryB p) (entryC p)
            (Real.log 2 * Phi (contactAt p u)) x)
          (constantScalar (diagonalMass p) (entryB p) (entryC p)
            (Real.log 2 * Phi (contactAt p u)) z)
        ≤ constantScalar (diagonalMass p) (entryB p) (entryC p)
            (Real.log 2 * Phi (contactAt p u)) y := by
  have hs := diagonalMass_pos h.fullSupport
  have hb : 0 < entryB p := h.fullSupport (0, 1)
  have hc : 0 < entryC p := h.fullSupport (1, 0)
  have hmid : chordMidpoint p ≤ chordTop p u := (chordMidpoint_lt_chordTop h).le
  have hA : chordTop p u < diagonalMass p := chordTop_lt_diagonalMass h
  obtain ⟨c0, hc0, hleft, hright⟩ := constantCurvature_sign_switch (diagonalMass p)
    (entryB p) (entryC p) (chordTop p u) hs (by simpa [chordMidpoint] using hmid) hA hb hc
  have hc0L : chordMidpoint p ≤ c0 := by simpa [chordMidpoint] using hc0.1
  refine min_endpoints_le_of_curvature_switch (chordMidpoint p) (chordTop p u) c0 _
    (constantSlope (diagonalMass p) (entryB p) (entryC p))
    (constantCurvature (diagonalMass p) (entryB p) (entryC p))
    (continuous_constantScalar _ _ _ _).continuousOn
    (by
      simpa [chordMidpoint] using continuousOn_constantSlope (diagonalMass p)
        (entryB p) (entryC p) hb hc (chordTop p u) hA)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := args_pos_Ioo h hx
    exact hasDerivAt_constantScalar _ _ _ _ _ h1 h2 h3 h4
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := args_pos_Ioo h hx
    exact hasDerivAt_constantSlope _ _ _ _ h1 h2 h3 h4
  · simpa [chordMidpoint] using
      constantSlope_chordMidpoint (diagonalMass p) (entryB p) (entryC p)
  · simpa [chordMidpoint] using hc0
  · intro x hx
    exact constantCurvature_nonneg h ⟨hx.1, hx.2.trans_le hc0.2⟩
      (by simpa [chordMidpoint] using hleft x hx)
  · intro x hx
    exact constantCurvature_nonpos h ⟨hc0L.trans_lt hx.1, hx.2⟩ (hright x hx)

/-- The constant margin attains no interior minimum: on every subinterval of
the chord it stays above the smaller of the two endpoint values. -/
theorem constantMargin_min_le (h : ChordDomain p u) :
    ∀ x y z, x ∈ Set.Icc (chordMidpoint p) (chordTop p u) →
      z ∈ Set.Icc (chordMidpoint p) (chordTop p u) → x ≤ y → y ≤ z →
      min (constantMargin p u x) (constantMargin p u z) ≤ constantMargin p u y := by
  intro x y z hx hz hxy hyz
  have hy : y ∈ Set.Icc (chordMidpoint p) (chordTop p u) :=
    ⟨hx.1.trans hxy, hyz.trans hz.2⟩
  have hmin := constantScalar_min_le h x y z hx hz hxy hyz
  rw [← log_two_mul_constantMargin_eq h hx, ← log_two_mul_constantMargin_eq h hy,
    ← log_two_mul_constantMargin_eq h hz,
    ← mul_min_of_nonneg _ _ log_two_pos.le] at hmin
  exact le_of_mul_le_mul_left hmin log_two_pos

/-! ## The three gates -/

/-- First gate: the constant margin nonnegative at the midpoint. -/
theorem chordMargin_of_constantCentre (h : ChordDomain p u)
    (hmid : 0 ≤ constantMargin p u (chordMidpoint p)) :
    ∀ t ∈ Set.Icc (chordMidpoint p) (chordTop p u),
      0 ≤ constantMargin p u t ∨ 0 ≤ singletonMargin p u t := by
  intro t ht
  refine Or.inl (le_trans (le_min hmid (constantMargin_chordTop_nonneg h)) ?_)
  exact constantMargin_min_le h (chordMidpoint p) t (chordTop p u)
    ⟨le_rfl, (chordMidpoint_lt_chordTop h).le⟩
    ⟨(chordMidpoint_lt_chordTop h).le, le_rfl⟩ ht.1 ht.2

/-- Second gate: the isolating margin nonnegative at both ends. -/
theorem chordMargin_of_singletonEnds (h : ChordDomain p u)
    (hmid : 0 ≤ singletonMargin p u (chordMidpoint p))
    (htop : 0 ≤ singletonMargin p u (chordTop p u)) :
    ∀ t ∈ Set.Icc (chordMidpoint p) (chordTop p u),
      0 ≤ constantMargin p u t ∨ 0 ≤ singletonMargin p u t := by
  intro t ht
  refine Or.inr ((le_min hmid htop).trans ?_)
  exact (singletonMargin_concaveOn h).min_le_of_mem_Icc
    ⟨le_rfl, (chordMidpoint_lt_chordTop h).le⟩
    ⟨(chordMidpoint_lt_chordTop h).le, le_rfl⟩ ht

/-- Third gate: the isolating margin nonnegative at the midpoint and at an
interior point where the constant margin is nonnegative too. -/
theorem chordMargin_of_crossover (h : ChordDomain p u) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Set.Icc (chordMidpoint p) (chordTop p u))
    (hmid : 0 ≤ singletonMargin p u (chordMidpoint p))
    (hsing : 0 ≤ singletonMargin p u t₀)
    (hconst : 0 ≤ constantMargin p u t₀) :
    ∀ t ∈ Set.Icc (chordMidpoint p) (chordTop p u),
      0 ≤ constantMargin p u t ∨ 0 ≤ singletonMargin p u t := by
  intro z hz
  by_cases hzt : z ≤ t₀
  · refine Or.inr ((le_min hmid hsing).trans ?_)
    exact (singletonMargin_concaveOn h).min_le_of_mem_Icc
      ⟨le_rfl, (chordMidpoint_lt_chordTop h).le⟩ ht₀ ⟨hz.1, hzt⟩
  · refine Or.inl ((le_min hconst (constantMargin_chordTop_nonneg h)).trans ?_)
    exact constantMargin_min_le h t₀ z (chordTop p u) ht₀
      ⟨(chordMidpoint_lt_chordTop h).le, le_rfl⟩ (le_of_not_ge hzt) hz.2

/-! ## The binary factor-two bound from the gates -/

/-- On the constant branch of the stochastic optimum the deterministic optimum
is already below the stochastic one. -/
private theorem T_le_two_tau_of_constantBranch {q : RealTable} (hq : IsPMF q)
    (htau : tau q = Psi q - Phi q) : T q ≤ 2 * tau q := by
  have hT := T_le_psi_sub_phi hq
  have h0 := tau_nonneg q
  rw [← htau] at hT
  linarith

/-- The centre gate at one law: on a chord domain, a constant margin that is
nonnegative at the midpoint of the diagonal bounds that law's deterministic
optimum. -/
theorem T_le_two_mul_tau_of_centerGate (h : ChordDomain p u)
    (h0 : 0 ≤ constantMargin p u (chordMidpoint p)) :
    T p ≤ 2 * tau p :=
  T_le_two_tau_of_chordMargin h (chordMargin_of_constantCentre h h0)

/-- The cut gates at one law: an isolating margin that is nonnegative at the
midpoint and at an interior point where the constant margin is nonnegative too
bounds that law's deterministic optimum. -/
theorem T_le_two_mul_tau_of_cutGates (h : ChordDomain p u) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Set.Icc (chordMidpoint p) (chordTop p u))
    (hmid : 0 ≤ singletonMargin p u (chordMidpoint p))
    (hsing : 0 ≤ singletonMargin p u t₀)
    (hconst : 0 ≤ constantMargin p u t₀) :
    T p ≤ 2 * tau p :=
  T_le_two_tau_of_chordMargin h (chordMargin_of_crossover h t₀ ht₀ hmid hsing hconst)

/-- `T p ≤ 2 * tau p` for every probability law, given the three gates on every
chord domain.  The hypothesis is one-dimensional: it compares two explicit
scalar functions with zero at the midpoint, at the upper contact, and at one
interior point. -/
theorem T_le_two_tau_of_gates
    (hgates : ∀ (q : RealTable) (w : ℝ), ChordDomain q w →
      0 ≤ constantMargin q w (chordMidpoint q)
        ∨ (0 ≤ singletonMargin q w (chordMidpoint q)
            ∧ 0 ≤ singletonMargin q w (chordTop q w))
        ∨ (∃ t ∈ Set.Icc (chordMidpoint q) (chordTop q w),
            0 ≤ singletonMargin q w (chordMidpoint q)
              ∧ 0 ≤ singletonMargin q w t ∧ 0 ≤ constantMargin q w t))
    (hp : IsPMF p) : T p ≤ 2 * tau p := by
  refine T_le_mul_tau_of_oriented (by norm_num) ?_ p hp
  intro q hq hqpos hqdet hda hcb
  obtain ⟨htop, hbranch⟩ := tau_eq_at_topRoot hq hqpos hqdet
  rcases hbranch with ⟨hnc, _⟩ | ⟨_, htau⟩
  · have hdet := determinant_pos_of_nonconstant hq hqpos hqdet htop hnc
    have hdom : ChordDomain q (cubicRoot q) := ⟨hq, hqpos, hdet, htop, hnc, hda, hcb⟩
    refine T_le_two_tau_of_chordMargin hdom ?_
    rcases hgates q (cubicRoot q) hdom with hg | ⟨hm, he⟩ | ⟨t, ht, hm, hd, h0⟩
    · exact chordMargin_of_constantCentre hdom hg
    · exact chordMargin_of_singletonEnds hdom hm he
    · exact chordMargin_of_crossover hdom t ht hm hd h0
  · exact T_le_two_tau_of_constantBranch hq htau

end StochasticToDeterministicLatents.Binary
