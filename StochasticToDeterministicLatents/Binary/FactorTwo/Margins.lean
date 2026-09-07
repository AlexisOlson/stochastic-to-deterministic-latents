import StochasticToDeterministicLatents.Binary.FactorTwo.SingletonScore
import StochasticToDeterministicLatents.Binary.FactorTwo.Shape

/-!
# The two margins as scalar functions of the moving coordinate

Both competitors' margins along the chord are functions of four numbers -- the
diagonal mass, the two off-diagonal cells, and the contact's `Phi` -- and of
the moving coordinate alone.  This module names those functions, connects them
to the margins of the previous modules, and differentiates them twice.

Everything is in natural-log units.  That is what makes the second derivatives
here the very expressions
[`Shape.lean`](Shape.lean) already analyses: `constantCurvature` is the left
side of `constantCurvature_eq_numerator_div`, and `singletonCurvature` is
`singletonCurvature_neg` at `d = s - t`.  In bits each would carry a factor of
`Real.log 2` and every sign argument would have to push through it.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

variable {p : RealTable} {u t : ℝ}

/-! ## The scalar functions -/

/-- The chord law's entropy, in natural-log units. -/
noncomputable def chordLogEntropy (s b c t : ℝ) : ℝ :=
  -(xLogX t + xLogX b + xLogX c + xLogX (s - t))

/-- The chord law's row marginal entropy. -/
noncomputable def rowLogEntropy (s b c t : ℝ) : ℝ :=
  -(xLogX (t + b) + xLogX (s - t + c))

/-- The chord law's column marginal entropy. -/
noncomputable def columnLogEntropy (s b c t : ℝ) : ℝ :=
  -(xLogX (t + c) + xLogX (s - t + b))

/-- The part of the isolating code's score that the constant code does not
share. -/
noncomputable def singletonLogCost (b c t : ℝ) : ℝ :=
  3 * xLogX t - 2 * xLogX (t + b) - 2 * xLogX (t + c) + xLogX (t + b + c)
    + xLogX b + xLogX c

/-- The constant code's margin along the chord, as a function of the moving
coordinate.  `k` is the contact's `Phi` in natural-log units. -/
noncomputable def constantScalar (s b c k t : ℝ) : ℝ :=
  5 * chordLogEntropy s b c t - 3 * rowLogEntropy s b c t
    - 3 * columnLogEntropy s b c t - 2 * k

/-- The isolating code's margin along the chord. -/
noncomputable def singletonScalar (s b c k t : ℝ) : ℝ :=
  2 * chordLogEntropy s b c t - rowLogEntropy s b c t - columnLogEntropy s b c t
    - singletonLogCost b c t - 2 * k

/-- The constant margin's slope. -/
noncomputable def constantSlope (s b c t : ℝ) : ℝ :=
  5 * (Real.log (s - t) - Real.log t)
    - 3 * (Real.log (s - t + c) - Real.log (t + b))
    - 3 * (Real.log (s - t + b) - Real.log (t + c))

/-- The isolating margin's slope. -/
noncomputable def singletonSlope (s b c t : ℝ) : ℝ :=
  -5 * Real.log t + 2 * Real.log (s - t) + 3 * Real.log (t + b)
    + 3 * Real.log (t + c) - Real.log (s - t + c) - Real.log (s - t + b)
    - Real.log (t + b + c)

/-- The constant margin's curvature, the left side of
`constantCurvature_eq_numerator_div`. -/
noncomputable def constantCurvature (s b c t : ℝ) : ℝ :=
  -5 * (1 / t + 1 / (s - t)) + 3 * (1 / (t + b) + 1 / (s - t + c))
    + 3 * (1 / (t + c) + 1 / (s - t + b))

/-- The isolating margin's curvature, the expression of
`singletonCurvature_neg` at `d = s - t`. -/
noncomputable def singletonCurvature (s b c t : ℝ) : ℝ :=
  -5 / t - 2 / (s - t) + 3 / (t + b) + 3 / (t + c) + 1 / (s - t + c)
    + 1 / (s - t + b) - 1 / (t + b + c)

/-! ## The two bridges -/

/-- The constant margin is its scalar function. -/
theorem log_two_mul_constantMargin_eq (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * constantMargin p u t
      = constantScalar (diagonalMass p) (entryB p) (entryC p)
          (Real.log 2 * Phi (contactAt p u)) t := by
  rw [log_two_mul_constantMargin h ht]
  unfold constantScalar chordLogEntropy rowLogEntropy columnLogEntropy
  rw [show diagonalMass p - t + entryC p = entryC p + (diagonalMass p - t) from by ring,
    show diagonalMass p - t + entryB p = entryB p + (diagonalMass p - t) from by ring]
  ring

/-- The isolating margin is its scalar function. -/
theorem log_two_mul_singletonMargin_eq (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    Real.log 2 * singletonMargin p u t
      = singletonScalar (diagonalMass p) (entryB p) (entryC p)
          (Real.log 2 * Phi (contactAt p u)) t := by
  rw [log_two_mul_singletonMargin h ht]
  unfold singletonScalar chordLogEntropy rowLogEntropy columnLogEntropy singletonLogCost
  rw [show diagonalMass p - t + entryC p = entryC p + (diagonalMass p - t) from by ring,
    show diagonalMass p - t + entryB p = entryB p + (diagonalMass p - t) from by ring]
  ring

/-! ## Continuity -/

attribute [local fun_prop] continuous_xLogX

theorem continuous_constantScalar (s b c k : ℝ) :
    Continuous (constantScalar s b c k) := by
  unfold constantScalar chordLogEntropy rowLogEntropy columnLogEntropy
  fun_prop

theorem continuous_singletonScalar (s b c k : ℝ) :
    Continuous (singletonScalar s b c k) := by
  unfold singletonScalar chordLogEntropy rowLogEntropy columnLogEntropy
    singletonLogCost
  fun_prop

/-! ## The first derivative -/

theorem hasDerivAt_constantScalar (s b c k t : ℝ) (ht : 0 < t) (hd : 0 < s - t)
    (hb : 0 < b) (hc : 0 < c) :
    HasDerivAt (constantScalar s b c k) (constantSlope s b c t) t := by
  have het := hasDerivAt_xLogX ht.ne'
  have hed := (hasDerivAt_xLogX hd.ne').comp t
    ((hasDerivAt_const t s).sub (hasDerivAt_id t))
  have hetb := (hasDerivAt_xLogX (add_pos ht hb).ne').comp t
    ((hasDerivAt_id t).add_const b)
  have hetc := (hasDerivAt_xLogX (add_pos ht hc).ne').comp t
    ((hasDerivAt_id t).add_const c)
  have hedc := (hasDerivAt_xLogX (add_pos hd hc).ne').comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const c)
  have hedb := (hasDerivAt_xLogX (add_pos hd hb).ne').comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const b)
  have heb0 := hasDerivAt_const t (xLogX b)
  have hec0 := hasDerivAt_const t (xLogX c)
  have hJ := ((het.add heb0).add hec0).add hed
  have hR := hetb.add hedc
  have hC := hetc.add hedb
  have hall := (((hJ.neg.const_mul 5).sub (hR.neg.const_mul 3)).sub
    (hC.neg.const_mul 3)).sub_const (2 * k)
  convert hall using 1 <;> try rfl
  unfold constantSlope
  ring

theorem hasDerivAt_singletonScalar (s b c k t : ℝ) (ht : 0 < t) (hd : 0 < s - t)
    (hb : 0 < b) (hc : 0 < c) :
    HasDerivAt (singletonScalar s b c k) (singletonSlope s b c t) t := by
  have het := hasDerivAt_xLogX ht.ne'
  have hed := (hasDerivAt_xLogX hd.ne').comp t
    ((hasDerivAt_const t s).sub (hasDerivAt_id t))
  have hetb := (hasDerivAt_xLogX (add_pos ht hb).ne').comp t
    ((hasDerivAt_id t).add_const b)
  have hetc := (hasDerivAt_xLogX (add_pos ht hc).ne').comp t
    ((hasDerivAt_id t).add_const c)
  have hedc := (hasDerivAt_xLogX (add_pos hd hc).ne').comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const c)
  have hedb := (hasDerivAt_xLogX (add_pos hd hb).ne').comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const b)
  have hetbc := (hasDerivAt_xLogX (add_pos (add_pos ht hb) hc).ne').comp t
    (((hasDerivAt_id t).add_const b).add_const c)
  have heb0 := hasDerivAt_const t (xLogX b)
  have hec0 := hasDerivAt_const t (xLogX c)
  have hJ := ((het.add heb0).add hec0).add hed
  have hR := hetb.add hedc
  have hC := hetc.add hedb
  have hQ := (((((het.const_mul 3).sub (hetb.const_mul 2)).sub
    (hetc.const_mul 2)).add hetbc).add heb0).add hec0
  have hall := ((((hJ.neg.const_mul 2).sub hR.neg).sub hC.neg).sub hQ).sub_const (2 * k)
  convert hall using 1 <;> try rfl
  unfold singletonSlope
  ring

/-! ## The second derivative -/

private theorem hasDerivAt_log {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.log (1 / x) x := by
  simpa [one_div] using Real.hasDerivAt_log hx.ne'

theorem hasDerivAt_constantSlope (s b c t : ℝ) (ht : 0 < t) (hd : 0 < s - t)
    (hb : 0 < b) (hc : 0 < c) :
    HasDerivAt (constantSlope s b c) (constantCurvature s b c t) t := by
  have hlt := hasDerivAt_log ht
  have hld := (hasDerivAt_log hd).comp t ((hasDerivAt_const t s).sub (hasDerivAt_id t))
  have hltb := (hasDerivAt_log (add_pos ht hb)).comp t ((hasDerivAt_id t).add_const b)
  have hltc := (hasDerivAt_log (add_pos ht hc)).comp t ((hasDerivAt_id t).add_const c)
  have hldc := (hasDerivAt_log (add_pos hd hc)).comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const c)
  have hldb := (hasDerivAt_log (add_pos hd hb)).comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const b)
  have hall := (((hld.sub hlt).const_mul 5).sub ((hldc.sub hltb).const_mul 3)).sub
    ((hldb.sub hltc).const_mul 3)
  convert hall using 1 <;> try rfl
  unfold constantCurvature
  ring

theorem hasDerivAt_singletonSlope (s b c t : ℝ) (ht : 0 < t) (hd : 0 < s - t)
    (hb : 0 < b) (hc : 0 < c) :
    HasDerivAt (singletonSlope s b c) (singletonCurvature s b c t) t := by
  have hlt := hasDerivAt_log ht
  have hld := (hasDerivAt_log hd).comp t ((hasDerivAt_const t s).sub (hasDerivAt_id t))
  have hltb := (hasDerivAt_log (add_pos ht hb)).comp t ((hasDerivAt_id t).add_const b)
  have hltc := (hasDerivAt_log (add_pos ht hc)).comp t ((hasDerivAt_id t).add_const c)
  have hldc := (hasDerivAt_log (add_pos hd hc)).comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const c)
  have hldb := (hasDerivAt_log (add_pos hd hb)).comp t
    (((hasDerivAt_const t s).sub (hasDerivAt_id t)).add_const b)
  have hltbc := (hasDerivAt_log (add_pos (add_pos ht hb) hc)).comp t
    (((hasDerivAt_id t).add_const b).add_const c)
  have hall := ((((((hlt.const_mul (-5)).add (hld.const_mul 2)).add
    (hltb.const_mul 3)).add (hltc.const_mul 3)).sub hldc).sub hldb).sub hltbc
  convert hall using 1 <;> try rfl
  unfold singletonCurvature
  ring

/-! ## Continuity of the constant slope, and its value at the midpoint -/

theorem continuousOn_constantSlope (s b c : ℝ) (hb : 0 < b) (hc : 0 < c) (A : ℝ)
    (hA : A < s) : ContinuousOn (constantSlope s b c) (Set.Icc (s / 2) A) := by
  intro x hx
  have hxpos : 0 < x := by
    have := hx.2
    have := hx.1
    linarith
  have hdxpos : 0 < s - x := by linarith [hx.2]
  have hlt : ContinuousAt Real.log x := Real.continuousAt_log hxpos.ne'
  have hld : ContinuousAt (fun y : ℝ => Real.log (s - y)) x :=
    (Real.continuousAt_log hdxpos.ne').comp_of_eq
      (continuousAt_const.sub continuousAt_id) rfl
  have hltb : ContinuousAt (fun y : ℝ => Real.log (y + b)) x :=
    (Real.continuousAt_log (add_pos hxpos hb).ne').comp_of_eq
      (show ContinuousAt (fun y : ℝ => y + b) x by fun_prop) rfl
  have hltc : ContinuousAt (fun y : ℝ => Real.log (y + c)) x :=
    (Real.continuousAt_log (add_pos hxpos hc).ne').comp_of_eq
      (show ContinuousAt (fun y : ℝ => y + c) x by fun_prop) rfl
  have hldb : ContinuousAt (fun y : ℝ => Real.log (s - y + b)) x :=
    (Real.continuousAt_log (add_pos hdxpos hb).ne').comp_of_eq
      (show ContinuousAt (fun y : ℝ => s - y + b) x by fun_prop) rfl
  have hldc : ContinuousAt (fun y : ℝ => Real.log (s - y + c)) x :=
    (Real.continuousAt_log (add_pos hdxpos hc).ne').comp_of_eq
      (show ContinuousAt (fun y : ℝ => s - y + c) x by fun_prop) rfl
  exact ((((hld.sub hlt).const_mul 5).sub ((hldc.sub hltb).const_mul 3)).sub
    ((hldb.sub hltc).const_mul 3)).continuousWithinAt

/-- The chord is parametrized so that the constant margin is stationary at the
midpoint of the diagonal. -/
theorem constantSlope_chordMidpoint (s b c : ℝ) : constantSlope s b c (s / 2) = 0 := by
  unfold constantSlope
  rw [show s - s / 2 = s / 2 from by ring]
  ring

/-! ## The chord's arguments are positive -/

/-- Every argument the scalar functions differentiate at is positive on the
chord. -/
theorem chordArguments_pos (h : ChordDomain p u)
    (ht : t ∈ Set.Icc (chordMidpoint p) (chordTop p u)) :
    0 < t ∧ 0 < diagonalMass p - t ∧ 0 < entryB p ∧ 0 < entryC p := by
  have hs := fullSupport_chordAt h ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [chordAt] using hs (0, 0)
  · simpa [chordAt] using hs (1, 1)
  · simpa [entryB] using h.fullSupport (0, 1)
  · simpa [entryC] using h.fullSupport (1, 0)

end StochasticToDeterministicLatents.Binary
