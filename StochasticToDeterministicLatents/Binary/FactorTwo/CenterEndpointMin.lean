/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Renamed, restated over the
public interfaces of this library, and re-proved where the argument differs.
-/
import Mathlib.Analysis.Convex.Deriv

/-!
# An endpoint minimum principle

A scalar function of the ray's radius whose derivative has the form
`w t * sigma t`, with `w` positive and `sigma` antitone, attains no interior
value below both of its endpoint values.  That is the shape the centre's
endpoint comparisons take, and it is the only thing they need from calculus.

This module isolates that principle.  Like `Shape.lean`, it is **pure real
analysis**: every statement quantifies over arbitrary real functions, so no
probability law, code, chart, margin or information quantity appears, and
nothing from this library is imported.  It is the centre arm's counterpart of
`Shape.lean`, which serves the chord route.

* `antitoneOn_Ioo_of_hasDerivAt_nonpos` is the wrapper that turns a
  nonpositive derivative on an open interval into antitonicity there.  It is
  the twin of `Shape.lean`'s private `antitoneOn_of_hasDerivAt_nonpos`, which
  is stated on a closed interval and therefore needs a continuity hypothesis
  that this one derives.
* `min_endpoints_le_of_antitoneSlope_affine` is the form the centre uses: the
  same conclusion for `F - A - B * V`, where `F` and `V` have derivatives
  `w * sigma` and `w` against the same positive weight.  Subtracting the
  affine part shifts the antitone factor by the constant `B` and leaves it
  antitone, which is the whole content of the reduction.

**Nothing here bounds anything about a law.**  The functions are arbitrary,
and no declaration in this module names a margin, a code or a radius.
-/

namespace StochasticToDeterministicLatents.Binary

/-- A function with a nonpositive derivative at every point of an open
interval is antitone on it.  No continuity hypothesis is needed: it follows
from differentiability. -/
theorem antitoneOn_Ioo_of_hasDerivAt_nonpos (a b : ℝ) (f g : ℝ → ℝ)
    (hfg : ∀ t ∈ Set.Ioo a b, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.Ioo a b, g t ≤ 0) : AntitoneOn f (Set.Ioo a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo a b)
    (fun t ht => (hfg t ht).continuousAt.continuousWithinAt)
  · intro t ht
    rw [interior_Ioo] at ht
    exact (hfg t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(hfg t ht).deriv]
    exact hg t ht

/-- If `G` is continuous on `[a, b]` and has derivative `w t * sigma t` on the
interior, with `w` positive and `sigma` antitone, then `G` is bounded below by
the smaller of its two endpoint values.

The derivative changes sign at most once, from nonnegative to nonpositive, so
`G` rises and then falls; a point where `sigma` is still nonnegative is
reached from the left by a monotone stretch, and one where it is negative is
reached from the right by an antitone one. -/
private theorem min_endpoints_le_of_antitoneSlope (a b : ℝ) (G w sigma : ℝ → ℝ)
    (hG : ContinuousOn G (Set.Icc a b))
    (hsigma : AntitoneOn sigma (Set.Ioo a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt G (w t * sigma t) t)
    (hw : ∀ t ∈ Set.Ioo a b, 0 < w t)
    {r : ℝ} (hr : r ∈ Set.Icc a b) : min (G a) (G b) ≤ G r := by
  rcases hr with ⟨har, hrb⟩
  rcases eq_or_lt_of_le har with rfl | har
  · exact min_le_left _ _
  rcases eq_or_lt_of_le hrb with rfl | hrb
  · exact min_le_right _ _
  by_cases hs : 0 ≤ sigma r
  · have hmono : MonotoneOn G (Set.Icc a r) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a r)
      · exact hG.mono (Set.Icc_subset_Icc_right hrb.le)
      · intro t ht
        rw [interior_Icc] at ht
        have ht' : t ∈ Set.Ioo a b := ⟨ht.1, lt_of_le_of_lt ht.2.le hrb⟩
        exact (hd t ht').hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht' : t ∈ Set.Ioo a b := ⟨ht.1, lt_of_le_of_lt ht.2.le hrb⟩
        have hr' : r ∈ Set.Ioo a b := ⟨har, hrb⟩
        exact mul_nonneg (hw t ht').le (le_trans hs (hsigma ht' hr' ht.2.le))
    exact le_trans (min_le_left _ _)
      (hmono (by simp [har.le]) (by simp [har.le]) har.le)
  · have hanti : AntitoneOn G (Set.Icc r b) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc r b)
      · exact hG.mono (Set.Icc_subset_Icc_left har.le)
      · intro t ht
        rw [interior_Icc] at ht
        have ht' : t ∈ Set.Ioo a b := ⟨lt_of_lt_of_le har ht.1.le, ht.2⟩
        exact (hd t ht').hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht' : t ∈ Set.Ioo a b := ⟨lt_of_lt_of_le har ht.1.le, ht.2⟩
        have hr' : r ∈ Set.Ioo a b := ⟨har, hrb⟩
        exact mul_nonpos_of_nonneg_of_nonpos (hw t ht').le
          (le_trans (hsigma hr' ht' ht.1.le) (le_of_not_ge hs))
    exact le_trans (min_le_right _ _)
      (hanti (by simp [hrb.le]) (by simp [hrb.le]) hrb.le)

/-- The affine form of the principle.  If `F` and `V` are continuous on
`[a, b]` with derivatives `w t * sigma t` and `w t` against the same positive
weight, and `sigma` is antitone, then for every affine correction `A + B * V`
the difference `F - A - B * V` is bounded below on `[a, b]` by the smaller of
its two endpoint values.

The affine correction is what turns the conclusion into a bound.  Choosing
`A` and `B` so that the two endpoint values are the ones already known makes
the left side of the conclusion a number, and what is left is a lower bound
for `F` in terms of `V` throughout the interval. -/
theorem min_endpoints_le_of_antitoneSlope_affine (a b : ℝ) (F V w sigma : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc a b)) (hV : ContinuousOn V (Set.Icc a b))
    (hsigma : AntitoneOn sigma (Set.Ioo a b))
    (hFd : ∀ t ∈ Set.Ioo a b, HasDerivAt F (w t * sigma t) t)
    (hVd : ∀ t ∈ Set.Ioo a b, HasDerivAt V (w t) t)
    (hw : ∀ t ∈ Set.Ioo a b, 0 < w t) (A B : ℝ) {r : ℝ}
    (hr : r ∈ Set.Icc a b) :
    min (F a - A - B * V a) (F b - A - B * V b) ≤ F r - A - B * V r := by
  apply min_endpoints_le_of_antitoneSlope a b (fun t => F t - A - B * V t) w
    (fun t => sigma t - B)
  · exact (hF.sub continuousOn_const).sub (continuousOn_const.mul hV)
  · intro x hx y hy hxy
    exact sub_le_sub_right (hsigma hx hy hxy) B
  · intro t ht
    have hder := ((hFd t ht).sub_const A).sub ((hVd t ht).const_mul B)
    convert hder using 1
    all_goals first | rfl | ring
  · exact hw
  · exact hr

end StochasticToDeterministicLatents.Binary
