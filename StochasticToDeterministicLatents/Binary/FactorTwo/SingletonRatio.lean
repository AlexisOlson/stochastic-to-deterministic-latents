import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The singleton margin's ratio term at the fixed cut

In the estimate a later module supplies, the singleton margin at the fixed
cut is bounded below by two copies of

`psi x = (3 + x) log (3 + x) + 3 x log x - 4 x log (1 + x) - 3 log 3`,

evaluated at the two off-diagonal cells over the contact cell, plus a part
depending on the two masses.  This module supplies that function and the fact
the estimate needs about it.  That the two ratios sum to at least `2` is part
of what the later module supplies; on that half plane

`8 log 2 - 6 log 3 <= psi x + psi y`.

The bound is exact -- no decimal enclosure enters it.  Its proof is the
symmetric slice: `P x = psi x + psi (2 - x)` has a critical point at `x = 1`
by symmetry, and `P'' > 0` on `(0, 2)`, which after clearing denominators is a
cubic in `(x - 1)^2` on `[0, 1)`; so `P` is least at `x = 1`, where it is
`2 psi 1`.  Off the diagonal `x + y > 2`, and `psi` is strictly increasing
above `1`, which carries the bound the rest of the way.  The monotonicity is
itself the substitution `t = 1 / x`, under which `psi'` becomes
`log (1 + 3 t) - 4 log (1 + t) + 4 t / (1 + t)`, concave on `[0, 1]` and so
above its chord there.

Like `Shape` and `LogSeries`, this module mentions no probability law, no code
and no information quantity, and imports nothing from this library.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-- The singleton margin's contribution from one off-diagonal cell over the
contact cell, at the fixed cut. -/
noncomputable def singletonRatioTerm (x : ℝ) : ℝ :=
  (3 + x) * Real.log (3 + x) + 3 * x * Real.log x - 4 * x * Real.log (1 + x) - 3 * Real.log 3

/-- The derivative of `singletonRatioTerm`. -/
private noncomputable def singletonDeriv (x : ℝ) : ℝ :=
  Real.log (x + 3) + 3 * Real.log x - 4 * Real.log (1 + x) + 4 / (1 + x)

/-- The second derivative of `singletonRatioTerm`. -/
private noncomputable def singletonDeriv2 (x : ℝ) : ℝ :=
  (-3 * x ^ 2 - 2 * x + 9) / (x * (x + 1) ^ 2 * (x + 3))

private theorem singletonRatioTerm_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt singletonRatioTerm (singletonDeriv x) x := by
  have h3 : 3 + x ≠ 0 := by positivity
  have h1 : 1 + x ≠ 0 := by positivity
  have ha := (Real.hasDerivAt_mul_log h3).comp x ((hasDerivAt_const x 3).add (hasDerivAt_id x))
  have hb := (Real.hasDerivAt_mul_log hx.ne').const_mul 3
  have hc := ((hasDerivAt_id x).mul ((Real.hasDerivAt_log h1).comp x
    ((hasDerivAt_const x 1).add (hasDerivAt_id x)))).const_mul 4
  have h := (ha.add hb).sub hc |>.sub (hasDerivAt_const x (3 * Real.log 3))
  norm_num [Function.comp_apply] at h
  convert h using 1
  case e'_4 => rfl
  case e'_5 => rfl
  case e'_8 =>
    funext y
    unfold singletonRatioTerm
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply]
    ring
  case e'_9 =>
    unfold singletonDeriv
    field_simp [h1]
    ring_nf

private theorem singletonDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt singletonDeriv (singletonDeriv2 x) x := by
  have h3 : x + 3 ≠ 0 := by positivity
  have h1 : 1 + x ≠ 0 := by positivity
  have ha := (Real.hasDerivAt_log h3).comp x ((hasDerivAt_id x).add_const 3)
  have hb := (Real.hasDerivAt_log hx.ne').const_mul 3
  have hc := ((Real.hasDerivAt_log h1).comp x
    ((hasDerivAt_const x 1).add (hasDerivAt_id x))).const_mul 4
  have hd := (hasDerivAt_const x 4).div ((hasDerivAt_const x 1).add (hasDerivAt_id x)) h1
  have h := (ha.add hb).sub hc |>.add hd
  norm_num [Function.comp_apply] at h
  change HasDerivAt singletonDeriv _ x at h
  have heq : (x + 3)⁻¹ + 3 * x⁻¹ - 4 * (1 + x)⁻¹ + -4 / (1 + x) ^ 2 = singletonDeriv2 x := by
    unfold singletonDeriv2
    field_simp
    ring
  rw [heq] at h
  exact h

/-- The derivative of `singletonRatioTerm` read in the reciprocal variable
`t = 1 / x`, on which it is concave. -/
private noncomputable def derivInReciprocal (t : ℝ) : ℝ :=
  Real.log (1 + 3 * t) - 4 * Real.log (1 + t) + 4 * t / (1 + t)

private noncomputable def derivInReciprocalDeriv (t : ℝ) : ℝ :=
  3 / (1 + 3 * t) - 4 / (1 + t) + 4 / (1 + t) ^ 2

private noncomputable def derivInReciprocalDeriv2 (t : ℝ) : ℝ :=
  -9 / (1 + 3 * t) ^ 2 - 4 * (1 - t) / (1 + t) ^ 3

private theorem derivInReciprocal_hasDerivAt {t : ℝ} (ht0 : 0 ≤ t) :
    HasDerivAt derivInReciprocal (derivInReciprocalDeriv t) t := by
  have h3 : 1 + 3 * t ≠ 0 := by positivity
  have h1 : 1 + t ≠ 0 := by positivity
  have h := (((Real.hasDerivAt_log h3).comp t
      ((hasDerivAt_const t 1).add ((hasDerivAt_const t 3).mul (hasDerivAt_id t)))).sub
      (((Real.hasDerivAt_log h1).comp t
        ((hasDerivAt_const t 1).add (hasDerivAt_id t))).const_mul 4)).add
      (((hasDerivAt_const t 4).mul (hasDerivAt_id t)).div
        ((hasDerivAt_const t 1).add (hasDerivAt_id t)) h1)
  norm_num [Function.comp_apply] at h
  change HasDerivAt derivInReciprocal _ t at h
  have heq : (1 + 3 * t)⁻¹ * 3 - 4 * (1 + t)⁻¹ +
      (4 * (1 + t) - 4 * t) / (1 + t) ^ 2 = derivInReciprocalDeriv t := by
    unfold derivInReciprocalDeriv
    field_simp [h1, h3]
    ring
  rw [heq] at h
  exact h

private theorem derivInReciprocalDeriv_hasDerivAt {t : ℝ} (ht0 : 0 ≤ t) :
    HasDerivAt derivInReciprocalDeriv (derivInReciprocalDeriv2 t) t := by
  have h3 : 1 + 3 * t ≠ 0 := by positivity
  have h1 : 1 + t ≠ 0 := by positivity
  have h := (((hasDerivAt_const t 3).div
      ((hasDerivAt_const t 1).add ((hasDerivAt_const t 3).mul (hasDerivAt_id t))) h3).sub
      ((hasDerivAt_const t 4).div
        ((hasDerivAt_const t 1).add (hasDerivAt_id t)) h1)).add
      ((hasDerivAt_const t 4).div
        (((hasDerivAt_const t 1).add (hasDerivAt_id t)).pow 2) (pow_ne_zero 2 h1))
  norm_num [Function.comp_apply] at h
  change HasDerivAt derivInReciprocalDeriv _ t at h
  have heq : -9 / (1 + 3 * t) ^ 2 - -4 / (1 + t) ^ 2 +
      -(4 * (2 * (1 + t))) / ((1 + t) ^ 2) ^ 2 = derivInReciprocalDeriv2 t := by
    unfold derivInReciprocalDeriv2
    field_simp [h1, h3]
    ring
  rw [heq] at h
  exact h

private theorem derivInReciprocal_concaveOn :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) derivInReciprocal := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
  · intro t ht
    exact (derivInReciprocal_hasDerivAt ht.1).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (derivInReciprocal_hasDerivAt ht.1.le).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (derivInReciprocalDeriv_hasDerivAt ht.1.le).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    unfold derivInReciprocalDeriv2
    have hb3 : 0 < 1 + 3 * t := by nlinarith [ht.1]
    have hb1 : 0 < 1 + t := by linarith
    have ha : -9 / (1 + 3 * t) ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_pos hb3 2).le
    have hb : -(4 * (1 - t) / (1 + t) ^ 3) ≤ 0 := by
      rw [neg_nonpos]
      have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht.2.le
      positivity
    exact add_nonpos ha hb

private theorem derivInReciprocal_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (2 - 2 * Real.log 2) ≤ derivInReciprocal t := by
  have h := derivInReciprocal_concaveOn.2 (Set.left_mem_Icc.mpr zero_le_one)
    (Set.right_mem_Icc.mpr zero_le_one) (sub_nonneg.mpr ht1) ht0 (by ring)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  simp [derivInReciprocal] at h
  norm_num at h
  rw [hlog4] at h
  unfold derivInReciprocal
  linarith [h]

private theorem singletonDeriv_eq {x : ℝ} (hx : 0 < x) :
    singletonDeriv x = derivInReciprocal (1 / x) := by
  have hx0 : x ≠ 0 := hx.ne'
  have h3 : 0 < 1 + 3 / x := by positivity
  have h1 : 0 < 1 + 1 / x := by positivity
  have hx3 : x + 3 = x * (1 + 3 / x) := by field_simp
  have hx1 : 1 + x = x * (1 + 1 / x) := by field_simp; ring
  rw [singletonDeriv, derivInReciprocal, hx3, hx1, Real.log_mul hx0 h3.ne',
    Real.log_mul hx0 h1.ne']
  field_simp
  ring

private theorem singletonDeriv_pos {x : ℝ} (hx : 1 ≤ x) : 0 < singletonDeriv x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [singletonDeriv_eq hxpos]
  have ht0 : 0 ≤ 1 / x := by positivity
  have ht1 : 1 / x ≤ 1 := (div_le_one hxpos).2 hx
  have hge := derivInReciprocal_ge ht0 ht1
  have hc : 0 < 2 - 2 * Real.log 2 := by
    have hlog := Real.log_two_lt_d9
    norm_num at hlog ⊢
    linarith
  exact lt_of_lt_of_le (mul_pos (by positivity) hc) hge

private theorem singletonRatioTerm_strictMonoOn :
    StrictMonoOn singletonRatioTerm (Set.Ici (1 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 1)
  · intro x hx
    exact (singletonRatioTerm_hasDerivAt
      (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (singletonRatioTerm_hasDerivAt (lt_trans zero_lt_one hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact singletonDeriv_pos hx.le

private theorem singletonRatioTerm_one :
    singletonRatioTerm 1 = 4 * Real.log 2 - 3 * Real.log 3 := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [singletonRatioTerm, show 3 + (1 : ℝ) = 4 by norm_num,
    show 1 + (1 : ℝ) = 2 by norm_num, Real.log_one, hlog4]
  ring

/-- The symmetric slice of the pair sum: `x + y = 2`. -/
private noncomputable def pairSum (x : ℝ) : ℝ :=
  singletonRatioTerm x + singletonRatioTerm (2 - x)

private theorem pairSum_hasDerivAt {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    HasDerivAt pairSum (singletonDeriv x - singletonDeriv (2 - x)) x := by
  have hsub : 0 < 2 - x := sub_pos.mpr hx2
  have h := (singletonRatioTerm_hasDerivAt hx).add
    ((singletonRatioTerm_hasDerivAt hsub).comp x
      ((hasDerivAt_const x 2).sub (hasDerivAt_id x)))
  change HasDerivAt pairSum _ x at h
  convert h using 1
  ring

private theorem pairSum_hasDerivAt2 {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    HasDerivAt (fun x => singletonDeriv x - singletonDeriv (2 - x))
      (singletonDeriv2 x + singletonDeriv2 (2 - x)) x := by
  have hsub : 0 < 2 - x := sub_pos.mpr hx2
  have h := (singletonDeriv_hasDerivAt hx).sub ((singletonDeriv_hasDerivAt hsub).comp x
    ((hasDerivAt_const x 2).sub (hasDerivAt_id x)))
  change HasDerivAt (fun z => singletonDeriv z - singletonDeriv (2 - z)) _ x at h
  convert h using 1
  ring

private theorem pairSum_deriv_one : singletonDeriv 1 - singletonDeriv (2 - 1) = 0 := by ring_nf

private theorem pairSum_second_eq {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    singletonDeriv2 x + singletonDeriv2 (2 - x) =
      (-6 * x ^ 6 + 36 * x ^ 5 - 106 * x ^ 4 + 184 * x ^ 3 + 518 * x ^ 2 -
        1308 * x + 810) /
        (x * (x + 1) ^ 2 * (x + 3) * (2 - x) * (3 - x) ^ 2 * (5 - x)) := by
  unfold singletonDeriv2
  have hx1 : 0 < x + 1 := by linarith
  have hx3 : 0 < x + 3 := by linarith
  have h2x : 0 < 2 - x := by linarith
  have h3x : 0 < 3 - x := by linarith
  have h5x : 0 < 5 - x := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity),
    div_eq_div_iff (by positivity) (by positivity)]
  ring

private theorem pairSum_second_pos {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    0 < singletonDeriv2 x + singletonDeriv2 (2 - x) := by
  rw [pairSum_second_eq hx hx2]
  apply div_pos
  · set s : ℝ := (x - 1) ^ 2 with hs
    have hs0 : 0 ≤ s := sq_nonneg (x - 1)
    have hs1 : s < 1 := by
      rw [hs]
      nlinarith [mul_pos hx (sub_pos.mpr hx2)]
    have hs2 : s ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1.le)]
    have hs3 : s ^ 3 ≤ 1 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs2)]
    have hid :
        -6 * x ^ 6 + 36 * x ^ 5 - 106 * x ^ 4 + 184 * x ^ 3 + 518 * x ^ 2 -
          1308 * x + 810 = -6 * s ^ 3 - 16 * s ^ 2 + 704 * s + 128 := by
      rw [hs]
      ring
    rw [hid]
    nlinarith
  · have hx1 : 0 < x + 1 := by linarith
    have hx3 : 0 < x + 3 := by linarith
    have h2x : 0 < 2 - x := by linarith
    have h3x : 0 < 3 - x := by linarith
    have h5x : 0 < 5 - x := by linarith
    positivity

private theorem pairSumDeriv_monotoneOn {a b : ℝ} (ha : 0 < a) (hb : b < 2) :
    MonotoneOn (fun x => singletonDeriv x - singletonDeriv (2 - x)) (Set.Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
  · intro x hx
    exact (pairSum_hasDerivAt2 (lt_of_lt_of_le ha hx.1)
      (lt_of_le_of_lt hx.2 hb)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (pairSum_hasDerivAt2 (lt_trans ha hx.1) (lt_trans hx.2 hb)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (pairSum_second_pos (lt_trans ha hx.1) (lt_trans hx.2 hb)).le

private theorem pairSum_ge {x : ℝ} (hx : 0 < x) (hx2 : x < 2) : pairSum 1 ≤ pairSum x := by
  rcases le_total x 1 with hx1 | h1x
  · have hmono := pairSumDeriv_monotoneOn hx (show (1 : ℝ) < 2 by norm_num)
    have hp_nonpos : ∀ z ∈ Set.Icc x 1, singletonDeriv z - singletonDeriv (2 - z) ≤ 0 := by
      intro z hz
      rw [← pairSum_deriv_one]
      exact hmono hz (Set.right_mem_Icc.mpr hx1) hz.2
    have hanti : AntitoneOn pairSum (Set.Icc x 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 1)
      · intro z hz
        exact (pairSum_hasDerivAt (lt_of_lt_of_le hx hz.1)
          (lt_of_le_of_lt hz.2 (by norm_num))).continuousAt.continuousWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        exact (pairSum_hasDerivAt (lt_trans hx hz.1)
          (lt_trans hz.2 (by norm_num))).hasDerivWithinAt
      · intro z hz
        exact hp_nonpos z (interior_subset hz)
    exact hanti (Set.left_mem_Icc.mpr hx1) (Set.right_mem_Icc.mpr hx1) hx1
  · have hmono := pairSumDeriv_monotoneOn (show (0 : ℝ) < 1 by norm_num) hx2
    have hp_nonneg : ∀ z ∈ Set.Icc 1 x, 0 ≤ singletonDeriv z - singletonDeriv (2 - z) := by
      intro z hz
      rw [← pairSum_deriv_one]
      exact hmono (Set.left_mem_Icc.mpr h1x) hz hz.1
    have hinc : MonotoneOn pairSum (Set.Icc 1 x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      · intro z hz
        exact (pairSum_hasDerivAt (lt_of_lt_of_le (by norm_num) hz.1)
          (lt_of_le_of_lt hz.2 hx2)).continuousAt.continuousWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        exact (pairSum_hasDerivAt (lt_trans (by norm_num) hz.1)
          (lt_trans hz.2 hx2)).hasDerivWithinAt
      · intro z hz
        exact hp_nonneg z (interior_subset hz)
    exact hinc (Set.left_mem_Icc.mpr h1x) (Set.right_mem_Icc.mpr h1x) h1x

/-- On the half plane the fixed cut supplies, `x + y >= 2`, the two ratio
terms of the singleton margin sum to at least `8 log 2 - 6 log 3`. -/
theorem singletonRatioTerm_pair {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : 2 ≤ x + y) :
    8 * Real.log 2 - 6 * Real.log 3 ≤ singletonRatioTerm x + singletonRatioTerm y := by
  have hbase : 8 * Real.log 2 - 6 * Real.log 3 = pairSum 1 := by
    unfold pairSum
    norm_num
    rw [singletonRatioTerm_one]
    ring
  rw [hbase]
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hsub1 : 1 ≤ 2 - x := by linarith
    have hsuby : 2 - x ≤ y := by linarith
    have hmono : singletonRatioTerm (2 - x) ≤ singletonRatioTerm y :=
      singletonRatioTerm_strictMonoOn.monotoneOn hsub1 (le_trans hsub1 hsuby) hsuby
    calc
      pairSum 1 ≤ pairSum x := pairSum_ge hx (by linarith)
      _ = singletonRatioTerm x + singletonRatioTerm (2 - x) := rfl
      _ ≤ singletonRatioTerm x + singletonRatioTerm y := by linarith
  · rcases lt_or_ge y 1 with hy1 | hy1
    · have hsub1 : 1 ≤ 2 - y := by linarith
      have hsubx : 2 - y ≤ x := by linarith
      have hmono : singletonRatioTerm (2 - y) ≤ singletonRatioTerm x :=
        singletonRatioTerm_strictMonoOn.monotoneOn hsub1 (le_trans hsub1 hsubx) hsubx
      calc
        pairSum 1 ≤ pairSum y := pairSum_ge hy (by linarith)
        _ = singletonRatioTerm y + singletonRatioTerm (2 - y) := rfl
        _ ≤ singletonRatioTerm x + singletonRatioTerm y := by linarith
    · have hxmono : singletonRatioTerm 1 ≤ singletonRatioTerm x :=
        singletonRatioTerm_strictMonoOn.monotoneOn (by simp) hx1 hx1
      have hymono : singletonRatioTerm 1 ≤ singletonRatioTerm y :=
        singletonRatioTerm_strictMonoOn.monotoneOn (by simp) hy1 hy1
      rw [pairSum]
      norm_num
      linarith

end StochasticToDeterministicLatents.Binary
