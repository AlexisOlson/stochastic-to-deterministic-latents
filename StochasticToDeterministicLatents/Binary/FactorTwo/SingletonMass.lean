import StochasticToDeterministicLatents.Binary.FactorTwo.Shape
import StochasticToDeterministicLatents.Binary.FactorTwo.LogValues
import StochasticToDeterministicLatents.Binary.FactorTwo.SingletonRatio

/-!
# The singleton margin's mass term at the fixed cut

In the estimate a later module supplies, the last part of the singleton
margin at the fixed cut depends on the two masses rather than on a ratio of
cells:

`E v d = 2 - d - d^2 - 2 log (1 - v - d) - 8 log (1 + v / (2 (1 - v - d)))
        - 8 log (1 + v / (2 (1 - v - 3 d)))`,

with `v` the off-diagonal mass and `d` the contact cell.  On the box
`0 < v <= 1/8`, `0 <= d <= v/2` it is concave in `d`, so it is least at one of
the two ends, and each end is antitone in `v`, so each is least at `v = 1/8`,
where it is an explicit combination of logarithms of `2`, `3`, `5`, `7`, `11`
and `13`.

What that estimate will consume is not the bound on its own but its sum with
the two ratio terms of `SingletonRatio`, which is `singletonTerms_gt`: on the
fixed cut's box the three terms together exceed `1 / 100`.  Stating it that
way keeps the two corner values private, as the tangent constants are private
in `ConstantRatio`.

Like `Shape` and `LogSeries`, this module mentions no probability law, no code
and no information quantity.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {v d : ℝ}

/-- The singleton margin's contribution from the off-diagonal mass `v` and the
contact cell `d`, at the fixed cut. -/
noncomputable def singletonMassTerm (v d : ℝ) : ℝ :=
  2 - d - d ^ 2 - 2 * Real.log (1 - v - d)
    - 8 * Real.log (1 + v / (2 * (1 - v - d)))
    - 8 * Real.log (1 + v / (2 * (1 - v - 3 * d)))

/-- The derivative of `singletonMassTerm v` in the contact cell. -/
private noncomputable def massDeriv (v d : ℝ) : ℝ :=
  -1 - 2 * d + 2 / (1 - v - d)
    - 8 * v / ((1 - v - d) * (2 * (1 - v - d) + v))
    - 24 * v / ((1 - v - 3 * d) * (2 * (1 - v - 3 * d) + v))

/-- The second derivative of `singletonMassTerm v` in the contact cell. -/
private noncomputable def massDeriv2 (v d : ℝ) : ℝ :=
  -2 + 2 / (1 - v - d) ^ 2
    - 8 * v * (4 * (1 - v - d) + v) /
      ((1 - v - d) ^ 2 * (2 * (1 - v - d) + v) ^ 2)
    - 72 * v * (4 * (1 - v - 3 * d) + v) /
      ((1 - v - 3 * d) ^ 2 * (2 * (1 - v - 3 * d) + v) ^ 2)

private theorem near_ge (hv : v ≤ 1 / 8) (hd : d ≤ v / 2) :
    13 / 16 ≤ 1 - v - d := by
  nlinarith

private theorem far_ge (hv : v ≤ 1 / 8) (hd : d ≤ v / 2) :
    11 / 16 ≤ 1 - v - 3 * d := by
  nlinarith

private theorem massDeriv2_neg (hv0 : 0 < v) (hv : v ≤ 1 / 8)
    (hd0 : 0 ≤ d) (hd : d ≤ v / 2) : massDeriv2 v d < 0 := by
  set A : ℝ := 1 - v - d with hAdef
  set a : ℝ := 1 - v - 3 * d with hadef
  have hA : 13 / 16 ≤ A := near_ge hv hd
  have ha : 11 / 16 ≤ a := far_ge hv hd
  have hA1 : A ≤ 1 := by rw [hAdef]; linarith
  have ha1 : a ≤ 1 := by rw [hadef]; linarith
  have hAp : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hap : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hAv : 0 < 2 * A + v := by positivity
  have hav : 0 < 2 * a + v := by positivity
  have hAden : A ^ 2 * (2 * A + v) < 3 := by nlinarith [sq_nonneg A]
  have haden : a ^ 2 * (2 * a + v) < 3 := by nlinarith [sq_nonneg a]
  have hcorr : 2 / A ^ 2 - 2 ≤ (1536 / 169) * v := by
    have hgap : 1 - A ≤ 3 * v / 2 := by rw [hAdef]; linarith
    rw [div_sub' (by positivity : A ^ 2 ≠ 0)]
    apply (div_le_iff₀ (by positivity : 0 < A ^ 2)).2
    have hp : (1 - A) * (1 + A) ≤ (3 * v / 2) * 2 :=
      mul_le_mul hgap (by nlinarith : 1 + A ≤ 2) (by positivity) (by positivity)
    nlinarith [sq_nonneg (A - 13 / 16)]
  have hbigA : 8 * v / 3 ≤ 8 * v * (4 * A + v) / (A ^ 2 * (2 * A + v) ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < A ^ 2 * (2 * A + v) ^ 2)).2
    have hfac : A ^ 2 * (2 * A + v) ^ 2 ≤ 3 * (4 * A + v) := by
      have hm : A ^ 2 * (2 * A + v) ^ 2 < 3 * (2 * A + v) := by
        nlinarith [mul_lt_mul_of_pos_right hAden hAv]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hv0.le]
  have hbiga : 24 * v ≤ 72 * v * (4 * a + v) / (a ^ 2 * (2 * a + v) ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < a ^ 2 * (2 * a + v) ^ 2)).2
    have hfac : a ^ 2 * (2 * a + v) ^ 2 ≤ 3 * (4 * a + v) := by
      have hm : a ^ 2 * (2 * a + v) ^ 2 < 3 * (2 * a + v) := by
        nlinarith [mul_lt_mul_of_pos_right haden hav]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hv0.le]
  unfold massDeriv2
  rw [← hAdef, ← hadef]
  nlinarith

private theorem logRest_hasDerivAt (hA : 1 - v - d ≠ 0) :
    HasDerivAt (fun d => Real.log (1 - v - d)) (-1 / (1 - v - d)) d := by
  have h := ((hasDerivAt_id' (x := d)).const_sub (1 - v)).log hA
  simpa only [id] using h

private theorem logNear_hasDerivAt (hv0 : 0 ≤ v) (hA : 0 < 1 - v - d) :
    HasDerivAt (fun d => Real.log (1 + v / (2 * (1 - v - d))))
      (v / ((1 - v - d) * (2 * (1 - v - d) + v))) d := by
  have hden : 2 * (1 - v - d) ≠ 0 := by positivity
  have hinner : 0 < 1 + v / (2 * (1 - v - d)) := by positivity
  have h := ((hasDerivAt_const d 1).add ((hasDerivAt_const d v).div
    (((hasDerivAt_id' (x := d)).const_sub (1 - v)).const_mul 2) hden)).log hinner.ne'
  change HasDerivAt (fun d => Real.log (1 + v / (2 * (1 - v - d)))) _ d at h
  exact h.congr_deriv (by simp only [Pi.add_apply, Pi.div_apply]; field_simp; ring)

private theorem logFar_hasDerivAt (hv0 : 0 ≤ v) (ha : 0 < 1 - v - 3 * d) :
    HasDerivAt (fun d => Real.log (1 + v / (2 * (1 - v - 3 * d))))
      (3 * v / ((1 - v - 3 * d) * (2 * (1 - v - 3 * d) + v))) d := by
  have hden : 2 * (1 - v - 3 * d) ≠ 0 := by positivity
  have hinner : 0 < 1 + v / (2 * (1 - v - 3 * d)) := by positivity
  have haff := ((hasDerivAt_id' (x := d)).const_mul 3).const_sub (1 - v)
  have h := ((hasDerivAt_const d 1).add
    ((hasDerivAt_const d v).div (haff.const_mul 2) hden)).log hinner.ne'
  change HasDerivAt (fun d => Real.log (1 + v / (2 * (1 - v - 3 * d)))) _ d at h
  exact h.congr_deriv (by simp only [Pi.add_apply, Pi.div_apply]; field_simp; ring)

private theorem singletonMassTerm_hasDerivAt (hv0 : 0 < v) (hv : v ≤ 1 / 8)
    (hd : d ≤ v / 2) :
    HasDerivAt (singletonMassTerm v) (massDeriv v d) d := by
  have hA := near_ge hv hd
  have ha := far_ge hv hd
  have hlogA := logRest_hasDerivAt (v := v) (d := d) (ne_of_gt (by linarith))
  have hlogB := logNear_hasDerivAt hv0.le (by linarith)
  have hlogC := logFar_hasDerivAt hv0.le (by linarith)
  have hpoly := ((hasDerivAt_const d 2).sub (hasDerivAt_id' (x := d))).sub
    ((hasDerivAt_id' (x := d)).pow 2)
  have h := ((hpoly.sub (hlogA.const_mul 2)).sub (hlogB.const_mul 8)).sub
    (hlogC.const_mul 8)
  change HasDerivAt (singletonMassTerm v) _ d at h
  refine h.congr_deriv ?_
  unfold massDeriv
  field_simp
  ring

private theorem nearFraction_hasDerivAt (hv0 : 0 ≤ v) (hA : 0 < 1 - v - d) :
    HasDerivAt (fun d => v / ((1 - v - d) * (2 * (1 - v - d) + v)))
      (v * (4 * (1 - v - d) + v) /
        ((1 - v - d) ^ 2 * (2 * (1 - v - d) + v) ^ 2)) d := by
  have h1 := (hasDerivAt_id' (x := d)).const_sub (1 - v)
  have h2 := (h1.const_mul 2).add_const v
  have hden : (1 - v - d) * (2 * (1 - v - d) + v) ≠ 0 := by positivity
  have h := (hasDerivAt_const d v).div (h1.mul h2) hden
  change HasDerivAt (fun d => v / ((1 - v - d) * (2 * (1 - v - d) + v))) _ d at h
  exact h.congr_deriv (by simp only [Pi.mul_apply]; field_simp; ring)

private theorem farFraction_hasDerivAt (hv0 : 0 ≤ v) (ha : 0 < 1 - v - 3 * d) :
    HasDerivAt (fun d => 3 * v / ((1 - v - 3 * d) * (2 * (1 - v - 3 * d) + v)))
      (9 * v * (4 * (1 - v - 3 * d) + v) /
        ((1 - v - 3 * d) ^ 2 * (2 * (1 - v - 3 * d) + v) ^ 2)) d := by
  have h1 := ((hasDerivAt_id' (x := d)).const_mul 3).const_sub (1 - v)
  have h2 := (h1.const_mul 2).add_const v
  have hden : (1 - v - 3 * d) * (2 * (1 - v - 3 * d) + v) ≠ 0 := by positivity
  have h := (hasDerivAt_const d (3 * v)).div (h1.mul h2) hden
  change HasDerivAt (fun d => 3 * v / ((1 - v - 3 * d) * (2 * (1 - v - 3 * d) + v))) _ d at h
  exact h.congr_deriv (by simp only [Pi.mul_apply]; field_simp; ring)

private theorem massDeriv_hasDerivAt (hv0 : 0 < v) (hv : v ≤ 1 / 8)
    (hd : d ≤ v / 2) :
    HasDerivAt (massDeriv v) (massDeriv2 v d) d := by
  have hA := near_ge hv hd
  have ha := far_ge hv hd
  have hden : 1 - v - d ≠ 0 := by positivity
  have hrec := (hasDerivAt_const d 2).div ((hasDerivAt_id' (x := d)).const_sub (1 - v)) hden
  have hB := nearFraction_hasDerivAt hv0.le (by linarith)
  have hC := farFraction_hasDerivAt hv0.le (by linarith)
  have hpoly := (hasDerivAt_const d (-1)).sub ((hasDerivAt_id' (x := d)).const_mul 2)
  have h := ((hpoly.add hrec).sub (hB.const_mul 8)).sub (hC.const_mul 8)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold massDeriv2
    field_simp
    ring
  · unfold massDeriv
    simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply]
    ring

private theorem singletonMassTerm_concaveOn (hv0 : 0 < v) (hv : v ≤ 1 / 8) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) (v / 2)) (singletonMassTerm v) := by
  apply concaveOn_Icc_of_hasDerivAt2_nonpos 0 (v / 2) (singletonMassTerm v)
    (massDeriv v) (massDeriv2 v)
  · intro t ht
    exact (singletonMassTerm_hasDerivAt hv0 hv ht.2).continuousAt.continuousWithinAt
  · intro t ht
    exact singletonMassTerm_hasDerivAt hv0 hv ht.2.le
  · intro t ht
    exact massDeriv_hasDerivAt hv0 hv ht.2.le
  · intro t ht
    exact (massDeriv2_neg hv0 hv ht.1.le ht.2.le).le

private theorem singletonMassTerm_ge_min (hv0 : 0 < v) (hv : v ≤ 1 / 8)
    (hd0 : 0 ≤ d) (hd : d ≤ v / 2) :
    min (singletonMassTerm v 0) (singletonMassTerm v (v / 2)) ≤ singletonMassTerm v d := by
  apply (singletonMassTerm_concaveOn hv0 hv).min_le_of_mem_Icc
  · exact Set.left_mem_Icc.mpr (by positivity)
  · exact Set.right_mem_Icc.mpr (by positivity)
  · exact ⟨hd0, hd⟩

/-- The mass term at `d = 0`, as a function of the off-diagonal mass. -/
private noncomputable def cornerAtZero (v : ℝ) : ℝ :=
  2 + 14 * Real.log (1 - v) - 16 * Real.log (1 - v / 2)

/-- The mass term at `d = v / 2`, as a function of the off-diagonal mass. -/
private noncomputable def cornerAtHalf (v : ℝ) : ℝ :=
  2 - v / 2 - v ^ 2 / 4 + 6 * Real.log (1 - 3 * v / 2) - 8 * Real.log (1 - v)
    + 8 * Real.log (1 - 5 * v / 2) - 8 * Real.log (1 - 2 * v)

private theorem singletonMassTerm_zero (hv0 : 0 < v) (hv : v ≤ 1 / 8) :
    singletonMassTerm v 0 = cornerAtZero v := by
  unfold singletonMassTerm cornerAtZero
  simp only [sub_zero, mul_zero, pow_two]
  have hd : 1 - v ≠ 0 := by linarith
  have h : 1 + v / (2 * (1 - v)) = (1 - v / 2) / (1 - v) := by
    field_simp
    ring
  rw [h, Real.log_div (by linarith) (by linarith)]
  ring

private theorem singletonMassTerm_half (hv0 : 0 < v) (hv : v ≤ 1 / 8) :
    singletonMassTerm v (v / 2) = cornerAtHalf v := by
  have hne1 : 2 * (1 - 3 * v / 2) ≠ 0 := by nlinarith
  have hne2 : 2 * (1 - 5 * v / 2) ≠ 0 := by nlinarith
  have h1 : 1 + v / (2 * (1 - 3 * v / 2)) = (1 - v) / (1 - 3 * v / 2) := by
    rw [add_div' _ _ _ hne1]
    rw [show (1 : ℝ) * (2 * (1 - 3 * v / 2)) + v = 2 * (1 - v) by ring,
      mul_div_mul_left _ _ two_ne_zero]
  have h2 : 1 + v / (2 * (1 - 5 * v / 2)) = (1 - 2 * v) / (1 - 5 * v / 2) := by
    rw [add_div' _ _ _ hne2]
    rw [show (1 : ℝ) * (2 * (1 - 5 * v / 2)) + v = 2 * (1 - 2 * v) by ring,
      mul_div_mul_left _ _ two_ne_zero]
  unfold singletonMassTerm cornerAtHalf
  rw [show 1 - v - v / 2 = 1 - 3 * v / 2 by ring,
    show 1 - v - 3 * (v / 2) = 1 - 5 * v / 2 by ring, h1, h2,
    Real.log_div (by linarith) (by linarith),
    Real.log_div (by linarith) (by linarith)]
  ring

private theorem affineLog_hasDerivAt (a c x : ℝ) (h : a - c * x ≠ 0) :
    HasDerivAt (fun x => Real.log (a - c * x)) (-c / (a - c * x)) x := by
  have hx := (((hasDerivAt_id' (x := x)).const_mul c).const_sub a).log h
  exact hx.congr_deriv (by ring)

private theorem cornerAtZero_hasDerivAt (hv : v < 1) :
    HasDerivAt cornerAtZero ((-6 - v) / ((1 - v) * (1 - v / 2))) v := by
  have h1 := affineLog_hasDerivAt 1 1 v (by linarith)
  have h2 := affineLog_hasDerivAt 1 (1 / 2) v (by linarith)
  have hn1 : 1 - v ≠ 0 := by linarith
  have hn2 : (2 : ℝ) - v ≠ 0 := by linarith
  have hnh : 1 - v / 2 ≠ 0 := by linarith
  have h := ((h1.const_mul 14).const_add 2).sub (h2.const_mul 16)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · field_simp
    ring
  · unfold cornerAtZero
    simp only [Pi.sub_apply]
    ring_nf

private theorem cornerAtHalf_hasDerivAt (hv : v < 2 / 5) :
    HasDerivAt cornerAtHalf
      (-1 / 2 - v / 2 - (1 + 3 * v) / ((1 - 3 * v / 2) * (1 - v)) -
        4 / ((1 - 5 * v / 2) * (1 - 2 * v))) v := by
  have hi := hasDerivAt_id' (x := v)
  have hpoly := ((hi.const_mul (1 / 2)).const_sub 2).sub ((hi.pow 2).const_mul (1 / 4))
  have h3 := affineLog_hasDerivAt 1 (3 / 2) v (by linarith)
  have h1 := affineLog_hasDerivAt 1 1 v (by linarith)
  have h5 := affineLog_hasDerivAt 1 (5 / 2) v (by linarith)
  have h2 := affineLog_hasDerivAt 1 2 v (by linarith)
  have hn1 : 1 - v ≠ 0 := by linarith
  have hn2 : 1 - 2 * v ≠ 0 := by linarith
  have hn3 : (2 : ℝ) - 3 * v ≠ 0 := by linarith
  have hn5 : (2 : ℝ) - 5 * v ≠ 0 := by linarith
  have hn3' : (2 : ℝ) - v * 3 ≠ 0 := by linarith
  have hn5' : (2 : ℝ) - v * 5 ≠ 0 := by linarith
  have hd3 : 1 - 3 * v / 2 ≠ 0 := by linarith
  have hd5 : 1 - 5 * v / 2 ≠ 0 := by linarith
  have h := (((hpoly.add (h3.const_mul 6)).sub (h1.const_mul 8)).add
    (h5.const_mul 8)).sub (h2.const_mul 8)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · field_simp
    ring
  · unfold cornerAtHalf
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    ring_nf

private theorem cornerAtZero_antitoneOn : AntitoneOn cornerAtZero (Set.Icc (0 : ℝ) (1 / 8)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / 8))
  · intro x hx
    exact (cornerAtZero_hasDerivAt (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (cornerAtZero_hasDerivAt (by linarith [hx.2])).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx.1]) (by nlinarith [hx.1, hx.2])

private theorem cornerAtHalf_antitoneOn : AntitoneOn cornerAtHalf (Set.Icc (0 : ℝ) (1 / 8)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / 8))
  · intro x hx
    exact (cornerAtHalf_hasDerivAt (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (cornerAtHalf_hasDerivAt (by linarith [hx.2])).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    have hx8 : x < 1 / 8 := hx.2
    have t1 : 0 ≤ (1 + 3 * x) / ((1 - 3 * x / 2) * (1 - x)) :=
      div_nonneg (by linarith) (by nlinarith)
    have t2 : 0 ≤ 4 / ((1 - 5 * x / 2) * (1 - 2 * x)) :=
      div_nonneg (by norm_num) (by nlinarith)
    linarith

private theorem cornerAtZero_eighth :
    cornerAtZero (1 / 8) =
      2 + 22 * Real.log 2 - 16 * Real.log 3 - 16 * Real.log 5 + 14 * Real.log 7 := by
  unfold cornerAtZero
  norm_num
  rw [show (7 / 8 : ℝ) = 7 / 2 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow,
    show (15 / 16 : ℝ) = 15 / 2 ^ 4 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow,
    show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

private theorem cornerAtHalf_eighth :
    cornerAtHalf (1 / 8) =
      495 / 256 - 16 * Real.log 2 - 8 * Real.log 3 - 8 * Real.log 7 + 8 * Real.log 11
        + 6 * Real.log 13 := by
  unfold cornerAtHalf
  norm_num
  rw [show (13 / 16 : ℝ) = 13 / 2 ^ 4 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow,
    show (7 / 8 : ℝ) = 7 / 2 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow,
    show (11 / 16 : ℝ) = 11 / 2 ^ 4 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow,
    show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  ring

private theorem corner_sum_gt_zero :
    (1 : ℝ) / 100 < 8 * Real.log 2 - 6 * Real.log 3 + cornerAtZero (1 / 8) := by
  rw [cornerAtZero_eighth]
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  norm_num at h2 h2'
  linarith [log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2,
    log_seven_bounds.1, log_seven_bounds.2]

private theorem corner_sum_gt_half :
    (1 : ℝ) / 100 < 8 * Real.log 2 - 6 * Real.log 3 + cornerAtHalf (1 / 8) := by
  rw [cornerAtHalf_eighth]
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  norm_num at h2 h2'
  linarith [log_three_bounds.1, log_three_bounds.2, log_seven_bounds.1, log_seven_bounds.2,
    log_eleven_bounds.1, log_eleven_bounds.2, log_thirteen_bounds.1, log_thirteen_bounds.2]

/-- On the box the fixed cut supplies, the singleton margin's three scalar
terms exceed `1 / 100`: the two ratio terms at cells whose ratios sum to at
least `2`, and the mass term at `(v, d)` with `v <= 1/8` and `d <= v/2`. -/
theorem singletonTerms_gt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : 2 ≤ x + y)
    (hv0 : 0 < v) (hv : v ≤ 1 / 8) (hd0 : 0 ≤ d) (hd : d ≤ v / 2) :
    (1 : ℝ) / 100 <
      singletonRatioTerm x + singletonRatioTerm y + singletonMassTerm v d := by
  have hpair := singletonRatioTerm_pair hx hy hxy
  have hmass := singletonMassTerm_ge_min hv0 hv hd0 hd
  rw [singletonMassTerm_zero hv0 hv, singletonMassTerm_half hv0 hv] at hmass
  have hz : cornerAtZero (1 / 8) ≤ cornerAtZero v :=
    cornerAtZero_antitoneOn ⟨hv0.le, hv⟩ ⟨by norm_num, le_refl _⟩ hv
  have hh : cornerAtHalf (1 / 8) ≤ cornerAtHalf v :=
    cornerAtHalf_antitoneOn ⟨hv0.le, hv⟩ ⟨by norm_num, le_refl _⟩ hv
  rcases le_total (cornerAtZero v) (cornerAtHalf v) with hmin | hmin
  · rw [min_eq_left hmin] at hmass
    linarith [corner_sum_gt_zero]
  · rw [min_eq_right hmin] at hmass
    linarith [corner_sum_gt_half]

end StochasticToDeterministicLatents.Binary
