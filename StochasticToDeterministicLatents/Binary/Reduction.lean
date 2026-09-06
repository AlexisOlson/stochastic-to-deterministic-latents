import StochasticToDeterministicLatents.Binary.ContactChart

/-!
# Deterministic-code reduction on a binary transpose chart

For a supplied transpose chart, this module proves that every binary code is
dominated in determinization cost by the constant code or the distinguished
singleton code.  The phase selector therefore has no greater cost than any
binary code, and the minimum of the two chart-code costs has the same bound.

The root exports this result as `BIN-REDUCE`; the factor-nine proof does not
depend on it. A factor-eight upper bound needs only `w3 L <= w3Cost L g` at
the phase-selected code, which `w3_le_w3Cost` already gives. The dominance
proved here supplies the reverse inequality needed to identify the infimum
with the selected cost. The arbitrary-code reward bound is used internally
by the phase-selector cost bound.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

open Set

namespace StochasticToDeterministicLatents.Binary

noncomputable section

/-! ## Scalar entropy inequalities -/

private lemma binaryEntropy_le_of_le_and_sum_le_one
    {c b : Real} (hc : 0 ≤ c) (hcb : c ≤ b) (hsum : b + c ≤ 1) :
    Real.binEntropy c ≤ Real.binEntropy b := by
  by_cases hb : b ≤ 1 / 2
  · have hb' : b ≤ (2 : Real)⁻¹ := by norm_num at hb ⊢; exact hb
    exact Real.binEntropy_strictMonoOn.monotoneOn
      ⟨hc, hcb.trans hb'⟩ ⟨hc.trans hcb, hb'⟩ hcb
  · have hhalf : 1 / 2 ≤ b := le_of_not_ge hb
    have hc_le : c ≤ 1 - b := by linarith
    have hzero : 0 ≤ 1 - b := by linarith
    have hone_half : 1 - b ≤ (2 : Real)⁻¹ := by norm_num; linarith
    calc
      Real.binEntropy c ≤ Real.binEntropy (1 - b) :=
        Real.binEntropy_strictMonoOn.monotoneOn
          ⟨hc, hc_le.trans hone_half⟩ ⟨hzero, hone_half⟩ hc_le
      _ = Real.binEntropy b := Real.binEntropy_one_sub b

private lemma one_div_mul_one_sub
    {x : Real} (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    1 / (x * (1 - x)) = 1 / (1 - x) + 1 / x := by
  field_simp [hx, hx1]
  ring

private lemma concaveOn_scalarSingletonReward_difference
    {c b : Real} (hc : 0 < c) (hcb : c ≤ b) (hsum : b + c < 1) :
    ConcaveOn Real (Icc 0 (1 / 2)) (fun pi =>
      scalarSingletonReward pi c b - scalarSingletonReward pi b c) := by
  let delta : Real := b - c
  let entropyGap : Real := Real.binEntropy b - Real.binEntropy c
  let f : Real → Real := fun pi =>
    Real.binEntropy (c + pi * delta) -
      Real.binEntropy (b - pi * delta) +
        4 * (1 - 2 * pi) * entropyGap
  let f' : Real → Real := fun pi =>
    delta * (Real.log (1 - (c + pi * delta)) -
      Real.log (c + pi * delta)) +
    delta * (Real.log (1 - (b - pi * delta)) -
      Real.log (b - pi * delta)) - 8 * entropyGap
  let f'' : Real → Real := fun pi =>
    delta * ((-delta) / (1 - (c + pi * delta)) -
      delta / (c + pi * delta)) +
    delta * (delta / (1 - (b - pi * delta)) +
      delta / (b - pi * delta))
  have hdelta : 0 ≤ delta := by dsimp [delta]; linarith
  have hfun :
      (fun pi => scalarSingletonReward pi c b -
        scalarSingletonReward pi b c) = f := by
    funext pi
    simp only [scalarSingletonReward, f, delta, entropyGap]
    ring_nf
  rw [hfun]
  refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := f') (f'' := f'')
    (convex_Icc 0 (1 / 2)) (by dsimp [f]; fun_prop) ?_ ?_ ?_
  · intro pi hpi
    simp only [interior_Icc, mem_Ioo] at hpi
    have hvpos : 0 < c + pi * delta :=
      add_pos_of_pos_of_nonneg hc (mul_nonneg hpi.1.le hdelta)
    have hvlt : c + pi * delta < 1 := by
      have hpile : pi ≤ 1 := by linarith
      dsimp [delta]
      nlinarith
    have hupos : 0 < b - pi * delta := by
      have hpile : pi ≤ 1 := by linarith
      dsimp [delta]
      nlinarith
    have hult : b - pi * delta < 1 := by
      have hb_lt : b < 1 := by linarith
      exact lt_of_le_of_lt (sub_le_self _ (mul_nonneg hpi.1.le hdelta)) hb_lt
    have hv : HasDerivAt (fun t : Real => c + t * delta) delta pi := by
      have h := (hasDerivAt_const (x := pi) (c := c)).add
        ((hasDerivAt_id' (x := pi)).mul_const delta)
      convert! h using 1
      simp
    have hu : HasDerivAt (fun t : Real => b - t * delta) (-delta) pi := by
      have h := (hasDerivAt_const (x := pi) (c := b)).sub
        ((hasDerivAt_id' (x := pi)).mul_const delta)
      convert! h using 1
      simp
    have hhv : HasDerivAt
        (fun t : Real => Real.binEntropy (c + t * delta))
        ((Real.log (1 - (c + pi * delta)) - Real.log (c + pi * delta)) * delta) pi := by
      convert! (Real.hasDerivAt_binEntropy hvpos.ne' hvlt.ne).comp pi hv using 1
    have hhu : HasDerivAt
        (fun t : Real => Real.binEntropy (b - t * delta))
        ((Real.log (1 - (b - pi * delta)) - Real.log (b - pi * delta)) *
          (-delta)) pi := by
      convert! (Real.hasDerivAt_binEntropy hupos.ne' hult.ne).comp pi hu using 1
    have hlinear : HasDerivAt
        (fun t : Real => 4 * (1 - 2 * t) * entropyGap)
        (-8 * entropyGap) pi := by
      have haff : HasDerivAt (fun t : Real => 1 - 2 * t) (-2) pi := by
        have h := (hasDerivAt_const (x := pi) (c := (1 : Real))).sub
          ((hasDerivAt_id' (x := pi)).const_mul 2)
        convert! h using 1
        simp
      have h := (haff.const_mul 4).mul_const entropyGap
      have heq : (-8 : Real) * entropyGap = 4 * (-2) * entropyGap := by ring
      rw [heq]
      exact h
    have hder : HasDerivAt f (f' pi) pi := by
      dsimp [f, f']
      convert! (hhv.sub hhu).add hlinear using 1
      simp
      ring
    exact hder.hasDerivWithinAt
  · intro pi hpi
    simp only [interior_Icc, mem_Ioo] at hpi
    have hvpos : 0 < c + pi * delta :=
      add_pos_of_pos_of_nonneg hc (mul_nonneg hpi.1.le hdelta)
    have hvlt : c + pi * delta < 1 := by
      have hpile : pi ≤ 1 := by linarith
      dsimp [delta]
      nlinarith
    have hupos : 0 < b - pi * delta := by
      have hpile : pi ≤ 1 := by linarith
      dsimp [delta]
      nlinarith
    have hult : b - pi * delta < 1 := by
      have hb_lt : b < 1 := by linarith
      exact lt_of_le_of_lt (sub_le_self _ (mul_nonneg hpi.1.le hdelta)) hb_lt
    have hv : HasDerivAt (fun t : Real => c + t * delta) delta pi := by
      have h := (hasDerivAt_const (x := pi) (c := c)).add
        ((hasDerivAt_id' (x := pi)).mul_const delta)
      convert! h using 1
      simp
    have hu : HasDerivAt (fun t : Real => b - t * delta) (-delta) pi := by
      have h := (hasDerivAt_const (x := pi) (c := b)).sub
        ((hasDerivAt_id' (x := pi)).mul_const delta)
      convert! h using 1
      simp
    have hvlog : HasDerivAt
        (fun t : Real => Real.log (1 - (c + t * delta)) -
          Real.log (c + t * delta))
        ((-delta) / (1 - (c + pi * delta)) - delta / (c + pi * delta)) pi := by
      have h := (((hasDerivAt_const pi 1).sub hv).log
        (sub_pos.mpr hvlt).ne').sub (hv.log hvpos.ne')
      convert! h using 1
      simp
    have hulog : HasDerivAt
        (fun t : Real => Real.log (1 - (b - t * delta)) -
          Real.log (b - t * delta))
        (delta / (1 - (b - pi * delta)) + delta / (b - pi * delta)) pi := by
      have h := (((hasDerivAt_const pi 1).sub hu).log
        (sub_pos.mpr hult).ne').sub (hu.log hupos.ne')
      convert! h using 1
      simp
      ring
    have hder : HasDerivAt f' (f'' pi) pi := by
      have hraw : HasDerivAt f'
          (delta * ((-delta) / (1 - (c + pi * delta)) -
            delta / (c + pi * delta)) +
          delta * (delta / (1 - (b - pi * delta)) +
            delta / (b - pi * delta))) pi := by
        dsimp [f']
        convert! ((hvlog.const_mul delta).add
          (hulog.const_mul delta)).sub_const (8 * entropyGap) using 1
      simpa [f''] using hraw
    exact hder.hasDerivWithinAt
  · intro pi hpi
    simp only [interior_Icc, mem_Ioo] at hpi
    have hvpos : 0 < c + pi * delta :=
      add_pos_of_pos_of_nonneg hc (mul_nonneg hpi.1.le hdelta)
    have hvlt : c + pi * delta < 1 := by
      have hpile : pi ≤ 1 := by linarith
      dsimp [delta]
      nlinarith
    have hupos : 0 < b - pi * delta := by
      have hpile : pi ≤ 1 := by linarith
      dsimp [delta]
      nlinarith
    have hult : b - pi * delta < 1 := by
      have hb_lt : b < 1 := by linarith
      exact lt_of_le_of_lt (sub_le_self _ (mul_nonneg hpi.1.le hdelta)) hb_lt
    have hv_le_u : c + pi * delta ≤ b - pi * delta := by
      dsimp [delta]
      nlinarith
    have hsum_vu : (c + pi * delta) + (b - pi * delta) < 1 := by
      dsimp [delta]
      linarith
    have hden_le :
        (c + pi * delta) * (1 - (c + pi * delta)) ≤
          (b - pi * delta) * (1 - (b - pi * delta)) := by
      nlinarith
    have hrecip :
        1 / ((b - pi * delta) * (1 - (b - pi * delta))) ≤
          1 / ((c + pi * delta) * (1 - (c + pi * delta))) := by
      exact one_div_le_one_div_of_le
        (mul_pos hvpos (sub_pos.mpr hvlt)) hden_le
    have hscaled := mul_le_mul_of_nonneg_left hrecip (sq_nonneg delta)
    have hvsplit := one_div_mul_one_sub hvpos.ne' (sub_pos.mpr hvlt).ne'
    have husplit := one_div_mul_one_sub hupos.ne' (sub_pos.mpr hult).ne'
    calc
      f'' pi = delta ^ 2 *
          (1 / ((b - pi * delta) * (1 - (b - pi * delta))) -
            1 / ((c + pi * delta) * (1 - (c + pi * delta)))) := by
        dsimp [f'']
        rw [hvsplit, husplit]
        ring
      _ ≤ 0 := by
        rw [mul_sub]
        linarith

private lemma scalarSingletonReward_low_le_high
    {pi c b : Real} (hc : 0 < c) (hcb : c ≤ b) (hsum : b + c < 1)
    (hpi0 : 0 ≤ pi) (hpih : pi ≤ 1 / 2) :
    scalarSingletonReward pi b c ≤ scalarSingletonReward pi c b := by
  let F : Real → Real := fun t =>
    scalarSingletonReward t c b - scalarSingletonReward t b c
  have hconc : ConcaveOn Real (Icc 0 (1 / 2)) F :=
    concaveOn_scalarSingletonReward_difference hc hcb hsum
  have hmin := hconc.min_le_of_mem_Icc
    (show (0 : Real) ∈ Icc 0 (1 / 2) by norm_num)
    (show (1 / 2 : Real) ∈ Icc 0 (1 / 2) by norm_num)
    ⟨hpi0, hpih⟩
  have hdelta : 0 ≤ Real.binEntropy b - Real.binEntropy c := by
    exact sub_nonneg.mpr
      (binaryEntropy_le_of_le_and_sum_le_one hc.le hcb hsum.le)
  have hF0 : F 0 = 3 * (Real.binEntropy b - Real.binEntropy c) := by
    simp [F, scalarSingletonReward]
    ring
  have hFhalf : F (1 / 2) = 0 := by
    simp [F, scalarSingletonReward]
    ring_nf
  rw [hF0, hFhalf, min_eq_right] at hmin
  · dsimp [F] at hmin
    linarith
  · linarith

/-! ## Equal-mass allocation between output blocks -/

/-- One output block's contribution to a scaled reward.  This private helper
is in natural-log units; public information quantities remain in bits. -/
private def scalarBlockReward (pi x y : Real) : Real :=
  ((1 - pi) * x + pi * y).negMulLog -
    4 * ((1 - pi) * x.negMulLog + pi * y.negMulLog)

private lemma one_div_weighted_sum_le_weighted_one_div
    {pi x y : Real} (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hx : 0 < x) (hy : 0 < y) :
    1 / ((1 - pi) * x + pi * y) ≤ (1 - pi) / x + pi / y := by
  have h1pi : 0 ≤ 1 - pi := by linarith
  have hm : 0 < (1 - pi) * x + pi * y := by
    by_cases hpi : pi = 0
    · simp [hpi, hx]
    · have hpipos : 0 < pi := lt_of_le_of_ne hpi0 (Ne.symm hpi)
      exact add_pos_of_nonneg_of_pos (mul_nonneg h1pi hx.le) (mul_pos hpipos hy)
  have hid :
      ((1 - pi) / x + pi / y) - 1 / ((1 - pi) * x + pi * y) =
        pi * (1 - pi) * (x - y) ^ 2 /
          (x * y * ((1 - pi) * x + pi * y)) := by
    field_simp [hx.ne', hy.ne', hm.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

private lemma convexOn_scalarBlockReward_add_equalMass
    {pi x y n : Real} (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (_hn : 0 < n) :
    ConvexOn Real (Icc 0 n) (fun t => scalarBlockReward pi (x + t) (y + t)) := by
  let mix : Real := (1 - pi) * x + pi * y
  let f : Real → Real := fun t =>
    Real.negMulLog (mix + t) -
      4 * ((1 - pi) * Real.negMulLog (x + t) +
        pi * Real.negMulLog (y + t))
  let f' : Real → Real := fun t =>
    (-Real.log (mix + t) - 1) -
      4 * ((1 - pi) * (-Real.log (x + t) - 1) +
        pi * (-Real.log (y + t) - 1))
  let f'' : Real → Real := fun t =>
    -(1 / (mix + t)) +
      4 * ((1 - pi) / (x + t) + pi / (y + t))
  have hmix : 0 ≤ mix := by
    dsimp [mix]
    exact add_nonneg (mul_nonneg (by linarith) hx) (mul_nonneg hpi0 hy)
  have hfun : (fun t => scalarBlockReward pi (x + t) (y + t)) = f := by
    funext t
    dsimp [f, scalarBlockReward, mix]
    congr 2
    ring
  rw [hfun]
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'')
    (convex_Icc 0 n) (by dsimp [f, scalarBlockReward]; fun_prop) ?_ ?_ ?_
  · intro t ht
    simp only [interior_Icc, mem_Ioo] at ht
    have hxt : 0 < x + t := add_pos_of_nonneg_of_pos hx ht.1
    have hyt : 0 < y + t := add_pos_of_nonneg_of_pos hy ht.1
    have hmt : 0 < mix + t := add_pos_of_nonneg_of_pos hmix ht.1
    have hxm : HasDerivAt (fun s : Real => x + s) 1 t := by
      exact (hasDerivAt_id' (x := t)).const_add x
    have hym : HasDerivAt (fun s : Real => y + s) 1 t := by
      exact (hasDerivAt_id' (x := t)).const_add y
    have hmm : HasDerivAt (fun s : Real => mix + s) 1 t := by
      exact (hasDerivAt_id' (x := t)).const_add mix
    have hM := (Real.hasDerivAt_negMulLog hmt.ne').comp t hmm
    have hX := (Real.hasDerivAt_negMulLog hxt.ne').comp t hxm
    have hY := (Real.hasDerivAt_negMulLog hyt.ne').comp t hym
    have hder : HasDerivAt f (f' t) t := by
      have hraw := hM.sub (((hX.const_mul (1 - pi)).add
        (hY.const_mul pi)).const_mul 4)
      convert! hraw using 1
      simp only [f']
      ring
    exact hder.hasDerivWithinAt
  · intro t ht
    simp only [interior_Icc, mem_Ioo] at ht
    have hxt : 0 < x + t := add_pos_of_nonneg_of_pos hx ht.1
    have hyt : 0 < y + t := add_pos_of_nonneg_of_pos hy ht.1
    have hmt : 0 < mix + t := add_pos_of_nonneg_of_pos hmix ht.1
    have hxm : HasDerivAt (fun s : Real => x + s) 1 t := by
      exact (hasDerivAt_id' (x := t)).const_add x
    have hym : HasDerivAt (fun s : Real => y + s) 1 t := by
      exact (hasDerivAt_id' (x := t)).const_add y
    have hmm : HasDerivAt (fun s : Real => mix + s) 1 t := by
      exact (hasDerivAt_id' (x := t)).const_add mix
    have hM := (hmm.log hmt.ne').neg
    have hX := (hxm.log hxt.ne').neg
    have hY := (hym.log hyt.ne').neg
    have hM' : HasDerivAt (fun s : Real => -Real.log (mix + s) - 1)
        (-(1 / (mix + t))) t := by
      simpa only [Pi.neg_apply, Function.comp_apply, mul_one, one_div] using
        hM.sub_const 1
    have hX' : HasDerivAt (fun s : Real => -Real.log (x + s) - 1)
        (-(1 / (x + t))) t := by
      simpa only [Pi.neg_apply, Function.comp_apply, mul_one, one_div] using
        hX.sub_const 1
    have hY' : HasDerivAt (fun s : Real => -Real.log (y + s) - 1)
        (-(1 / (y + t))) t := by
      simpa only [Pi.neg_apply, Function.comp_apply, mul_one, one_div] using
        hY.sub_const 1
    have hder : HasDerivAt f' (f'' t) t := by
      have hraw := hM'.sub
        (((hX'.const_mul (1 - pi)).add
          (hY'.const_mul pi)).const_mul 4)
      convert! hraw using 1
      simp only [f'']
      ring
    exact hder.hasDerivWithinAt
  · intro t ht
    simp only [interior_Icc, mem_Ioo] at ht
    have hxt : 0 < x + t := add_pos_of_nonneg_of_pos hx ht.1
    have hyt : 0 < y + t := add_pos_of_nonneg_of_pos hy ht.1
    have hmt : 0 < mix + t := add_pos_of_nonneg_of_pos hmix ht.1
    have hrec := one_div_weighted_sum_le_weighted_one_div hpi0 hpi1 hxt hyt
    have hmexpr : (1 - pi) * (x + t) + pi * (y + t) = mix + t := by
      dsimp [mix]
      ring
    rw [hmexpr] at hrec
    have hmrec : 0 < 1 / (mix + t) := one_div_pos.mpr hmt
    dsimp [f'', mix]
    linarith

private lemma convexOn_comp_sub_Icc
    {n : Real} {f : Real → Real} (hf : ConvexOn Real (Icc 0 n) f) :
    ConvexOn Real (Icc 0 n) (fun t => f (n - t)) := by
  refine ⟨convex_Icc 0 n, ?_⟩
  intro t ht u hu a b ha hb hab
  have hnt : n - t ∈ Icc (0 : Real) n := by constructor <;> linarith [ht.1, ht.2]
  have hnu : n - u ∈ Icc (0 : Real) n := by constructor <;> linarith [hu.1, hu.2]
  have h := hf.2 hnt hnu ha hb hab
  have harg : n - (a • t + b • u) = a • (n - t) + b • (n - u) := by
    simp only [smul_eq_mul]
    calc
      n - (a * t + b * u) = (a + b) * n - (a * t + b * u) := by
        rw [hab]
        ring
      _ = a * (n - t) + b * (n - u) := by ring
  change f (n - (a • t + b • u)) ≤ a • f (n - t) + b • f (n - u)
  rw [harg]
  exact h

private lemma scalarBlockReward_split_le_max_endpoints
    {pi x0 y0 x1 y1 n t : Real}
    (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hx0 : 0 ≤ x0) (hy0 : 0 ≤ y0) (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hn : 0 < n) (ht : t ∈ Icc (0 : Real) n) :
    scalarBlockReward pi (x0 + t) (y0 + t) +
        scalarBlockReward pi (x1 + (n - t)) (y1 + (n - t)) ≤
      max
        (scalarBlockReward pi x0 y0 + scalarBlockReward pi (x1 + n) (y1 + n))
        (scalarBlockReward pi (x0 + n) (y0 + n) + scalarBlockReward pi x1 y1) := by
  have h0 := convexOn_scalarBlockReward_add_equalMass hpi0 hpi1 hx0 hy0 hn
  have h1base := convexOn_scalarBlockReward_add_equalMass hpi0 hpi1 hx1 hy1 hn
  have h1 := convexOn_comp_sub_Icc h1base
  have hsum : ConvexOn Real (Icc 0 n) (fun s =>
      scalarBlockReward pi (x0 + s) (y0 + s) +
        scalarBlockReward pi (x1 + (n - s)) (y1 + (n - s))) := by
    refine ⟨convex_Icc 0 n, ?_⟩
    intro x hx y hy a b ha hb hab
    have hleft := h0.2 hx hy ha hb hab
    have hright := h1.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hleft hright ⊢
    linarith
  have hmax := hsum.le_max_of_mem_Icc
    (show (0 : Real) ∈ Icc 0 n by constructor <;> linarith)
    (show n ∈ Icc (0 : Real) n by constructor <;> linarith)
    ht
  simpa using hmax

private lemma scalarBlockReward_add_equalMass_le_merge
    {pi c b n : Real} (hc : 0 < c) (hcb : c ≤ b) (hn : 0 < n)
    (hpi0 : 0 ≤ pi) (hpih : pi ≤ 1 / 2) :
    scalarBlockReward pi b c + scalarBlockReward pi n n ≤
      scalarBlockReward pi (b + n) (c + n) := by
  have hb : 0 < b := hc.trans_le hcb
  have hpi1 : pi ≤ 1 := hpih.trans (by norm_num)
  have h1pi : 0 ≤ 1 - pi := by linarith
  let mix : Real := (1 - pi) * b + pi * c
  let f : Real → Real := fun t =>
    scalarBlockReward pi (b + t) (c + t) -
      scalarBlockReward pi t t - scalarBlockReward pi b c
  let f' : Real → Real := fun t =>
    4 * ((1 - pi) * Real.log (b + t) + pi * Real.log (c + t)) -
      Real.log (mix + t) - 3 * Real.log t
  have hmix : 0 < mix := by
    dsimp [mix]
    by_cases hpi : pi = 1
    · simp [hpi, hc]
    · have h1pipos : 0 < 1 - pi := sub_pos.mpr (lt_of_le_of_ne hpi1 hpi)
      exact add_pos_of_pos_of_nonneg (mul_pos h1pipos hb)
        (mul_nonneg hpi0 hc.le)
  have hcont : ContinuousOn f (Icc (0 : Real) n) := by
    dsimp [f, scalarBlockReward]
    fun_prop
  have hderiv : ∀ t ∈ interior (Icc (0 : Real) n), HasDerivAt f (f' t) t := by
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := ht.1
    have hbt : 0 < b + t := add_pos hb ht0
    have hct : 0 < c + t := add_pos hc ht0
    have hmt : 0 < mix + t := add_pos hmix ht0
    have htDer : HasDerivAt (fun s : Real => s) 1 t := hasDerivAt_id t
    have hbDer : HasDerivAt (fun s : Real => b + s) 1 t := htDer.const_add b
    have hcDer : HasDerivAt (fun s : Real => c + s) 1 t := htDer.const_add c
    have hmDer : HasDerivAt (fun s : Real => mix + s) 1 t := htDer.const_add mix
    have hB := (Real.hasDerivAt_negMulLog hbt.ne').comp t hbDer
    have hC := (Real.hasDerivAt_negMulLog hct.ne').comp t hcDer
    have hM := (Real.hasDerivAt_negMulLog hmt.ne').comp t hmDer
    have hT := Real.hasDerivAt_negMulLog ht0.ne'
    have hfirst : HasDerivAt
        (fun s : Real => scalarBlockReward pi (b + s) (c + s))
        ((-Real.log (mix + t) - 1) -
          4 * ((1 - pi) * (-Real.log (b + t) - 1) +
            pi * (-Real.log (c + t) - 1))) t := by
      have hraw := hM.sub (((hB.const_mul (1 - pi)).add
        (hC.const_mul pi)).const_mul 4)
      have hfun :
          (fun s : Real => scalarBlockReward pi (b + s) (c + s)) =
            fun s => Real.negMulLog (mix + s) -
              4 * ((1 - pi) * Real.negMulLog (b + s) +
                pi * Real.negMulLog (c + s)) := by
        funext s
        dsimp [scalarBlockReward, mix]
        congr 2
        ring
      rw [hfun]
      have hraw' : HasDerivAt
          (fun s : Real => Real.negMulLog (mix + s) -
            4 * ((1 - pi) * Real.negMulLog (b + s) +
              pi * Real.negMulLog (c + s)))
          ((-Real.log (mix + t) - 1) -
            4 * ((1 - pi) * (-Real.log (b + t) - 1) +
              pi * (-Real.log (c + t) - 1))) t := by
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => by rfl)).congr_deriv ?_
        ring
      exact hraw'
    have hequal : HasDerivAt
        (fun s : Real => scalarBlockReward pi s s)
        (3 * (Real.log t + 1)) t := by
      have hraw := hT.sub (((hT.const_mul (1 - pi)).add
        (hT.const_mul pi)).const_mul 4)
      have hfun :
          (fun s : Real => scalarBlockReward pi s s) =
            fun s => Real.negMulLog s -
              4 * ((1 - pi) * Real.negMulLog s +
                pi * Real.negMulLog s) := by
        funext s
        dsimp [scalarBlockReward]
        congr 2
        ring
      rw [hfun]
      have hraw' : HasDerivAt
          (fun s : Real => Real.negMulLog s -
            4 * ((1 - pi) * Real.negMulLog s + pi * Real.negMulLog s))
          ((-Real.log t - 1) -
            4 * ((1 - pi) * (-Real.log t - 1) +
              pi * (-Real.log t - 1))) t := by
        refine hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => ?_)
        rfl
      convert hraw' using 1
      ring
    have hraw := (hfirst.sub hequal).sub_const (scalarBlockReward pi b c)
    convert! hraw using 1
    simp only [f']
    ring
  have hderiv_nonneg : ∀ t ∈ interior (Icc (0 : Real) n), 0 ≤ deriv f t := by
    intro t ht
    rw [(hderiv t ht).deriv]
    rw [interior_Icc] at ht
    have ht0 : 0 < t := ht.1
    have hbt : 0 < b + t := add_pos hb ht0
    have hct : 0 < c + t := add_pos hc ht0
    have hmt : 0 < mix + t := add_pos hmix ht0
    have hlogcb : Real.log (c + t) ≤ Real.log (b + t) :=
      Real.log_le_log hct (by linarith)
    have hweight :
        (1 / 2 : Real) * (Real.log (b + t) + Real.log (c + t)) ≤
          (1 - pi) * Real.log (b + t) + pi * Real.log (c + t) := by
      have hprod := mul_nonneg (sub_nonneg.mpr hpih) (sub_nonneg.mpr hlogcb)
      nlinarith
    have hbase : 0 ≤ pi * b + (1 - pi) * c :=
      add_nonneg (mul_nonneg hpi0 hb.le) (mul_nonneg h1pi hc.le)
    have hproduct : t * (mix + t) ≤ (b + t) * (c + t) := by
      have hbc : 0 ≤ b * c := mul_nonneg hb.le hc.le
      have htbase : 0 ≤ t * (pi * b + (1 - pi) * c) :=
        mul_nonneg ht0.le hbase
      dsimp [mix]
      nlinarith
    have hlogproduct := Real.log_le_log (mul_pos ht0 hmt) hproduct
    rw [Real.log_mul ht0.ne' hmt.ne', Real.log_mul hbt.ne' hct.ne'] at hlogproduct
    have hlogtb : Real.log t ≤ Real.log (b + t) :=
      Real.log_le_log ht0 (by linarith)
    have hlogtc : Real.log t ≤ Real.log (c + t) :=
      Real.log_le_log ht0 (by linarith)
    dsimp [f']
    linarith
  have hmono : MonotoneOn f (Icc (0 : Real) n) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : Real) n) hcont
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
      hderiv_nonneg
  have hle := hmono
    (show (0 : Real) ∈ Icc 0 n by constructor <;> linarith)
    (show n ∈ Icc (0 : Real) n by constructor <;> linarith) hn.le
  have hf0 : f 0 = 0 := by simp [f, scalarBlockReward]
  have hfn : f n = scalarBlockReward pi (b + n) (c + n) -
      (scalarBlockReward pi n n + scalarBlockReward pi b c) := by
    dsimp [f]
    ring
  rw [hf0, hfn] at hle
  linarith

private lemma scalarSingletonReward_eq_add_scalarBlockRewards (pi x y : Real) :
    scalarSingletonReward pi x y = scalarBlockReward pi x y +
      scalarBlockReward pi (1 - x) (1 - y) := by
  unfold scalarSingletonReward
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold scalarBlockReward
  have hcomp :
      (1 - pi) * (1 - x) + pi * (1 - y) =
        1 - ((1 - pi) * x + pi * y) := by ring
  rw [hcomp]
  ring

/-! ## A private generic-label reward decomposition -/

/-- The generic-label version of `codeReward`, kept private because the public
cost and reward vocabulary is specialized to `BinaryCode`. -/
private def finiteCodeReward
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : RealTable} (L : Latent p) (g : Cell → γ) : Real :=
  entropyOf g p -
    4 * condEntropy (fun w : L.ι × Cell => g w.2) (fun w => w.1) L.joint

private lemma log_two_mul_entropyOf_eq_sum_negMulLog
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : RealTable} (hp : IsPMF p) (g : Cell → γ) :
    Real.log 2 * entropyOf g p =
      ∑ label, Real.negMulLog (pushforward g p label) := by
  have h := stoch_to_det.H_eq_negMulLog
    (pushforward_isPMF (f := g) hp).isFiniteMeasure
  have htotal := (pushforward_isPMF (f := g) hp).total
  rw [htotal, Real.log_one, mul_zero, zero_add] at h
  simpa [entropyOf, stoch_to_det.Hvar] using h

private lemma pushforward_transposeChart_law
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : TransposeChart) (g : Cell → γ) (label : γ) :
    pushforward g D.law label =
      (1 - D.pi) * pushforward g D.firstComponent label +
        D.pi * pushforward g D.secondComponent label := by
  unfold pushforward stoch_to_det.push TransposeChart.law transposeMixtureLaw
    TransposeChart.firstComponent TransposeChart.secondComponent
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private lemma log_two_mul_finiteCodeReward_eq_sum_scalarBlockRewards
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : TransposeChart) (g : Cell → γ) :
    Real.log 2 * finiteCodeReward D.latent g =
      ∑ label, scalarBlockReward D.pi
        (pushforward g D.firstComponent label)
        (pushforward g D.secondComponent label) := by
  have hG := log_two_mul_entropyOf_eq_sum_negMulLog D.law_isPMF g
  have h0 := log_two_mul_entropyOf_eq_sum_negMulLog D.firstComponent_isPMF g
  have h1 := log_two_mul_entropyOf_eq_sum_negMulLog D.secondComponent_isPMF g
  have hcond :
      condEntropy (fun w : D.latent.ι × Cell => g w.2)
          (fun w => w.1) D.latent.joint =
        ∑ i, D.latent.prior i * entropyOf g (D.latent.comp i) := by
    have hdecomp := stoch_to_det.Hvar_pair_eq_sum_fibers D.latent.joint_isPMF
      (fun w : D.latent.ι × Cell => g w.2) (fun w => w.1)
    change stoch_to_det.condH
        (fun w : D.latent.ι × Cell => g w.2)
        (fun w => w.1) D.latent.joint = _
    calc
      stoch_to_det.condH
          (fun w : D.latent.ι × Cell => g w.2)
          (fun w => w.1) D.latent.joint =
          ∑ i, stoch_to_det.H
            (stoch_to_det.push (fun w : D.latent.ι × Cell => g w.2)
              (fun w => if w.1 = i then D.latent.joint w else 0)) := by
        unfold stoch_to_det.condH
        rw [hdecomp]
        ring
      _ = ∑ i, D.latent.prior i * entropyOf g (D.latent.comp i) := by
        apply Finset.sum_congr rfl
        intro i _
        have hfiber :
            stoch_to_det.push (fun w : D.latent.ι × Cell => g w.2)
                (fun w => if w.1 = i then D.latent.joint w else 0) =
              fun label => D.latent.prior i *
                stoch_to_det.push g (D.latent.comp i) label := by
          funext label
          unfold stoch_to_det.push
          rw [Finset.sum_filter, Fintype.sum_prod_type]
          simp only [Latent.joint, stoch_to_det.Latent.joint]
          rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : g z = label
          · simp only [hz, if_true]
            simp
          · simp [hz]
        rw [hfiber]
        by_cases hi : D.latent.prior i = 0
        · simp [hi, entropyOf, stoch_to_det.H]
        · have hipos : 0 < D.latent.prior i :=
            lt_of_le_of_ne (D.latent.prior_isPMF.nonneg i) (Ne.symm hi)
          simpa [entropyOf, stoch_to_det.Hvar] using stoch_to_det.H_smul
            (stoch_to_det.isFinMeas_push
              (IsPMF.isFiniteMeasure (D.latent.comp_isPMF i))) hipos.le
  have hcondScale :
      Real.log 2 * condEntropy
          (fun w : D.latent.ι × Cell => g w.2)
          (fun w => w.1) D.latent.joint =
        (1 - D.pi) *
            (∑ label, Real.negMulLog
              (pushforward g D.firstComponent label)) +
          D.pi *
            (∑ label, Real.negMulLog
              (pushforward g D.secondComponent label)) := by
    rw [hcond]
    change Real.log 2 *
        (∑ i : Bit, D.latent.prior i * entropyOf g (D.latent.comp i)) = _
    rw [Fin.sum_univ_two]
    simp only [TransposeChart.latent, TransposeChart.prior, twoPointPrior,
      ↓reduceIte, one_ne_zero]
    calc
      Real.log 2 * ((1 - D.pi) * entropyOf g D.firstComponent +
          D.pi * entropyOf g D.secondComponent) =
          (1 - D.pi) * (Real.log 2 * entropyOf g D.firstComponent) +
            D.pi * (Real.log 2 * entropyOf g D.secondComponent) := by ring
      _ = _ := by rw [h0, h1]
  calc
    Real.log 2 * finiteCodeReward D.latent g =
        Real.log 2 * entropyOf g D.law -
          4 * (Real.log 2 * condEntropy
            (fun w : D.latent.ι × Cell => g w.2)
            (fun w => w.1) D.latent.joint) := by
      unfold finiteCodeReward
      ring
    _ = (∑ label, Real.negMulLog (pushforward g D.law label)) -
        4 * ((1 - D.pi) *
            (∑ label, Real.negMulLog
              (pushforward g D.firstComponent label)) +
          D.pi *
            (∑ label, Real.negMulLog
              (pushforward g D.secondComponent label))) := by
      rw [hG, hcondScale]
    _ = ∑ label, scalarBlockReward D.pi
        (pushforward g D.firstComponent label)
        (pushforward g D.secondComponent label) := by
      simp_rw [pushforward_transposeChart_law D g]
      unfold scalarBlockReward
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]

/-! ## Coalescing the two equal-mass cells -/

private def replaceCellLabel
    {γ : Type*} [DecidableEq Cell]
    (g : Cell → γ) (cell : Cell) (label : γ) : Cell → γ :=
  fun z => if z = cell then label else g z

private def coalesceEqualMassAt00 {γ : Type*} (g : Cell → γ) : Cell → γ :=
  replaceCellLabel g cell11 (g cell00)

private def coalesceEqualMassAt11 {γ : Type*} (g : Cell → γ) : Cell → γ :=
  replaceCellLabel g cell00 (g cell11)

private lemma pushforward_replaceCellLabel
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (g : Cell → γ) (p : RealTable) (cell : Cell) (label target : γ) :
    pushforward (replaceCellLabel g cell label) p target =
      pushforward g p target - (if g cell = target then p cell else 0) +
        (if label = target then p cell else 0) := by
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, Finset.sum_filter]
  let f : Cell → Real := fun z => if g z = target then p z else 0
  let f' : Cell → Real := fun z =>
    if replaceCellLabel g cell label z = target then p z else 0
  have hf := Finset.sum_erase_add (s := (Finset.univ : Finset Cell))
    (f := f) (Finset.mem_univ cell)
  have hf' := Finset.sum_erase_add (s := (Finset.univ : Finset Cell))
    (f := f') (Finset.mem_univ cell)
  have hrest :
      (∑ z ∈ (Finset.univ : Finset Cell).erase cell, f' z) =
        ∑ z ∈ (Finset.univ : Finset Cell).erase cell, f z := by
    apply Finset.sum_congr rfl
    intro z hz
    have hzc : z ≠ cell := (Finset.mem_erase.mp hz).1
    simp [f, f', replaceCellLabel, hzc]
  change (∑ z, f' z) = (∑ z, f z) -
    (if g cell = target then p cell else 0) +
      (if label = target then p cell else 0)
  rw [← hf', hrest, ← hf]
  simp [f, f', replaceCellLabel]

private lemma cell_mass_le_pushforward
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : RealTable} (hp : ∀ z, 0 ≤ p z) (g : Cell → γ) (cell : Cell) :
    p cell ≤ pushforward g p (g cell) := by
  unfold pushforward stoch_to_det.push
  apply Finset.single_le_sum
  · intro z _
    exact hp z
  · simp

private lemma sum_univ_eq_two_terms_add_erase
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (F : γ → Real) {g0 g1 : γ} (hne : g0 ≠ g1) :
    (∑ label, F label) = F g0 + F g1 +
      ∑ label ∈ ((Finset.univ.erase g0).erase g1), F label := by
  have h0 := Finset.sum_erase_add (s := (Finset.univ : Finset γ))
    (f := F) (Finset.mem_univ g0)
  have hg1 : g1 ∈ (Finset.univ : Finset γ).erase g0 :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ g1⟩
  have h1 := Finset.sum_erase_add (s := (Finset.univ.erase g0)) (f := F) hg1
  rw [← h0, ← h1]
  ring

private lemma finiteCodeReward_le_max_equalMassCoalescings
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : TransposeChart) (g : Cell → γ) :
    finiteCodeReward D.latent g ≤
      max (finiteCodeReward D.latent (coalesceEqualMassAt00 g))
        (finiteCodeReward D.latent (coalesceEqualMassAt11 g)) := by
  classical
  let g0 := g cell00
  let g1 := g cell11
  by_cases hsame : g0 = g1
  · have h00 : coalesceEqualMassAt00 g = g := by
      funext z
      by_cases hz : z = cell11
      · subst z
        simp [coalesceEqualMassAt00, replaceCellLabel, g0, g1, hsame]
      · simp [coalesceEqualMassAt00, replaceCellLabel, hz]
    have h11 : coalesceEqualMassAt11 g = g := by
      funext z
      by_cases hz : z = cell00
      · subst z
        simp [coalesceEqualMassAt11, replaceCellLabel, g0, g1, hsame]
      · simp [coalesceEqualMassAt11, replaceCellLabel, hz]
    simp [h00, h11]
  · let x0 := pushforward g D.firstComponent g0 - D.a
    let y0 := pushforward g D.secondComponent g0 - D.a
    let x1 := pushforward g D.firstComponent g1 - D.d
    let y1 := pushforward g D.secondComponent g1 - D.d
    let n := D.a + D.d
    have h10 : g1 ≠ g0 := Ne.symm hsame
    have h0011 : g cell00 ≠ g cell11 := by simpa [g0, g1] using hsame
    have h1100 : g cell11 ≠ g cell00 := Ne.symm h0011
    have hg0 : g cell00 = g0 := by rfl
    have hg1 : g cell11 = g1 := by rfl
    have hg1_ne_g0 : g cell11 ≠ g0 := by simpa [g1] using h10
    have hg0_ne_g1 : g cell00 ≠ g1 := by simpa [g0] using h0011
    have hx0 : 0 ≤ x0 := by
      dsimp [x0, g0]
      have h := cell_mass_le_pushforward D.firstComponent_isPMF.nonneg g cell00
      simpa [TransposeChart.firstComponent, tableOfEntries, cell00] using
        sub_nonneg.mpr h
    have hy0 : 0 ≤ y0 := by
      dsimp [y0, g0]
      have h := cell_mass_le_pushforward D.secondComponent_isPMF.nonneg g cell00
      simpa [TransposeChart.secondComponent, transposeTableOfEntries,
        tableOfEntries, cell00] using sub_nonneg.mpr h
    have hx1 : 0 ≤ x1 := by
      dsimp [x1, g1]
      have h := cell_mass_le_pushforward D.firstComponent_isPMF.nonneg g cell11
      simpa [TransposeChart.firstComponent, tableOfEntries, cell11] using
        sub_nonneg.mpr h
    have hy1 : 0 ≤ y1 := by
      dsimp [y1, g1]
      have h := cell_mass_le_pushforward D.secondComponent_isPMF.nonneg g cell11
      simpa [TransposeChart.secondComponent, transposeTableOfEntries,
        tableOfEntries, cell11] using sub_nonneg.mpr h
    have hn : 0 < n := by dsimp [n]; linarith [D.a_pos, D.d_pos]
    have hta : D.a ∈ Icc (0 : Real) n := by
      dsimp [n]
      constructor <;> linarith [D.a_pos, D.d_pos]
    have halloc := scalarBlockReward_split_le_max_endpoints
      D.pi_pos.le D.pi_lt_one.le hx0 hy0 hx1 hy1 hn hta
    let F : (Cell → γ) → γ → Real := fun code label =>
      scalarBlockReward D.pi
        (pushforward code D.firstComponent label)
        (pushforward code D.secondComponent label)
    have hg0value : F g g0 =
        scalarBlockReward D.pi (x0 + D.a) (y0 + D.a) := by
      dsimp [F, x0, y0]
      congr 1 <;> ring
    have hg1value : F g g1 =
        scalarBlockReward D.pi (x1 + D.d) (y1 + D.d) := by
      dsimp [F, x1, y1]
      congr 2 <;> ring
    have h00g0 : F (coalesceEqualMassAt00 g) g0 =
        scalarBlockReward D.pi (x0 + n) (y0 + n) := by
      dsimp [F, coalesceEqualMassAt00]
      rw [pushforward_replaceCellLabel, pushforward_replaceCellLabel]
      simp only [if_neg hg1_ne_g0, if_pos hg0, sub_zero]
      simp [TransposeChart.firstComponent, TransposeChart.secondComponent,
        transposeTableOfEntries, tableOfEntries, cell11, x0, y0, n]
      congr 1 <;> ring
    have h00g1 : F (coalesceEqualMassAt00 g) g1 =
        scalarBlockReward D.pi x1 y1 := by
      dsimp [F, coalesceEqualMassAt00]
      rw [pushforward_replaceCellLabel, pushforward_replaceCellLabel]
      simp only [if_pos hg1, if_neg hg0_ne_g1, add_zero]
      simp [TransposeChart.firstComponent, TransposeChart.secondComponent,
        transposeTableOfEntries, tableOfEntries, cell11, x1, y1]
    have h11g0 : F (coalesceEqualMassAt11 g) g0 =
        scalarBlockReward D.pi x0 y0 := by
      dsimp [F, coalesceEqualMassAt11]
      rw [pushforward_replaceCellLabel, pushforward_replaceCellLabel]
      simp only [if_pos hg0, if_neg hg1_ne_g0, add_zero]
      simp [TransposeChart.firstComponent, TransposeChart.secondComponent,
        transposeTableOfEntries, tableOfEntries, cell00, x0, y0]
    have h11g1 : F (coalesceEqualMassAt11 g) g1 =
        scalarBlockReward D.pi (x1 + n) (y1 + n) := by
      dsimp [F, coalesceEqualMassAt11]
      rw [pushforward_replaceCellLabel, pushforward_replaceCellLabel]
      simp only [if_neg hg0_ne_g1, if_pos hg1, sub_zero]
      simp [TransposeChart.firstComponent, TransposeChart.secondComponent,
        transposeTableOfEntries, tableOfEntries, cell00, x1, y1, n]
    have hrest00 : ∀ label ∈ ((Finset.univ.erase g0).erase g1),
        F (coalesceEqualMassAt00 g) label = F g label := by
      intro label hlabel
      have hlabel1 : label ≠ g1 := (Finset.mem_erase.mp hlabel).1
      have hlabel0 : label ≠ g0 :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hlabel).2).1
      have hc11 : g cell11 ≠ label := by simpa [g1] using Ne.symm hlabel1
      have hc00 : g cell00 ≠ label := by simpa [g0] using Ne.symm hlabel0
      dsimp [F, coalesceEqualMassAt00]
      rw [pushforward_replaceCellLabel, pushforward_replaceCellLabel]
      simp [hc00, hc11]
    have hrest11 : ∀ label ∈ ((Finset.univ.erase g0).erase g1),
        F (coalesceEqualMassAt11 g) label = F g label := by
      intro label hlabel
      have hlabel1 : label ≠ g1 := (Finset.mem_erase.mp hlabel).1
      have hlabel0 : label ≠ g0 :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hlabel).2).1
      have hc11 : g cell11 ≠ label := by simpa [g1] using Ne.symm hlabel1
      have hc00 : g cell00 ≠ label := by simpa [g0] using Ne.symm hlabel0
      dsimp [F, coalesceEqualMassAt11]
      rw [pushforward_replaceCellLabel, pushforward_replaceCellLabel]
      simp [hc00, hc11]
    have hsumg := sum_univ_eq_two_terms_add_erase (F g) hsame
    have hsum00 :=
      sum_univ_eq_two_terms_add_erase (F (coalesceEqualMassAt00 g)) hsame
    have hsum11 :=
      sum_univ_eq_two_terms_add_erase (F (coalesceEqualMassAt11 g)) hsame
    rw [Finset.sum_congr rfl hrest00] at hsum00
    rw [Finset.sum_congr rfl hrest11] at hsum11
    rw [hg0value, hg1value] at hsumg
    rw [h00g0, h00g1] at hsum00
    rw [h11g0, h11g1] at hsum11
    have hscaled : Real.log 2 * finiteCodeReward D.latent g ≤
        max
          (Real.log 2 * finiteCodeReward D.latent (coalesceEqualMassAt00 g))
          (Real.log 2 * finiteCodeReward D.latent (coalesceEqualMassAt11 g)) := by
      rw [log_two_mul_finiteCodeReward_eq_sum_scalarBlockRewards,
        log_two_mul_finiteCodeReward_eq_sum_scalarBlockRewards,
        log_two_mul_finiteCodeReward_eq_sum_scalarBlockRewards]
      change (∑ label, F g label) ≤
        max (∑ label, F (coalesceEqualMassAt00 g) label)
          (∑ label, F (coalesceEqualMassAt11 g) label)
      rw [hsumg, hsum00, hsum11]
      have halloc' :
          scalarBlockReward D.pi (x0 + D.a) (y0 + D.a) +
              scalarBlockReward D.pi (x1 + D.d) (y1 + D.d) ≤
            max
              (scalarBlockReward D.pi (x0 + n) (y0 + n) +
                scalarBlockReward D.pi x1 y1)
              (scalarBlockReward D.pi x0 y0 +
                scalarBlockReward D.pi (x1 + n) (y1 + n)) := by
        have hnda : n - D.a = D.d := by dsimp [n]; ring
        have hallocD := halloc
        rw [hnda] at hallocD
        simpa only [max_comm] using hallocD
      let R := ∑ label ∈ ((Finset.univ.erase g0).erase g1), F g label
      change
        (scalarBlockReward D.pi (x0 + D.a) (y0 + D.a) +
            scalarBlockReward D.pi (x1 + D.d) (y1 + D.d)) + R ≤
          max
            ((scalarBlockReward D.pi (x0 + n) (y0 + n) +
              scalarBlockReward D.pi x1 y1) + R)
            ((scalarBlockReward D.pi x0 y0 +
              scalarBlockReward D.pi (x1 + n) (y1 + n)) + R)
      calc
        _ ≤ max
              (scalarBlockReward D.pi (x0 + n) (y0 + n) +
                scalarBlockReward D.pi x1 y1)
              (scalarBlockReward D.pi x0 y0 +
                scalarBlockReward D.pi (x1 + n) (y1 + n)) + R := by
          simpa only [add_comm] using add_le_add_right halloc' R
        _ = _ := (max_add_add_right _ _ _).symm
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [← mul_max_of_nonneg _ _ hlog.le] at hscaled
    exact le_of_mul_le_mul_left hscaled hlog

/-! ## Three-label reduction -/

private lemma pushforward_eq_four_cells
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (g : Cell → γ) (p : RealTable) (label : γ) :
    pushforward g p label =
      (if g cell00 = label then p cell00 else 0) +
      (if g cell01 = label then p cell01 else 0) +
      (if g cell10 = label then p cell10 else 0) +
      (if g cell11 = label then p cell11 else 0) := by
  unfold pushforward stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, cell00, cell01, cell10, cell11]
  abel

private lemma sum_scalarBlockRewards_eq_sum_on_label_range
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : TransposeChart) (g : Cell → γ) (S : Finset γ)
    (hrange : ∀ z, g z ∈ S) :
    (∑ label, scalarBlockReward D.pi
      (pushforward g D.firstComponent label)
      (pushforward g D.secondComponent label)) =
      ∑ label ∈ S, scalarBlockReward D.pi
        (pushforward g D.firstComponent label)
        (pushforward g D.secondComponent label) := by
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro label _ hlabel
  have hne : ∀ z, g z ≠ label := by
    intro z hzg
    apply hlabel
    rw [← hzg]
    exact hrange z
  have hfirst : pushforward g D.firstComponent label = 0 := by
    unfold pushforward stoch_to_det.push
    rw [Finset.sum_filter]
    simp [hne]
  have hsecond : pushforward g D.secondComponent label = 0 := by
    unfold pushforward stoch_to_det.push
    rw [Finset.sum_filter]
    simp [hne]
  simp [hfirst, hsecond, scalarBlockReward]

private lemma scalarBlockReward_equal_nonpos
    {pi x : Real} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    scalarBlockReward pi x x ≤ 0 := by
  have hmix : (1 - pi) * x + pi * x = x := by ring
  rw [scalarBlockReward, hmix]
  have hneg := Real.negMulLog_nonneg hx0 hx1
  nlinarith

private lemma finiteCodeReward_of_equalMassCells_le_max
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : TransposeChart) (g : Cell → γ)
    (hequal : g cell00 = g cell11) :
    finiteCodeReward D.latent g ≤
      max 0 (codeReward D.latent (singletonCode cell10)) := by
  classical
  let gn := g cell00
  let gl := g cell01
  let gh := g cell10
  let n := D.a + D.d
  let F : γ → Real := fun label =>
    scalarBlockReward D.pi
      (pushforward g D.firstComponent label)
      (pushforward g D.secondComponent label)
  have hn : 0 < n := by dsimp [n]; linarith [D.a_pos, D.d_pos]
  have htotaln : n + D.b + D.c = 1 := by
    dsimp [n]
    linarith [D.total]
  have htotaln' : n + D.c + D.b = 1 := by linarith [htotaln]
  have hcompb : 1 - D.b = D.c + n := by linarith
  have hcompc : 1 - D.c = D.b + n := by linarith
  have hequal' : g (0, 0) = g (1, 1) := by
    simpa [cell00, cell11] using hequal
  have hrange : ∀ z, g z ∈ ({gn, gl, gh} : Finset γ) := by
    intro z
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [gn, gl, gh, cell01, cell10, cell11, hequal, hequal']
  have hF : ∀ label, F label = scalarBlockReward D.pi
      ((if gn = label then n else 0) +
        (if gl = label then D.b else 0) +
        (if gh = label then D.c else 0))
      ((if gn = label then n else 0) +
        (if gl = label then D.c else 0) +
        (if gh = label then D.b else 0)) := by
    intro label
    dsimp [F]
    rw [pushforward_eq_four_cells, pushforward_eq_four_cells]
    simp only [TransposeChart.firstComponent, TransposeChart.secondComponent,
      transposeTableOfEntries, tableOfEntries, cell00, cell01, cell10, cell11]
    have h11 : g (1, 1) = gn := by
      simpa [gn, cell00, cell11] using hequal.symm
    simp only [show g (0, 0) = gn by rfl,
      show g (0, 1) = gl by rfl, show g (1, 0) = gh by rfl, h11]
    by_cases hng : gn = label
    · simp [hng]
      congr 1 <;> dsimp [n] <;> ring
    · simp [hng]
  have hsum : Real.log 2 * finiteCodeReward D.latent g =
      ∑ label ∈ ({gn, gl, gh} : Finset γ), F label := by
    rw [log_two_mul_finiteCodeReward_eq_sum_scalarBlockRewards]
    change (∑ label, F label) = _
    exact sum_scalarBlockRewards_eq_sum_on_label_range D g _ hrange
  have hhigh : Real.log 2 * codeReward D.latent (singletonCode cell10) =
      scalarBlockReward D.pi D.c D.b +
        scalarBlockReward D.pi (D.b + n) (D.c + n) := by
    rw [log_two_mul_codeReward_singleton D cell10]
    simp only [TransposeChart.firstComponent, TransposeChart.secondComponent,
      transposeTableOfEntries, tableOfEntries, cell10]
    rw [scalarSingletonReward_eq_add_scalarBlockRewards, hcompc, hcompb]
  have hlowHigh :
      scalarBlockReward D.pi D.b D.c +
          scalarBlockReward D.pi (D.c + n) (D.b + n) ≤
        scalarBlockReward D.pi D.c D.b +
          scalarBlockReward D.pi (D.b + n) (D.c + n) := by
    have hsumBC : D.b + D.c < 1 := by
      nlinarith [D.a_pos, D.d_pos, D.total]
    have h := scalarSingletonReward_low_le_high
      D.c_pos D.order hsumBC D.pi_pos.le D.pi_le_half
    rw [scalarSingletonReward_eq_add_scalarBlockRewards,
      scalarSingletonReward_eq_add_scalarBlockRewards, hcompb, hcompc] at h
    exact h
  have hmerge :
      scalarBlockReward D.pi D.b D.c + scalarBlockReward D.pi n n ≤
        scalarBlockReward D.pi (D.b + n) (D.c + n) :=
    scalarBlockReward_add_equalMass_le_merge D.c_pos D.order hn
      D.pi_pos.le D.pi_le_half
  have hnle : n ≤ 1 := by linarith [D.b_pos, D.c_pos, htotaln]
  have hbc0 : 0 ≤ D.b + D.c := by linarith [D.b_pos, D.c_pos]
  have hbcle : D.b + D.c ≤ 1 := by
    linarith [D.a_pos, D.d_pos, D.total]
  have hmain : Real.log 2 * finiteCodeReward D.latent g ≤
      max 0 (Real.log 2 * codeReward D.latent (singletonCode cell10)) := by
    rw [hsum, hhigh]
    by_cases hln : gl = gn
    · by_cases hhn : gh = gn
      · have hcase : (∑ label ∈ ({gn, gl, gh} : Finset γ), F label) = 0 := by
          simp [hln, hhn, hF, htotaln, htotaln', scalarBlockReward]
        rw [hcase]
        exact le_max_left _ _
      · have hcase : (∑ label ∈ ({gn, gl, gh} : Finset γ), F label) =
            scalarBlockReward D.pi D.c D.b +
              scalarBlockReward D.pi (D.b + n) (D.c + n) := by
          simp [hln, hhn, Ne.symm hhn, hF, add_comm, add_left_comm]
        rw [hcase]
        exact le_max_right _ _
    · by_cases hhn : gh = gn
      · have hcase : (∑ label ∈ ({gn, gl, gh} : Finset γ), F label) =
            scalarBlockReward D.pi D.b D.c +
              scalarBlockReward D.pi (D.c + n) (D.b + n) := by
          simp [hln, hhn, Ne.symm hln, hF, add_comm]
        rw [hcase]
        exact hlowHigh.trans (le_max_right _ _)
      · by_cases hhl : gh = gl
        · have hcase : (∑ label ∈ ({gn, gl, gh} : Finset γ), F label) =
              scalarBlockReward D.pi n n +
                scalarBlockReward D.pi (D.b + D.c) (D.b + D.c) := by
            simp [hln, hhl, Ne.symm hln, hF,
              add_comm, add_left_comm]
          rw [hcase]
          have hnneg := scalarBlockReward_equal_nonpos
            (pi := D.pi) (x := n) hn.le hnle
          have hbcneg := scalarBlockReward_equal_nonpos
            (pi := D.pi) (x := D.b + D.c) hbc0 hbcle
          exact (add_nonpos hnneg hbcneg).trans (le_max_left _ _)
        · have hcase : (∑ label ∈ ({gn, gl, gh} : Finset γ), F label) =
              scalarBlockReward D.pi n n + scalarBlockReward D.pi D.b D.c +
                scalarBlockReward D.pi D.c D.b := by
            simp [hln, hhn, hhl, Ne.symm hln, Ne.symm hhn,
              Ne.symm hhl, hF]
            ring
          rw [hcase]
          have hthree :
              scalarBlockReward D.pi n n + scalarBlockReward D.pi D.b D.c +
                  scalarBlockReward D.pi D.c D.b ≤
                scalarBlockReward D.pi D.c D.b +
                  scalarBlockReward D.pi (D.b + n) (D.c + n) := by
            linarith [hmerge]
          exact hthree.trans (le_max_right _ _)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  apply (mul_le_mul_iff_right₀ hlog).mp
  rw [mul_max_of_nonneg _ _ hlog.le, mul_zero]
  exact hmain

private lemma finiteCodeReward_le_max_chartCodeRewards
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (D : TransposeChart) (g : Cell → γ) :
    finiteCodeReward D.latent g ≤
      max 0 (codeReward D.latent (singletonCode cell10)) := by
  have hcoalesce := finiteCodeReward_le_max_equalMassCoalescings D g
  have h00equal :
      coalesceEqualMassAt00 g cell00 = coalesceEqualMassAt00 g cell11 := by
    simp [coalesceEqualMassAt00, replaceCellLabel]
  have h11equal :
      coalesceEqualMassAt11 g cell00 = coalesceEqualMassAt11 g cell11 := by
    simp [coalesceEqualMassAt11, replaceCellLabel]
  have h00 := finiteCodeReward_of_equalMassCells_le_max D
    (coalesceEqualMassAt00 g) h00equal
  have h11 := finiteCodeReward_of_equalMassCells_le_max D
    (coalesceEqualMassAt11 g) h11equal
  exact hcoalesce.trans (max_le h00 h11)

namespace TransposeChart

/-- The reward of any binary code is at most the larger reward of the two
chart codes. -/
theorem codeReward_le_max_chartCodeRewards
    (D : TransposeChart) (g : BinaryCode) :
    codeReward D.latent g ≤
      max (codeReward D.latent constantCode)
        (codeReward D.latent (singletonCode cell10)) := by
  have h := finiteCodeReward_le_max_chartCodeRewards D g
  change codeReward D.latent g ≤
    max 0 (codeReward D.latent (singletonCode cell10)) at h
  simpa [codeReward_constantCode] using h

/-- The chart phase selector has no greater cost than any supplied binary
code. -/
theorem w3Cost_phaseSelector_le_w3Cost
    (D : TransposeChart) (g : BinaryCode) :
    w3Cost D.latent (phaseSelector D) ≤ w3Cost D.latent g := by
  have hreward := D.codeReward_le_max_chartCodeRewards g
  have hconstantReward := codeReward_constantCode D.latent
  rw [hconstantReward] at hreward
  have hphase : codeReward D.latent g ≤
      codeReward D.latent (phaseSelector D) := by
    by_cases h : 0 ≤ codeReward D.latent (singletonCode cell10)
    · rw [phaseSelector_eq_singletonCode_of_codeReward_nonneg D h]
      simpa [max_eq_right h] using hreward
    · have hneg : codeReward D.latent (singletonCode cell10) < 0 :=
        lt_of_not_ge h
      rw [phaseSelector_eq_constantCode_of_codeReward_neg D hneg,
        codeReward_constantCode]
      simpa [max_eq_left (le_of_lt hneg)] using hreward
  rw [w3Cost_eq_observableInfo_sub_codeReward,
    w3Cost_eq_observableInfo_sub_codeReward]
  linarith

/-- On a transpose chart, the better of the constant and distinguished
singleton chart codes costs no more than any binary code. -/
theorem min_chartCodes_le_w3Cost
    (D : Binary.TransposeChart) (g : Binary.BinaryCode) :
    min
        (w3Cost D.latent Binary.constantCode)
        (w3Cost D.latent (Binary.singletonCode Binary.cell10))
      ≤ w3Cost D.latent g := by
  have hselector := D.w3Cost_phaseSelector_le_w3Cost g
  calc
    min
        (w3Cost D.latent Binary.constantCode)
        (w3Cost D.latent (Binary.singletonCode Binary.cell10)) =
        observableInfo D.latent -
          max 0 (codeReward D.latent (singletonCode cell10)) := by
      rw [w3Cost_constantCode, w3Cost_eq_observableInfo_sub_codeReward]
      by_cases h : 0 ≤ codeReward D.latent (singletonCode cell10)
      · rw [max_eq_right h, min_eq_right]
        linarith
      · have hnonpos : codeReward D.latent (singletonCode cell10) ≤ 0 :=
          le_of_not_ge h
        rw [max_eq_left hnonpos, min_eq_left (by linarith)]
        ring
    _ = w3Cost D.latent (phaseSelector D) :=
      (w3Cost_phaseSelector_eq_observableInfo_sub_max D).symm
    _ ≤ w3Cost D.latent g := hselector

end TransposeChart

end

end StochasticToDeterministicLatents.Binary
