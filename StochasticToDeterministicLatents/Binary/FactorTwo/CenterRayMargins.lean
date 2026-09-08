/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  The private working
material's radial-derivative module is taken in full; four of its nine public
declarations are consumed nowhere and are private here.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRayMass
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterDictionary
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterDerivatives
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterCurvature

/-!
# The margins along the ray

The page differentiates along a ray of fixed imbalance with the **off-diagonal
mass** as the parameter, writing `D = v d/dv`.  Lean differentiates in the
radius, so every statement here carries the factor `rayMassDeriv`, which is
`dv/dr`; dividing it out is the change of variable, and `CenterRayMass` shows
that it never vanishes strictly inside the ray.

Each margin is differentiated twice.  The first derivative exhibits a slope,
which is `d/dv` of the margin; differentiating the slope again exhibits the
chart's second-order expressions as `v^2 d^2/dv^2` of the margin, which is what
the page's display (4.3) asserts.  No sign, monotonicity or bound is claimed
here: the inequalities of (4.3) belong to the modules above this one.
-/

namespace StochasticToDeterministicLatents.Binary

variable {z r : ℝ}

/-! ## The three slopes -/

/-- The contact height's slope in the off-diagonal mass, `dk/dv`. -/
noncomputable def rayHeightSlope (z r : ℝ) : ℝ :=
  Real.log (certDiagonal (1 - rayMass z r) (rayRoot z r))
    + (1 + z) / 2
      * Real.log (certOffDiagonal ((1 + z) / 2 * rayMass z r)
          ((1 - z) / 2 * rayMass z r) (rayRoot z r))
    + (1 - z) / 2
      * Real.log (certOffDiagonal ((1 - z) / 2 * rayMass z r)
          ((1 + z) / 2 * rayMass z r) (rayRoot z r))

/-- The constant code's margin slope in the off-diagonal mass.  The first two
groups are the entropy and marginal slopes; the last is `rayHeightSlope`. -/
noncomputable def rayConstantSlope (z r : ℝ) : ℝ :=
  5 * (Real.log ((1 - rayMass z r) / 2)
        - (1 + z) / 2 * Real.log ((1 + z) / 2 * rayMass z r)
        - (1 - z) / 2 * Real.log ((1 - z) / 2 * rayMass z r))
    - 6 * (-z / 2 * Real.log ((1 + z * rayMass z r) / (1 - z * rayMass z r)))
    + 2 * rayHeightSlope z r

/-- The isolating code's margin slope in the off-diagonal mass. -/
noncomputable def raySingletonSlope (z r : ℝ) : ℝ :=
  3 * (Real.log ((1 - rayMass z r) / 2)
        - (1 + z) / 2 * Real.log ((1 + z) / 2 * rayMass z r)
        - (1 - z) / 2 * Real.log ((1 - z) / 2 * rayMass z r))
    - 4 * (-z / 2 * Real.log ((1 + z * rayMass z r) / (1 - z * rayMass z r)))
    - 1 / 2 * Real.log ((1 + rayMass z r) / (1 - rayMass z r))
    + 2 * rayHeightSlope z r

/-- The ray's two cells, in the mass and in the root. -/
private theorem rayCells (z r : ℝ) :
    (1 + z) * r / 2 * rayRoot z r = (1 + z) / 2 * rayMass z r
      ∧ (1 - z) * r / 2 * rayRoot z r = (1 - z) / 2 * rayMass z r
      ∧ chartDiagonalMass r (rayProductCoeff z * r ^ 2) = 1 - rayMass z r := by
  refine ⟨?_, ?_, ?_⟩
  · unfold rayMass rayRoot chartOffDiagonalMass
    ring
  · unfold rayMass rayRoot chartOffDiagonalMass
    ring
  · unfold rayMass chartDiagonalMass
    ring

/-! ## The height along the ray -/

/-- **The contact height, differentiated along the ray.**  Its slope in the
off-diagonal mass is `rayHeightSlope`. -/
theorem hasDerivAt_rayHeight (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (fun t => chartHeight ((1 + z) * t / 2) ((1 - z) * t / 2))
      (rayMassDeriv z r * rayHeightSlope z r) r := by
  have hX : HasDerivAt (fun t : ℝ => (1 + z) * t / 2) ((1 + z) / 2) r := by
    simpa [mul_assoc] using ((hasDerivAt_id r).const_mul (1 + z)).div_const 2
  have hY : HasDerivAt (fun t : ℝ => (1 - z) * t / 2) ((1 - z) / 2) r := by
    simpa [mul_assoc] using ((hasDerivAt_id r).const_mul (1 - z)).div_const 2
  have hU : HasDerivAt (fun s : ℝ => chartRoot ((1 + z) * s / 2 + (1 - z) * s / 2)
      ((1 + z) * s / 2 * ((1 - z) * s / 2)))
      (rayProductCoeff z * r * (2 - r - rayProductCoeff z * r ^ 3)
        / chartNorm r (rayProductCoeff z * r ^ 2) ^ 2) r := by
    rw [rayRoot_eq_chartRoot]
    exact hasDerivAt_rayRoot hz hr
  have hx : 0 < (1 + z) * r / 2 := by nlinarith [hz.1, hr.1]
  have hy : 0 < (1 - z) * r / 2 := by nlinarith [hz.2, hr.1]
  have hr1 : (1 + z) * r / 2 + (1 - z) * r / 2 < 1 := by
    have := (criticalRadius_spec hz).2.1
    nlinarith [hr.2]
  have hk0 := hasDerivAt_chartHeight hX hY hU hx hy hr1
  rw [show (1 + z) * r / 2 + (1 - z) * r / 2 = r from by ring,
    show (1 + z) * r / 2 * ((1 - z) * r / 2) = rayProductCoeff z * r ^ 2 from by
      unfold rayProductCoeff; ring] at hk0
  obtain ⟨hb, hc, hs⟩ := rayCells z r
  rw [show chartRoot r (rayProductCoeff z * r ^ 2) = rayRoot z r from rfl,
    hs, hb, hc] at hk0
  refine hk0.congr_deriv ?_
  have hsum : rayMassDeriv z r = rayRoot z r
      + r * (rayProductCoeff z * r * (2 - r - rayProductCoeff z * r ^ 3)
        / chartNorm r (rayProductCoeff z * r ^ 2) ^ 2) := by
    unfold rayMassDeriv rayRoot chartRoot chartNorm
    field_simp
    ring
  unfold rayHeightSlope
  rw [hsum]
  ring

/-! ## The two entropies along the ray -/

/-- The centre law's entropy, differentiated in the off-diagonal mass. -/
private theorem hasDerivAt_centerLogEntropy (hz : z ∈ Set.Ico (0 : ℝ) 1) {v : ℝ}
    (hv : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun t => centerLogEntropy t z)
      (Real.log ((1 - v) / 2) - (1 + z) / 2 * Real.log ((1 + z) / 2 * v)
        - (1 - z) / 2 * Real.log ((1 - z) / 2 * v)) v := by
  have hq : (1 - v) / 2 ≠ 0 := (div_pos (sub_pos.mpr hv1) (by norm_num)).ne'
  have hp : (1 + z) / 2 * v ≠ 0 :=
    (mul_pos (div_pos (by linarith [hz.1]) (by norm_num)) hv).ne'
  have hm : (1 - z) / 2 * v ≠ 0 :=
    (mul_pos (div_pos (sub_pos.mpr hz.2) (by norm_num)) hv).ne'
  have hq' : HasDerivAt (fun t : ℝ => (1 - t) / 2) (-1 / 2) v := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).div_const 2
  have hp' : HasDerivAt (fun t : ℝ => (1 + z) / 2 * t) ((1 + z) / 2) v := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id v).const_mul ((1 + z) / 2)
  have hm' : HasDerivAt (fun t : ℝ => (1 - z) / 2 * t) ((1 - z) / 2) v := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id v).const_mul ((1 - z) / 2)
  have h1 := (Real.hasDerivAt_mul_log hq).comp v hq'
  have h2 := (Real.hasDerivAt_mul_log hp).comp v hp'
  have h3 := (Real.hasDerivAt_mul_log hm).comp v hm'
  have hd : Real.log ((1 - v) / 2) - (1 + z) / 2 * Real.log ((1 + z) / 2 * v)
        - (1 - z) / 2 * Real.log ((1 - z) / 2 * v) =
      -2 * ((Real.log ((1 - v) / 2) + 1) * (-1 / 2))
        - (Real.log ((1 + z) / 2 * v) + 1) * ((1 + z) / 2)
        - (Real.log ((1 - z) / 2 * v) + 1) * ((1 - z) / 2) := by ring
  refine ((((h1.const_mul (-2)).sub h2).sub h3).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv hd.symm
  intro t
  simp only [Function.comp_apply, Pi.sub_apply]
  unfold centerLogEntropy xLogX
  rw [show ((1 + z) / 2 * t : ℝ) = t * (1 + z) / 2 from by ring,
    show ((1 - z) / 2 * t : ℝ) = t * (1 - z) / 2 from by ring]
  ring

/-- The centre law's marginal entropy, differentiated in the off-diagonal
mass. -/
private theorem hasDerivAt_centerMarginalEntropy {v : ℝ} (hvz : |z * v| < 1) :
    HasDerivAt (fun t => centerMarginalEntropy t z)
      (-z / 2 * Real.log ((1 + z * v) / (1 - z * v))) v := by
  have hp : (1 + v * z) / 2 ≠ 0 := by
    have := (abs_lt.mp hvz).1
    exact (div_pos (by nlinarith) (by norm_num)).ne'
  have hm : (1 - v * z) / 2 ≠ 0 := by
    have := (abs_lt.mp hvz).2
    exact (div_pos (by nlinarith) (by norm_num)).ne'
  have hp' : HasDerivAt (fun t : ℝ => (1 + t * z) / 2) (z / 2) v := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul] using
      ((hasDerivAt_const v (1 : ℝ)).add ((hasDerivAt_id v).mul_const z)).div_const 2
  have hm' : HasDerivAt (fun t : ℝ => (1 - t * z) / 2) (-z / 2) v := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, one_mul] using
      ((hasDerivAt_const v (1 : ℝ)).sub ((hasDerivAt_id v).mul_const z)).div_const 2
  have h1 := (Real.hasDerivAt_mul_log hp).comp v hp'
  have h2 := (Real.hasDerivAt_mul_log hm).comp v hm'
  have hlog : Real.log ((1 + z * v) / (1 - z * v)) =
      Real.log ((1 + v * z) / 2) - Real.log ((1 - v * z) / 2) := by
    rw [← Real.log_div hp hm]
    congr 1
    field_simp
  have hd : -z / 2 * Real.log ((1 + z * v) / (1 - z * v)) =
      -((Real.log ((1 + v * z) / 2) + 1) * (z / 2))
        - (Real.log ((1 - v * z) / 2) + 1) * (-z / 2) := by rw [hlog]; ring
  refine ((h1.neg.sub h2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv hd.symm
  intro t
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply]
  unfold centerMarginalEntropy xLogX
  ring

/-- The isolating code's extra diagonal pair, differentiated in the
off-diagonal mass. -/
private theorem hasDerivAt_centerDiagonalPair {v : ℝ} (hv : |v| < 1) :
    HasDerivAt (fun t => xLogX ((1 - t) / 2) + xLogX ((1 + t) / 2))
      (1 / 2 * Real.log ((1 + v) / (1 - v))) v := by
  have hm : (1 - v) / 2 ≠ 0 :=
    (div_pos (sub_pos.mpr (abs_lt.mp hv).2) (by norm_num)).ne'
  have hp : (1 + v) / 2 ≠ 0 :=
    (div_pos (by linarith [(abs_lt.mp hv).1]) (by norm_num)).ne'
  have hm' : HasDerivAt (fun t : ℝ => (1 - t) / 2) (-1 / 2) v := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).div_const 2
  have hp' : HasDerivAt (fun t : ℝ => (1 + t) / 2) (1 / 2) v := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      ((hasDerivAt_const v (1 : ℝ)).add (hasDerivAt_id v)).div_const 2
  have h1 := (Real.hasDerivAt_mul_log hm).comp v hm'
  have h2 := (Real.hasDerivAt_mul_log hp).comp v hp'
  have hlog : Real.log ((1 + v) / (1 - v)) =
      Real.log ((1 + v) / 2) - Real.log ((1 - v) / 2) := by
    rw [← Real.log_div hp hm]
    congr 1
    field_simp
  have hd : 1 / 2 * Real.log ((1 + v) / (1 - v)) =
      (Real.log ((1 - v) / 2) + 1) * (-1 / 2)
        + (Real.log ((1 + v) / 2) + 1) * (1 / 2) := by rw [hlog]; ring
  refine ((h1.add h2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv hd.symm
  intro t
  simp only [Function.comp_apply, Pi.add_apply]
  unfold xLogX
  ring

/-! ## The two margins along the ray -/

/-- **The constant code's ray margin, differentiated.**  Its slope in the
off-diagonal mass is `rayConstantSlope`. -/
theorem hasDerivAt_rayConstantScalar (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (rayConstantScalar z)
      (rayMassDeriv z r * rayConstantSlope z r) r := by
  have hdom := chartDomain_ray hz hr
  have hv : 0 < rayMass z r := (chart_pos hdom).2.2.2.1
  have hv1 : rayMass z r < 1 := by
    have h := chartOffDiagonalMass_lt_third hdom
    unfold rayMass
    linarith
  have hzv : |z * rayMass z r| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hz.1, hz.2]
  have hV := hasDerivAt_rayMass hz hr
  have hJ := (hasDerivAt_centerLogEntropy hz hv hv1).comp r hV
  have hR := (hasDerivAt_centerMarginalEntropy hzv).comp r hV
  have hk := hasDerivAt_rayHeight hz hr
  have hh := ((hJ.const_mul 5).sub (hR.const_mul 6)).add (hk.const_mul 2)
  unfold rayConstantScalar centerConstantScalar
  refine (hh.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro t
    simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply]
    ring
  · unfold rayConstantSlope
    ring

/-- **The isolating code's ray margin, differentiated.**  Its slope in the
off-diagonal mass is `raySingletonSlope`. -/
theorem hasDerivAt_raySingletonScalar (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (raySingletonScalar z)
      (rayMassDeriv z r * raySingletonSlope z r) r := by
  have hdom := chartDomain_ray hz hr
  have hv : 0 < rayMass z r := (chart_pos hdom).2.2.2.1
  have hv1 : rayMass z r < 1 := by
    have h := chartOffDiagonalMass_lt_third hdom
    unfold rayMass
    linarith
  have hzv : |z * rayMass z r| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hz.1, hz.2]
  have habsv : |rayMass z r| < 1 := by rw [abs_of_pos hv]; exact hv1
  have hV := hasDerivAt_rayMass hz hr
  have hJ := (hasDerivAt_centerLogEntropy hz hv hv1).comp r hV
  have hR := (hasDerivAt_centerMarginalEntropy hzv).comp r hV
  have hk := hasDerivAt_rayHeight hz hr
  have hp := (hasDerivAt_centerDiagonalPair habsv).comp r hV
  have hh := (((hJ.const_mul 3).sub (hR.const_mul 4)).add
    (hk.const_mul 2)).sub hp
  unfold raySingletonScalar centerSingletonScalar
  refine (hh.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro t
    simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply]
    ring
  · unfold raySingletonSlope
    ring

/-! ## The height slope, differentiated

The page's `L_k` is `v^2 d^2 k / dv^2`, display (3.7).  What is proved below is
its form in the radius: the height slope's radial derivative is the mass's
derivative times `chartContactSecondOrder` over the mass squared.

The four algebraic stages carry no chart names.  They are the quotient rule's
output rearranged into the chart's expressions, and they are stated over bare
reals so that the rearrangement is checked once, away from the definitions. -/

/-- The ray root's derivative, as `CenterRayMass` computes it. -/
private noncomputable def rayRootDeriv (z r : ℝ) : ℝ :=
  rayProductCoeff z * r * (2 - r - rayProductCoeff z * r ^ 3)
    / chartNorm r (rayProductCoeff z * r ^ 2) ^ 2

/-- The chart at a point of the ray. -/
private theorem rayChart_at (z t : ℝ) :
    chartRoot ((1 + z) * t / 2 + (1 - z) * t / 2)
        ((1 + z) * t / 2 * ((1 - z) * t / 2)) = rayRoot z t
      ∧ chartDiagonalMass ((1 + z) * t / 2 + (1 - z) * t / 2)
          ((1 + z) * t / 2 * ((1 - z) * t / 2)) = 1 - rayMass z t := by
  rw [show (1 + z) * t / 2 + (1 - z) * t / 2 = t from by ring,
    show (1 + z) * t / 2 * ((1 - z) * t / 2) = rayProductCoeff z * t ^ 2 from by
      unfold rayProductCoeff; ring]
  exact ⟨rfl, rfl⟩

/-- **`chartRootDeriv` is the root's derivative in the off-diagonal mass**,
times that mass.  Along the ray both coordinates are differentiable in the
radius, and this identity divides the two derivatives: it is the sense in which
the chart's radial expression is a radial derivative, the page's `D u` with
`D = v d/dv`. -/
theorem chartRootDeriv_mul_rayMassDeriv (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    chartRootDeriv r (rayProductCoeff z * r ^ 2) * rayMassDeriv z r
      = rayMass z r * rayRootDeriv z r := by
  have hdom := chartDomain_ray hz hr
  obtain ⟨ha, hb, -, -, hf⟩ := chartFactors_pos hdom
  have hn : (1 - r) * (1 - rayProductCoeff z * r ^ 2) ≠ 0 := (mul_pos ha hb).ne'
  have hf' : (3 : ℝ) - 2 * r - rayProductCoeff z * r ^ 2 ≠ 0 := hf.ne'
  rw [chartRootDeriv_eq hdom]
  unfold rayMassDeriv rayMass rayRootDeriv chartOffDiagonalMass chartRoot chartNorm
  rw [div_mul_div_comm, ← mul_div_assoc r, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hn hf') (pow_ne_zero 2 hn))
      (mul_ne_zero hn (pow_ne_zero 2 hn))]
  ring

/-- The logarithm of an off-diagonal certificate value, along any
differentiable path. -/
private theorem hasDerivAt_log_certOffDiagonal {B C U : ℝ → ℝ} {db dc du t : ℝ}
    (hB : HasDerivAt B db t) (hC : HasDerivAt C dc t) (hU : HasDerivAt U du t)
    (hb : 0 < B t) (hq : 0 < U t ^ 2 + B t - B t * C t) :
    HasDerivAt (fun t => Real.log (certOffDiagonal (B t) (C t) (U t)))
      (3 * db / B t - 2 * (2 * U t * du + db - db * C t - B t * dc) /
        (U t ^ 2 + B t - B t * C t)) t := by
  show HasDerivAt
    (fun t => Real.log ((B t) ^ 3 / ((U t) ^ 2 + B t - B t * C t) ^ 2)) _ t
  have hpow := hB.pow 3
  have hden := ((hU.pow 2).add hB).sub (hB.mul hC)
  have hquot := hpow.div (hden.pow 2) (pow_ne_zero 2 hq.ne')
  have hl := hquot.log
    (div_ne_zero (pow_ne_zero 3 hb.ne') (pow_ne_zero 2 hq.ne'))
  simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
    Nat.cast_ofNat, Nat.reduceSubDiff] at hl
  exact hl.congr_deriv (by field_simp [hb.ne', hq.ne']; ring)

/-! ### The four algebraic stages -/

/-- The diagonal certificate's contribution. -/
private theorem contactSlope_stage_diag (r u du Du D1 D2 : ℝ)
    (hDu : Du * (u + r * du) = (r * u) * du)
    (hv : r * u ≠ 0) (hdv : u + r * du ≠ 0)
    (h1 : D1 ≠ 0) (h2 : D2 ≠ 0) :
    ((-(u + r * du) + 2 * du) / D1 - 2 * (-(u + r * du) + du) / D2) =
      (u + r * du) / (r * u) ^ 2 *
        ((r * u) * ((-(r * u) + 2 * Du) / D1 - 2 * (-(r * u) + Du) / D2)) := by
  rw [show Du = (r * u) * du / (u + r * du) from (eq_div_iff hdv).2 hDu]
  have hr : r ≠ 0 := fun h => hv (by rw [h]; simp)
  have hu : u ≠ 0 := fun h => hv (by rw [h]; simp)
  field_simp [hr, hu]

/-- The two cube terms' contribution. -/
private theorem contactSlope_stage_cubes (wb wc r u du : ℝ) (hab : wb + wc = 1)
    (hv : r * u ≠ 0) (hb : wc ≠ 0) :
    wb * (3 * (wb * u + wb * r * du) / (wb * (r * u))) +
        wc * (3 * (wc * u + wc * r * du) / (wc * (r * u))) =
      (u + r * du) / (r * u) ^ 2 * (3 * (r * u)) := by
  have hr : r ≠ 0 := fun h => hv (by rw [h]; simp)
  have hu : u ≠ 0 := fun h => hv (by rw [h]; simp)
  field_simp [hr, hu]
  have hc : wc = 1 - wb := by linarith
  subst hc
  ring

/-- The two quadratic denominators' contribution, cleared. -/
private theorem contactSlope_stage_quad_core (wb wc r u du Du D3 D4 : ℝ)
    (hab : wb + wc = 1)
    (hD3 : D3 = u ^ 2 + wb * (r * u) - wb * (r * u) * (wc * (r * u)))
    (hD4 : D4 = u ^ 2 + wc * (r * u) - wc * (r * u) * (wb * (r * u)))
    (hDu : Du * (u + r * du) = (r * u) * du) :
    (r * u) ^ 2 *
      (wb * (2 * u * du + (wb * u + wb * r * du)
          - (wb * u + wb * r * du) * (wc * (r * u))
          - (wb * (r * u)) * (wc * u + wc * r * du)) * D4 +
       wc * (2 * u * du + (wc * u + wc * r * du)
          - (wc * u + wc * r * du) * (wb * (r * u))
          - (wc * (r * u)) * (wb * u + wb * r * du)) * D3) =
    (u + r * du) *
      ((2 * u * Du - 2 * (wb * wc * (r * u) ^ 2)) *
          ((u ^ 2 - wb * wc * (r * u) ^ 2) * (r * u)
            + 2 * (wb * wc * (r * u) ^ 2)) +
       (u ^ 2 - wb * wc * (r * u) ^ 2) *
          ((r * u) ^ 2 - 2 * (wb * wc * (r * u) ^ 2)) +
       (wb * wc * (r * u) ^ 2) * (r * u)) := by
  rw [hD3, hD4]
  have hc : wc = 1 - wb := by linarith
  subst hc
  linear_combination
    (-(2 * u * ((u ^ 2 - wb * (1 - wb) * (r * u) ^ 2) * (r * u) +
      2 * (wb * (1 - wb) * (r * u) ^ 2)))) * hDu

/-- The two quadratic denominators' contribution. -/
private theorem contactSlope_stage_quad (wb wc r u du Du D3 D4 : ℝ)
    (hab : wb + wc = 1)
    (hD3 : D3 = u ^ 2 + wb * (r * u) - wb * (r * u) * (wc * (r * u)))
    (hD4 : D4 = u ^ 2 + wc * (r * u) - wc * (r * u) * (wb * (r * u)))
    (hDu : Du * (u + r * du) = (r * u) * du)
    (hv : r * u ≠ 0) (h3 : D3 ≠ 0) (h4 : D4 ≠ 0) :
    wb * (-2 * (2 * u * du + (wb * u + wb * r * du)
          - (wb * u + wb * r * du) * (wc * (r * u))
          - (wb * (r * u)) * (wc * u + wc * r * du)) / D3) +
      wc * (-2 * (2 * u * du + (wc * u + wc * r * du)
          - (wc * u + wc * r * du) * (wb * (r * u))
          - (wc * (r * u)) * (wb * u + wb * r * du)) / D4) =
    (u + r * du) / (r * u) ^ 2 *
      (-2 * (((2 * u * Du - 2 * (wb * wc * (r * u) ^ 2)) *
          ((u ^ 2 - wb * wc * (r * u) ^ 2) * (r * u)
            + 2 * (wb * wc * (r * u) ^ 2)) +
        (u ^ 2 - wb * wc * (r * u) ^ 2) *
          ((r * u) ^ 2 - 2 * (wb * wc * (r * u) ^ 2)) +
        (wb * wc * (r * u) ^ 2) * (r * u)) / (D3 * D4))) := by
  have key := contactSlope_stage_quad_core wb wc r u du Du D3 D4 hab hD3 hD4 hDu
  have e1 :
      wb * (-2 * (2 * u * du + (wb * u + wb * r * du)
          - (wb * u + wb * r * du) * (wc * (r * u))
          - (wb * (r * u)) * (wc * u + wc * r * du)) / D3) +
        wc * (-2 * (2 * u * du + (wc * u + wc * r * du)
          - (wc * u + wc * r * du) * (wb * (r * u))
          - (wc * (r * u)) * (wb * u + wb * r * du)) / D4) =
      (-2 * (wb * (2 * u * du + (wb * u + wb * r * du)
          - (wb * u + wb * r * du) * (wc * (r * u))
          - (wb * (r * u)) * (wc * u + wc * r * du)) * D4 +
        wc * (2 * u * du + (wc * u + wc * r * du)
          - (wc * u + wc * r * du) * (wb * (r * u))
          - (wc * (r * u)) * (wb * u + wb * r * du)) * D3)) /
        (D3 * D4) := by
    field_simp
    ring
  rw [e1]
  have e2 :
      (u + r * du) / (r * u) ^ 2 *
          (-2 * (((2 * u * Du - 2 * (wb * wc * (r * u) ^ 2)) *
              ((u ^ 2 - wb * wc * (r * u) ^ 2) * (r * u)
                + 2 * (wb * wc * (r * u) ^ 2)) +
            (u ^ 2 - wb * wc * (r * u) ^ 2) *
              ((r * u) ^ 2 - 2 * (wb * wc * (r * u) ^ 2)) +
            (wb * wc * (r * u) ^ 2) * (r * u)) / (D3 * D4))) =
        (-2 * ((u + r * du) *
          ((2 * u * Du - 2 * (wb * wc * (r * u) ^ 2)) *
              ((u ^ 2 - wb * wc * (r * u) ^ 2) * (r * u)
                + 2 * (wb * wc * (r * u) ^ 2)) +
            (u ^ 2 - wb * wc * (r * u) ^ 2) *
              ((r * u) ^ 2 - 2 * (wb * wc * (r * u) ^ 2)) +
            (wb * wc * (r * u) ^ 2) * (r * u)))) / ((r * u) ^ 2 * (D3 * D4)) := by
    field_simp [hv, h3, h4]
  rw [e2]
  rw [div_eq_div_iff (mul_ne_zero h3 h4)
    (mul_ne_zero (pow_ne_zero 2 hv) (mul_ne_zero h3 h4))]
  linear_combination (-2 * (D3 * D4)) * key

/-- The three stages assembled: the quotient rule's output is the chart's
second-order expression over the mass squared, times the mass's derivative. -/
private theorem contactSlope_deriv_eq
    (wb wc r u du Du D1 D2 D3 D4 : ℝ)
    (hab : wb + wc = 1)
    (_hD1 : D1 = 1 - r * u + 2 * u) (_hD2 : D2 = 1 - r * u + u)
    (hD3 : D3 = u ^ 2 + wb * (r * u) - wb * (r * u) * (wc * (r * u)))
    (hD4 : D4 = u ^ 2 + wc * (r * u) - wc * (r * u) * (wb * (r * u)))
    (hDu : Du * (u + r * du) = (r * u) * du)
    (hv : r * u ≠ 0) (hdv : u + r * du ≠ 0)
    (hb : wc ≠ 0)
    (h1 : D1 ≠ 0) (h2 : D2 ≠ 0) (h3 : D3 ≠ 0) (h4 : D4 ≠ 0) :
    (-(u + r * du) + 2 * du) / D1 - 2 * (-(u + r * du) + du) / D2 +
      wb * (3 * (wb * u + wb * r * du) / (wb * (r * u)) -
        2 * (2 * u * du + (wb * u + wb * r * du)
          - (wb * u + wb * r * du) * (wc * (r * u))
          - (wb * (r * u)) * (wc * u + wc * r * du)) / D3) +
      wc * (3 * (wc * u + wc * r * du) / (wc * (r * u)) -
        2 * (2 * u * du + (wc * u + wc * r * du)
          - (wc * u + wc * r * du) * (wb * (r * u))
          - (wc * (r * u)) * (wb * u + wb * r * du)) / D4) =
    (u + r * du) / (r * u) ^ 2 *
      ((r * u) * ((-(r * u) + 2 * Du) / D1 - 2 * (-(r * u) + Du) / D2)
        + 3 * (r * u) -
        2 * (((2 * u * Du - 2 * (wb * wc * (r * u) ^ 2)) *
          ((u ^ 2 - wb * wc * (r * u) ^ 2) * (r * u)
            + 2 * (wb * wc * (r * u) ^ 2)) +
        (u ^ 2 - wb * wc * (r * u) ^ 2) *
          ((r * u) ^ 2 - 2 * (wb * wc * (r * u) ^ 2)) +
        (wb * wc * (r * u) ^ 2) * (r * u)) / (D3 * D4))) := by
  have hSA := contactSlope_stage_diag r u du Du D1 D2 hDu hv hdv h1 h2
  have hSB := contactSlope_stage_cubes wb wc r u du hab hv hb
  have hSC := contactSlope_stage_quad wb wc r u du Du D3 D4 hab hD3 hD4 hDu hv h3 h4
  rw [show
    (-(u + r * du) + 2 * du) / D1 - 2 * (-(u + r * du) + du) / D2 +
        wb * (3 * (wb * u + wb * r * du) / (wb * (r * u)) -
          2 * (2 * u * du + (wb * u + wb * r * du)
            - (wb * u + wb * r * du) * (wc * (r * u))
            - (wb * (r * u)) * (wc * u + wc * r * du)) / D3) +
        wc * (3 * (wc * u + wc * r * du) / (wc * (r * u)) -
          2 * (2 * u * du + (wc * u + wc * r * du)
            - (wc * u + wc * r * du) * (wb * (r * u))
            - (wc * (r * u)) * (wb * u + wb * r * du)) / D4) =
      ((-(u + r * du) + 2 * du) / D1 - 2 * (-(u + r * du) + du) / D2) +
      (wb * (3 * (wb * u + wb * r * du) / (wb * (r * u))) +
        wc * (3 * (wc * u + wc * r * du) / (wc * (r * u)))) +
      (wb * (-2 * (2 * u * du + (wb * u + wb * r * du)
        - (wb * u + wb * r * du) * (wc * (r * u))
        - (wb * (r * u)) * (wc * u + wc * r * du)) / D3) +
       wc * (-2 * (2 * u * du + (wc * u + wc * r * du)
        - (wc * u + wc * r * du) * (wb * (r * u))
        - (wc * (r * u)) * (wb * u + wb * r * du)) / D4)) from by ring]
  rw [hSA, hSB, hSC]
  ring

/-! ### The three logarithms along the ray -/

/-- The diagonal certificate's logarithm, differentiated along the ray. -/
private theorem hasDerivAt_ray_log_certDiagonal (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (fun t => Real.log (certDiagonal (1 - rayMass z t) (rayRoot z t)))
      ((-((1 + z) / 2 * rayRoot z r + (1 + z) * r / 2 * rayRootDeriv z r
            + ((1 - z) / 2 * rayRoot z r + (1 - z) * r / 2 * rayRootDeriv z r))
          + 2 * rayRootDeriv z r) / (1 - rayMass z r + 2 * rayRoot z r)
        - 2 * (-((1 + z) / 2 * rayRoot z r + (1 + z) * r / 2 * rayRootDeriv z r
              + ((1 - z) / 2 * rayRoot z r + (1 - z) * r / 2 * rayRootDeriv z r))
            + rayRootDeriv z r) / (1 - rayMass z r + rayRoot z r)) r := by
  have hX : HasDerivAt (fun t : ℝ => (1 + z) * t / 2) ((1 + z) / 2) r := by
    simpa [mul_assoc] using ((hasDerivAt_id r).const_mul (1 + z)).div_const 2
  have hY : HasDerivAt (fun t : ℝ => (1 - z) * t / 2) ((1 - z) / 2) r := by
    simpa [mul_assoc] using ((hasDerivAt_id r).const_mul (1 - z)).div_const 2
  have hU : HasDerivAt (fun s : ℝ => chartRoot ((1 + z) * s / 2 + (1 - z) * s / 2)
      ((1 + z) * s / 2 * ((1 - z) * s / 2))) (rayRootDeriv z r) r := by
    rw [rayRoot_eq_chartRoot]
    exact hasDerivAt_rayRoot hz hr
  have hx : 0 < (1 + z) * r / 2 := by nlinarith [hz.1, hr.1]
  have hy : 0 < (1 - z) * r / 2 := by nlinarith [hz.2, hr.1]
  have hr1 : (1 + z) * r / 2 + (1 - z) * r / 2 < 1 := by
    have := (criticalRadius_spec hz).2.1
    nlinarith [hr.2]
  have h := hasDerivAt_log_certDiagonal hX hY hU hx hy hr1
  rw [(rayChart_at z r).1, (rayChart_at z r).2] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro t
  simp only []
  rw [(rayChart_at z t).1, (rayChart_at z t).2]

/-- The first off-diagonal certificate's logarithm, differentiated along the
ray. -/
private theorem hasDerivAt_ray_log_certOffB (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (fun t => Real.log (certOffDiagonal ((1 + z) / 2 * rayMass z t)
        ((1 - z) / 2 * rayMass z t) (rayRoot z t)))
      (3 * ((1 + z) / 2 * rayMassDeriv z r) / ((1 + z) / 2 * rayMass z r) -
        2 * (2 * rayRoot z r * rayRootDeriv z r + (1 + z) / 2 * rayMassDeriv z r
            - (1 + z) / 2 * rayMassDeriv z r * ((1 - z) / 2 * rayMass z r)
            - (1 + z) / 2 * rayMass z r * ((1 - z) / 2 * rayMassDeriv z r))
          / (rayRoot z r ^ 2 + (1 + z) / 2 * rayMass z r
              - (1 + z) / 2 * rayMass z r * ((1 - z) / 2 * rayMass z r))) r := by
  have hdom := chartDomain_ray hz hr
  have hV := hasDerivAt_rayMass hz hr
  have hu : 0 < rayRoot z r := (chart_pos hdom).2.1
  have hb : 0 < (1 + z) / 2 * rayMass z r :=
    mul_pos (by linarith [hz.1]) (chart_pos hdom).2.2.2.1
  have hcoef : 0 < 1 - (1 + z) / 2 * ((1 - z) / 2) * r ^ 2 := by
    have h := (chartFactors_pos hdom).2.1
    unfold rayProductCoeff at h
    nlinarith
  have hq : 0 < rayRoot z r ^ 2 + (1 + z) / 2 * rayMass z r
      - (1 + z) / 2 * rayMass z r * ((1 - z) / 2 * rayMass z r) := by
    rw [show rayMass z r = r * rayRoot z r from rfl,
      show rayRoot z r ^ 2 + (1 + z) / 2 * (r * rayRoot z r)
          - (1 + z) / 2 * (r * rayRoot z r) * ((1 - z) / 2 * (r * rayRoot z r)) =
        rayRoot z r * (rayRoot z r * (1 - (1 + z) / 2 * ((1 - z) / 2) * r ^ 2)
          + r * ((1 + z) / 2)) from by ring]
    exact mul_pos hu (add_pos (mul_pos hu hcoef)
      (mul_pos hr.1 (by linarith [hz.1])))
  exact hasDerivAt_log_certOffDiagonal (hV.const_mul ((1 + z) / 2))
    (hV.const_mul ((1 - z) / 2)) (hasDerivAt_rayRoot hz hr) hb hq

/-- The second off-diagonal certificate's logarithm, differentiated along the
ray. -/
private theorem hasDerivAt_ray_log_certOffC (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (fun t => Real.log (certOffDiagonal ((1 - z) / 2 * rayMass z t)
        ((1 + z) / 2 * rayMass z t) (rayRoot z t)))
      (3 * ((1 - z) / 2 * rayMassDeriv z r) / ((1 - z) / 2 * rayMass z r) -
        2 * (2 * rayRoot z r * rayRootDeriv z r + (1 - z) / 2 * rayMassDeriv z r
            - (1 - z) / 2 * rayMassDeriv z r * ((1 + z) / 2 * rayMass z r)
            - (1 - z) / 2 * rayMass z r * ((1 + z) / 2 * rayMassDeriv z r))
          / (rayRoot z r ^ 2 + (1 - z) / 2 * rayMass z r
              - (1 - z) / 2 * rayMass z r * ((1 + z) / 2 * rayMass z r))) r := by
  have hdom := chartDomain_ray hz hr
  have hV := hasDerivAt_rayMass hz hr
  have hu : 0 < rayRoot z r := (chart_pos hdom).2.1
  have hb : 0 < (1 - z) / 2 * rayMass z r :=
    mul_pos (by linarith [hz.2]) (chart_pos hdom).2.2.2.1
  have hcoef : 0 < 1 - (1 - z) / 2 * ((1 + z) / 2) * r ^ 2 := by
    have h := (chartFactors_pos hdom).2.1
    unfold rayProductCoeff at h
    nlinarith
  have hq : 0 < rayRoot z r ^ 2 + (1 - z) / 2 * rayMass z r
      - (1 - z) / 2 * rayMass z r * ((1 + z) / 2 * rayMass z r) := by
    rw [show rayMass z r = r * rayRoot z r from rfl,
      show rayRoot z r ^ 2 + (1 - z) / 2 * (r * rayRoot z r)
          - (1 - z) / 2 * (r * rayRoot z r) * ((1 + z) / 2 * (r * rayRoot z r)) =
        rayRoot z r * (rayRoot z r * (1 - (1 - z) / 2 * ((1 + z) / 2) * r ^ 2)
          + r * ((1 - z) / 2)) from by ring]
    exact mul_pos hu (add_pos (mul_pos hu hcoef)
      (mul_pos hr.1 (by linarith [hz.2])))
  exact hasDerivAt_log_certOffDiagonal (hV.const_mul ((1 - z) / 2))
    (hV.const_mul ((1 + z) / 2)) (hasDerivAt_rayRoot hz hr) hb hq

/-- **The height slope, differentiated along the ray.**  Dividing by the
mass's derivative, this says that `chartContactSecondOrder` is the page's
`L_k = v^2 d^2 k / dv^2` of display (3.7). -/
theorem hasDerivAt_rayHeightSlope (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (rayHeightSlope z)
      (rayMassDeriv z r
        * (chartContactSecondOrder r (rayProductCoeff z * r ^ 2)
            / rayMass z r ^ 2)) r := by
  have hdom := chartDomain_ray hz hr
  have hu : 0 < rayRoot z r := (chart_pos hdom).2.1
  have hv1 : rayMass z r < 1 := by
    have h := chartOffDiagonalMass_lt_third hdom
    unfold rayMass
    linarith
  have hcu : chartRoot r (rayProductCoeff z * r ^ 2) = rayRoot z r := rfl
  have hcv : chartOffDiagonalMass r (rayProductCoeff z * r ^ 2)
      = r * rayRoot z r := rfl
  have hcs : chartDiagonalMass r (rayProductCoeff z * r ^ 2)
      = 1 - r * rayRoot z r := rfl
  have hVU : rayMass z r = r * rayRoot z r := rfl
  have hsum : rayMassDeriv z r = rayRoot z r + r * rayRootDeriv z r := by
    unfold rayMassDeriv rayRoot rayRootDeriv chartRoot chartNorm
    field_simp
    ring
  have hdv : rayRoot z r + r * rayRootDeriv z r ≠ 0 := by
    rw [← hsum]
    exact (rayMassDeriv_pos hz hr).ne'
  have hv : r * rayRoot z r ≠ 0 := (mul_pos hr.1 hu).ne'
  have hDu' : chartRootDeriv r (rayProductCoeff z * r ^ 2)
      * (rayRoot z r + r * rayRootDeriv z r) = (r * rayRoot z r) * rayRootDeriv z r := by
    have h := chartRootDeriv_mul_rayMassDeriv hz hr
    rw [hsum, hVU] at h
    exact h
  have hb : (1 - z) / 2 ≠ 0 := by
    have := hz.2
    intro h0
    linarith
  have h1 : 1 - r * rayRoot z r + 2 * rayRoot z r ≠ 0 := by
    rw [hVU] at hv1
    intro h0
    linarith
  have h2 : 1 - r * rayRoot z r + rayRoot z r ≠ 0 := by
    rw [hVU] at hv1
    intro h0
    linarith
  have hfac : 0 < 1 - (1 + z) / 2 * ((1 - z) / 2) * r ^ 2 := by
    have h := (chartFactors_pos hdom).2.1
    unfold rayProductCoeff at h
    nlinarith
  have h3 : rayRoot z r ^ 2 + (1 + z) / 2 * (r * rayRoot z r) -
      (1 + z) / 2 * (r * rayRoot z r) * ((1 - z) / 2 * (r * rayRoot z r)) ≠ 0 := by
    rw [show rayRoot z r ^ 2 + (1 + z) / 2 * (r * rayRoot z r) -
        (1 + z) / 2 * (r * rayRoot z r) * ((1 - z) / 2 * (r * rayRoot z r)) =
      rayRoot z r * (rayRoot z r * (1 - (1 + z) / 2 * ((1 - z) / 2) * r ^ 2) +
        r * ((1 + z) / 2)) from by ring]
    exact (mul_pos hu (add_pos (mul_pos hu hfac)
      (mul_pos hr.1 (by linarith [hz.1])))).ne'
  have hfac' : 0 < 1 - (1 - z) / 2 * ((1 + z) / 2) * r ^ 2 := by nlinarith [hfac]
  have h4 : rayRoot z r ^ 2 + (1 - z) / 2 * (r * rayRoot z r) -
      (1 - z) / 2 * (r * rayRoot z r) * ((1 + z) / 2 * (r * rayRoot z r)) ≠ 0 := by
    rw [show rayRoot z r ^ 2 + (1 - z) / 2 * (r * rayRoot z r) -
        (1 - z) / 2 * (r * rayRoot z r) * ((1 + z) / 2 * (r * rayRoot z r)) =
      rayRoot z r * (rayRoot z r * (1 - (1 - z) / 2 * ((1 + z) / 2) * r ^ 2) +
        r * ((1 - z) / 2)) from by ring]
    exact (mul_pos hu (add_pos (mul_pos hu hfac')
      (mul_pos hr.1 (by linarith [hz.2])))).ne'
  have key := contactSlope_deriv_eq ((1 + z) / 2) ((1 - z) / 2) r (rayRoot z r)
    (rayRootDeriv z r) (chartRootDeriv r (rayProductCoeff z * r ^ 2)) _ _ _ _
    (by ring) rfl rfl rfl rfl hDu' hv hdv hb h1 h2 h3 h4
  have h := ((hasDerivAt_ray_log_certDiagonal hz hr).add
    ((hasDerivAt_ray_log_certOffB hz hr).const_mul ((1 + z) / 2))).add
      ((hasDerivAt_ray_log_certOffC hz hr).const_mul ((1 - z) / 2))
  refine h.congr_deriv ?_
  rw [hsum]
  simp only [hVU]
  unfold chartContactSecondOrder chartLogKDeriv chartWeightedLogDeriv
    chartCommonDeriv
  simp only [hcv, hcs, hcu]
  have hWden : chartDeterminant r (rayProductCoeff z * r ^ 2) ^ 2
      + chartDeterminant r (rayProductCoeff z * r ^ 2) * (r * rayRoot z r)
      + chartOffDiagonalProduct r (rayProductCoeff z * r ^ 2) =
      (rayRoot z r ^ 2 + (1 + z) / 2 * (r * rayRoot z r) -
        (1 + z) / 2 * (r * rayRoot z r) * ((1 - z) / 2 * (r * rayRoot z r))) *
      (rayRoot z r ^ 2 + (1 - z) / 2 * (r * rayRoot z r) -
        (1 - z) / 2 * (r * rayRoot z r) * ((1 + z) / 2 * (r * rayRoot z r))) := by
    unfold chartDeterminant chartOffDiagonalProduct
    simp only [hcu]
    unfold rayProductCoeff
    ring
  rw [hWden]
  unfold chartDeterminant chartOffDiagonalProduct
  simp only [hcu]
  unfold rayProductCoeff at key ⊢
  linear_combination key

/-! ## The two slopes, differentiated

Dividing by the mass's derivative, these are the two equalities of the page's
display (4.3): the chart's second-order expressions are `v^2 d^2 M / dv^2` for
the two margins.  The inequalities of (4.3) are not proved here. -/

/-- **The constant code's margin slope, differentiated along the ray.** -/
theorem hasDerivAt_rayConstantSlope (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (rayConstantSlope z)
      (rayMassDeriv z r
        * (chartConstantSecondOrder r (rayProductCoeff z * r ^ 2)
            / rayMass z r ^ 2)) r := by
  have hdom := chartDomain_ray hz hr
  have hv : 0 < rayMass z r := (chart_pos hdom).2.2.2.1
  have hv1 : rayMass z r < 1 := by
    have h := chartOffDiagonalMass_lt_third hdom
    unfold rayMass
    linarith
  have hzv : |z * rayMass z r| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hz.1, hz.2]
  have hV := hasDerivAt_rayMass hz hr
  have hj0 := ((hV.const_sub 1).div_const 2).log
    (div_ne_zero (sub_pos.mpr hv1).ne' (by norm_num))
  have hj1 := (hV.const_mul ((1 + z) / 2)).log
    (mul_ne_zero (by linarith [hz.1]) hv.ne')
  have hj2 := (hV.const_mul ((1 - z) / 2)).log
    (mul_ne_zero (by linarith [hz.2]) hv.ne')
  have hjv := (hj0.sub (hj1.const_mul ((1 + z) / 2))).sub
    (hj2.const_mul ((1 - z) / 2))
  have hjv' : HasDerivAt
      (fun t => Real.log ((1 - rayMass z t) / 2) -
        (1 + z) / 2 * Real.log ((1 + z) / 2 * rayMass z t) -
        (1 - z) / 2 * Real.log ((1 - z) / 2 * rayMass z t))
      (rayMassDeriv z r * (-1 / (1 - rayMass z r) - 1 / rayMass z r)) r := by
    refine hjv.congr_deriv ?_
    field_simp [hv.ne', (sub_pos.mpr hv1).ne']
    ring
  have hp : 1 + z * rayMass z r ≠ 0 := by nlinarith [(abs_lt.mp hzv).1]
  have hm : 1 - z * rayMass z r ≠ 0 := by nlinarith [(abs_lt.mp hzv).2]
  have hratio := (((hV.const_mul z).const_add 1).div
    ((hV.const_mul z).const_sub 1) hm).log (div_ne_zero hp hm)
  have hrv := hratio.const_mul (-z / 2)
  have hrv' : HasDerivAt
      (fun t => -z / 2 * Real.log ((1 + z * rayMass z t) / (1 - z * rayMass z t)))
      (-z / 2 * (z * rayMassDeriv z r / (1 + z * rayMass z r) +
        z * rayMassDeriv z r / (1 - z * rayMass z r))) r := by
    refine hrv.congr_deriv ?_
    dsimp only [Pi.div_apply]
    field_simp [hp, hm]
    ring
  have hkv := hasDerivAt_rayHeightSlope hz hr
  have hh := ((hjv'.const_mul 5).sub (hrv'.const_mul 6)).add (hkv.const_mul 2)
  unfold rayConstantSlope
  refine hh.congr_deriv ?_
  have hd2 : (r ^ 2 - 4 * (rayProductCoeff z * r ^ 2)) *
      chartRoot r (rayProductCoeff z * r ^ 2) ^ 2 = z ^ 2 * rayMass z r ^ 2 := by
    unfold rayMass chartOffDiagonalMass rayProductCoeff
    ring
  have hcv : chartOffDiagonalMass r (rayProductCoeff z * r ^ 2)
      = rayMass z r := rfl
  have hvs : 1 - rayMass z r ≠ 0 := (sub_pos.mpr hv1).ne'
  have hd : 1 - z ^ 2 * rayMass z r ^ 2 ≠ 0 := by
    rw [show 1 - z ^ 2 * rayMass z r ^ 2 =
      (1 - z * rayMass z r) * (1 + z * rayMass z r) from by ring]
    exact mul_ne_zero hm hp
  have hp' : 1 + rayMass z r * z ≠ 0 := by nlinarith [(abs_lt.mp hzv).1]
  have hm' : 1 - rayMass z r * z ≠ 0 := by nlinarith [(abs_lt.mp hzv).2]
  have hd' : 1 - rayMass z r ^ 2 * z ^ 2 ≠ 0 := by
    rw [show 1 - rayMass z r ^ 2 * z ^ 2 =
      (1 - rayMass z r * z) * (1 + rayMass z r * z) from by ring]
    exact mul_ne_zero hm' hp'
  unfold chartConstantSecondOrder chartDiscriminant chartDiagonalMass
  rw [hd2, hcv]
  field_simp [hv.ne', hvs, hp, hm, hp', hm', hd, hd']
  ring

/-- **The isolating code's margin slope, differentiated along the ray.** -/
theorem hasDerivAt_raySingletonSlope (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    HasDerivAt (raySingletonSlope z)
      (rayMassDeriv z r
        * (chartSingletonSecondOrder r (rayProductCoeff z * r ^ 2)
            / rayMass z r ^ 2)) r := by
  have hdom := chartDomain_ray hz hr
  have hv : 0 < rayMass z r := (chart_pos hdom).2.2.2.1
  have hv1 : rayMass z r < 1 := by
    have h := chartOffDiagonalMass_lt_third hdom
    unfold rayMass
    linarith
  have hzv : |z * rayMass z r| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hz.1, hz.2]
  have hV := hasDerivAt_rayMass hz hr
  have hj0 := ((hV.const_sub 1).div_const 2).log
    (div_ne_zero (sub_pos.mpr hv1).ne' (by norm_num))
  have hj1 := (hV.const_mul ((1 + z) / 2)).log
    (mul_ne_zero (by linarith [hz.1]) hv.ne')
  have hj2 := (hV.const_mul ((1 - z) / 2)).log
    (mul_ne_zero (by linarith [hz.2]) hv.ne')
  have hjv := (hj0.sub (hj1.const_mul ((1 + z) / 2))).sub
    (hj2.const_mul ((1 - z) / 2))
  have hjv' : HasDerivAt
      (fun t => Real.log ((1 - rayMass z t) / 2) -
        (1 + z) / 2 * Real.log ((1 + z) / 2 * rayMass z t) -
        (1 - z) / 2 * Real.log ((1 - z) / 2 * rayMass z t))
      (rayMassDeriv z r * (-1 / (1 - rayMass z r) - 1 / rayMass z r)) r := by
    refine hjv.congr_deriv ?_
    field_simp [hv.ne', (sub_pos.mpr hv1).ne']
    ring
  have hp : 1 + z * rayMass z r ≠ 0 := by nlinarith [(abs_lt.mp hzv).1]
  have hm : 1 - z * rayMass z r ≠ 0 := by nlinarith [(abs_lt.mp hzv).2]
  have hratio := (((hV.const_mul z).const_add 1).div
    ((hV.const_mul z).const_sub 1) hm).log (div_ne_zero hp hm)
  have hrv := hratio.const_mul (-z / 2)
  have hrv' : HasDerivAt
      (fun t => -z / 2 * Real.log ((1 + z * rayMass z t) / (1 - z * rayMass z t)))
      (-z / 2 * (z * rayMassDeriv z r / (1 + z * rayMass z r) +
        z * rayMassDeriv z r / (1 - z * rayMass z r))) r := by
    refine hrv.congr_deriv ?_
    dsimp only [Pi.div_apply]
    field_simp [hp, hm]
    ring
  have hvp : 1 + rayMass z r ≠ 0 := by nlinarith
  have hvm : 1 - rayMass z r ≠ 0 := (sub_pos.mpr hv1).ne'
  have hpair := ((hV.const_add 1).div (hV.const_sub 1) hvm).log
    (div_ne_zero hvp hvm)
  have hpl := hpair.const_mul (1 / 2)
  have hpl' : HasDerivAt
      (fun t => 1 / 2 * Real.log ((1 + rayMass z t) / (1 - rayMass z t)))
      (1 / 2 * (rayMassDeriv z r / (1 + rayMass z r) +
        rayMassDeriv z r / (1 - rayMass z r))) r := by
    refine hpl.congr_deriv ?_
    dsimp only [Pi.div_apply]
    field_simp [hvp, hvm]
    ring
  have hkv := hasDerivAt_rayHeightSlope hz hr
  have hh := (((hjv'.const_mul 3).sub (hrv'.const_mul 4)).sub hpl').add
    (hkv.const_mul 2)
  unfold raySingletonSlope
  refine hh.congr_deriv ?_
  have hd2 : (r ^ 2 - 4 * (rayProductCoeff z * r ^ 2)) *
      chartRoot r (rayProductCoeff z * r ^ 2) ^ 2 = z ^ 2 * rayMass z r ^ 2 := by
    unfold rayMass chartOffDiagonalMass rayProductCoeff
    ring
  have hcv : chartOffDiagonalMass r (rayProductCoeff z * r ^ 2)
      = rayMass z r := rfl
  have hd : 1 - z ^ 2 * rayMass z r ^ 2 ≠ 0 := by
    rw [show 1 - z ^ 2 * rayMass z r ^ 2 =
      (1 - z * rayMass z r) * (1 + z * rayMass z r) from by ring]
    exact mul_ne_zero hm hp
  have hp' : 1 + rayMass z r * z ≠ 0 := by nlinarith [(abs_lt.mp hzv).1]
  have hm' : 1 - rayMass z r * z ≠ 0 := by nlinarith [(abs_lt.mp hzv).2]
  have hd' : 1 - rayMass z r ^ 2 * z ^ 2 ≠ 0 := by
    rw [show 1 - rayMass z r ^ 2 * z ^ 2 =
      (1 - rayMass z r * z) * (1 + rayMass z r * z) from by ring]
    exact mul_ne_zero hm' hp'
  have hvd : 1 - rayMass z r ^ 2 ≠ 0 := by
    rw [show 1 - rayMass z r ^ 2 =
      (1 - rayMass z r) * (1 + rayMass z r) from by ring]
    exact mul_ne_zero hvm hvp
  unfold chartSingletonSecondOrder chartDiscriminant chartDiagonalMass
  rw [hd2, hcv]
  field_simp [hv.ne', hvm, hvp, hp, hm, hp', hm', hd, hd', hvd]
  ring

end StochasticToDeterministicLatents.Binary
