import StochasticToDeterministicLatents.Binary.FactorTwo.Shape
import StochasticToDeterministicLatents.Binary.FactorTwo.Contact

/-!
# The norm bound from the positivity gate

`Contact` reduces the majorant property of the tangent certificate at a law `q`
to `NormBound q`, a Hölder-type inequality over the two marginals.  This module
proves `NormBound q` from `PositivityGate q`, which is the analytic half of the
factor-two argument and the only place where a non-rational inequality is used.

The route is the one the gate is named for.  The gate expressions are the
coefficients of the norm-gate quartic, which `Shape.normGateQuartic_nonneg`
makes nonnegative on the half line from the gate inequality alone.  That
quartic is `(x - 1) ^ 2` times the norm-gate polynomial of `q`, so the
polynomial is nonnegative too, and weighted Hölder at the conjugate exponents
`3 / 2` and `3` turns the resulting cube bound into `NormBound q`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

open Finset

/-! ## The norm-gate polynomial -/

/-- The norm-gate polynomial of a law: the difference between the square of the
column-marginal cubic and the two row-normalized cubes. -/
noncomputable def gatePolynomial (q : RealTable) (x : ℝ) : ℝ :=
  (stoch_to_det.mY q 0 * x ^ 3 + stoch_to_det.mY q 1) ^ 2
    - (q (0, 0) * x ^ 2 + q (0, 1)) ^ 3 / stoch_to_det.mX q 0 ^ 2
    - (q (1, 0) * x ^ 2 + q (1, 1)) ^ 3 / stoch_to_det.mX q 1 ^ 2

variable {q : RealTable}

private theorem cells_sum_one (hq : IsPMF q) :
    q (0, 0) + q (0, 1) + q (1, 0) + q (1, 1) = 1 := by
  have ht := hq.total
  rw [stoch_to_det.mass, sum_cells] at ht
  exact ht

/-- The norm-gate polynomial is `(x - 1) ^ 2` times the quartic whose
coefficients are the gate expressions.  The identity uses normalization. -/
private theorem gatePolynomial_factor (hpos : FullSupport q) (hq : IsPMF q) (x : ℝ) :
    gatePolynomial q x = (x - 1) ^ 2
      * (gateA q * x ^ 4 + 2 * gateA q * x ^ 3 - 3 * gateV q * x ^ 2
        + 2 * gateE q * x + gateE q) := by
  have hx0 : q (0, 0) + q (0, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have hx1 : q (1, 0) + q (1, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have hd : q (1, 1) = 1 - q (0, 0) - q (0, 1) - q (1, 0) := by
    have := cells_sum_one hq; linarith
  rw [gatePolynomial, gateA, gateE, gateV, determinant_eq, entryA, entryB,
    entryC, entryD, marginalX_zero, marginalX_one, marginalY_zero, marginalY_one]
  field_simp
  rw [hd]
  ring

/-- The two outer gate expressions sum to the marginal product less three times
the determinant term.  Normalization is essential. -/
private theorem gate_sum (hpos : FullSupport q) (hq : IsPMF q) :
    gateA q + gateE q = gateM q - 3 * gateV q := by
  have hx0 : q (0, 0) + q (0, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have hx1 : q (1, 0) + q (1, 1) ≠ 0 := (add_pos (hpos _) (hpos _)).ne'
  have hd : q (1, 1) = 1 - q (0, 0) - q (0, 1) - q (1, 0) := by
    have := cells_sum_one hq; linarith
  rw [gateA, gateE, gateV, gateM, determinant_eq, entryA, entryB, entryC,
    entryD, marginalX_zero, marginalX_one, marginalY_zero, marginalY_one]
  field_simp
  rw [hd]
  ring

/-- The norm-gate polynomial is nonnegative on the half line at any law that
passes the positivity gate. -/
theorem gatePolynomial_nonneg (hpos : FullSupport q) (hq : IsPMF q)
    (hgate : PositivityGate q) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gatePolynomial q x := by
  obtain ⟨hA, hE, hcubic⟩ := hgate
  have hsum := gate_sum hpos hq
  have hM : gateM q = gateA q + gateE q + 3 * gateV q := by linarith
  have hV : 0 ≤ gateV q := by
    rw [gateV, marginalX_zero, marginalX_one]
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (add_pos (hpos _) (hpos _)).le (add_pos (hpos _) (hpos _)).le)
  rw [gatePolynomial_factor hpos hq x]
  exact mul_nonneg (sq_nonneg _) (normGateQuartic_nonneg _ _ _ hA hE hV (hM ▸ hcubic) x hx)

/-! ## Weighted Hölder on two points -/

private theorem rpow_two_thirds_cancel {a : ℝ} (ha : 0 ≤ a) :
    (a ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = a := by
  rw [← Real.rpow_mul ha]
  norm_num

private theorem bit_sum {u : Bit → ℝ} (hu : IsPMF u) : u 0 + u 1 = 1 := by
  have ht := hu.total
  rw [stoch_to_det.mass] at ht
  simpa [Fin.sum_univ_two] using ht

/-- Weighted Hölder on a two-point space, at the conjugate exponents `3 / 2`
and `3`. -/
private theorem holder_two_point (m0 m1 f0 f1 h0 h1 : ℝ)
    (hm0 : 0 ≤ m0) (hm1 : 0 ≤ m1) (hf0 : 0 ≤ f0) (hf1 : 0 ≤ f1)
    (hh0 : 0 ≤ h0) (hh1 : 0 ≤ h1) :
    m0 * f0 * h0 + m1 * f1 * h1
      ≤ (m0 * f0 ^ ((3 : ℝ) / 2) + m1 * f1 ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)
        * (m0 * h0 ^ 3 + m1 * h1 ^ 3) ^ ((1 : ℝ) / 3) := by
  set m : Bit → ℝ := fun i => if i = 0 then m0 else m1 with hm
  set f : Bit → ℝ := fun i => if i = 0 then f0 else f1 with hf
  set h : Bit → ℝ := fun i => if i = 0 then h0 else h1 with hh
  have hmn : ∀ i, 0 ≤ m i := by intro i; fin_cases i <;> simp [hm, hm0, hm1]
  have hfn : ∀ i, 0 ≤ f i := by intro i; fin_cases i <;> simp [hf, hf0, hf1]
  have hhn : ∀ i, 0 ≤ h i := by intro i; fin_cases i <;> simp [hh, hh0, hh1]
  set F : Bit → ℝ := fun i => m i ^ ((2 : ℝ) / 3) * f i with hF
  set G : Bit → ℝ := fun i => m i ^ ((1 : ℝ) / 3) * h i with hG
  have hFn : ∀ i ∈ (univ : Finset Bit), 0 ≤ F i :=
    fun i _ => mul_nonneg (Real.rpow_nonneg (hmn i) _) (hfn i)
  have hGn : ∀ i ∈ (univ : Finset Bit), 0 ≤ G i :=
    fun i _ => mul_nonneg (Real.rpow_nonneg (hmn i) _) (hhn i)
  have hpq : Real.HolderConjugate ((3 : ℝ) / 2) 3 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have H := Real.inner_le_Lp_mul_Lq_of_nonneg (s := (univ : Finset Bit))
    (f := F) (g := G) hpq hFn hGn
  have hprod (i : Bit) : F i * G i = m i * f i * h i := by
    rw [hF, hG]
    calc m i ^ ((2 : ℝ) / 3) * f i * (m i ^ ((1 : ℝ) / 3) * h i)
        = m i ^ ((2 : ℝ) / 3) * m i ^ ((1 : ℝ) / 3) * f i * h i := by ring
      _ = m i ^ ((2 : ℝ) / 3 + (1 : ℝ) / 3) * f i * h i := by
          rw [Real.rpow_add' (hmn i)]; norm_num
      _ = m i * f i * h i := by norm_num
  have hpowF (i : Bit) : F i ^ ((3 : ℝ) / 2) = m i * f i ^ ((3 : ℝ) / 2) := by
    rw [hF, Real.mul_rpow (Real.rpow_nonneg (hmn i) _) (hfn i),
      ← Real.rpow_mul (hmn i)]
    norm_num
  have hpowG (i : Bit) : G i ^ (3 : ℝ) = m i * h i ^ (3 : ℝ) := by
    rw [hG, Real.mul_rpow (Real.rpow_nonneg (hmn i) _) (hhn i),
      ← Real.rpow_mul (hmn i)]
    norm_num
  simp only [Fin.sum_univ_two, hprod, hpowF, hpowG] at H
  norm_num at H
  simpa [hm, hf, hh] using H

/-! ## The cube bound and the norm bound -/

/-- The scalar form of the cube bound: nonnegativity of the norm-gate
polynomial at `x` bounds the two row cubes at the scaled argument. -/
private theorem cube_bound_scalar (m0 m1 n0 n1 q00 q01 q10 q11 x g : ℝ)
    (hm0 : 0 < m0) (hm1 : 0 < m1) (hg : 0 < g)
    (hP : 0 ≤ (n0 * x ^ 3 + n1) ^ 2 - (q00 * x ^ 2 + q01) ^ 3 / m0 ^ 2
      - (q10 * x ^ 2 + q11) ^ 3 / m1 ^ 2) :
    m0 * ((q00 * (g * x ^ 2) + q01 * g) / m0) ^ 3
        + m1 * ((q10 * (g * x ^ 2) + q11 * g) / m1) ^ 3
      ≤ g ^ 3 * (n0 * x ^ 3 + n1) ^ 2 := by
  have hbase : (q00 * x ^ 2 + q01) ^ 3 / m0 ^ 2
      + (q10 * x ^ 2 + q11) ^ 3 / m1 ^ 2 ≤ (n0 * x ^ 3 + n1) ^ 2 := by linarith
  calc m0 * ((q00 * (g * x ^ 2) + q01 * g) / m0) ^ 3
        + m1 * ((q10 * (g * x ^ 2) + q11 * g) / m1) ^ 3
      = g ^ 3 * ((q00 * x ^ 2 + q01) ^ 3 / m0 ^ 2
        + (q10 * x ^ 2 + q11) ^ 3 / m1 ^ 2) := by
        field_simp
    _ ≤ g ^ 3 * (n0 * x ^ 3 + n1) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (pow_pos hg 3).le

/-- The two row cubes of a nonnegative pair are bounded by the square of the
column-marginal combination. -/
private theorem cube_bound (hpos : FullSupport q) (hq : IsPMF q)
    (hgate : PositivityGate q) {g0 g1 : ℝ} (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) :
    stoch_to_det.mX q 0 * ((q (0, 0) * g0 + q (0, 1) * g1) / stoch_to_det.mX q 0) ^ 3
        + stoch_to_det.mX q 1
          * ((q (1, 0) * g0 + q (1, 1) * g1) / stoch_to_det.mX q 1) ^ 3
      ≤ (stoch_to_det.mY q 0 * g0 ^ ((3 : ℝ) / 2)
        + stoch_to_det.mY q 1 * g1 ^ ((3 : ℝ) / 2)) ^ 2 := by
  have hmx0 : 0 < stoch_to_det.mX q 0 := marginalX_pos hpos 0
  have hmx1 : 0 < stoch_to_det.mX q 1 := marginalX_pos hpos 1
  rcases h1.eq_or_lt with rfl | h1pos
  · have hz : (0 : ℝ) ^ ((3 : ℝ) / 2) = 0 := by
      rw [Real.zero_rpow]; norm_num
    rw [hz]
    simp only [mul_zero, add_zero]
    have hgateA := hgate.1
    rw [gateA] at hgateA
    have hbase : q (0, 0) ^ 3 / stoch_to_det.mX q 0 ^ 2
        + q (1, 0) ^ 3 / stoch_to_det.mX q 1 ^ 2 ≤ stoch_to_det.mY q 0 ^ 2 := by
      linarith
    have hcube : (g0 ^ ((3 : ℝ) / 2)) ^ 2 = g0 ^ 3 := by
      rw [← Real.rpow_natCast (g0 ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul h0]
      norm_num
    calc stoch_to_det.mX q 0 * (q (0, 0) * g0 / stoch_to_det.mX q 0) ^ 3
          + stoch_to_det.mX q 1 * (q (1, 0) * g0 / stoch_to_det.mX q 1) ^ 3
        = g0 ^ 3 * (q (0, 0) ^ 3 / stoch_to_det.mX q 0 ^ 2
          + q (1, 0) ^ 3 / stoch_to_det.mX q 1 ^ 2) := by field_simp
      _ ≤ g0 ^ 3 * stoch_to_det.mY q 0 ^ 2 :=
          mul_le_mul_of_nonneg_left hbase (pow_nonneg h0 3)
      _ = (stoch_to_det.mY q 0 * g0 ^ ((3 : ℝ) / 2)) ^ 2 := by rw [← hcube]; ring
  · have hquot : 0 ≤ g0 / g1 := div_nonneg h0 h1pos.le
    set x := √(g0 / g1) with hxd
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hxsq : x ^ 2 = g0 / g1 := by rw [hxd]; exact Real.sq_sqrt hquot
    have hg0 : g0 = g1 * x ^ 2 := by rw [hxsq]; field_simp
    have hg0r : g0 ^ ((3 : ℝ) / 2) = g1 ^ ((3 : ℝ) / 2) * x ^ 3 := by
      rw [hg0, Real.mul_rpow h1pos.le (sq_nonneg _),
        ← Real.rpow_natCast, ← Real.rpow_mul hx0]
      norm_num
    have hg1sq : (g1 ^ ((3 : ℝ) / 2)) ^ 2 = g1 ^ 3 := by
      rw [← Real.rpow_natCast (g1 ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul h1pos.le]
      norm_num
    have key := gatePolynomial_nonneg hpos hq hgate hx0
    rw [gatePolynomial] at key
    have hs := cube_bound_scalar (stoch_to_det.mX q 0) (stoch_to_det.mX q 1)
      (stoch_to_det.mY q 0) (stoch_to_det.mY q 1) (q (0, 0)) (q (0, 1))
      (q (1, 0)) (q (1, 1)) (x) g1 hmx0 hmx1 h1pos key
    calc stoch_to_det.mX q 0
            * ((q (0, 0) * g0 + q (0, 1) * g1) / stoch_to_det.mX q 0) ^ 3
          + stoch_to_det.mX q 1
            * ((q (1, 0) * g0 + q (1, 1) * g1) / stoch_to_det.mX q 1) ^ 3
        = stoch_to_det.mX q 0
            * ((q (0, 0) * (g1 * x ^ 2) + q (0, 1) * g1)
              / stoch_to_det.mX q 0) ^ 3
          + stoch_to_det.mX q 1
            * ((q (1, 0) * (g1 * x ^ 2) + q (1, 1) * g1)
              / stoch_to_det.mX q 1) ^ 3 := by rw [← hg0]
      _ ≤ g1 ^ 3 * (stoch_to_det.mY q 0 * x ^ 3
            + stoch_to_det.mY q 1) ^ 2 := hs
      _ = (stoch_to_det.mY q 0 * g0 ^ ((3 : ℝ) / 2)
            + stoch_to_det.mY q 1 * g1 ^ ((3 : ℝ) / 2)) ^ 2 := by
          rw [hg0r, ← hg1sq]; ring

/-- The positivity gate implies the norm bound.  With
`majorizes_tangentCert_of_normBound` this closes the certificate side of the
contact bound. -/
theorem normBound_of_positivityGate (hpos : FullSupport q) (hq : IsPMF q)
    (hgate : PositivityGate q) : NormBound q := by
  intro u v hu hv
  have hmx0 : 0 < stoch_to_det.mX q 0 := marginalX_pos hpos 0
  have hmx1 : 0 < stoch_to_det.mX q 1 := marginalX_pos hpos 1
  have hmy0 : 0 < stoch_to_det.mY q 0 := marginalY_pos hpos 0
  have hmy1 : 0 < stoch_to_det.mY q 1 := marginalY_pos hpos 1
  set f0 := (u 0 / stoch_to_det.mX q 0) ^ ((2 : ℝ) / 3) with hf0d
  set f1 := (u 1 / stoch_to_det.mX q 1) ^ ((2 : ℝ) / 3) with hf1d
  set g0 := (v 0 / stoch_to_det.mY q 0) ^ ((2 : ℝ) / 3) with hg0d
  set g1 := (v 1 / stoch_to_det.mY q 1) ^ ((2 : ℝ) / 3) with hg1d
  set k0 := (q (0, 0) * g0 + q (0, 1) * g1) / stoch_to_det.mX q 0 with hk0d
  set k1 := (q (1, 0) * g0 + q (1, 1) * g1) / stoch_to_det.mX q 1 with hk1d
  have hf0 : 0 ≤ f0 := Real.rpow_nonneg (div_nonneg (hu.nonneg _) hmx0.le) _
  have hf1 : 0 ≤ f1 := Real.rpow_nonneg (div_nonneg (hu.nonneg _) hmx1.le) _
  have hg0 : 0 ≤ g0 := Real.rpow_nonneg (div_nonneg (hv.nonneg _) hmy0.le) _
  have hg1 : 0 ≤ g1 := Real.rpow_nonneg (div_nonneg (hv.nonneg _) hmy1.le) _
  have hk0 : 0 ≤ k0 :=
    div_nonneg (add_nonneg (mul_nonneg (hpos _).le hg0) (mul_nonneg (hpos _).le hg1))
      hmx0.le
  have hk1 : 0 ≤ k1 :=
    div_nonneg (add_nonneg (mul_nonneg (hpos _).le hg0) (mul_nonneg (hpos _).le hg1))
      hmx1.le
  have hsum : (∑ z : Cell, q z * (u z.1 / stoch_to_det.mX q z.1) ^ ((2 : ℝ) / 3)
        * (v z.2 / stoch_to_det.mY q z.2) ^ ((2 : ℝ) / 3))
      = stoch_to_det.mX q 0 * f0 * k0 + stoch_to_det.mX q 1 * f1 * k1 := by
    rw [sum_cells, hf0d, hf1d, hk0d, hk1d, hg0d, hg1d]
    field_simp
    ring
  rw [hsum]
  have hh := holder_two_point (stoch_to_det.mX q 0) (stoch_to_det.mX q 1) f0 f1
    k0 k1 hmx0.le hmx1.le hf0 hf1 hk0 hk1
  have hf0c : f0 ^ ((3 : ℝ) / 2) = u 0 / stoch_to_det.mX q 0 :=
    rpow_two_thirds_cancel (div_nonneg (hu.nonneg _) hmx0.le)
  have hf1c : f1 ^ ((3 : ℝ) / 2) = u 1 / stoch_to_det.mX q 1 :=
    rpow_two_thirds_cancel (div_nonneg (hu.nonneg _) hmx1.le)
  have hA : stoch_to_det.mX q 0 * f0 ^ ((3 : ℝ) / 2)
      + stoch_to_det.mX q 1 * f1 ^ ((3 : ℝ) / 2) = 1 := by
    rw [hf0c, hf1c, mul_div_cancel₀ _ hmx0.ne', mul_div_cancel₀ _ hmx1.ne']
    exact bit_sum hu
  have hg0c : g0 ^ ((3 : ℝ) / 2) = v 0 / stoch_to_det.mY q 0 :=
    rpow_two_thirds_cancel (div_nonneg (hv.nonneg _) hmy0.le)
  have hg1c : g1 ^ ((3 : ℝ) / 2) = v 1 / stoch_to_det.mY q 1 :=
    rpow_two_thirds_cancel (div_nonneg (hv.nonneg _) hmy1.le)
  have hV : (stoch_to_det.mY q 0 * g0 ^ ((3 : ℝ) / 2)
      + stoch_to_det.mY q 1 * g1 ^ ((3 : ℝ) / 2)) ^ 2 = 1 := by
    rw [hg0c, hg1c, mul_div_cancel₀ _ hmy0.ne', mul_div_cancel₀ _ hmy1.ne',
      bit_sum hv]
    norm_num
  have hB : stoch_to_det.mX q 0 * k0 ^ 3 + stoch_to_det.mX q 1 * k1 ^ 3 ≤ 1 := by
    have hn := cube_bound hpos hq hgate hg0 hg1
    rw [hV] at hn
    exact hn
  have hB0 : 0 ≤ stoch_to_det.mX q 0 * k0 ^ 3 + stoch_to_det.mX q 1 * k1 ^ 3 := by
    positivity
  calc stoch_to_det.mX q 0 * f0 * k0 + stoch_to_det.mX q 1 * f1 * k1
      ≤ (stoch_to_det.mX q 0 * f0 ^ ((3 : ℝ) / 2)
          + stoch_to_det.mX q 1 * f1 ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)
        * (stoch_to_det.mX q 0 * k0 ^ 3
          + stoch_to_det.mX q 1 * k1 ^ 3) ^ ((1 : ℝ) / 3) := hh
    _ = (stoch_to_det.mX q 0 * k0 ^ 3
          + stoch_to_det.mX q 1 * k1 ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [hA, Real.one_rpow, one_mul]
    _ ≤ 1 := Real.rpow_le_one hB0 hB (by norm_num)

end StochasticToDeterministicLatents.Binary
