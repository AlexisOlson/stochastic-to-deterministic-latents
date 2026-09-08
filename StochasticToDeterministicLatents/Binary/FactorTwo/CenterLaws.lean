/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Four definitions of the
private working material are dropped as already public here: the two
certificate values, the entropy term, and the cell constructor.  One statement
is lifted forward from a later private module, where it sits only by import
layering.
-/
import StochasticToDeterministicLatents.Binary.ContactChart
import StochasticToDeterministicLatents.Binary.FactorTwo.CertValues
import StochasticToDeterministicLatents.Binary.FactorTwo.Chord
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterRay

/-!
# The chart and the laws it describes

The chart modules of this directory work in the two rescaled off-diagonal
cells `x` and `y`, or in their symmetric functions `r = x + y` and
`omega = x * y`, and no declaration in them mentions a law.  This module
supplies the correspondence, in both directions:

* a chord domain's rescaled cells lie in the chart domain, and its top root is
  the chart's root;
* the certificate values of its contact have closed forms in the chart, and so
  does the contact's own height;
* a radius below the critical one puts a ray's parameters in the chart domain,
  and the law there is a chord domain.

The last two compose: together they are the first statement in this tree that
a chart result applies to a law.  Nothing here differentiates anything.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u x y z r : ℝ}

/-! ## The height in the chart -/

/-- The height of a chord domain's contact, in the chart and in nats. -/
noncomputable def chartHeight (x y : ℝ) : ℝ :=
  -chartDiagonalMass (x + y) (x * y)
      * Real.log (certDiagonal (chartDiagonalMass (x + y) (x * y))
          (chartRoot (x + y) (x * y)))
    + xLogX (x * chartRoot (x + y) (x * y))
    + xLogX (y * chartRoot (x + y) (x * y))
    + 2 * chartOffDiagonalMass (x + y) (x * y) * Real.log (1 - (x + y))
    - 2 * (x * chartRoot (x + y) (x * y)) * Real.log (1 - x)
    - 2 * (y * chartRoot (x + y) (x * y)) * Real.log (1 - y)

/-! ## The certificate values in the chart -/

private theorem chartRoot_mul_norm (hx : 0 < x) (hy : 0 < y) (hr : x + y < 1) :
    chartRoot (x + y) (x * y) * ((1 - x - y) * (1 - x * y)) = x * y := by
  have hxy : (0 : ℝ) < 1 - x * y := by nlinarith
  have hD : (0 : ℝ) < 1 - x - y := by linarith
  unfold chartRoot chartNorm
  rw [show 1 - (x + y) = 1 - x - y by ring]
  field_simp

private theorem chartRoot_pos_of_cells (hx : 0 < x) (hy : 0 < y)
    (hr : x + y < 1) : 0 < chartRoot (x + y) (x * y) := by
  have hxy : (0 : ℝ) < 1 - x * y := by nlinarith
  unfold chartRoot chartNorm
  rw [show 1 - (x + y) = 1 - x - y by ring]
  exact div_pos (mul_pos hx hy) (mul_pos (by linarith) hxy)

private theorem certValues_of_root (hx : 0 < x) (hy : 0 < y) (hr : x + y < 1)
    (hu_pos : 0 < u) (hu : u * ((1 - x - y) * (1 - x * y)) = x * y) :
    certDiagonal (1 - x * u - y * u) u
        = (1 - x) * (1 - y) * (1 - x * y) / (1 - x - y)
      ∧ certOffDiagonal (x * u) (y * u) u
        = x * u * (1 - x - y) ^ 2 / (1 - x) ^ 2
      ∧ certOffDiagonal (y * u) (x * u) u
        = y * u * (1 - x - y) ^ 2 / (1 - y) ^ 2 := by
  have hD : (0 : ℝ) < 1 - x - y := by linarith
  have hxy : (0 : ℝ) < 1 - x * y := by nlinarith
  have hD1 : (1 : ℝ) - x - y ≠ 0 := hD.ne'
  have hxy1 : (1 : ℝ) - x * y ≠ 0 := hxy.ne'
  have hx10 : (1 : ℝ) - x ≠ 0 := by
    have : (0 : ℝ) < 1 - x := by linarith
    exact this.ne'
  have hy10 : (1 : ℝ) - y ≠ 0 := by
    have : (0 : ℝ) < 1 - y := by linarith
    exact this.ne'
  have hu0 : u ≠ 0 := hu_pos.ne'
  have hsu : 1 - x * u - y * u + u = 1 / (1 - x * y) := by
    rw [eq_div_iff hxy1]
    linear_combination hu
  have hs2 : 1 - x * u - y * u + 2 * u
      = (1 - x) * (1 - y) / ((1 - x - y) * (1 - x * y)) := by
    rw [eq_div_iff (mul_ne_zero hD1 hxy1)]
    linear_combination (2 - x - y) * hu
  have hq : u ^ 2 + x * u - x * u * (y * u) = u * x * (1 - x) / (1 - x - y) := by
    rw [eq_div_iff hD1]
    linear_combination u * hu
  have hq' : u ^ 2 + y * u - y * u * (x * u) = u * y * (1 - y) / (1 - x - y) := by
    rw [eq_div_iff hD1]
    linear_combination u * hu
  refine ⟨?_, ?_, ?_⟩
  · unfold certDiagonal
    rw [hs2, hsu]
    field_simp
  · unfold certOffDiagonal
    rw [hq]
    field_simp
  · unfold certOffDiagonal
    rw [hq']
    field_simp

/-- The page's display (3.5), in the chart: the diagonal certificate value and
the two off-diagonal ones.  The page states the contact masses `P_b` and
`P_c`; these are `b ^ 3 / P_b ^ 2` and `c ^ 3 / P_c ^ 2`. -/
theorem chart_certValues (hx : 0 < x) (hy : 0 < y) (hr : x + y < 1) :
    certDiagonal (chartDiagonalMass (x + y) (x * y))
          (chartRoot (x + y) (x * y))
        = (1 - x) * (1 - y) * (1 - x * y) / (1 - x - y)
      ∧ certOffDiagonal (x * chartRoot (x + y) (x * y))
          (y * chartRoot (x + y) (x * y)) (chartRoot (x + y) (x * y))
        = x * chartRoot (x + y) (x * y) * (1 - x - y) ^ 2 / (1 - x) ^ 2
      ∧ certOffDiagonal (y * chartRoot (x + y) (x * y))
          (x * chartRoot (x + y) (x * y)) (chartRoot (x + y) (x * y))
        = y * chartRoot (x + y) (x * y) * (1 - x - y) ^ 2 / (1 - y) ^ 2 := by
  have hs : chartDiagonalMass (x + y) (x * y)
      = 1 - x * chartRoot (x + y) (x * y) - y * chartRoot (x + y) (x * y) := by
    unfold chartDiagonalMass chartOffDiagonalMass
    ring
  rw [hs]
  exact certValues_of_root hx hy hr (chartRoot_pos_of_cells hx hy hr)
    (chartRoot_mul_norm hx hy hr)

/-! ## A chord domain, read in the chart -/

/-- The forward direction of the page's Lemma 3.3: a chord domain's
rescaled off-diagonal cells are positive and ordered, they lie in the
chart domain, and its top root is the chart's root. -/
theorem chartDomain_of_chordDomain (h : ChordDomain p u) :
    0 < entryC p / u ∧ entryC p / u ≤ entryB p / u
      ∧ ChartDomain (entryB p / u + entryC p / u)
          (entryB p / u * (entryC p / u))
      ∧ u = chartRoot (entryB p / u + entryC p / u)
          (entryB p / u * (entryC p / u)) := by
  have hu : 0 < u := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hu0 : u ≠ 0 := hu.ne'
  have hb : 0 < entryB p := h.fullSupport (0, 1)
  have hc : 0 < entryC p := h.fullSupport (1, 0)
  have hsum : diagonalMass p = 1 - entryB p - entryC p := by
    have hs := diagonalMass_add_offDiagonalMass h.isPMF
    unfold offDiagonalMass at hs
    linarith
  have hcub : u ^ 3 - (entryB p + entryC p) * u ^ 2 - entryB p * entryC p * u
      - entryB p * entryC p * (1 - entryB p - entryC p) = 0 := by
    have hz := h.topRoot.2.1
    unfold cubic offDiagonalMass at hz
    rw [offDiagonalProduct_eq, hsum] at hz
    linear_combination hz
  have hmid : 2 * u < 1 - entryB p - entryC p := by
    have hm := topRoot_lt_chordMidpoint h
    unfold chordMidpoint at hm
    rw [hsum] at hm
    linarith
  have hvu : entryB p + entryC p < u := by
    have hv := offDiagonalMass_lt_topRoot h.isPMF h.fullSupport h.topRoot
    unfold offDiagonalMass at hv
    linarith
  have hxpos : 0 < entryB p / u := div_pos hb hu
  have hypos : 0 < entryC p / u := div_pos hc hu
  have hrlt : entryB p / u + entryC p / u < 1 := by
    rw [show entryB p / u + entryC p / u = (entryB p + entryC p) / u by ring,
      div_lt_one hu]
    exact hvu
  have hfac : (u - entryB p - entryC p) * (u ^ 2 - entryB p * entryC p)
      = entryB p * entryC p := by linear_combination hcub
  refine ⟨hypos, (div_le_div_iff_of_pos_right hu).2 h.offDiagonal_le, ?_, ?_⟩
  · refine ⟨mul_pos hxpos hypos, add_pos hxpos hypos, hrlt, ?_, ?_⟩
    · have key : (1 - (entryB p / u + entryC p / u)
          - 3 * (entryB p / u * (entryC p / u))) * u ^ 3
          = entryB p * entryC p * (1 - entryB p - entryC p - 2 * u) := by
        field_simp
        linear_combination hcub
      have hrhs : 0 < entryB p * entryC p * (1 - entryB p - entryC p - 2 * u) :=
        mul_pos (mul_pos hb hc) (by linarith)
      nlinarith [key, pow_pos hu 3]
    · nlinarith [sq_nonneg (entryB p / u - entryC p / u)]
  · have hfirst : 0 < 1 - (entryB p / u + entryC p / u) := by linarith
    have hsecond : 0 < 1 - entryB p / u * (entryC p / u) := by
      have hx1 : entryB p / u < 1 := by linarith
      have hy1 : entryC p / u < 1 := by linarith
      nlinarith
    have hne : chartNorm (entryB p / u + entryC p / u)
        (entryB p / u * (entryC p / u)) ≠ 0 := by
      unfold chartNorm
      exact (mul_pos hfirst hsecond).ne'
    unfold chartRoot
    rw [eq_div_iff hne]
    unfold chartNorm
    field_simp
    linear_combination hfac

/-- The height of a chord domain's contact, in the chart.  The public `Phi` is
the negative of the private material's height, so the identity carries a
minus.  Both sides are in nats. -/
theorem log_two_mul_phi_contact_chart (h : ChordDomain p u) :
    Real.log 2 * Phi (contactAt p u)
      = -chartHeight (entryB p / u) (entryC p / u) := by
  have hu : 0 < u := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hu0 : u ≠ 0 := hu.ne'
  have hb : 0 < entryB p := h.fullSupport (0, 1)
  have hc : 0 < entryC p := h.fullSupport (1, 0)
  obtain ⟨hy, hyx, hdom, hinv⟩ := chartDomain_of_chordDomain h
  have hx : 0 < entryB p / u := lt_of_lt_of_le hy hyx
  have hqpmf : IsPMF (contactAt p u) :=
    isPMF_contactAt h.isPMF h.fullSupport hu h.nonconstant
  have hqpos : FullSupport (contactAt p u) := fun w =>
    contactAt_pos h.fullSupport hu h.nonconstant w
  have had : entryA (contactAt p u) * entryD (contactAt p u) = u ^ 2 := by
    have := chordTop_mul_chordBottom h
    unfold chordTop chordBottom at this
    exact this
  have hroot : cubic (contactAt p u) u = 0 := by
    rw [← chordAt_chordTop (p := p) (u := u), cubic_chordAt]
    exact h.topRoot.2.1
  have hbase := log_two_mul_phi_contact hqpmf hqpos hu had hroot
  have hsq : diagonalMass (contactAt p u) = diagonalMass p := by
    simp only [diagonalMass, entryA, entryD, contactAt]
    norm_num
    ring
  have hbq : entryB (contactAt p u) = entryB p := by
    simp [entryB, contactAt]
  have hcq : entryC (contactAt p u) = entryC p := by
    simp [entryC, contactAt]
  rw [hsq, hbq, hcq] at hbase
  have hsum : diagonalMass p = 1 - entryB p - entryC p := by
    have hs := diagonalMass_add_offDiagonalMass h.isPMF
    unfold offDiagonalMass at hs
    linarith
  have hxu : entryB p / u * u = entryB p := div_mul_cancel₀ _ hu0
  have hyu : entryC p / u * u = entryC p := div_mul_cancel₀ _ hu0
  have hcert := certValues_of_root hx hy hdom.sum_lt_one hu
    (by
      have := chartRoot_mul_norm hx hy hdom.sum_lt_one
      rw [← hinv] at this
      exact this)
  have hK : (1 : ℝ) - entryB p / u * u - entryC p / u * u = diagonalMass p := by
    rw [hxu, hyu, hsum]
  have hD1 : (1 : ℝ) - entryB p / u - entryC p / u ≠ 0 := by
    have : (0 : ℝ) < 1 - entryB p / u - entryC p / u := by
      have := hdom.sum_lt_one
      linarith
    exact this.ne'
  have hx10 : (1 : ℝ) - entryB p / u ≠ 0 := by
    have : (0 : ℝ) < 1 - entryB p / u := by
      have := hdom.sum_lt_one
      linarith
    exact this.ne'
  have hy10 : (1 : ℝ) - entryC p / u ≠ 0 := by
    have : (0 : ℝ) < 1 - entryC p / u := by
      have := hdom.sum_lt_one
      linarith
    exact this.ne'
  obtain ⟨hcK, hcLb, hcLc⟩ := hcert
  rw [hK] at hcK
  rw [hxu, hyu] at hcLb hcLc
  unfold chartHeight
  have hs : chartDiagonalMass (entryB p / u + entryC p / u)
      (entryB p / u * (entryC p / u)) = diagonalMass p := by
    unfold chartDiagonalMass chartOffDiagonalMass
    rw [← hinv, hsum]
    field_simp
    ring
  have hv : chartOffDiagonalMass (entryB p / u + entryC p / u)
      (entryB p / u * (entryC p / u)) = entryB p + entryC p := by
    unfold chartOffDiagonalMass
    rw [← hinv]
    field_simp
  rw [hs, hv, ← hinv, hxu, hyu, hbase, hcK, hcLb, hcLc]
  rw [Real.log_div (mul_ne_zero hb.ne' (pow_ne_zero 2 hD1)) (pow_ne_zero 2 hx10),
    Real.log_div (mul_ne_zero hc.ne' (pow_ne_zero 2 hD1)) (pow_ne_zero 2 hy10),
    Real.log_mul hb.ne' (pow_ne_zero 2 hD1),
    Real.log_mul hc.ne' (pow_ne_zero 2 hD1),
    Real.log_pow, Real.log_pow, Real.log_pow]
  unfold xLogX
  rw [show 1 - (entryB p / u + entryC p / u)
    = 1 - entryB p / u - entryC p / u by ring]
  ring

/-! ## The ray lies in the chart, and carries chord domains -/

/-- A radius strictly between zero and the critical one puts the ray's
parameters in the chart domain. -/
theorem chartDomain_ray (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : r ∈ Set.Ioo (0 : ℝ) (criticalRadius z)) :
    ChartDomain r (rayProductCoeff z * r ^ 2) := by
  have hk : 0 < rayProductCoeff z := by
    unfold rayProductCoeff
    have hp : (0 : ℝ) < 1 + z := by linarith [hz.1]
    nlinarith [mul_pos (sub_pos.mpr hz.2) hp]
  have hr1 : r < 1 := lt_trans hr.2 (criticalRadius_spec hz).2.1
  have hq : 0 < 1 - r - 3 * (rayProductCoeff z * r ^ 2) := by
    have hi := (radius_lt_criticalRadius_iff hz hr.1 hr1).mp hr.2
    linarith [hi, mul_assoc (3 : ℝ) (rayProductCoeff z) (r ^ 2)]
  refine ⟨mul_pos hk (pow_pos hr.1 2), hr.1, hr1, hq, ?_⟩
  unfold rayProductCoeff
  nlinarith [sq_nonneg (z * r)]

/-- The chart's root at a ray's cell coordinates is the ray's root.  This is
the form the radial modules consume. -/
theorem rayRoot_eq_chartRoot (z : ℝ) :
    (fun s : ℝ => chartRoot ((1 + z) * s / 2 + (1 - z) * s / 2)
      ((1 + z) * s / 2 * ((1 - z) * s / 2))) = rayRoot z := by
  funext s
  unfold rayRoot rayProductCoeff
  congr 1 <;> ring

/-- A ray law's own chart coordinates, rescaled by the ray's root, are the
radius and the ray's product.  Without this the chart's results would be about
a different pair of parameters from the ones the ray is indexed by. -/
theorem rayLaw_chartCoordinates (hr : ChartDomain r (rayProductCoeff z * r ^ 2)) :
    entryB (rayLaw z r) / rayRoot z r + entryC (rayLaw z r) / rayRoot z r = r
      ∧ entryB (rayLaw z r) / rayRoot z r
          * (entryC (rayLaw z r) / rayRoot z r) = rayProductCoeff z * r ^ 2 := by
  obtain ⟨-, hroot0, -, -, -, -, -⟩ := chart_pos hr
  have h0 : rayRoot z r ≠ 0 := hroot0.ne'
  have hV : rayMass z r = r * rayRoot z r := rfl
  have hB : entryB (rayLaw z r) = rayMass z r * (1 + z) / 2 := rfl
  have hC : entryC (rayLaw z r) = rayMass z r * (1 - z) / 2 := rfl
  rw [hB, hC, hV]
  unfold rayProductCoeff
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- A law on the ray, at a radius whose chart parameters lie in the chart
domain, is a chord domain with the ray's root. -/
theorem chordDomain_rayLaw (hz : z ∈ Set.Ico (0 : ℝ) 1)
    (hr : ChartDomain r (rayProductCoeff z * r ^ 2)) :
    ChordDomain (rayLaw z r) (rayRoot z r) := by
  obtain ⟨hnorm, hroot0, -, hmass0, -, -, -⟩ := chart_pos hr
  have hV : rayMass z r = r * rayRoot z r := rfl
  have hU : rayRoot z r * chartNorm r (rayProductCoeff z * r ^ 2)
      = rayProductCoeff z * r ^ 2 := by
    unfold rayRoot chartRoot
    exact div_mul_cancel₀ _ hnorm.ne'
  have hU0 : 0 < rayRoot z r := hroot0
  have hV0 : 0 < rayMass z r := hmass0
  have hq : 0 < 1 - r - 3 * (rayProductCoeff z * r ^ 2) := hr.interior
  have hs2 : 0 < 1 - rayMass z r - 2 * rayRoot z r := by
    have key : (1 - rayMass z r - 2 * rayRoot z r)
        * chartNorm r (rayProductCoeff z * r ^ 2)
        = 1 - r - 3 * (rayProductCoeff z * r ^ 2) := by
      rw [hV]
      unfold chartNorm at hU ⊢
      linear_combination (-r - 2) * hU
    by_contra hcon
    push Not at hcon
    nlinarith [key, mul_nonneg (neg_nonneg.mpr hcon) hnorm.le]
  have hrc : r < criticalRadius z :=
    (radius_lt_criticalRadius_iff hz hr.sum_pos hr.sum_lt_one).2
      (by rw [mul_assoc]; exact hq)
  have hzplus : (0 : ℝ) < 1 + z := by linarith [hz.1]
  have hzminus : (0 : ℝ) < 1 - z := sub_pos.mpr hz.2
  have hpmf := rayLaw_isPMF hz ⟨hr.sum_pos.le, hrc.le⟩
  have hA : entryA (rayLaw z r) = (1 - rayMass z r) / 2 := rfl
  have hB : entryB (rayLaw z r) = rayMass z r * (1 + z) / 2 := rfl
  have hC : entryC (rayLaw z r) = rayMass z r * (1 - z) / 2 := rfl
  have hD : entryD (rayLaw z r) = (1 - rayMass z r) / 2 := rfl
  have hprod : rayMass z r * (1 + z) / 2 * (rayMass z r * (1 - z) / 2)
      = rayProductCoeff z * r ^ 2 * rayRoot z r ^ 2 := by
    rw [hV]
    unfold rayProductCoeff
    ring
  refine ⟨hpmf.1, hpmf.2 hr.sum_pos, ?_, ?_, ?_, ?_, ?_⟩
  · unfold determinant diagonalProduct offDiagonalProduct
    rw [show (rayLaw z r) cell00 = (1 - rayMass z r) / 2 from hA,
      show (rayLaw z r) cell11 = (1 - rayMass z r) / 2 from hD,
      show (rayLaw z r) cell01 = rayMass z r * (1 + z) / 2 from hB,
      show (rayLaw z r) cell10 = rayMass z r * (1 - z) / 2 from hC, hprod]
    have hp1 : rayProductCoeff z * r ^ 2 < 1 := by nlinarith [hr.sum_pos, hq]
    have hhalf : rayRoot z r < (1 - rayMass z r) / 2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hhalf) (add_pos (lt_trans hU0 hhalf) hU0),
      mul_pos (sub_pos.mpr hp1) (pow_pos hU0 2)]
  · refine isTopRoot_of_pos_root ?_ ?_ hU0 ?_
    · rw [offDiagonalProduct_eq, hB, hC]
      exact (mul_pos (by positivity) (by positivity)).le
    · unfold diagonalMass
      rw [hA, hD]
      linarith
    · have hcubic : cubic (rayLaw z r) (rayRoot z r)
          = rayRoot z r ^ 2
            * (rayRoot z r * chartNorm r (rayProductCoeff z * r ^ 2)
                - rayProductCoeff z * r ^ 2) := by
        unfold cubic offDiagonalMass diagonalMass chartNorm
        rw [offDiagonalProduct_eq, hA, hB, hC, hD, hV]
        unfold rayProductCoeff
        ring
      rw [hcubic, hU]
      ring
  · unfold Nonconstant diagonalProduct
    rw [show (rayLaw z r) cell00 = (1 - rayMass z r) / 2 from hA,
      show (rayLaw z r) cell11 = (1 - rayMass z r) / 2 from hD,
      show (1 - rayMass z r) / 2 * ((1 - rayMass z r) / 2)
        = ((1 - rayMass z r) / 2) ^ 2 by ring,
      Real.sqrt_sq (by linarith : (0 : ℝ) ≤ (1 - rayMass z r) / 2)]
    linarith
  · rw [hA, hD]
  · rw [hB, hC]
    nlinarith [hV0, hz.1]

end StochasticToDeterministicLatents.Binary
