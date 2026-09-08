/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  Two of the private working
material's four theorems become private here, and the numeric bound its
balanced value rests on, which a previous module left behind, is supplied and
kept private.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterSeamDerivative
import StochasticToDeterministicLatents.Binary.FactorTwo.CenterMajorant
import StochasticToDeterministicLatents.Binary.FactorTwo.Planes
import StochasticToDeterministicLatents.Binary.FactorTwo.LogValues

/-!
# The margin along the seam

Every law whose off-diagonal mass is one eighth of the whole meets the seam,
and on the seam the isolating code's margin depends on the radius alone.  This
module bounds it below, closing the seam.

The argument has three steps.  At the balanced radius, where the two
off-diagonal cells are equal, the margin is bounded below by a fixed reference
plane, and that bound is a rational combination of six logarithms, which the
enclosures of `3`, `5` and `7` settle, `Real.log 2` coming from Mathlib: it
exceeds `1 / 250` nats.  Away from the balanced
radius the margin's derivative exists and is positive, so the margin is
monotone from the balanced radius outward.  And every law on the seam has
radius at least the balanced one, since the squared imbalance is a square.

`seamSingletonScalar_monotoneOn` is the statement `CenterSeamDerivative`
supplied a derivative for and deliberately did not draw;
`seam_singletonMargin_gt` is the bound itself, in bits.

**This is the bound half of the page's Proposition 4.6, and only that** --
the constant of its display (4.17), which in the prime basis is exactly the
page's, and which bounds the balanced law's margin below.  The page's quadratic growth in
the imbalance is not claimed anywhere here; monotonicity in the radius takes
its place, and the two are not the same statement.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u r rb R : ℝ}

/-! ## The value at the balanced radius

The bound is one comparison of six logarithms against a rational.  Each
logarithm is resolved over the prime basis and the enclosures of `3`, `5` and
`7` do the rest, `Real.log 2` coming from Mathlib.  Over that basis the
combination is `(204 log 2 - 50 log 3 - 96 log 5 + 35 log 7) / 16`, which is
the constant the page's display (4.17) names. -/

/-- The rational lower bound the balanced seam's plane comparison reduces to.
-/
private theorem balancedSeam_scalar_ge :
    (1 / 4 : ℝ) * Real.log (8 / 375) - 3 / 8 * Real.log (1 / 16)
        - 49 / 16 * Real.log (7 / 16) - 9 / 16 * Real.log (9 / 16)
        - 7 / 4 * Real.log (375 / 343) - 4 * Real.log 2
      ≥ 36063 / 8000000 := by
  have e8375 : Real.log (8 / 375 : ℝ) = 3 * Real.log 2 - Real.log 3
      - 3 * Real.log 5 := by
    rw [show (8 / 375 : ℝ) = 2 ^ 3 / (3 ^ 1 * 5 ^ 3) by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have e116 : Real.log (1 / 16 : ℝ) = -4 * Real.log 2 := by
    rw [show (1 / 16 : ℝ) = 1 / 2 ^ 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_one]
    push_cast
    ring
  have e716 : Real.log (7 / 16 : ℝ) = -4 * Real.log 2 + Real.log 7 := by
    rw [show (7 / 16 : ℝ) = 7 ^ 1 / 2 ^ 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have e916 : Real.log (9 / 16 : ℝ) = -4 * Real.log 2 + 2 * Real.log 3 := by
    rw [show (9 / 16 : ℝ) = 3 ^ 2 / 2 ^ 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have e375343 : Real.log (375 / 343 : ℝ) = Real.log 3 + 3 * Real.log 5
      - 3 * Real.log 7 := by
    rw [show (375 / 343 : ℝ) = (3 ^ 1 * 5 ^ 3) / 7 ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  rw [e8375, e116, e716, e916, e375343]
  linarith [log_three_bounds.1, log_three_bounds.2, log_five_bounds.1,
    log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2,
    Real.log_two_gt_d9, Real.log_two_lt_d9]

/-! ## The plane comparison at the seam's balanced law -/

/-- **A reference plane bounds the contact's `Phi` for any law whose chord at
its midpoint is the balanced seam law.**  The two diagonal cells carry seven
sixteenths each and the two off-diagonal cells one sixteenth each, so the
pairing collapses to three rational multiples of the plane's three values. -/
private theorem seam_phi_le_plane (i : Fin 4) (h : ChordDomain p u)
    (hp0 : chordAt p (chordMidpoint p) = seamLaw 0) :
    Phi (contactAt p u)
      ≤ 7 / 8 * Real.logb 2 (referencePlanes i).diagValue
        - 1 / 16 * Real.logb 2 (referencePlanes i).offValueB
        - 1 / 16 * Real.logb 2 (referencePlanes i).offValueC := by
  have hm := phi_contact_le_chordMidpoint_pairing h (chordDomain_referencePlane i)
  obtain ⟨v00, v11, v01, v10⟩ := tangentCert_referencePlane i
  rw [hp0, Fintype.sum_prod_type] at hm
  simp only [Fin.sum_univ_two, v00, v11, v01, v10, seamLaw, tableOfEntries] at hm
  norm_num at hm
  linarith

/-! ## The margin at the balanced radius -/

/-- **At the balanced radius the isolating code's margin exceeds `1 / 250`
nats.**  The two off-diagonal cells are equal there, the law is the balanced
seam law, and the first reference plane supplies the bound. -/
private theorem seamSingletonScalar_gt_of_balanced
    (hb : rb ∈ Set.Ioo ((1 : ℝ) / 2) 1) (hzero : seamImbalanceSq rb = 0) :
    (1 : ℝ) / 250 < seamSingletonScalar rb := by
  have hh : 0 ≤ seamImbalanceSq rb := hzero.ge
  obtain ⟨hz, hdom, _, hU, hV, hray⟩ := rayValues_of_seamRadius hb hh
  have hsqrt : Real.sqrt (seamImbalanceSq rb) = 0 := by
    rw [hzero, Real.sqrt_zero]
  have hr0 : rb ≠ 0 := by
    have := hb.1
    intro hc
    rw [hc] at this
    linarith
  have hcd : ChordDomain (rayLaw 0 rb) (rayRoot 0 rb) := by
    simpa [hsqrt] using chordDomain_rayLaw hz hdom
  have hray0 : rayLaw 0 rb = seamLaw 0 := by simpa [hsqrt] using hray
  have hU0 : rayRoot 0 rb = 1 / (8 * rb) := by simpa [hsqrt] using hU
  have hV0 : rayMass 0 rb = 1 / 8 := by simpa [hsqrt] using hV
  have hp0 : chordAt (rayLaw 0 rb) (chordMidpoint (rayLaw 0 rb)) = seamLaw 0 := by
    rw [hray0]
    funext a
    obtain ⟨x, y⟩ := a
    fin_cases x <;> fin_cases y <;>
      simp [chordAt, chordMidpoint, diagonalMass, entryA, entryD, seamLaw,
        tableOfEntries]
  have hplane := seam_phi_le_plane 0 hcd hp0
  have hheight := log_two_mul_phi_contact_chart hcd
  have hx : entryB (rayLaw 0 rb) / rayRoot 0 rb = rb / 2 := by
    rw [hU0]
    simp [entryB, rayLaw, tableOfEntries, hV0]
    field_simp [hr0]
  have hy : entryC (rayLaw 0 rb) / rayRoot 0 rb = rb / 2 := by
    rw [hU0]
    simp [entryC, rayLaw, tableOfEntries, hV0]
    field_simp [hr0]
  have hT : seamSingletonScalar rb
      = centerSingletonScalar (1 / 8) 0
        (Real.log 2 * Phi (contactAt (rayLaw 0 rb) (rayRoot 0 rb))) := by
    unfold seamSingletonScalar seamCellB seamCellC
    rw [hsqrt]
    norm_num
    rw [hheight, hx, hy]
  rw [hT]
  have hK : (referencePlanes 0).diagValue = (375 / 343 : ℝ) := by rfl
  have hB : (referencePlanes 0).offValueB = (8 / 375 : ℝ) := by rfl
  have hC : (referencePlanes 0).offValueC = (8 / 375 : ℝ) := by rfl
  rw [hK, hB, hC] at hplane
  simp only [Real.logb] at hplane
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hplane' := mul_le_mul_of_nonneg_left hplane hlog.le
  field_simp [hlog.ne'] at hplane'
  ring_nf at hplane'
  unfold centerSingletonScalar centerLogEntropy centerMarginalEntropy xLogX
  norm_num
  have hhalf : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  linarith [balancedSeam_scalar_ge, hplane', hhalf]

/-! ## From the balanced radius outward -/

/-- Every radius from the balanced one up stays in the seam's interval and has
a nonnegative squared imbalance. -/
private theorem seam_radius_mem (hb : rb ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hzero : seamImbalanceSq rb = 0) (hR : R ∈ Set.Ico rb 1) :
    ∀ r ∈ Set.Icc rb R, 0 ≤ seamImbalanceSq r ∧ r ∈ Set.Ioo ((1 : ℝ) / 2) 1 := by
  intro r hr
  have hr' : r ∈ Set.Ioo ((1 : ℝ) / 2) 1 :=
    ⟨lt_of_lt_of_le hb.1 hr.1, lt_of_le_of_lt hr.2 hR.2⟩
  have hm := seamImbalanceSq_strictMonoOn.monotoneOn hb hr' hr.1
  exact ⟨by rw [hzero] at hm; exact hm, hr'⟩

/-- The margin's closed form, with every logarithm named.  It agrees with
`seamSingletonScalar` wherever the squared imbalance is nonnegative, and unlike
it is visibly continuous. -/
private noncomputable def seamSingletonForm (r : ℝ) : ℝ :=
  centerSingletonScalar (1 / 8) (Real.sqrt (seamImbalanceSq r))
    (-(-(7 / 8) * Real.log (certDiagonal (7 / 8) (1 / (8 * r)))
      + xLogX ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
      + xLogX ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
      + (1 / 4) * Real.log (1 - r)
      - 2 * ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
          * Real.log (1 - seamCellB r)
      - 2 * ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
          * Real.log (1 - seamCellC r)))

private theorem seamSingletonScalar_eq_form (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hh : 0 ≤ seamImbalanceSq r) : seamSingletonScalar r = seamSingletonForm r := by
  unfold seamSingletonScalar seamSingletonForm
  rw [seamHeight_eq hr hh]

/-- The isolating code's seam form is continuous on a closed subinterval. -/
private theorem seamSingletonForm_continuousOn (hb : rb ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hzero : seamImbalanceSq rb = 0) (hR : R ∈ Set.Ico rb 1) :
    ContinuousOn seamSingletonForm (Set.Icc rb R) := by
  set S := Set.Icc rb R with hS
  have hmem := seam_radius_mem hb hzero hR
  have hhcont : ContinuousOn seamImbalanceSq S := fun r hr =>
    ((hasDerivAt_seamImbalanceSq (hmem r hr).2).continuousAt).continuousWithinAt
  have hZ : ContinuousOn (fun r => Real.sqrt (seamImbalanceSq r)) S :=
    Real.continuous_sqrt.comp_continuousOn hhcont
  have hplus : ContinuousOn (fun r => (1 + Real.sqrt (seamImbalanceSq r)) / 16) S :=
    (continuousOn_const.add hZ).div_const 16
  have hminus : ContinuousOn (fun r => (1 - Real.sqrt (seamImbalanceSq r)) / 16) S :=
    (continuousOn_const.sub hZ).div_const 16
  have hrcont : ContinuousOn (fun r : ℝ => 1 / (8 * r)) S :=
    continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun r hr => by have := (hmem r hr).2.1; positivity)
  have hK : ContinuousOn (fun r => certDiagonal (7 / 8) (1 / (8 * r))) S := by
    unfold certDiagonal
    apply (continuousOn_const.add (continuousOn_const.mul hrcont)).div
      ((continuousOn_const.add hrcont).pow 2)
    intro r hr
    have hrp := (hmem r hr).2.1
    have hpos : 0 < (7 / 8 : ℝ) + 1 / (8 * r) := by positivity
    exact pow_ne_zero 2 hpos.ne'
  have hlogK := hK.log (fun r hr => by
    have hrp := (hmem r hr).2.1
    unfold certDiagonal
    positivity)
  have hlogr : ContinuousOn (fun r : ℝ => Real.log (1 - r)) S :=
    (continuousOn_const.sub continuousOn_id).log (fun r hr => by
      have ht := (hmem r hr).2.2
      show 1 - r ≠ 0
      linarith)
  have hsx : ContinuousOn seamCellB S := by
    unfold seamCellB
    exact (continuousOn_id.mul (continuousOn_const.add hZ)).div_const 2
  have hsy : ContinuousOn seamCellC S := by
    unfold seamCellC
    exact (continuousOn_id.mul (continuousOn_const.sub hZ)).div_const 2
  have hlogx : ContinuousOn (fun r => Real.log (1 - seamCellB r)) S :=
    (continuousOn_const.sub hsx).log (fun r hr => by
      obtain ⟨hc, _, _, _, _, _⟩ := rayValues_of_seamRadius (hmem r hr).2 (hmem r hr).1
      unfold seamCellB
      have hrp := (hmem r hr).2.1
      have hrlt := (hmem r hr).2.2
      have hm : r * (1 + Real.sqrt (seamImbalanceSq r)) < 1 * 2 :=
        mul_lt_mul hrlt (by linarith [hc.2]) (by positivity) (by linarith)
      show 1 - r * (1 + Real.sqrt (seamImbalanceSq r)) / 2 ≠ 0
      linarith)
  have hlogy : ContinuousOn (fun r => Real.log (1 - seamCellC r)) S :=
    (continuousOn_const.sub hsy).log (fun r hr => by
      obtain ⟨hc, _, _, _, _, _⟩ := rayValues_of_seamRadius (hmem r hr).2 (hmem r hr).1
      unfold seamCellC
      have hrp := (hmem r hr).2.1
      have hrlt := (hmem r hr).2.2
      have hz0 := Real.sqrt_nonneg (seamImbalanceSq r)
      have hfac0 : 0 ≤ 1 - Real.sqrt (seamImbalanceSq r) := by linarith [hc.2]
      have hmle : r * (1 - Real.sqrt (seamImbalanceSq r)) ≤ r * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      show 1 - r * (1 - Real.sqrt (seamImbalanceSq r)) / 2 ≠ 0
      linarith)
  have hJ : ContinuousOn
      (fun r => centerLogEntropy (1 / 8) (Real.sqrt (seamImbalanceSq r))) S := by
    unfold centerLogEntropy
    exact ((continuousOn_const.add (continuousOn_xLogX
      ((continuousOn_const.mul (continuousOn_const.add hZ)).div_const 2))).add
      (continuousOn_xLogX
        ((continuousOn_const.mul (continuousOn_const.sub hZ)).div_const 2))).neg
  have hRfun : ContinuousOn
      (fun r => centerMarginalEntropy (1 / 8) (Real.sqrt (seamImbalanceSq r))) S := by
    unfold centerMarginalEntropy
    exact ((continuousOn_xLogX ((continuousOn_const.add
      (continuousOn_const.mul hZ)).div_const 2)).add
      (continuousOn_xLogX ((continuousOn_const.sub
        (continuousOn_const.mul hZ)).div_const 2))).neg
  have hbody : ContinuousOn (fun r =>
      -(-(7 / 8) * Real.log (certDiagonal (7 / 8) (1 / (8 * r)))
        + xLogX ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
        + xLogX ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
        + (1 / 4) * Real.log (1 - r)
        - 2 * ((1 + Real.sqrt (seamImbalanceSq r)) / 16)
            * Real.log (1 - seamCellB r)
        - 2 * ((1 - Real.sqrt (seamImbalanceSq r)) / 16)
            * Real.log (1 - seamCellC r))) S :=
    (((((continuousOn_const.mul hlogK).add (continuousOn_xLogX hplus)).add
      (continuousOn_xLogX hminus)).add
      (continuousOn_const.mul hlogr)).sub
      ((continuousOn_const.mul hplus).mul hlogx)).sub
      ((continuousOn_const.mul hminus).mul hlogy) |>.neg
  unfold seamSingletonForm centerSingletonScalar
  exact ((((continuousOn_const.mul hJ).sub (continuousOn_const.mul hRfun)).sub
    (continuousOn_const.mul hbody)).sub continuousOn_const).sub continuousOn_const

private theorem seamSingletonScalar_continuousOn (hb : rb ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hzero : seamImbalanceSq rb = 0) (hR : R ∈ Set.Ico rb 1) :
    ContinuousOn seamSingletonScalar (Set.Icc rb R) :=
  (seamSingletonForm_continuousOn hb hzero hR).congr (fun r hr =>
    seamSingletonScalar_eq_form (seam_radius_mem hb hzero hR r hr).2
      (seam_radius_mem hb hzero hR r hr).1)

/-- **The isolating code's margin increases along the seam.**  From the
balanced radius outward the margin's derivative is a positive multiple of the
logarithm `seam_logRatio_pos` bounds below, so it is nonnegative, and the
margin is continuous at the balanced radius itself, where the derivative does
not exist. -/
theorem seamSingletonScalar_monotoneOn (hb : rb ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hzero : seamImbalanceSq rb = 0) (hR : R ∈ Set.Ico rb 1) :
    MonotoneOn seamSingletonScalar (Set.Icc rb R) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc rb R)
    (seamSingletonScalar_continuousOn hb hzero hR)
  · intro r hr
    rw [interior_Icc] at hr
    have hr' : r ∈ Set.Ioo ((1 : ℝ) / 2) 1 :=
      ⟨lt_trans hb.1 hr.1, lt_trans hr.2 hR.2⟩
    have hhlt := seamImbalanceSq_strictMonoOn hb hr' hr.1
    have hh : 0 < seamImbalanceSq r := by rw [hzero] at hhlt; exact hhlt
    exact (hasDerivAt_seamSingletonScalar hr' hh).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    have hr' : r ∈ Set.Ioo ((1 : ℝ) / 2) 1 :=
      ⟨lt_trans hb.1 hr.1, lt_trans hr.2 hR.2⟩
    have hhlt := seamImbalanceSq_strictMonoOn hb hr' hr.1
    have hh : 0 < seamImbalanceSq r := by rw [hzero] at hhlt; exact hhlt
    have hp : 0 < seamImbalanceSqDeriv r := by
      unfold seamImbalanceSqDeriv
      have hn : 0 < 1 + 10 * r - 7 * r ^ 2 := by nlinarith [hr'.1, hr'.2]
      apply div_pos (mul_pos (by norm_num) hn)
      have hr0 : 0 < r := by linarith [hr'.1]
      have hd : 0 < 1 + 7 * r := by linarith [hr'.1]
      positivity
    exact mul_nonneg (div_nonneg hp.le (by positivity))
      (seam_logRatio_pos hr' hh).le

/-! ## The seam's bound -/

/-- **Every law on the seam gives the isolating code a margin above
`1 / (250 log 2)` bits at its chord's midpoint.**  The law's radius is at
least the balanced one because the squared imbalance is a square; the margin
increases from there; and at the balanced radius the first reference plane
bounds it.  This is the bound of the page's display (4.17) and not its
quadratic growth term. -/
theorem seam_singletonMargin_gt (h : ChordDomain p u)
    (hv : offDiagonalMass p = 1 / 8) :
    (1 : ℝ) / (250 * Real.log 2) < singletonMargin p u (chordMidpoint p) := by
  obtain ⟨rb, hb0, hzero⟩ := exists_balanced_seamRadius
  have hb : rb ∈ Set.Ioo ((1 : ℝ) / 2) 1 := ⟨hb0.1, by linarith [hb0.2]⟩
  obtain ⟨hr, _, hh, hT⟩ := chordDomain_seamCoordinates h hv
  have hrb : rb ≤ offDiagonalMass p / u := by
    by_contra hn
    have hlt : offDiagonalMass p / u < rb := lt_of_not_ge hn
    have hm := seamImbalanceSq_strictMonoOn hr hb hlt
    rw [hzero, hh] at hm
    nlinarith [sq_nonneg ((entryB p - entryC p) / offDiagonalMass p)]
  have hmono := seamSingletonScalar_monotoneOn hb hzero
    (show offDiagonalMass p / u ∈ Set.Ico rb 1 from ⟨hrb, hr.2⟩)
  have hle : seamSingletonScalar rb ≤ seamSingletonScalar (offDiagonalMass p / u) :=
    hmono ⟨le_rfl, hrb⟩ ⟨hrb, le_rfl⟩ hrb
  have hbal := seamSingletonScalar_gt_of_balanced hb hzero
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  rw [hT] at hle
  rw [div_lt_iff₀ (mul_pos (by norm_num) hlog)]
  nlinarith

end StochasticToDeterministicLatents.Binary
