import StochasticToDeterministicLatents.Binary.FactorTwo.FixedCutConstant
import StochasticToDeterministicLatents.Binary.FactorTwo.SingletonMass
import StochasticToDeterministicLatents.Binary.FactorTwo.SingletonScore

/-!
# The singleton margin's lower bound at the fixed cut

This module is the singleton arm of the cut gates, the companion of
`ConstantBound`.  Its one export is `fixedCut_singletonMargin_gt`: below an
eighth of off-diagonal mass, the isolating code's margin at the fixed cut
exceeds the contact mass over a hundred, in natural-log units.

The route is longer than the constant arm's because the margin does not
reduce to the scalar by an identity alone.  The margin at the cut is first
written out in `pairInfo`, `binaryEntropyNat` and `cornerInfo` against the
chord potential at the contact mass.  Divided by the contact mass, that is
two copies of `singletonRatioTerm` plus a correction, and the correction is
bounded below by `singletonMassTerm` through four estimates: the corner
information at the upper contact is at least half the one at the cut, the
entropy of the contact mass has a quadratic tangent, `pairInfo` grows over an
interval by at most the slope at its left end times its length, and the two
cell logarithms are dominated by their mean.  `singletonTerms_gt` then bounds the three scalar
terms together, and what is left is `1 / 100`.

Nothing here is public but the bound, and it is stated multiplied through by
`Real.log 2`, as `ConstantBound`'s is.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable} {u : ℝ}

/-! ## Four scalar estimates -/

/-- Twice the corner information at a smaller first argument dominates the
one at a larger, when the larger is at least the smaller plus the two cells.
The two arguments here are the upper contact and the fixed cut. -/
private theorem cornerInfo_diff_nonneg {a a' b c : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (hb : 0 < b) (hc : 0 < c) (hle : a' + b + c ≤ 2 * a) :
    0 ≤ 2 * cornerInfo a' b c - cornerInfo a b c := by
  have hlow := (cornerInfo_bounds ha' hb hc).1
  have hhigh := (cornerInfo_bounds ha hb hc).2
  have hden : 0 < a' + b + c := add_pos (add_pos ha' hb) hc
  have hrat : b * c / a ≤ 2 * (b * c / (a' + b + c)) := by
    rw [show 2 * (b * c / (a' + b + c)) = 2 * (b * c) / (a' + b + c) by ring]
    refine (div_le_div_iff₀ ha hden).2 ?_
    nlinarith [mul_pos hb hc]
  linarith

/-- A quadratic tangent below `-log (1 - d)` on `[0, 1)`. -/
private theorem neg_log_one_sub_ge {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    d + d ^ 2 / 2 ≤ -Real.log (1 - d) := by
  let g : ℝ → ℝ := (-Real.log ∘ fun t => 1 - t) - id - fun t => t ^ 2 / 2
  have hg' (t : ℝ) (ht : t < 1) : HasDerivAt g (t ^ 2 / (1 - t)) t := by
    have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hlog := (Real.hasDerivAt_log (by linarith : 1 - t ≠ 0)).comp t hinner
    have hraw := ((hlog.neg.sub (hasDerivAt_id t)).sub
      (((hasDerivAt_id t).pow 2).div_const 2))
    have heq : -((1 - t)⁻¹ * -1) - 1 - (2 : ℝ) * t ^ (2 - 1) * 1 / 2
        = t ^ 2 / (1 - t) := by
      field_simp [show 1 - t ≠ 0 by linarith]
      ring
    exact hraw.congr_deriv heq
  have hmono : MonotoneOn g (Set.Icc 0 d) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 d)
    · intro t ht
      exact (hg' t (lt_of_le_of_lt ht.2 hd1)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hg' t (lt_trans ht.2 hd1)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact div_nonneg (sq_nonneg t) (by linarith [ht.2, hd1])
  have hg := hmono (by simp [hd0]) (by simp [hd0]) hd0
  dsimp [g] at hg
  norm_num [Real.log_one] at hg
  nlinarith

/-- The entropy term of the contact mass, divided by that mass, is at least a
quadratic. -/
private theorem entropyCorrection_ge {D : ℝ} (hD0 : 0 < D) (hD1 : D < 1) :
    2 - D - D ^ 2 ≤ -2 * (1 - D) * Real.log (1 - D) / D := by
  have hlog := neg_log_one_sub_ge hD0.le hD1
  have hfac : (0 : ℝ) < 2 * (1 - D) / D := by positivity
  have hm := mul_le_mul_of_nonneg_left hlog hfac.le
  calc
    2 - D - D ^ 2 = 2 * (1 - D) / D * (D + D ^ 2 / 2) := by
      field_simp [hD0.ne']
      ring
    _ ≤ 2 * (1 - D) / D * -Real.log (1 - D) := hm
    _ = -2 * (1 - D) * Real.log (1 - D) / D := by ring

/-- Two cell logarithms against a common denominator are dominated by twice
the one at their mean. -/
private theorem log_pair_le {T b c : ℝ} (hT : 0 < T) (hb : 0 < b) (hc : 0 < c) :
    Real.log (1 + b / T) + Real.log (1 + c / T)
      ≤ 2 * Real.log (1 + (b + c) / (2 * T)) := by
  have hleft1 : (0 : ℝ) < 1 + b / T := by positivity
  have hleft2 : (0 : ℝ) < 1 + c / T := by positivity
  have hprod : (1 + b / T) * (1 + c / T) ≤ (1 + (b + c) / (2 * T)) ^ 2 := by
    field_simp [hT.ne']
    nlinarith [sq_nonneg (b - c)]
  have hlog := Real.log_le_log (mul_pos hleft1 hleft2) hprod
  rw [Real.log_mul hleft1.ne' hleft2.ne', Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

/-! ## The margin at the cut, written out -/

/-- The isolating code's margin at the fixed cut, against the chord potential
at the contact mass. -/
private theorem log_two_mul_singletonMargin_fixedCut (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    Real.log 2 * singletonMargin p u (fixedCut p u)
      = 2 * (pairInfo (fixedCut p u) (entryB p) + pairInfo (fixedCut p u) (entryC p)
          - pairInfo (chordTop p u) (entryB p) - pairInfo (chordTop p u) (entryC p))
        + pairInfo (3 * chordBottom p u) (entryB p)
        + pairInfo (3 * chordBottom p u) (entryC p)
        - 4 * pairInfo (chordBottom p u) (entryB p)
        - 4 * pairInfo (chordBottom p u) (entryC p)
        + 2 * binaryEntropyNat (chordBottom p u)
        + 2 * cornerInfo (chordTop p u) (entryB p) (entryC p)
        - cornerInfo (fixedCut p u) (entryB p) (entryC p) := by
  have hcut := fixedCut_mem_chord h hv
  have hmem : fixedCut p u ∈ Set.Icc (chordMidpoint p) (chordTop p u) :=
    ⟨hcut.1.le, hcut.2.le⟩
  have hsum := diagonalMass_add_offDiagonalMass h.isPMF
  have hAD := chordTop_add_chordBottom (p := p) (u := u)
  have hsd : diagonalMass p - fixedCut p u = 3 * chordBottom p u := by
    rw [fixedCut]
    ring
  have habc : fixedCut p u + entryB p + entryC p = 1 - 3 * chordBottom p u := by
    rw [fixedCut, offDiagonalMass] at *
    linarith
  have hAbc : chordTop p u + entryB p + entryC p = 1 - chordBottom p u := by
    rw [offDiagonalMass] at hsum
    linarith
  rw [log_two_mul_singletonMargin h hmem, ← chordPotential_chordBottom h, chordPotential,
    show diagonalMass p - chordBottom p u = chordTop p u from by linarith,
    hsd, pairInfo, pairInfo, pairInfo, pairInfo, pairInfo, pairInfo, pairInfo, pairInfo,
    binaryEntropyNat, cornerInfo, cornerInfo, habc, hAbc]
  ring_nf

/-- The correction that separates the margin at the cut, divided by the
contact mass, from two copies of `singletonRatioTerm`. -/
private noncomputable def singletonCorrection (p : RealTable) (u : ℝ) : ℝ :=
  6 * Real.log (chordTop p u) - 4 * Real.log (chordTop p u + entryB p)
    - 4 * Real.log (chordTop p u + entryC p)
    - 2 * (1 - chordBottom p u) * Real.log (1 - chordBottom p u) / chordBottom p u
    + 2 / chordBottom p u * (pairInfo (fixedCut p u) (entryB p)
        + pairInfo (fixedCut p u) (entryC p) - pairInfo (chordTop p u) (entryB p)
        - pairInfo (chordTop p u) (entryC p))
    + (2 * cornerInfo (chordTop p u) (entryB p) (entryC p)
        - cornerInfo (fixedCut p u) (entryB p) (entryC p)) / chordBottom p u

/-- Dividing the margin at the cut by the contact mass leaves two copies of
the ratio term and the correction. -/
private theorem log_two_mul_singletonMargin_ratio (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    Real.log 2 * singletonMargin p u (fixedCut p u) / chordBottom p u
      = singletonRatioTerm (entryB p / chordBottom p u)
        + singletonRatioTerm (entryC p / chordBottom p u) + singletonCorrection p u := by
  have hD := chordBottom_pos h
  have hA : 0 < chordTop p u :=
    lt_trans (by linarith [chordBottom_lt_chordMidpoint h]) (chordMidpoint_lt_chordTop h)
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hsum := diagonalMass_add_offDiagonalMass h.isPMF
  have hAD := chordTop_add_chordBottom (p := p) (u := u)
  have habc : fixedCut p u + entryB p + entryC p = 1 - 3 * chordBottom p u := by
    rw [fixedCut, offDiagonalMass] at *
    linarith
  have hAbc : chordTop p u + entryB p + entryC p = 1 - chordBottom p u := by
    rw [offDiagonalMass] at hsum
    linarith
  have h1D : 0 < 1 - chordBottom p u := by
    rw [← hAbc]
    positivity
  have hcut := fixedCut_mem_chord h hv
  have hmid : 0 < chordMidpoint p := by linarith [chordBottom_lt_chordMidpoint h]
  have ha : 0 < fixedCut p u := lt_trans hmid hcut.1
  have h3D : 0 < 1 - 3 * chordBottom p u := by
    rw [← habc]
    positivity
  have e3b : Real.log (3 + entryB p / chordBottom p u)
      = Real.log (3 * chordBottom p u + entryB p) - Real.log (chordBottom p u) := by
    rw [← Real.log_div (by positivity) hD.ne']
    congr 1
    field_simp
  have e3c : Real.log (3 + entryC p / chordBottom p u)
      = Real.log (3 * chordBottom p u + entryC p) - Real.log (chordBottom p u) := by
    rw [← Real.log_div (by positivity) hD.ne']
    congr 1
    field_simp
  have exb : Real.log (entryB p / chordBottom p u)
      = Real.log (entryB p) - Real.log (chordBottom p u) := Real.log_div hb.ne' hD.ne'
  have exc : Real.log (entryC p / chordBottom p u)
      = Real.log (entryC p) - Real.log (chordBottom p u) := Real.log_div hc.ne' hD.ne'
  have e1b : Real.log (1 + entryB p / chordBottom p u)
      = Real.log (chordBottom p u + entryB p) - Real.log (chordBottom p u) := by
    rw [← Real.log_div (by positivity) hD.ne']
    congr 1
    field_simp
  have e1c : Real.log (1 + entryC p / chordBottom p u)
      = Real.log (chordBottom p u + entryC p) - Real.log (chordBottom p u) := by
    rw [← Real.log_div (by positivity) hD.ne']
    congr 1
    field_simp
  have e3D : Real.log (3 * chordBottom p u)
      = Real.log 3 + Real.log (chordBottom p u) := Real.log_mul (by norm_num) hD.ne'
  have htouch := contactEnds_log_eq h
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at htouch
  rw [div_eq_iff hD.ne', log_two_mul_singletonMargin_fixedCut h hv]
  simp only [singletonRatioTerm, singletonCorrection, pairInfo,
    binaryEntropyNat, cornerInfo, xLogX]
  rw [e3b, e3c, exb, exc, e1b, e1c, e3D, habc, hAbc]
  field_simp
  linear_combination (-2 * chordBottom p u) * htouch

/-! ## The correction against the mass term -/

/-- `pairInfo` differentiated in its first argument. -/
private theorem pairInfo_hasDerivAt {j t : ℝ} (hj : 0 < j) (ht : 0 < t) :
    HasDerivAt (fun t => pairInfo t j) (Real.log (1 + j / t)) t := by
  have htj : 0 < t + j := add_pos ht hj
  have hraw := (((Real.hasDerivAt_mul_log htj.ne').comp t
    ((hasDerivAt_id t).add_const j)).sub (Real.hasDerivAt_mul_log ht.ne')).sub_const (xLogX j)
  have heq : (Real.log (t + j) + 1) * 1 - (Real.log t + 1) = Real.log (1 + j / t) := by
    rw [show 1 + j / t = (t + j) / t by field_simp, Real.log_div htj.ne' ht.ne']
    ring
  change HasDerivAt (fun t => pairInfo t j) _ t at hraw
  exact hraw.congr_deriv heq

/-- `pairInfo` is concave in its first argument: over an interval it grows by
at most the slope at the left end times the length. -/
private theorem pairInfo_diff_ge {j a a' : ℝ} (hj : 0 < j) (ha : 0 < a) (haa' : a ≤ a') :
    -(a' - a) * Real.log (1 + j / a) ≤ pairInfo a j - pairInfo a' j := by
  have hanti : AntitoneOn (fun t : ℝ => pairInfo t j - t * Real.log (1 + j / a))
      (Set.Icc a a') := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a a')
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      exact ((pairInfo_hasDerivAt hj ht0).sub
        ((hasDerivAt_id t).mul_const (Real.log (1 + j / a)))).continuousAt.continuousWithinAt
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha (interior_subset ht).1
      exact ((pairInfo_hasDerivAt hj ht0).sub
        ((hasDerivAt_id t).mul_const (Real.log (1 + j / a)))).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_trans ha ht.1
      have hjt : (0 : ℝ) < 1 + j / t := by positivity
      have hfrac : j / t ≤ j / a :=
        (div_le_div_iff₀ ht0 ha).2 (mul_le_mul_of_nonneg_left ht.1.le hj.le)
      simpa using sub_nonpos.mpr (Real.log_le_log hjt (by linarith : 1 + j / t ≤ 1 + j / a))
  have hm := hanti ⟨le_rfl, haa'⟩ ⟨haa', le_rfl⟩ haa'
  dsimp only at hm
  linarith

/-- The correction is at least the mass term of `SingletonMass`. -/
private theorem singletonCorrection_ge (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    singletonMassTerm (offDiagonalMass p) (chordBottom p u) ≤ singletonCorrection p u := by
  have hD := chordBottom_pos h
  have hDv := contactMass_lt_half_disagreement h hv
  have hv0 := offDiagonalMass_pos h.fullSupport
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hsum := diagonalMass_add_offDiagonalMass h.isPMF
  have hAD := chordTop_add_chordBottom (p := p) (u := u)
  have hcut := fixedCut_mem_chord h hv
  have hmid : 0 < chordMidpoint p := by linarith [chordBottom_lt_chordMidpoint h]
  have hap : 0 < fixedCut p u := lt_trans hmid hcut.1
  have hAp : 0 < chordTop p u := lt_trans hmid (chordMidpoint_lt_chordTop h)
  have hvbc : offDiagonalMass p = entryB p + entryC p := rfl
  have hA : chordTop p u = 1 - offDiagonalMass p - chordBottom p u := by linarith
  have ha : fixedCut p u = 1 - offDiagonalMass p - 3 * chordBottom p u := by
    rw [fixedCut]
    linarith
  have hAa : chordTop p u - fixedCut p u = 2 * chordBottom p u := by
    rw [hA, ha]
    ring
  have hD1 : chordBottom p u < 1 := by linarith
  have hpairA := log_pair_le hAp hb hc
  have hpaira := log_pair_le hap hb hc
  rw [← hvbc] at hpairA hpaira
  have hFb := pairInfo_diff_ge (j := entryB p) hb hap (by linarith : fixedCut p u ≤ chordTop p u)
  have hFc := pairInfo_diff_ge (j := entryC p) hc hap (by linarith : fixedCut p u ≤ chordTop p u)
  rw [hAa] at hFb hFc
  have hF : -8 * Real.log (1 + offDiagonalMass p / (2 * fixedCut p u))
      ≤ 2 / chordBottom p u * (pairInfo (fixedCut p u) (entryB p)
          + pairInfo (fixedCut p u) (entryC p) - pairInfo (chordTop p u) (entryB p)
          - pairInfo (chordTop p u) (entryC p)) := by
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hFb hFc)
      (by positivity : (0 : ℝ) ≤ 2 / chordBottom p u)
    have heq : 2 / chordBottom p u * (-(2 * chordBottom p u) *
          Real.log (1 + entryB p / fixedCut p u)
          + -(2 * chordBottom p u) * Real.log (1 + entryC p / fixedCut p u))
        = -4 * (Real.log (1 + entryB p / fixedCut p u)
          + Real.log (1 + entryC p / fixedCut p u)) := by
      field_simp
      ring
    rw [heq] at hmul
    linarith
  have hent := entropyCorrection_ge hD hD1
  have hJ : 0 ≤ 2 * cornerInfo (chordTop p u) (entryB p) (entryC p)
      - cornerInfo (fixedCut p u) (entryB p) (entryC p) := by
    refine cornerInfo_diff_nonneg hap hAp hb hc ?_
    rw [hvbc] at hA
    linarith
  have hJdiv : 0 ≤ (2 * cornerInfo (chordTop p u) (entryB p) (entryC p)
      - cornerInfo (fixedCut p u) (entryB p) (entryC p)) / chordBottom p u :=
    div_nonneg hJ hD.le
  have hlogs : -2 * Real.log (chordTop p u)
        - 8 * Real.log (1 + offDiagonalMass p / (2 * chordTop p u))
      ≤ 6 * Real.log (chordTop p u) - 4 * Real.log (chordTop p u + entryB p)
        - 4 * Real.log (chordTop p u + entryC p) := by
    have hlb : Real.log (chordTop p u + entryB p)
        = Real.log (chordTop p u) + Real.log (1 + entryB p / chordTop p u) := by
      rw [show chordTop p u + entryB p = chordTop p u * (1 + entryB p / chordTop p u) by
        field_simp, Real.log_mul hAp.ne' (by positivity)]
    have hlc : Real.log (chordTop p u + entryC p)
        = Real.log (chordTop p u) + Real.log (1 + entryC p / chordTop p u) := by
      rw [show chordTop p u + entryC p = chordTop p u * (1 + entryC p / chordTop p u) by
        field_simp, Real.log_mul hAp.ne' (by positivity)]
    rw [hlb, hlc]
    linarith
  rw [singletonMassTerm, singletonCorrection, ← hA, ← ha]
  linear_combination hlogs + hent + hF + hJdiv

/-! ## The bound -/

/-- The two cell ratios against the contact mass sum to at least two. -/
private theorem ratio_sum_ge (h : ChordDomain p u) (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    2 ≤ entryB p / chordBottom p u + entryC p / chordBottom p u := by
  have hD := chordBottom_pos h
  have hDv := contactMass_lt_half_disagreement h hv
  rw [show entryB p / chordBottom p u + entryC p / chordBottom p u
      = offDiagonalMass p / chordBottom p u from by rw [offDiagonalMass]; ring]
  exact (le_div_iff₀ hD).2 (by linarith)

/-- Below an eighth of off-diagonal mass, the isolating code's margin at the
fixed cut is bounded below by the contact mass over a hundred, in natural-log
units.  This is the singleton arm of the cut gates. -/
theorem fixedCut_singletonMargin_gt (h : ChordDomain p u)
    (hv : offDiagonalMass p ≤ (1 : ℝ) / 8) :
    chordBottom p u / 100 < Real.log 2 * singletonMargin p u (fixedCut p u) := by
  have hD := chordBottom_pos h
  have hDv := contactMass_lt_half_disagreement h hv
  have hv0 := offDiagonalMass_pos h.fullSupport
  have hb : 0 < entryB p := (cell_pos h.fullSupport).2.1
  have hc : 0 < entryC p := (cell_pos h.fullSupport).2.2.1
  have hterms := singletonTerms_gt (div_pos hb hD) (div_pos hc hD) (ratio_sum_ge h hv)
    hv0 hv hD.le hDv.le
  have hratio : (1 : ℝ) / 100
      < Real.log 2 * singletonMargin p u (fixedCut p u) / chordBottom p u := by
    rw [log_two_mul_singletonMargin_ratio h hv]
    linarith [singletonCorrection_ge h hv]
  linarith [(lt_div_iff₀ hD).mp hratio]

end StochasticToDeterministicLatents.Binary
