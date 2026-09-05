import StochasticToDeterministicLatents.Binary.CatalogRecovery

/-!
# Selected binary optimizers in contact normal form

This module carries the selection branch from the duplicate-quotient normal form to an
explicit contact presentation.  It chooses and orients a representative in the eight-element
binary table orbit, solves the two-contact kernel model by positive root parameters, packages
the resulting transpose chart over the original law, and handles the one-class zero-cost case.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents

open Finset

noncomputable section

namespace Binary

/-! ## The eight chart symmetries -/

/-- The eight table symmetries used to orient a binary contact chart. -/
def chartTableSymmetry : Fin 8 → TableSymmetry :=
  ![.refl, .swapRows, .swapColumns, .comp .swapRows .swapColumns,
    .transpose, .comp .transpose .swapRows, .comp .transpose .swapColumns,
    .comp .transpose (.comp .swapRows .swapColumns)]

/-- Reflection across the anti-diagonal of a binary table. -/
def antiDiagonalSymmetry : TableSymmetry :=
  .comp .transpose (.comp .swapRows .swapColumns)

/-- The table-symmetry syntax and the cell-equivalence chart enumerate the same eight maps. -/
def ChartTableSymmetryAgreesWithCellEquiv : Prop :=
  ∀ j : Fin 8, (chartTableSymmetry j).equiv = chartCellEquiv j

/-- Every oriented two-class chart candidate admits positive contact-root parameters. -/
def ChartCandidateHasContactRoots : Prop :=
  ∀ {p : RealTable} {D : SeedSetup p} (K : Clustering D)
    (j : Fin 8) (A : ChartCandidate K j),
  ∃ (rootReflected : Bool) (lambda mu : ℝ),
    0 < lambda ∧ lambda < mu ∧
    0 < lambda + mu - lambda ^ 2 * mu ^ 2 ∧
    0 < lambda * mu * (lambda + mu) - 1 ∧
    let R := lambda + mu
    let K0 := lambda ^ 2 + lambda * mu + mu ^ 2
    let den := R * (1 + lambda ^ 3) * (1 + mu ^ 3)
    let rootRelabel :=
      if rootReflected then
        .comp (chartTableSymmetry j) antiDiagonalSymmetry
      else chartTableSymmetry j
    pushforward rootRelabel.equiv (K.Q (A.classEquiv.symm 0)) =
      fun z => match z with
        | (0, 0) => (R - lambda ^ 2 * mu ^ 2) / den
        | (0, 1) => mu ^ 2 * K0 / den
        | (1, 0) => lambda ^ 2 * K0 / den
        | (1, 1) => lambda ^ 2 * mu ^ 2 * (lambda * mu * R - 1) / den

/-- The eight table symmetries agree pointwise with `chartCellEquiv`. -/
theorem chartTableSymmetry_agreesWithCellEquiv :
    ChartTableSymmetryAgreesWithCellEquiv := by
  intro j
  fin_cases j <;>
    ext z <;> rcases z with ⟨x, y⟩ <;>
    fin_cases x <;> fin_cases y <;>
    simp [chartTableSymmetry, chartCellEquiv, TableSymmetry.equiv,
      antiDiagonalSymmetry, bitFlip, swapRowsCell, swapColumnsCell, transposeCell]

/-- Anti-diagonal reflection commutes with transposition. -/
theorem antiDiagonalSymmetry_commutes_transpose :
    antiDiagonalSymmetry.equiv.trans transposeCell =
      transposeCell.trans antiDiagonalSymmetry.equiv := by
  apply Equiv.ext
  intro z
  rcases z with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    simp [antiDiagonalSymmetry, TableSymmetry.equiv, bitFlip,
      swapRowsCell, swapColumnsCell, transposeCell]

/-- Anti-diagonal pushforward commutes with transposing a binary law. -/
theorem pushforward_antiDiagonal_transpose (q : RealTable) :
    pushforward antiDiagonalSymmetry.equiv (fun z => q (transposeCell.symm z)) =
      fun z => pushforward antiDiagonalSymmetry.equiv q (transposeCell.symm z) := by
  funext z
  rw [pushforward_apply_equiv, pushforward_apply_equiv]
  exact congrArg q (Equiv.congr_fun
    antiDiagonalSymmetry_commutes_transpose.symm z)

/-- Anti-diagonal pushforward exchanges the diagonal entries of a displayed table. -/
theorem pushforward_antiDiagonal_tableOfEntries (a b c d : ℝ) :
    pushforward antiDiagonalSymmetry.equiv (tableOfEntries a b c d) =
      tableOfEntries d b c a := by
  funext z
  rcases z with ⟨i, k⟩
  fin_cases i <;> fin_cases k <;>
    rw [pushforward_apply_equiv] <;>
    simp [antiDiagonalSymmetry, TableSymmetry.equiv,
      tableOfEntries, bitFlip, swapRowsCell, swapColumnsCell, transposeCell]

/-! ## Contact-root scalars -/

/-- Sum of the two positive contact roots. -/
def contactR (lambda mu : ℝ) : ℝ := lambda + mu

/-- Quadratic symmetric contact-root scalar. -/
def contactK0 (lambda mu : ℝ) : ℝ :=
  lambda ^ 2 + lambda * mu + mu ^ 2

/-- Numerator of the lower diagonal contact coordinate. -/
def contactNA (lambda mu : ℝ) : ℝ :=
  contactR lambda mu - lambda ^ 2 * mu ^ 2

/-- Numerator of the upper diagonal contact coordinate. -/
def contactND (lambda mu : ℝ) : ℝ :=
  lambda * mu * contactR lambda mu - 1

/-- Positive square root of the ratio of the ordered contact roots. -/
def contactX (lambda mu : ℝ) : ℝ := Real.sqrt (lambda / mu)

/-- Normalized lower diagonal contact coordinate. -/
def contactA0 (lambda mu : ℝ) : ℝ :=
  contactNA lambda mu / (mu ^ 2 * contactK0 lambda mu)

/-- Normalized upper diagonal contact coordinate. -/
def contactD0 (lambda mu : ℝ) : ℝ :=
  lambda ^ 2 * contactND lambda mu / contactK0 lambda mu

theorem contactK0_pos {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) : 0 < contactK0 lambda mu := by
  have hmu : 0 < mu := lt_trans hlambda hlt
  unfold contactK0
  positivity

theorem contactR_pos {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) : 0 < contactR lambda mu := by
  have hmu : 0 < mu := lt_trans hlambda hlt
  unfold contactR
  positivity

theorem contactX_pos_lt_one {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) :
    0 < contactX lambda mu ∧ contactX lambda mu < 1 := by
  have hmu : 0 < mu := lt_trans hlambda hlt
  have hratio_pos : 0 < lambda / mu := div_pos hlambda hmu
  have hratio_lt : lambda / mu < 1 := (div_lt_one hmu).2 hlt
  constructor
  · exact Real.sqrt_pos.2 hratio_pos
  · rw [contactX, (Real.sqrt_lt' zero_lt_one)]
    simpa using hratio_lt

theorem contactX_sq {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) : contactX lambda mu ^ 2 = lambda / mu := by
  have hmu : 0 < mu := lt_trans hlambda hlt
  rw [contactX, Real.sq_sqrt (le_of_lt (div_pos hlambda hmu))]

theorem contactX_pow_four {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) : contactX lambda mu ^ 4 = lambda ^ 2 / mu ^ 2 := by
  rw [show contactX lambda mu ^ 4 = (contactX lambda mu ^ 2) ^ 2 by ring,
    contactX_sq hlambda hlt]
  field_simp

theorem contactA0_pos {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) (hNA : 0 < contactNA lambda mu) :
    0 < contactA0 lambda mu := by
  have hmu : 0 < mu := lt_trans hlambda hlt
  exact div_pos hNA (mul_pos (sq_pos_of_pos hmu) (contactK0_pos hlambda hlt))

theorem contactD0_pos {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) (hND : 0 < contactND lambda mu) :
    0 < contactD0 lambda mu := by
  exact div_pos (mul_pos (sq_pos_of_pos hlambda) hND) (contactK0_pos hlambda hlt)

theorem contact_root_identity {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) :
    (1 + contactX lambda mu ^ 2 + contactX lambda mu ^ 4) *
        contactA0 lambda mu * contactD0 lambda mu =
      contactX lambda mu ^ 4 *
        (contactX lambda mu ^ 2 - contactA0 lambda mu - contactD0 lambda mu) := by
  have hmu : 0 < mu := lt_trans hlambda hlt
  have hmu0 : mu ≠ 0 := ne_of_gt hmu
  have hK0 : 0 < contactK0 lambda mu := contactK0_pos hlambda hlt
  have hK00 : contactK0 lambda mu ≠ 0 := ne_of_gt hK0
  have hR : 0 < contactR lambda mu := contactR_pos hlambda hlt
  have hR0 : contactR lambda mu ≠ 0 := ne_of_gt hR
  rw [contactX_sq hlambda hlt, contactX_pow_four hlambda hlt]
  unfold contactA0 contactD0 contactNA contactND contactK0 contactR
  field_simp [hmu0, hK00, hR0]
  ring

theorem contactA0_le_contactD0_iff {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) :
    contactA0 lambda mu ≤ contactD0 lambda mu ↔ 1 ≤ lambda * mu := by
  have hmu : 0 < mu := lt_trans hlambda hlt
  have hK0 : 0 < contactK0 lambda mu := contactK0_pos hlambda hlt
  have hden : 0 < mu ^ 2 * contactK0 lambda mu :=
    mul_pos (sq_pos_of_pos hmu) hK0
  have hdiff :
      contactD0 lambda mu - contactA0 lambda mu =
        contactR lambda mu * ((lambda * mu) ^ 3 - 1) /
          (mu ^ 2 * contactK0 lambda mu) := by
    have hmu0 : mu ≠ 0 := ne_of_gt hmu
    have hK00 : contactK0 lambda mu ≠ 0 := ne_of_gt hK0
    unfold contactD0 contactA0 contactND contactNA contactR contactK0
    field_simp [hmu0, hK00]
    ring
  have hR : 0 < contactR lambda mu := contactR_pos hlambda hlt
  have hp : 0 < lambda * mu := mul_pos hlambda hmu
  have hfac : 0 < (lambda * mu) ^ 2 + lambda * mu + 1 := by positivity
  rw [← sub_nonneg, hdiff]
  constructor
  · intro hquot
    have hcub : 0 ≤ (lambda * mu) ^ 3 - 1 := by
      by_contra hn
      have hn' : (lambda * mu) ^ 3 - 1 < 0 := lt_of_not_ge hn
      have hneg : contactR lambda mu * ((lambda * mu) ^ 3 - 1) /
          (mu ^ 2 * contactK0 lambda mu) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hR hn') hden
      exact (not_lt_of_ge hquot) hneg
    have hpoly : ((lambda * mu) - 1) *
        ((lambda * mu) ^ 2 + lambda * mu + 1) = (lambda * mu) ^ 3 - 1 := by ring
    nlinarith [hfac]
  · intro hprod
    have hpoly : ((lambda * mu) - 1) *
        ((lambda * mu) ^ 2 + lambda * mu + 1) = (lambda * mu) ^ 3 - 1 := by ring
    have hcub : 0 ≤ (lambda * mu) ^ 3 - 1 := by nlinarith [hfac]
    exact div_nonneg (mul_nonneg (le_of_lt hR) hcub) (le_of_lt hden)

theorem contactD0_lt_contactA0_iff {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hlt : lambda < mu) :
    contactD0 lambda mu < contactA0 lambda mu ↔ lambda * mu < 1 := by
  rw [← not_le, contactA0_le_contactD0_iff hlambda hlt]
  exact not_le

/-! ## The two-contact root model -/

/-- The normalized contact law associated to two positive row parameters. -/
def rootLaw (s t : ℝ) : RealTable := fun z =>
  let R := s + t
  let K0 := s ^ 2 + s * t + t ^ 2
  let den := R * (1 + s ^ 3) * (1 + t ^ 3)
  if z = (0, 0) then (R - s ^ 2 * t ^ 2) / den
  else if z = (0, 1) then t ^ 2 * K0 / den
  else if z = (1, 0) then s ^ 2 * K0 / den
  else s ^ 2 * t ^ 2 * (s * t * R - 1) / den

/-- Two distinct contacts determine the symmetric two-root kernel model, up to column swap. -/
theorem exists_twoContactRootKernelModel
    (w q r : RealTable)
    (hw : Feasible (univ : Finset Cell) w)
    (hq : IsContact (univ : Finset Cell) w q)
    (hr : IsContact (univ : Finset Cell) w r)
    (hqr : q ≠ r) :
  ∃ lambda mu : ℝ,
    RowCubeParameter q lambda ∧
    RowCubeParameter r mu ∧
    lambda ≠ mu ∧
    let R := lambda + mu
    let T := lambda * mu
    let K0 := R ^ 2 - T
    let NA := R - T ^ 2
    let ND := R * T - 1
    let U := (1 + lambda ^ 3) * (1 + mu ^ 3)
    ∃ h : ℝ,
      0 < h ∧
      h ^ 3 = 1 / (R ^ 3 * U) ∧
      0 < NA ∧
      0 < ND ∧
      let ws : RealTable := fun z =>
        if z = (0, 0) then h * NA
        else if z = (0, 1) then h * K0
        else if z = (1, 0) then h * K0
        else h * ND
      w = ws ∨ pushforward swapColumnsCell w = ws := by
  rcases allNormalFormConditions with
    ⟨_, hC1, _, hC3, hC4, hC5, _, hC7, _, hC9, hC10,
      _, _, _, hC14, _, hC16, _, _, _, _, _⟩
  obtain ⟨s, hs⟩ := hC1 w q hw hq
  obtain ⟨t, ht⟩ := hC1 w r hw hr
  have hst : s ≠ t := by
    intro h
    apply hqr
    apply hC5 w q r hw hq hr s hs
    simpa [h] using ht
  let P := feasibilityPolynomial w
  have hnonneg : ∀ u : ℝ, 0 < u → 0 ≤ P.eval u := by
    intro u hu
    rw [feasibilityPolynomial_eval]
    exact hC3 w hw u hu
  have hsroot : P.eval s = 0 := by
    rw [feasibilityPolynomial_eval]
    exact (hC4 w q hw hq s hs).1
  have htroot : P.eval t = 0 := by
    rw [feasibilityPolynomial_eval]
    exact (hC4 w r hw hr t ht).1
  have hsdiv := hC7 P s hs.1 hnonneg hsroot
  have htdiv := hC7 P t ht.1 hnonneg htroot
  have hfactor := hC9 w hw s t hs.1 ht.1 hst P
    (feasibilityPolynomial_eval w) hsdiv htdiv
  obtain ⟨hm0, hm1, hm2, hm3⟩ :=
    hC10 (w (0, 0)) (w (0, 1)) (w (1, 0)) (w (1, 1)) s t hs.1 ht.1 hfactor
  have hwpos : ∀ z, 0 < w z := fun z => hw.1 z (by simp)
  have hnodes := hC14 w q r hw hq hr hqr
  obtain ⟨h, hh, hhcube, hwmodel⟩ :=
    hC16 w hwpos s t hs.1 ht.1 hst hm0 hm1 hm2 hm3 hnodes
  have hNA : 0 < s + t - (s * t) ^ 2 := by
    rcases hwmodel with hwmodel | hwmodel
    · have hp := hwpos (0, 0)
      rw [hwmodel] at hp
      simp only [if_pos] at hp
      rcases (mul_pos_iff.mp hp) with hp | hp
      · exact hp.2
      · linarith
    · have hp := hwpos (0, 1)
      have hp' : 0 < pushforward swapColumnsCell w (0, 0) := by
        rw [pushforward_apply_equiv]
        simpa [swapColumnsCell, bitFlip, Equiv.swap_apply_def] using hp
      rw [hwmodel] at hp'
      simp only [if_pos] at hp'
      rcases (mul_pos_iff.mp hp') with hp' | hp'
      · exact hp'.2
      · linarith
  have hND : 0 < (s + t) * (s * t) - 1 := by
    rcases hwmodel with hwmodel | hwmodel
    · have hp := hwpos (1, 1)
      rw [hwmodel] at hp
      norm_num at hp
      rcases (mul_pos_iff.mp hp) with hp | hp
      · exact hp.2
      · linarith
    · have hp := hwpos (1, 0)
      have hp' : 0 < pushforward swapColumnsCell w (1, 1) := by
        rw [pushforward_apply_equiv]
        simpa [swapColumnsCell, bitFlip, Equiv.swap_apply_def] using hp
      rw [hwmodel] at hp'
      norm_num at hp'
      rcases (mul_pos_iff.mp hp') with hp' | hp'
      · exact hp'.2
      · linarith
  exact ⟨s, t, hs, ht, hst, h, hh, hhcube, hNA, hND, hwmodel⟩

/-- A contact of the symmetric direct kernel is its explicit normalized root law. -/
theorem contact_eq_rootLaw
    (w q : RealTable) (s t h : ℝ)
    (hw : Feasible (univ : Finset Cell) w)
    (hq : IsContact (univ : Finset Cell) w q)
    (hs : RowCubeParameter q s)
    (htpos : 0 < t)
    (hh : 0 < h)
    (hmodel : w = fun z =>
      if z = (0, 0) then h * (s + t - (s * t) ^ 2)
      else if z = (0, 1) then h * ((s + t) ^ 2 - s * t)
      else if z = (1, 0) then h * ((s + t) ^ 2 - s * t)
      else h * ((s + t) * (s * t) - 1)) :
    q = rootLaw s t := by
  have hspos : 0 < s := hs.1
  obtain ⟨-, y, hy, hyratio⟩ :=
    contactParameter_bestResponse w q hw hq s hs
  have hden :
      s + t - (s * t) ^ 2 + ((s + t) ^ 2 - s * t) * s ^ 2 =
        (s + t) * (1 + s ^ 3) := by ring
  have hnum :
      ((s + t) ^ 2 - s * t) + ((s + t) * (s * t) - 1) * s ^ 2 =
        t * (s + t) * (1 + s ^ 3) := by ring
  have hyEq : y = t := by
    rw [hyratio, hmodel]
    norm_num
    exact bestResponse_quotient hh (by positivity) hspos hden hnum
  have htcol : ColumnCubeParameter q t := by simpa [hyEq] using hy
  have hxpow := normalized_cubeParameter_rpow_scale hs.1 hs.2.1 hs.2.2
  have hypow := normalized_cubeParameter_rpow_scale
    htcol.1 htcol.2.1 htcol.2.2
  let scale := h * (rowMarginal q 0) ^ ((2 : ℝ) / 3) *
    (columnMarginal q 0) ^ ((2 : ℝ) / 3)
  have hXq : stoch_to_det.mX q = rowMarginal q := by
    change pushforward Prod.fst q = rowMarginal q
    exact pushforward_fst_eq_rowMarginal q
  have hYq : stoch_to_det.mY q = columnMarginal q := by
    change pushforward Prod.snd q = columnMarginal q
    exact pushforward_snd_eq_columnMarginal q
  have h00 : q (0, 0) = scale * (s + t - s ^ 2 * t ^ 2) := by
    rw [hq.2.2 _ (mem_univ _), hmodel]
    norm_num
    rw [hXq, hYq]
    dsimp [scale]
    ring
  have h01 : q (0, 1) = scale * (t ^ 2 * (s ^ 2 + s * t + t ^ 2)) := by
    rw [hq.2.2 _ (mem_univ _), hmodel]
    norm_num
    rw [hXq, hYq, hypow]
    dsimp [scale]
    ring
  have h10 : q (1, 0) = scale * (s ^ 2 * (s ^ 2 + s * t + t ^ 2)) := by
    rw [hq.2.2 _ (mem_univ _), hmodel]
    norm_num
    rw [hXq, hYq, hxpow]
    dsimp [scale]
    ring
  have h11 : q (1, 1) = scale *
      (s ^ 2 * t ^ 2 * (s * t * (s + t) - 1)) := by
    rw [hq.2.2 _ (mem_univ _), hmodel]
    norm_num
    rw [hXq, hYq, hxpow, hypow]
    dsimp [scale]
    ring
  have hsum : q (0, 0) + q (0, 1) + (q (1, 0) + q (1, 1)) = 1 := by
    simpa [mass, stoch_to_det.mass, Fintype.sum_prod_type, Fin.sum_univ_two] using
      hq.1.total
  rw [h00, h01, h10, h11] at hsum
  have hpoly :
      (s + t - s ^ 2 * t ^ 2) +
          t ^ 2 * (s ^ 2 + s * t + t ^ 2) +
          s ^ 2 * (s ^ 2 + s * t + t ^ 2) +
          s ^ 2 * t ^ 2 * (s * t * (s + t) - 1) =
        (s + t) * (1 + s ^ 3) * (1 + t ^ 3) := by ring
  have hscale : scale = 1 / ((s + t) * (1 + s ^ 3) * (1 + t ^ 3)) := by
    have hdpos : 0 < (s + t) * (1 + s ^ 3) * (1 + t ^ 3) := by positivity
    apply (eq_div_iff hdpos.ne').2
    nlinarith [hsum, hpoly]
  apply binary_matrix_ext
  all_goals simp [rootLaw, h00, h01, h10, h11, hscale] <;>
    field_simp [(ne_of_gt (show 0 < s + t by positivity)),
      (ne_of_gt (show 0 < 1 + s ^ 3 by positivity)),
      (ne_of_gt (show 0 < 1 + t ^ 3 by positivity))] <;> ring

/-- The explicit root law is the normalized table of contact coordinates. -/
theorem rootLaw_eq_normalizedContactTable
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hlt : lambda < mu) :
    let x := contactX lambda mu
    let alpha := contactA0 lambda mu
    let rho := x ^ 4
    let delta := contactD0 lambda mu
    let Q := alpha + 1 + rho + delta
    rootLaw lambda mu =
      tableOfEntries (alpha / Q) (1 / Q) (rho / Q) (delta / Q) := by
  dsimp only
  have hmu : 0 < mu := lt_trans hlambda hlt
  have hmu0 : mu ≠ 0 := ne_of_gt hmu
  have hK : 0 < contactK0 lambda mu := contactK0_pos hlambda hlt
  have hK0 : contactK0 lambda mu ≠ 0 := ne_of_gt hK
  have hR : 0 < contactR lambda mu := contactR_pos hlambda hlt
  have hR0 : contactR lambda mu ≠ 0 := ne_of_gt hR
  have hx4 := contactX_pow_four hlambda hlt
  have hQ :
      contactA0 lambda mu + 1 + contactX lambda mu ^ 4 +
          contactD0 lambda mu =
        contactR lambda mu * (1 + lambda ^ 3) * (1 + mu ^ 3) /
          (mu ^ 2 * contactK0 lambda mu) := by
    rw [hx4]
    unfold contactA0 contactD0 contactNA contactND
    field_simp [hmu0, hK0]
    unfold contactR contactK0
    ring
  rw [hQ]
  apply binary_matrix_ext
  all_goals
    simp [rootLaw, tableOfEntries, contactA0, contactD0, contactNA, contactND, hx4]
    field_simp [hmu0, hK0, hR0]
    simp only [contactR, contactK0]
    <;> ring

/-- A chart candidate's two contacts are the root law and its parameter transpose,
possibly after a column reflection. -/
theorem chartCandidate_rootLaw
    {p : RealTable} {D : SeedSetup p} (K : Clustering D)
    (j : Fin 8) (A : ChartCandidate K j) :
    ∃ s t : ℝ,
      0 < s ∧ 0 < t ∧ s ≠ t ∧
      0 < s + t - s ^ 2 * t ^ 2 ∧
      0 < s * t * (s + t) - 1 ∧
      RowCubeParameter (rootLaw s t) s ∧
      RowCubeParameter (rootLaw t s) t ∧
      ((pushforward (chartCellEquiv j) (K.Q (A.classEquiv.symm 0)) = rootLaw s t ∧
        pushforward (chartCellEquiv j) (K.Q (A.classEquiv.symm 1)) = rootLaw t s) ∨
       (pushforward (chartCellEquiv j) (K.Q (A.classEquiv.symm 0)) =
          pushforward swapColumnsCell (rootLaw s t) ∧
        pushforward (chartCellEquiv j) (K.Q (A.classEquiv.symm 1)) =
          pushforward swapColumnsCell (rootLaw t s))) := by
  let c0 := A.classEquiv.symm 0
  let c1 := A.classEquiv.symm 1
  let q0 := K.Q c0
  let q1 := K.Q c1
  have hc : c0 ≠ c1 := by simp [c0, c1]
  have hq0pos : ∀ z, 0 < q0 z := by
    intro z
    simpa [q0, pushforward_apply_equiv] using A.q0_pos (chartCellEquiv j z)
  have hsupp : support p = (univ : Finset Cell) := by
    calc
      support p = support q0 :=
        (contact_support_eq D.feasible D.conn (K.Q_isContact c0)).symm
      _ = univ := support_eq_univ_of_pos hq0pos
  have hw0 : Feasible (univ : Finset Cell) D.w := by
    simpa [hsupp] using D.feasible
  have hcontact0 : IsContact (univ : Finset Cell) D.w q0 := by
    simpa [hsupp] using K.Q_isContact c0
  have hcontact1 : IsContact (univ : Finset Cell) D.w q1 := by
    simpa [hsupp] using K.Q_isContact c1
  have hqne : q0 ≠ q1 := fun h => hc (K.Q_injective h)
  let rel := chartTableSymmetry j
  have hrel : rel.equiv = chartCellEquiv j :=
    chartTableSymmetry_agreesWithCellEquiv j
  let wR := pushforward rel.equiv D.w
  let q0R := pushforward rel.equiv q0
  let q1R := pushforward rel.equiv q1
  have hwR : Feasible (univ : Finset Cell) wR :=
    feasible_pushforward rel hw0
  have hq0R : IsContact (univ : Finset Cell) wR q0R :=
    isContact_pushforward rel hcontact0
  have hq1R : IsContact (univ : Finset Cell) wR q1R :=
    isContact_pushforward rel hcontact1
  have hqRne : q0R ≠ q1R := by
    intro h
    apply hqne
    have hb := congrArg (pushforward rel.equiv.symm) h
    simpa [q0R, q1R, pushforward_symm_pushforward] using hb
  obtain ⟨s, t, hs, ht, hst, h, hh, _hhcube, hNA, hND, hmodel⟩ :=
    exists_twoContactRootKernelModel wR q0R q1R hwR hq0R hq1R hqRne
  have hNA' : 0 < s + t - s ^ 2 * t ^ 2 := by
    convert hNA using 1 <;> ring
  have hND' : 0 < s * t * (s + t) - 1 := by
    convert hND using 1 <;> ring
  rcases hmodel with hmodel | hmodel
  · have he0 := contact_eq_rootLaw wR q0R s t h hwR hq0R hs ht.1 hh hmodel
    have he1 := contact_eq_rootLaw wR q1R t s h hwR hq1R ht hs.1 hh (by
      simpa [mul_comm, add_comm, mul_left_comm, mul_assoc] using hmodel)
    refine ⟨s, t, hs.1, ht.1, hst, hNA', hND', ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
    · simpa [he0] using hs
    · simpa [he1] using ht
    · simpa [q0R, q0, hrel] using he0
    · simpa [q1R, q1, hrel] using he1
  · let wC := pushforward swapColumnsCell wR
    let q0C := pushforward swapColumnsCell q0R
    let q1C := pushforward swapColumnsCell q1R
    have hwC := feasible_pushforward (.swapColumns) hwR
    have hq0C := isContact_pushforward (.swapColumns) hq0R
    have hq1C := isContact_pushforward (.swapColumns) hq1R
    have hsC := rowCubeParameter_swapColumns hs
    have htC := rowCubeParameter_swapColumns ht
    have he0 := contact_eq_rootLaw wC q0C s t h hwC hq0C hsC ht.1 hh hmodel
    have he1 := contact_eq_rootLaw wC q1C t s h hwC hq1C htC hs.1 hh (by
      simpa [mul_comm, add_comm, mul_left_comm, mul_assoc] using hmodel)
    have back0 : q0R = pushforward swapColumnsCell (rootLaw s t) := by
      have hb := congrArg (pushforward swapColumnsCell.symm) he0
      rw [show pushforward swapColumnsCell.symm (rootLaw s t) =
          pushforward swapColumnsCell (rootLaw s t) by
        funext z
        rw [pushforward_apply_equiv, pushforward_apply_equiv]
        simp [swapColumnsCell, bitFlip, Equiv.swap_apply_def]] at hb
      simpa [q0C, pushforward_symm_pushforward] using hb
    have back1 : q1R = pushforward swapColumnsCell (rootLaw t s) := by
      have hb := congrArg (pushforward swapColumnsCell.symm) he1
      rw [show pushforward swapColumnsCell.symm (rootLaw t s) =
          pushforward swapColumnsCell (rootLaw t s) by
        funext z
        rw [pushforward_apply_equiv, pushforward_apply_equiv]
        simp [swapColumnsCell, bitFlip, Equiv.swap_apply_def]] at hb
      simpa [q1C, pushforward_symm_pushforward] using hb
    refine ⟨s, t, hs.1, ht.1, hst, hNA', hND', ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
    · have he0' : pushforward swapColumnsCell q0R = rootLaw s t := by
        simpa [q0C] using he0
      rw [he0'] at hsC
      exact hsC
    · have he1' : pushforward swapColumnsCell q1R = rootLaw t s := by
        simpa [q1C] using he1
      rw [he1'] at htC
      exact htC
    · simpa [q0R, q0, hrel] using back0
    · simpa [q1R, q1, hrel] using back1

/-- Strict off-diagonal orientation orders the row cube parameters of a transpose pair. -/
theorem rowCubeParameter_lt_of_transpose_strictOffDiagonal
    {q r : RealTable} {lambda mu : ℝ}
    (htranspose : r = fun z => q (transposeCell.symm z))
    (hstrict : q (1, 0) < q (0, 1))
    (hlambda : RowCubeParameter q lambda)
    (hmu : RowCubeParameter r mu) :
    lambda < mu := by
  rcases hlambda with ⟨hlambda_pos, -, hlambda_row⟩
  rcases hmu with ⟨hmu_pos, -, hmu_row⟩
  have hmarg : rowMarginal q 1 < rowMarginal r 1 := by
    simp only [rowMarginal, htranspose, transposeCell]
    change q (1, 0) + q (1, 1) < q (0, 1) + q (1, 1)
    simpa [add_comm] using add_lt_add_right hstrict (q (1, 1))
  rw [hlambda_row, hmu_row] at hmarg
  have hlambda_den : 0 < 1 + lambda ^ 3 := by positivity
  have hmu_den : 0 < 1 + mu ^ 3 := by positivity
  rw [div_lt_div_iff₀ hlambda_den hmu_den] at hmarg
  ring_nf at hmarg
  have hcube : lambda ^ 3 < mu ^ 3 := by nlinarith [hmarg]
  exact lt_of_pow_lt_pow_left₀ 3 hmu_pos.le hcube

/-- Exchanging the two root parameters transposes the explicit root law. -/
theorem rootLaw_transpose (s t : ℝ) :
    rootLaw t s = fun z => rootLaw s t (transposeCell.symm z) := by
  funext z
  rcases z with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    simp [rootLaw, transposeCell] <;> ring

/-- Swapping both columns twice leaves a binary law unchanged. -/
theorem pushforward_swapColumns_involutive (w : RealTable) :
    pushforward swapColumnsCell (pushforward swapColumnsCell w) = w := by
  funext z
  rcases z with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    rw [pushforward_apply_equiv, pushforward_apply_equiv] <;>
    simp [swapColumnsCell, bitFlip]

/-- The zeroth chart symmetry acts trivially on binary laws. -/
theorem pushforward_chartTableSymmetry_zero (w : RealTable) :
    pushforward (chartTableSymmetry 0).equiv w = w := by
  funext z
  rcases z with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    rw [pushforward_apply_equiv] <;>
    simp [chartTableSymmetry, TableSymmetry.equiv]

/-- Pushforward along the identity equivalence leaves a binary law unchanged. -/
theorem pushforward_refl (w : RealTable) :
    pushforward (Equiv.refl _) w = w := by
  funext z
  rw [pushforward_apply_equiv]
  rfl

/-- Choice of an anti-diagonal reflection and ordering of a transpose-paired contact pair. -/
structure OrientedChartChoice
    (q qT q0 : RealTable) (j : Fin 8) where
  rootReflected : Bool
  contactSwapped : Bool
  firstContact_eq :
    pushforward
        (if rootReflected then
          (TableSymmetry.comp (chartTableSymmetry j) antiDiagonalSymmetry).equiv
        else (chartTableSymmetry j).equiv) q0 =
      if contactSwapped then qT else q

/-- Every strict transpose-paired direct or column-swapped model has an oriented
representative in each of the eight charts. -/
theorem exists_orientedChartChoice
    (q qT q0 q1 : RealTable) (j : Fin 8)
    (hqT : qT = fun z => q (transposeCell.symm z))
    (hpair :
      pushforward (chartTableSymmetry j).equiv q1 = fun z =>
        pushforward (chartTableSymmetry j).equiv q0 (transposeCell.symm z))
    (hmodel :
      (q0 = q ∧ q1 = qT) ∨
      (pushforward swapColumnsCell q0 = q ∧
        pushforward swapColumnsCell q1 = qT))
    (hstrict :
      pushforward (chartTableSymmetry j).equiv q0 (1, 0) <
        pushforward (chartTableSymmetry j).equiv q0 (0, 1)) :
    Nonempty (OrientedChartChoice q qT q0 j) := by
  rcases hmodel with ⟨hq0, hq1⟩ | ⟨hq0, hq1⟩
  · subst q0
    subst q1
    subst qT
    fin_cases j <;>
      have h00 := congrFun hpair (0, 0) <;>
      have h01 := congrFun hpair (0, 1) <;>
      have h10 := congrFun hpair (1, 0) <;>
      have h11 := congrFun hpair (1, 1) <;>
      simp only [pushforward_apply_equiv] at h00 h01 h10 h11 hstrict <;>
      simp [chartTableSymmetry, TableSymmetry.equiv, bitFlip,
        swapRowsCell, swapColumnsCell, transposeCell] at h00 h01 h10 h11 hstrict <;>
      first
      | (refine ⟨⟨false, false, ?_⟩⟩ <;>
          simp only [Bool.false_eq_true, if_false] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell] <;>
            first | assumption | (symm; assumption))
      | (refine ⟨⟨true, true, ?_⟩⟩ <;>
          simp only [if_true] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell] <;>
            first | assumption | (symm; assumption))
      | (refine ⟨⟨false, true, ?_⟩⟩ <;>
          simp only [Bool.false_eq_true, if_false, if_true] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell] <;>
            first | assumption | (symm; assumption))
      | (refine ⟨⟨true, false, ?_⟩⟩ <;>
          simp only [Bool.false_eq_true, if_false, if_true] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell] <;>
            first | assumption | (symm; assumption))
      | linarith
  · subst qT
    have hq0_00 := congrFun hq0 (0, 0)
    have hq0_01 := congrFun hq0 (0, 1)
    have hq0_10 := congrFun hq0 (1, 0)
    have hq0_11 := congrFun hq0 (1, 1)
    have hq1_00 := congrFun hq1 (0, 0)
    have hq1_01 := congrFun hq1 (0, 1)
    have hq1_10 := congrFun hq1 (1, 0)
    have hq1_11 := congrFun hq1 (1, 1)
    simp only [pushforward_apply_equiv] at hq0_00 hq0_01 hq0_10 hq0_11 hq1_00 hq1_01 hq1_10 hq1_11
    simp [swapColumnsCell, bitFlip, transposeCell] at hq0_00 hq0_01 hq0_10 hq0_11 hq1_00 hq1_01 hq1_10 hq1_11
    fin_cases j <;>
      have h00 := congrFun hpair (0, 0) <;>
      have h01 := congrFun hpair (0, 1) <;>
      have h10 := congrFun hpair (1, 0) <;>
      have h11 := congrFun hpair (1, 1) <;>
      simp only [pushforward_apply_equiv] at h00 h01 h10 h11 hstrict <;>
      simp [chartTableSymmetry, TableSymmetry.equiv, bitFlip,
        swapRowsCell, swapColumnsCell, transposeCell,
        hq0_00, hq0_01, hq0_10, hq0_11,
        hq1_00, hq1_01, hq1_10, hq1_11] at h00 h01 h10 h11 hstrict <;>
      first
      | (refine ⟨⟨false, false, ?_⟩⟩ <;>
          simp only [Bool.false_eq_true, if_false] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell,
            hq0_00, hq0_01, hq0_10, hq0_11] <;>
            first | assumption | (symm; assumption))
      | (refine ⟨⟨true, true, ?_⟩⟩ <;>
          simp only [if_true] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell,
            hq0_00, hq0_01, hq0_10, hq0_11] <;>
            first | assumption | (symm; assumption))
      | (refine ⟨⟨false, true, ?_⟩⟩ <;>
          simp only [Bool.false_eq_true, if_false, if_true] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell,
            hq0_00, hq0_01, hq0_10, hq0_11] <;>
            first | assumption | (symm; assumption))
      | (refine ⟨⟨true, false, ?_⟩⟩ <;>
          simp only [Bool.false_eq_true, if_false, if_true] <;>
          funext z <;> rcases z with ⟨x, y⟩ <;> fin_cases x <;> fin_cases y <;>
          rw [pushforward_apply_equiv] <;>
          simp [chartTableSymmetry, antiDiagonalSymmetry, TableSymmetry.equiv,
            bitFlip, swapRowsCell, swapColumnsCell, transposeCell,
            hq0_00, hq0_01, hq0_10, hq0_11] <;>
            first | assumption | (symm; assumption))
      | linarith

/-- Every chart candidate supplies the contact roots in `ChartCandidateHasContactRoots`. -/
theorem chartCandidate_hasContactRoots : ChartCandidateHasContactRoots := by
  intro p D K j A
  obtain ⟨s, t, hs, ht, hne, hNA, hND, hsRow, htRow, hmodel⟩ :=
    chartCandidate_rootLaw K j A
  let q0 := K.Q (A.classEquiv.symm 0)
  let q1 := K.Q (A.classEquiv.symm 1)
  let q0R := pushforward (chartTableSymmetry j).equiv q0
  let q1R := pushforward (chartTableSymmetry j).equiv q1
  have hd4 : (chartTableSymmetry j).equiv = chartCellEquiv j :=
    chartTableSymmetry_agreesWithCellEquiv j
  have hpair : q1R = fun z => q0R (transposeCell.symm z) := by
    simpa [q0R, q1R, q0, q1, hd4] using A.transpose_pair
  have hstrict : q0R (1, 0) < q0R (0, 1) := by
    simpa [q0R, q0, hd4] using A.strict_offDiag
  have hmodelR :
      (q0R = rootLaw s t ∧ q1R = rootLaw t s) ∨
      (pushforward swapColumnsCell q0R = rootLaw s t ∧
        pushforward swapColumnsCell q1R = rootLaw t s) := by
    rcases hmodel with hmodel | hmodel
    · exact Or.inl ⟨by simpa [q0R, q0, hd4] using hmodel.1,
        by simpa [q1R, q1, hd4] using hmodel.2⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [show q0R = pushforward swapColumnsCell (rootLaw s t) by
          simpa [q0R, q0, hd4] using hmodel.1]
        exact pushforward_swapColumns_involutive (rootLaw s t)
      · rw [show q1R = pushforward swapColumnsCell (rootLaw t s) by
          simpa [q1R, q1, hd4] using hmodel.2]
        exact pushforward_swapColumns_involutive (rootLaw t s)
  obtain ⟨O⟩ := exists_orientedChartChoice
    (rootLaw s t) (rootLaw t s) q0R q1R 0
    (rootLaw_transpose s t)
    (by simpa only [pushforward_chartTableSymmetry_zero] using hpair)
    hmodelR (by simpa only [pushforward_chartTableSymmetry_zero] using hstrict)
  have hchosenStrict :
      (if O.contactSwapped then rootLaw t s else rootLaw s t) (1, 0) <
        (if O.contactSwapped then rootLaw t s else rootLaw s t) (0, 1) := by
    rw [← O.firstContact_eq]
    cases hroot : O.rootReflected
    · simp only [hroot, Bool.false_eq_true, if_false]
      rw [pushforward_apply_equiv, pushforward_apply_equiv]
      simpa [chartTableSymmetry, TableSymmetry.equiv] using hstrict
    · simp only [hroot, if_true]
      rw [TableSymmetry.equiv, pushforward_trans,
        pushforward_chartTableSymmetry_zero]
      rw [pushforward_apply_equiv, pushforward_apply_equiv]
      simpa [antiDiagonalSymmetry, TableSymmetry.equiv, bitFlip,
        swapRowsCell, swapColumnsCell, transposeCell] using hstrict
  cases hswap : O.contactSwapped with
  | false =>
      have hlt : s < t :=
        rowCubeParameter_lt_of_transpose_strictOffDiagonal
          (rootLaw_transpose s t) (by simpa [hswap] using hchosenStrict)
          hsRow htRow
      refine ⟨O.rootReflected, s, t, hs, hlt, hNA, hND, ?_⟩
      dsimp only
      calc
        _ = rootLaw s t := by
          have hfirst := O.firstContact_eq
          cases hroot : O.rootReflected
          · simp only [hroot, Bool.false_eq_true, if_false, hswap] at hfirst ⊢
            rw [pushforward_chartTableSymmetry_zero] at hfirst
            simpa [q0R, q0] using hfirst
          · simp only [hroot, if_true, hswap, Bool.false_eq_true, if_false] at hfirst ⊢
            rw [TableSymmetry.equiv, pushforward_trans,
              pushforward_chartTableSymmetry_zero] at hfirst
            rw [TableSymmetry.equiv, pushforward_trans]
            simpa [q0R, q0] using hfirst
        _ = _ := by
          funext z
          rcases z with ⟨x, y⟩
          fin_cases x <;> fin_cases y <;> simp [rootLaw] <;> ring
  | true =>
      have hlt : t < s :=
        rowCubeParameter_lt_of_transpose_strictOffDiagonal
          (rootLaw_transpose t s) (by simpa [hswap] using hchosenStrict)
          htRow hsRow
      refine ⟨O.rootReflected, t, s, ht, hlt, ?_, ?_, ?_⟩
      · simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hNA
      · simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hND
      · dsimp only
        calc
          _ = rootLaw t s := by
            have hfirst := O.firstContact_eq
            cases hroot : O.rootReflected
            · simp only [hroot, Bool.false_eq_true, if_false, hswap, if_true] at hfirst ⊢
              rw [pushforward_chartTableSymmetry_zero] at hfirst
              simpa [q0R, q0] using hfirst
            · simp only [hroot, if_true, hswap] at hfirst ⊢
              rw [TableSymmetry.equiv, pushforward_trans,
                pushforward_chartTableSymmetry_zero] at hfirst
              rw [TableSymmetry.equiv, pushforward_trans]
              simpa [q0R, q0] using hfirst
          _ = _ := by
            funext z
            rcases z with ⟨x, y⟩
            fin_cases x <;> fin_cases y <;> simp [rootLaw] <;> ring

/-! ## Oriented contact presentations -/

/-- A two-class chart candidate has an oriented transpose chart with ordered contact roots. -/
theorem exists_orientedTransposeChartWithRoots
    {p : RealTable} (_hp : IsPMF p) (_hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) (hcard : Fintype.card K.κ = 2)
    (j : Fin 8) (A : ChartCandidate K j) :
    ∃ (r : TableSymmetry) (B : TransposeChart) (x low ratio high norm : ℝ),
      B.pi = K.s (A.classEquiv.symm 1) ∧
      B.a = low / norm ∧ B.b = 1 / norm ∧ B.c = ratio / norm ∧
      B.d = high / norm ∧ norm = low + 1 + ratio + high ∧
      0 < x ∧ x < 1 ∧ ratio = x ^ 4 ∧ 0 < low ∧ 0 < high ∧ low ≤ high ∧
      (1 + x ^ 2 + x ^ 4) * low * high = x ^ 4 * (x ^ 2 - low - high) ∧
      (B.pi = (1 : ℝ) / 2 ∨ B.pi < (1 : ℝ) / 2) ∧
      B.firstComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 0)) ∧
      B.secondComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 1)) := by
  obtain ⟨rootReflected, lambda, mu, hlambda, hlt, hNA, hND, hroot⟩ :=
    chartCandidate_hasContactRoots K j A
  let baseSymmetry := if rootReflected then
      TableSymmetry.comp (chartTableSymmetry j) antiDiagonalSymmetry
    else chartTableSymmetry j
  have hroot' :
      pushforward baseSymmetry.equiv (K.Q (A.classEquiv.symm 0)) =
        rootLaw lambda mu := by
    dsimp only at hroot
    change pushforward baseSymmetry.equiv (K.Q (A.classEquiv.symm 0)) = _ at hroot
    rw [hroot]
    funext z
    rcases z with ⟨i, k⟩
    fin_cases i <;> fin_cases k <;> rfl
  have hbasePair :
      pushforward baseSymmetry.equiv (K.Q (A.classEquiv.symm 1)) =
        fun z => pushforward baseSymmetry.equiv
          (K.Q (A.classEquiv.symm 0)) (transposeCell.symm z) := by
    have hd4 := chartTableSymmetry_agreesWithCellEquiv j
    cases hrf : rootReflected
    · simpa [baseSymmetry, hrf, hd4] using A.transpose_pair
    · rw [show baseSymmetry = .comp (chartTableSymmetry j) antiDiagonalSymmetry by
        simp [baseSymmetry, hrf]]
      simp only [TableSymmetry.equiv, pushforward_trans]
      have hpair0 :
          pushforward (chartTableSymmetry j).equiv (K.Q (A.classEquiv.symm 1)) =
            fun z => pushforward (chartTableSymmetry j).equiv
              (K.Q (A.classEquiv.symm 0)) (transposeCell.symm z) := by
        simpa [hd4] using A.transpose_pair
      rw [hpair0, pushforward_antiDiagonal_transpose]
  let x := contactX lambda mu
  have hx := contactX_pos_lt_one hlambda hlt
  have hNA' : 0 < contactNA lambda mu := by
    simpa [contactNA, contactR] using hNA
  have hND' : 0 < contactND lambda mu := by
    simpa [contactND, contactR] using hND
  have hlow := contactA0_pos hlambda hlt hNA'
  have hhigh := contactD0_pos hlambda hlt hND'
  have hrootNorm := rootLaw_eq_normalizedContactTable hlambda hlt
  have hcontact := contact_root_identity hlambda hlt
  by_cases horient : 1 ≤ lambda * mu
  · let low := contactA0 lambda mu
    let ratio := x ^ 4
    let high := contactD0 lambda mu
    let norm := low + 1 + ratio + high
    have hnorm : 0 < norm := by dsimp [norm, low, ratio, high]; positivity
    let B : TransposeChart := {
      a := low / norm, b := 1 / norm, c := ratio / norm, d := high / norm
      pi := K.s (A.classEquiv.symm 1)
      a_pos := div_pos hlow hnorm
      b_pos := div_pos zero_lt_one hnorm
      c_pos := div_pos (pow_pos hx.1 4) hnorm
      d_pos := div_pos hhigh hnorm
      total := by
        change low / norm + 1 / norm + ratio / norm + high / norm = 1
        rw [← add_div, ← add_div, ← add_div]
        exact div_self (ne_of_gt hnorm)
      order := by
        apply div_le_div_of_nonneg_right _ hnorm.le
        dsimp [ratio, x]
        exact pow_le_one₀ hx.1.le hx.2.le
      pi_pos := K.s_pos _
      pi_le_half := A.minority }
    have hfirst :
        B.firstComponent = pushforward baseSymmetry.equiv
          (K.Q (A.classEquiv.symm 0)) := by
      rw [hroot']
      simpa [B, TransposeChart.firstComponent, low, ratio, high, norm, x] using
        hrootNorm.symm
    have hsecond :
        B.secondComponent = pushforward baseSymmetry.equiv
          (K.Q (A.classEquiv.symm 1)) := by
      rw [hbasePair, hroot', hrootNorm]
      funext z
      rcases z with ⟨i, k⟩
      fin_cases i <;> fin_cases k <;> rfl
    refine ⟨baseSymmetry, B, x, low, ratio, high, norm, rfl, rfl, rfl, rfl,
      rfl, rfl, hx.1, hx.2, rfl, hlow, hhigh,
      (contactA0_le_contactD0_iff hlambda hlt).2 horient, ?_,
      eq_or_lt_of_le A.minority, hfirst, hsecond⟩
    simpa [x, low, ratio, high] using hcontact
  · have hltprod : lambda * mu < 1 := lt_of_not_ge horient
    let r := TableSymmetry.comp baseSymmetry antiDiagonalSymmetry
    let low := contactD0 lambda mu
    let ratio := x ^ 4
    let high := contactA0 lambda mu
    let norm := low + 1 + ratio + high
    have hnorm : 0 < norm := by dsimp [norm, low, ratio, high]; positivity
    have hnormSwap :
        contactD0 lambda mu + 1 + x ^ 4 + contactA0 lambda mu =
          contactA0 lambda mu + 1 + x ^ 4 + contactD0 lambda mu := by ring
    let B : TransposeChart := {
      a := low / norm, b := 1 / norm, c := ratio / norm, d := high / norm
      pi := K.s (A.classEquiv.symm 1)
      a_pos := div_pos hhigh hnorm
      b_pos := div_pos zero_lt_one hnorm
      c_pos := div_pos (pow_pos hx.1 4) hnorm
      d_pos := div_pos hlow hnorm
      total := by
        change low / norm + 1 / norm + ratio / norm + high / norm = 1
        rw [← add_div, ← add_div, ← add_div]
        exact div_self (ne_of_gt hnorm)
      order := by
        apply div_le_div_of_nonneg_right _ hnorm.le
        dsimp [ratio, x]
        exact pow_le_one₀ hx.1.le hx.2.le
      pi_pos := K.s_pos _
      pi_le_half := A.minority }
    have hfirst :
        B.firstComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 0)) := by
      simp only [r, TableSymmetry.equiv, pushforward_trans, hroot']
      rw [hrootNorm, pushforward_antiDiagonal_tableOfEntries]
      simp [B, TransposeChart.firstComponent, low, ratio, high, norm, x, hnormSwap]
    have hsecond :
        B.secondComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 1)) := by
      simp only [r, TableSymmetry.equiv, pushforward_trans, hbasePair, hroot']
      rw [pushforward_antiDiagonal_transpose, hrootNorm,
        pushforward_antiDiagonal_tableOfEntries, ← hnormSwap]
      funext z
      rcases z with ⟨i, k⟩
      fin_cases i <;> fin_cases k <;> rfl
    refine ⟨r, B, x, low, ratio, high, norm, rfl, rfl, rfl, rfl, rfl, rfl,
      hx.1, hx.2, rfl, hhigh, hlow,
      ((contactD0_lt_contactA0_iff hlambda hlt).2 hltprod).le, ?_,
      eq_or_lt_of_le A.minority, hfirst, hsecond⟩
    dsimp [x, low, ratio, high]
    calc
      _ = (1 + contactX lambda mu ^ 2 + contactX lambda mu ^ 4) *
          contactA0 lambda mu * contactD0 lambda mu := by ring
      _ = contactX lambda mu ^ 4 *
          (contactX lambda mu ^ 2 - contactA0 lambda mu - contactD0 lambda mu) :=
        hcontact
      _ = _ := by ring

/-- The oriented root packet also identifies the mixture and joint laws. -/
theorem exists_orientedTransposeChartWithRootsAndJoint
    {p : RealTable} (hp : IsPMF p) (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) (hcard : Fintype.card K.κ = 2)
    (j : Fin 8) (A : ChartCandidate K j) :
    ∃ (r : TableSymmetry) (B : TransposeChart) (x low ratio high norm : ℝ),
      B.pi = K.s (A.classEquiv.symm 1) ∧
      B.a = low / norm ∧ B.b = 1 / norm ∧ B.c = ratio / norm ∧
      B.d = high / norm ∧ norm = low + 1 + ratio + high ∧
      0 < x ∧ x < 1 ∧ ratio = x ^ 4 ∧ 0 < low ∧ 0 < high ∧ low ≤ high ∧
      (1 + x ^ 2 + x ^ 4) * low * high = x ^ 4 * (x ^ 2 - low - high) ∧
      (B.pi = (1 : ℝ) / 2 ∨ B.pi < (1 : ℝ) / 2) ∧
      pushforward r.equiv p = B.law ∧
      B.firstComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 0)) ∧
      B.secondComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 1)) ∧
      (Latent.relabel r.equiv K.quotientLatent).joint =
        (Latent.reindex B.latent A.classEquiv).joint := by
  obtain ⟨r, B, x, low, ratio, high, norm, hpi, ha, hb, hc, hd, hnorm,
      hx0, hx1, hratio, hlow, hhigh, horder, heq, hpior, hfirst, hsecond⟩ :=
    exists_orientedTransposeChartWithRoots hp hfull D K hcard j A
  have hprior0 : K.s (A.classEquiv.symm 0) = 1 - B.pi := by
    have hsumAll := K.quotientLatent.prior_isPMF.total
    change (∑ v : K.κ, K.s v) = 1 at hsumAll
    rw [← A.classEquiv.symm.sum_comp K.s] at hsumAll
    have hsum : K.s (A.classEquiv.symm 0) + K.s (A.classEquiv.symm 1) = 1 := by
      simpa [mass, Fin.sum_univ_two] using hsumAll
    rw [← hpi] at hsum
    linarith
  have hlaw : pushforward r.equiv p = B.law := by
    funext z
    have hmix := (Latent.relabel r.equiv K.quotientLatent).mixture z
    have hsum := A.classEquiv.symm.sum_comp
      (fun v => (Latent.relabel r.equiv K.quotientLatent).prior v *
        (Latent.relabel r.equiv K.quotientLatent).comp v z)
    calc
      pushforward r.equiv p z =
          ∑ v : K.κ, (Latent.relabel r.equiv K.quotientLatent).prior v *
            (Latent.relabel r.equiv K.quotientLatent).comp v z := hmix.symm
      _ = ∑ i : Fin 2, (Latent.relabel r.equiv K.quotientLatent).prior
            (A.classEquiv.symm i) * (Latent.relabel r.equiv K.quotientLatent).comp
            (A.classEquiv.symm i) z := hsum.symm
      _ = B.law z := by
        rw [Fin.sum_univ_two]
        simp only [Latent.relabel, Clustering.quotientLatent]
        rw [hprior0, ← hpi, ← hfirst, ← hsecond]
        rfl
  have hjoint : (Latent.relabel r.equiv K.quotientLatent).joint =
      (Latent.reindex B.latent A.classEquiv).joint := by
    funext w
    rcases w with ⟨v, z⟩
    simp only [Latent.joint, stoch_to_det.Latent.joint, Latent.reindex,
      Latent.relabel, Clustering.quotientLatent, TransposeChart.latent]
    generalize hi : A.classEquiv v = i
    have hv : v = A.classEquiv.symm i := by
      rw [← hi]
      exact (A.classEquiv.symm_apply_apply v).symm
    rw [hv]
    change K.s (A.classEquiv.symm i) *
        pushforward r.equiv (K.Q (A.classEquiv.symm i)) z =
      B.prior i * (if i = 0 then B.firstComponent else B.secondComponent) z
    fin_cases i
    · change K.s (A.classEquiv.symm 0) *
          pushforward r.equiv (K.Q (A.classEquiv.symm 0)) z =
        B.prior 0 * B.firstComponent z
      rw [hprior0, ← hfirst]
      rfl
    · change K.s (A.classEquiv.symm 1) *
          pushforward r.equiv (K.Q (A.classEquiv.symm 1)) z =
        B.prior 1 * B.secondComponent z
      rw [← hpi, ← hsecond]
      rfl
  exact ⟨r, B, x, low, ratio, high, norm, hpi, ha, hb, hc, hd, hnorm,
    hx0, hx1, hratio, hlow, hhigh, horder, heq, hpior, hlaw, hfirst, hsecond,
    hjoint⟩

/-- An oriented root packet yields a contact presentation over the original law. -/
theorem exists_contactPresentation_of_orientedPacket
    {p : RealTable} (hp : IsPMF p) (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D) {j : Fin 8} (A : ChartCandidate K j)
    (r : TableSymmetry) (B : TransposeChart) (x low ratio high norm : ℝ)
    (hpi : B.pi = K.s (A.classEquiv.symm 1))
    (ha : B.a = low / norm) (hb : B.b = 1 / norm)
    (hc : B.c = ratio / norm) (hd : B.d = high / norm)
    (hnorm : norm = low + 1 + ratio + high)
    (hx0 : 0 < x) (hx1 : x < 1) (hratio : ratio = x ^ 4)
    (hlow : 0 < low) (hhigh : 0 < high) (horder : low ≤ high)
    (heq : (1 + x ^ 2 + x ^ 4) * low * high =
      x ^ 4 * (x ^ 2 - low - high))
    (hlaw : pushforward r.equiv p = B.law)
    (hfirst : B.firstComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 0)))
    (hsecond : B.secondComponent = pushforward r.equiv (K.Q (A.classEquiv.symm 1)))
    (hjoint : (Latent.relabel r.equiv K.quotientLatent).joint =
      (Latent.reindex B.latent A.classEquiv).joint) :
    ∃ M : ContactPresentation p,
      M.relabel = r ∧ M.chart.toTransposeChart = B ∧ M.chart.lowMass = low ∧
      M.chart.ratio = ratio ∧ M.chart.highMass = high ∧ M.chart.norm = norm ∧
      M.chart.kernel = pushforward r.equiv D.w ∧
      M.chart.ContactEquation x ∧
      M.chart.toTransposeChart.latent.score = K.quotientSeedSetup.L.score ∧
      (∀ g : BinaryCode,
        w3Cost M.chart.toTransposeChart.latent (transportCode r.equiv g) =
          w3Cost K.quotientSeedSetup.L g) ∧
      w3 M.chart.toTransposeChart.latent = w3 K.quotientSeedSetup.L := by
  have hratioPos : 0 < ratio := by rw [hratio]; positivity
  have hnormPos : 0 < norm := by rw [hnorm]; positivity
  have hratioLt : ratio < 1 := by
    rw [hratio]
    exact pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hgap : low * high < ratio := by
    rw [hratio]
    have hlhs : 0 < (1 + x ^ 2 + x ^ 4) * low * high := by positivity
    have hsum : 0 < x ^ 2 - low - high := by nlinarith
    have hfac : 1 < 1 + x ^ 2 + x ^ 4 := by
      nlinarith [sq_pos_of_pos hx0]
    nlinarith [mul_pos hlow hhigh, sq_pos_of_pos hx0]
  have hstrict : B.c < B.b := by
    rw [hc, hb]
    exact (div_lt_div_iff_of_pos_right hnormPos).2 hratioLt
  have hfeasible : Feasible (Finset.univ : Finset Cell) (pushforward r.equiv D.w) := by
    apply feasible_pushforward r
    simpa [support_eq_univ_of_pos hfull] using D.feasible
  have hcontact0 : IsContact (Finset.univ : Finset Cell)
      (pushforward r.equiv D.w) B.firstComponent := by
    rw [hfirst]
    apply isContact_pushforward r
    simpa [support_eq_univ_of_pos hfull] using K.Q_isContact (A.classEquiv.symm 0)
  have hcontact1 : IsContact (Finset.univ : Finset Cell)
      (pushforward r.equiv D.w) B.secondComponent := by
    rw [hsecond]
    apply isContact_pushforward r
    simpa [support_eq_univ_of_pos hfull] using K.Q_isContact (A.classEquiv.symm 1)
  have htau : tau B.law = tau p := by
    calc
      tau B.law = tau (pushforward r.equiv p) := congrArg tau hlaw.symm
      _ = tau p := tau_pushforward r p hp
  have hscore : B.latent.score = (Latent.relabel r.equiv K.quotientLatent).score := by
    have hscoreJoint :
        (Latent.relabel r.equiv K.quotientLatent).score =
          (Latent.reindex B.latent A.classEquiv).score := by
      have hjoint' :
          stoch_to_det.Latent.joint (Latent.relabel r.equiv K.quotientLatent) =
            stoch_to_det.Latent.joint (Latent.reindex B.latent A.classEquiv) := hjoint
      unfold Latent.score stoch_to_det.Latent.score
      rw [hjoint']
      rfl
    calc
      B.latent.score = (Latent.reindex B.latent A.classEquiv).score :=
        (Latent.score_reindex B.latent A.classEquiv).symm
      _ = (Latent.relabel r.equiv K.quotientLatent).score := hscoreJoint.symm
  have hattained : B.latent.score = tau B.law := by
    rw [hscore, Latent.score_relabel r K.quotientLatent,
      K.quotientLatent_score_eq, D.optimal, htau]
  have hscoreQ : B.latent.score = K.quotientSeedSetup.L.score := by
    rw [hscore, Latent.score_relabel r K.quotientLatent]
    rfl
  have hcost (g : BinaryCode) :
      w3Cost B.latent (transportCode r.equiv g) =
        w3Cost K.quotientSeedSetup.L g := by
    calc
      _ = w3Cost (Latent.relabel r.equiv K.quotientLatent)
          (transportCode r.equiv g) :=
        (w3Cost_eq_of_jointPresentation
          (Latent.relabel r.equiv K.quotientLatent) B A.classEquiv hjoint _).symm
      _ = _ := w3Cost_relabel r.equiv K.quotientLatent g
  have hw3 : w3 B.latent = w3 K.quotientSeedSetup.L := by
    calc
      _ = w3 (Latent.relabel r.equiv K.quotientLatent) :=
        (w3_eq_of_jointPresentation
          (Latent.relabel r.equiv K.quotientLatent) B A.classEquiv hjoint).symm
      _ = _ := w3_relabel r.equiv K.quotientLatent
  let C : ContactChart := {
    toTransposeChart := B
    kernel := pushforward r.equiv D.w
    lowMass := low, ratio := ratio, highMass := high, norm := norm
    lowMass_pos := hlow, ratio_pos := hratioPos, highMass_pos := hhigh,
    norm_pos := hnormPos
    norm_eq := hnorm, a_eq := ha, b_eq := hb, c_eq := hc, d_eq := hd
    ratio_lt_one := hratioLt, contactGap := hgap, strictOrder := hstrict
    feasible := hfeasible
    firstComponent_contact := hcontact0
    secondComponent_contact := hcontact1
    attained := hattained }
  let M : ContactPresentation p := { chart := C, relabel := r, oriented_law := hlaw }
  refine ⟨M, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hscoreQ, hcost, hw3⟩
  unfold ContactChart.ContactEquation
  change (1 + x ^ 2 + x ^ 4) * low * high =
    x ^ 4 * (x ^ 2 - (low + high))
  nlinarith [heq]

/-! ## The contact-presentation packet -/

/-- The complete contact presentation attached to an oriented two-class candidate. -/
def CandidatePresentation : Prop :=
  ∀ {p : RealTable} (hp : IsPMF p) (hfull : ∀ z, 0 < p z)
    (D : SeedSetup p) (K : Clustering D)
    (hcard : Fintype.card K.κ = 2)
    (j : Fin 8) (A : ChartCandidate K j),
  ∃ M : ContactPresentation p,
    ∃ P : QuotientPresentation hfull D K M,
    P.labelEquiv = A.classEquiv ∧
    M.chart.kernel = pushforward M.relabel.equiv D.w ∧
    M.chart.toTransposeChart.latent.score = K.quotientSeedSetup.L.score ∧
    K.quotientSeedSetup.L.score = tau p ∧
    (∀ g : BinaryCode,
      w3Cost M.chart.toTransposeChart.latent
          (transportCode M.relabel.equiv g) =
        w3Cost K.quotientSeedSetup.L g) ∧
    w3 M.chart.toTransposeChart.latent = w3 K.quotientSeedSetup.L ∧
    (M.chart.toTransposeChart.pi = (1 : ℝ) / 2 ∨
      M.chart.toTransposeChart.pi < (1 : ℝ) / 2) ∧
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ M.chart.ratio = x ^ 4 ∧
      M.chart.lowMass ≤ M.chart.highMass ∧ M.chart.ContactEquation x

/-- Every oriented two-class candidate has the complete contact-presentation packet. -/
theorem candidatePresentation : CandidatePresentation := by
  intro p hp hfull D K hcard j A
  obtain ⟨r, B, x, low, ratio, high, norm, hpi, ha, hb, hc, hd, hnorm,
      hx0, hx1, hratio, hlow, hhigh, horder, heq, hpior, hlaw, hfirst,
      hsecond, hjoint⟩ :=
    exists_orientedTransposeChartWithRootsAndJoint hp hfull D K hcard j A
  obtain ⟨M, hMr, hMB, hMlow, hMratio, hMhigh, hMnorm, hkernel,
      hcontact, hscore, hcost, hw3⟩ :=
    exists_contactPresentation_of_orientedPacket hp hfull D K A r B x low ratio high norm
      hpi ha hb hc hd hnorm hx0 hx1 hratio hlow hhigh horder heq hlaw hfirst
      hsecond hjoint
  have hprior0 : K.s (A.classEquiv.symm 0) = 1 - B.pi := by
    have hsumAll := K.quotientLatent.prior_isPMF.total
    change (∑ v : K.κ, K.s v) = 1 at hsumAll
    rw [← A.classEquiv.symm.sum_comp K.s] at hsumAll
    have hsum : K.s (A.classEquiv.symm 0) + K.s (A.classEquiv.symm 1) = 1 := by
      simpa [mass, Fin.sum_univ_two] using hsumAll
    rw [← hpi] at hsum
    linarith
  have hprior (v : K.κ) : K.s v = B.prior (A.classEquiv v) := by
    generalize hi : A.classEquiv v = i
    have hv : v = A.classEquiv.symm i := by
      rw [← hi]
      exact (A.classEquiv.symm_apply_apply v).symm
    rw [hv]
    fin_cases i
    · exact hprior0
    · exact hpi.symm
  have hcomp (v : K.κ) : pushforward r.equiv (K.Q v) =
      B.latent.comp (A.classEquiv v) := by
    generalize hi : A.classEquiv v = i
    have hv : v = A.classEquiv.symm i := by
      rw [← hi]
      exact (A.classEquiv.symm_apply_apply v).symm
    rw [hv]
    fin_cases i
    · exact hfirst.symm
    · exact hsecond.symm
  subst r
  subst B
  let P : QuotientPresentation hfull D K M := {
    labelEquiv := A.classEquiv
    prior_eq := by
      intro v
      change K.s v = M.chart.toTransposeChart.prior (A.classEquiv v)
      simpa [orientedQuotientSetup, SeedSetup.relabel,
        Clustering.quotientSeedSetup, Latent.relabel, TransposeChart.latent] using hprior v
    component_eq := by
      intro v z
      change pushforward M.relabel.equiv (K.Q v) z =
        M.chart.toTransposeChart.latent.comp (A.classEquiv v) z
      have hv := congrFun (hcomp v) z
      simpa [orientedQuotientSetup, SeedSetup.relabel,
        Clustering.quotientSeedSetup, Latent.relabel, TransposeChart.latent] using hv
  }
  refine ⟨M, P, rfl, hkernel, hscore, K.quotientSeedSetup.optimal, hcost,
    hw3, hpior, x, hx0, hx1, hMratio.trans hratio, ?_, hcontact⟩
  simpa [hMlow, hMhigh] using horder

/-! ## The one-class branch -/

/-- A latent with a subsingleton label type has zero optimal determinization cost. -/
theorem w3_eq_zero_of_subsingleton
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {p : α × β → ℝ} (L : Latent p) [Subsingleton L.ι] :
    w3 L = 0 := by
  have hlabel : Nonempty L.ι := by
    by_contra h
    let _ : IsEmpty L.ι := not_nonempty_iff.mp h
    have htotal := L.prior_isPMF.total
    simp [mass, stoch_to_det.mass] at htotal
  let i0 : L.ι := Classical.choice hlabel
  have hobs : Nonempty (α × β) := by
    by_contra h
    let _ : IsEmpty (α × β) := not_nonempty_iff.mp h
    have htotal := (L.comp_isPMF i0).total
    simp [mass, stoch_to_det.mass] at htotal
  let g0 : Fin (Fintype.card (α × β)) :=
    ⟨0, Fintype.card_pos_iff.mpr hobs⟩
  let g : Code α β := fun _ => g0
  have hcost : w3Cost L g = 0 := by
    unfold w3Cost condMutualInfo condEntropy
    unfold stoch_to_det.condMI stoch_to_det.condH
    simp only [g]
    have hL : (fun w : L.ι × (α × β) => w.1) = fun _ => i0 := by
      funext w
      exact Subsingleton.elim _ _
    have hLg : entropyOf (fun a : L.ι × (α × β) => (a.1, g0)) L.joint =
        entropyOf (fun a : L.ι × (α × β) => a.1) L.joint := by
      simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
        (fun a : L.ι × (α × β) => a.1) (fun x => (x, g0)) Prod.fst
        (by intro; rfl)
    have hZg : entropyOf (fun a : L.ι × (α × β) => (a.2, g0)) L.joint =
        entropyOf (fun a : L.ι × (α × β) => a.2) L.joint := by
      simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
        (fun a : L.ι × (α × β) => a.2) (fun x => (x, g0)) Prod.fst
        (by intro; rfl)
    have hLZg :
        entropyOf (fun a : L.ι × (α × β) => (a.1, a.2, g0)) L.joint =
          entropyOf (fun a : L.ι × (α × β) => (a.1, a.2)) L.joint := by
      simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
        (fun a : L.ι × (α × β) => (a.1, a.2))
        (fun x => (x.1, x.2, g0)) (fun y => (y.1, y.2.1)) (by intro; rfl)
    have hLZ : entropyOf (fun a : L.ι × (α × β) => (a.1, a.2)) L.joint =
        entropyOf (fun a : L.ι × (α × β) => a.2) L.joint := by
      have hpair : (fun a : L.ι × (α × β) => (a.1, a.2)) =
          fun a => (i0, a.2) := by
        funext a
        exact congrArg (fun i => (i, a.2)) (Subsingleton.elim _ _)
      rw [hpair]
      simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
        (fun a : L.ι × (α × β) => a.2) (fun x => (i0, x)) Prod.snd
        (by intro; rfl)
    have hgL : entropyOf (fun a : L.ι × (α × β) => (g0, a.1)) L.joint =
        entropyOf (fun a : L.ι × (α × β) => a.1) L.joint := by
      simpa [Function.comp_def] using stoch_to_det.Hvar_eq_of_leftInverse L.joint_isPMF
        (fun a : L.ι × (α × β) => a.1) (fun x => (g0, x)) Prod.snd
        (by intro; rfl)
    have hunit : entropyOf (fun _ : L.ι × (α × β) => ()) L.joint = 0 := by
      have hsum : ∑ w, L.joint w = 1 := by
        simpa [mass, stoch_to_det.mass] using L.joint_isPMF.total
      simp [entropyOf, entropy, pushforward, stoch_to_det.Hvar, stoch_to_det.H,
        stoch_to_det.push, stoch_to_det.mass, hsum]
    have hconstL : entropyOf (fun _ : L.ι × (α × β) => i0) L.joint = 0 := by
      apply le_antisymm
      · exact (stoch_to_det.Hvar_comp_le L.joint_isPMF
          (fun _ : L.ι × (α × β) => ()) (fun _ => i0)).trans_eq hunit
      · unfold entropyOf stoch_to_det.Hvar
        exact stoch_to_det.H_nonneg_of_isPMF (stoch_to_det.isPMF_push L.joint_isPMF)
    have hconstG : entropyOf (fun _ : L.ι × (α × β) => g0) L.joint = 0 := by
      apply le_antisymm
      · exact (stoch_to_det.Hvar_comp_le L.joint_isPMF
          (fun _ : L.ι × (α × β) => ()) (fun _ => g0)).trans_eq hunit
      · unfold entropyOf stoch_to_det.Hvar
        exact stoch_to_det.H_nonneg_of_isPMF (stoch_to_det.isPMF_push L.joint_isPMF)
    change stoch_to_det.Hvar (fun a : L.ι × (α × β) => (a.1, g0)) L.joint =
      stoch_to_det.Hvar (fun a : L.ι × (α × β) => a.1) L.joint at hLg
    change stoch_to_det.Hvar (fun a : L.ι × (α × β) => (a.2, g0)) L.joint =
      stoch_to_det.Hvar (fun a : L.ι × (α × β) => a.2) L.joint at hZg
    change stoch_to_det.Hvar
      (fun a : L.ι × (α × β) => (a.1, a.2, g0)) L.joint =
      stoch_to_det.Hvar (fun a : L.ι × (α × β) => (a.1, a.2)) L.joint at hLZg
    change stoch_to_det.Hvar (fun a : L.ι × (α × β) => (a.1, a.2)) L.joint =
      stoch_to_det.Hvar (fun a : L.ι × (α × β) => a.2) L.joint at hLZ
    change stoch_to_det.Hvar (fun a : L.ι × (α × β) => (g0, a.1)) L.joint =
      stoch_to_det.Hvar (fun a : L.ι × (α × β) => a.1) L.joint at hgL
    change stoch_to_det.Hvar (fun _ : L.ι × (α × β) => i0) L.joint = 0 at hconstL
    change stoch_to_det.Hvar (fun _ : L.ι × (α × β) => g0) L.joint = 0 at hconstG
    rw [hLg, hZg, hLZg, hLZ, hgL, hL, hconstL, hconstG]
    ring
  have hcost_nonneg (h : Code α β) : 0 ≤ w3Cost L h := by
    unfold w3Cost
    exact add_nonneg
      (condMutualInfo_nonneg L.joint_isPMF _ _ _)
      (mul_nonneg (by norm_num) (condEntropy_nonneg L.joint_isPMF _ _))
  apply le_antisymm
  · exact (w3_le_w3Cost L g).trans_eq hcost
  · obtain ⟨h, hh⟩ := exists_optimalW3Code L
    rw [← hh]
    exact hcost_nonneg h

/-- In the one-class branch, the quotient seed remains optimal and has zero cost. -/
theorem quotientSeedSetup_optimal_and_w3_eq_zero_of_card_eq_one
    {p : RealTable} (D : SeedSetup p) (K : Clustering D)
    (hcard : Fintype.card K.κ = 1) :
    K.quotientSeedSetup.L.score = tau p ∧ w3 K.quotientSeedSetup.L = 0 := by
  have hle : Fintype.card K.κ ≤ 1 := by omega
  letI : Subsingleton K.κ := Fintype.card_le_one_iff_subsingleton.mp hle
  letI : Subsingleton K.quotientSeedSetup.L.ι := by
    change Subsingleton K.κ
    infer_instance
  exact ⟨K.quotientSeedSetup.optimal,
    w3_eq_zero_of_subsingleton K.quotientSeedSetup.L⟩

/-! ## Selected optimizer normal form -/

/-- A selected full-support binary optimizer either has zero determinization cost or is
presented by an oriented contact chart with its positive contact root. -/
def SelectedOptimizerIsPresented : Prop :=
  ∀ (p : RealTable) (hp : IsPMF p) (hfull : ∀ z, 0 < p z),
  ∃ (D : SeedSetup p) (K : Clustering D),
    Function.Injective K.Q ∧
    K.quotientSeedSetup.L.score = tau p ∧
    (
      (Fintype.card K.κ = 1 ∧
       w3 K.quotientSeedSetup.L = 0 ∧
       w3 D.L = 0)
      ∨
      (Fintype.card K.κ = 2 ∧
       ∃ M : ContactPresentation p,
         ∃ P : QuotientPresentation hfull D K M,
         M.chart.kernel = pushforward M.relabel.equiv D.w ∧
         M.chart.toTransposeChart.latent.score = K.quotientSeedSetup.L.score ∧
         (∀ g : BinaryCode,
           w3Cost M.chart.toTransposeChart.latent
               (transportCode M.relabel.equiv g) =
             w3Cost K.quotientSeedSetup.L g) ∧
         w3 M.chart.toTransposeChart.latent = w3 K.quotientSeedSetup.L ∧
         (M.chart.toTransposeChart.pi = (1 : ℝ) / 2 ∨
           M.chart.toTransposeChart.pi < (1 : ℝ) / 2) ∧
         (∃ x : ℝ, 0 < x ∧ x < 1 ∧ M.chart.ratio = x ^ 4 ∧
           M.chart.lowMass ≤ M.chart.highMass ∧ M.chart.ContactEquation x))
    )

/-- The selected optimizer supplied by the normal form has zero cost or a contact
presentation. -/
theorem selectedOptimizer_zeroOrContactPresentation : SelectedOptimizerIsPresented := by
  intro p hp hfull
  obtain ⟨D, K, hcard⟩ := selectedOptimizerNormalForm p hp hfull
  refine ⟨D, K, K.Q_injective, K.quotientSeedSetup.optimal, ?_⟩
  rcases hcard with hcard | ⟨hcard, j, ⟨A⟩⟩
  · left
    have hzero :=
      quotientSeedSetup_optimal_and_w3_eq_zero_of_card_eq_one D K hcard
    refine ⟨hcard, hzero.2, ?_⟩
    rw [← K.quotientLatent_w3_eq]
    exact hzero.2
  · right
    refine ⟨hcard, ?_⟩
    obtain ⟨M, P, _hlabel, hkernel, hscore, _hoptimal, hcost, hw3, hpi, hroot⟩ :=
      candidatePresentation hp hfull D K hcard j A
    exact ⟨M, P, hkernel, hscore, hcost, hw3, hpi, hroot⟩

end Binary

end

end StochasticToDeterministicLatents
