import StochasticToDeterministicLatents.Binary.FactorTwo.Chord

/-!
# A positive mutual information at the contact

Every earlier module in this lane stops at *nonnegative* mutual information,
which is all `psi_sub_phi_nonneg` gives.  The chord argument's statement of the
constant margin at the upper contact asks for more: that the mutual information
there is strictly positive.  This module supplies it.

The mechanism is the standard divergence bound, specialised to four cells.
Mutual information is the divergence of a law from the product of its
marginals,

`(log 2) I(q) = sum over cells of q z * log (q z / (mX z.1 * mY z.2))`,

and `log x <= x - 1` bounds each term below by `q z - mX z.1 * mY z.2`.  Those
four lower bounds sum to `1 - 1 = 0`, so the mutual information is nonnegative;
and `log x < x - 1` holds strictly away from `x = 1`, so a single cell that
differs from its marginal product makes the whole sum strictly positive.

On a binary table the first cell differs from its marginal product exactly when
the determinant is nonzero -- the module states the direction it uses -- since

`a - (a + b)(a + c) = a(a + b + c + d) - (a + b)(a + c) = ad - bc`

for a law of total mass one.  That is `psi_sub_phi_pos`.

At the upper contact the determinant is nonzero for a reason already proved:
the contact's own diagonal product is `u ^ 2`, so its determinant is
`u ^ 2 - bc`, and the top root of a chord domain exceeds the geometric mean of
the off-diagonal.  Hence `constantMargin_chordTop_pos`.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p q : RealTable} {u : ℝ}

/-! ## The divergence bound, one cell at a time -/

/-- `log (y / x) <= y / x - 1`, cleared of denominators: the divergence bound
for a single cell of positive mass. -/
private theorem cell_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at h
  have hxy : x * (y / x - 1) = y - x := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h hx.le]

/-- The same bound, strict when the cell differs from its comparison value. -/
private theorem cell_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    x - y < x * (Real.log x - Real.log y) := by
  have hne' : y / x ≠ 1 := by
    intro hcon
    rw [div_eq_one_iff_eq (ne_of_gt hx)] at hcon
    exact hne hcon.symm
  have h := Real.log_lt_sub_one_of_pos (div_pos hy hx) hne'
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at h
  have hxy : x * (y / x - 1) = y - x := by field_simp
  nlinarith [mul_lt_mul_of_pos_left h hx]

/-! ## Mutual information cell by cell -/

/-- Mutual information as a sum over cells: `Psi - Phi` pairs each cell with
the logarithm of its ratio to the product of its two marginals. -/
private theorem psi_sub_phi_eq_sum (hq : IsPMF q) :
    Psi q - Phi q = ∑ z, q z * (Real.logb 2 (q z)
      - Real.logb 2 (stoch_to_det.mX q z.1) - Real.logb 2 (stoch_to_det.mY q z.2)) := by
  have hqX : IsPMF (stoch_to_det.mX q) := stoch_to_det.isPMF_push hq
  have hqY : IsPMF (stoch_to_det.mY q) := stoch_to_det.isPMF_push hq
  have h0 : (∑ z, q z * Real.logb 2 (q z)) = -stoch_to_det.H q := sum_mul_logb_self hq
  have hX : (∑ z, q z * Real.logb 2 (stoch_to_det.mX q z.1))
      = -stoch_to_det.H (stoch_to_det.mX q) := by
    rw [← stoch_to_det.sum_push_mul Prod.fst q fun x => Real.logb 2 (stoch_to_det.mX q x)]
    exact sum_mul_logb_self hqX
  have hY : (∑ z, q z * Real.logb 2 (stoch_to_det.mY q z.2))
      = -stoch_to_det.H (stoch_to_det.mY q) := by
    rw [← stoch_to_det.sum_push_mul Prod.snd q fun y => Real.logb 2 (stoch_to_det.mY q y)]
    exact sum_mul_logb_self hqY
  have hsplit : (∑ z, q z * (Real.logb 2 (q z)
      - Real.logb 2 (stoch_to_det.mX q z.1) - Real.logb 2 (stoch_to_det.mY q z.2)))
      = (∑ z, q z * Real.logb 2 (q z))
        - (∑ z, q z * Real.logb 2 (stoch_to_det.mX q z.1))
        - (∑ z, q z * Real.logb 2 (stoch_to_det.mY q z.2)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hsplit, h0, hX, hY]
  show (2 * stoch_to_det.H q - stoch_to_det.H (stoch_to_det.mX q)
      - stoch_to_det.H (stoch_to_det.mY q))
    - (3 * stoch_to_det.H q - 2 * stoch_to_det.H (stoch_to_det.mX q)
      - 2 * stoch_to_det.H (stoch_to_det.mY q)) = _
  ring

/-- The four marginal products sum to one, because each marginal does. -/
private theorem sum_marginal_products (hq : IsPMF q) :
    ∑ z : Cell, stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2 = 1 := by
  have hX := (stoch_to_det.isPMF_push (f := Prod.fst) hq).total
  have hY := (stoch_to_det.isPMF_push (f := Prod.snd) hq).total
  rw [stoch_to_det.mass] at hX hY
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hX, hY]
  norm_num

/-- A nonvanishing determinant makes the first cell differ from the product of
its marginals.  Only this direction is stated; the identity above gives the
converse as well, and nothing here needs it. -/
private theorem cell00_ne_of_det (hq : IsPMF q) (hdet : determinant q ≠ 0) :
    q (0, 0) ≠ stoch_to_det.mX q 0 * stoch_to_det.mY q 0 := by
  rw [marginalX_zero, marginalY_zero]
  intro hcon
  apply hdet
  have ht := hq.total
  rw [stoch_to_det.mass, sum_cells] at ht
  rw [determinant_eq, entryA, entryB, entryC, entryD]
  linear_combination (q (0, 0)) * ht + hcon

/-- **A law of nonvanishing determinant has positive mutual information.**  On
a fully supported binary table a nonvanishing determinant is exactly the
failure of the law to be the product of its own marginals; the direction used
here is that the determinant forces the failure. -/
theorem psi_sub_phi_pos (hq : IsPMF q) (hpos : FullSupport q)
    (hdet : determinant q ≠ 0) : 0 < Psi q - Phi q := by
  have hmX : ∀ z : Cell, 0 < stoch_to_det.mX q z.1 := fun z => marginalX_pos hpos z.1
  have hmY : ∀ z : Cell, 0 < stoch_to_det.mY q z.2 := fun z => marginalY_pos hpos z.2
  have hprod : ∀ z : Cell, 0 < stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2 :=
    fun z => mul_pos (hmX z) (hmY z)
  have hterm : ∀ z : Cell, q z - stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2
      ≤ q z * (Real.log (q z)
        - Real.log (stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2)) :=
    fun z => cell_le (hpos z) (hprod z)
  have hstrict : q (0, 0) - stoch_to_det.mX q 0 * stoch_to_det.mY q 0
      < q (0, 0) * (Real.log (q (0, 0))
        - Real.log (stoch_to_det.mX q 0 * stoch_to_det.mY q 0)) :=
    cell_lt (hpos _) (hprod ((0, 0) : Cell)) (cell00_ne_of_det hq hdet)
  have hlog : ∀ z : Cell, Real.log (stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2)
      = Real.log (stoch_to_det.mX q z.1) + Real.log (stoch_to_det.mY q z.2) :=
    fun z => Real.log_mul (ne_of_gt (hmX z)) (ne_of_gt (hmY z))
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rw [psi_sub_phi_eq_sum hq]
  have hexpand : ∀ z : Cell, q z * (Real.logb 2 (q z)
      - Real.logb 2 (stoch_to_det.mX q z.1) - Real.logb 2 (stoch_to_det.mY q z.2))
      = (q z * (Real.log (q z)
        - Real.log (stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2))) / Real.log 2 := by
    intro z
    rw [hlog z, Real.logb, Real.logb, Real.logb]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun z _ => hexpand z, ← Finset.sum_div]
  refine div_pos ?_ hlog2
  have hsum : ∑ z : Cell, (q z - stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2) = 0 := by
    rw [Finset.sum_sub_distrib, sum_marginal_products hq]
    have ht := hq.total
    rw [stoch_to_det.mass] at ht
    rw [ht]
    ring
  have hlt : ∑ z : Cell, (q z - stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2)
      < ∑ z : Cell, q z * (Real.log (q z)
        - Real.log (stoch_to_det.mX q z.1 * stoch_to_det.mY q z.2)) :=
    Finset.sum_lt_sum (fun z _ => hterm z) ⟨(0, 0), Finset.mem_univ _, hstrict⟩
  rw [hsum] at hlt
  exact hlt

/-! ## The contact -/

/-- The upper contact's diagonal product is `u ^ 2`, so its determinant is
`u ^ 2` less the off-diagonal product. -/
private theorem determinant_contactAt (hpos : FullSupport p) (hu : 0 < u)
    (hnc : Nonconstant p u) :
    determinant (contactAt p u) = u ^ 2 - offDiagonalProduct p := by
  rw [← chordAt_chordTop, determinant_chordAt, chordTop_eq]
  have h := contactRadius_sq hpos hu hnc
  nlinarith [h]

/-- **The constant margin at the upper contact is strictly positive.**  This is
the conjunct the chord-cut argument states and that the tree previously had only
in its nonnegative form: the margin there is the contact's own mutual
information, and the contact is not a product law because its determinant is
`u ^ 2 - bc`, which the top root keeps positive. -/
theorem constantMargin_chordTop_pos (h : ChordDomain p u) :
    0 < constantMargin p u (chordTop p u) := by
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  have hdet : determinant (contactAt p u) ≠ 0 := by
    rw [determinant_contactAt h.fullSupport hu h.nonconstant]
    exact ne_of_gt (by linarith [offDiagonalProduct_lt_sq_topRoot h])
  rw [(constantMargin_chordTop h).1]
  exact psi_sub_phi_pos (isPMF_contactAt h.isPMF h.fullSupport hu h.nonconstant)
    (contactAt_pos h.fullSupport hu h.nonconstant) hdet

end StochasticToDeterministicLatents.Binary
