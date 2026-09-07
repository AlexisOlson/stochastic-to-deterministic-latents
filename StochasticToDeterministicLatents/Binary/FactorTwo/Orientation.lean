import StochasticToDeterministicLatents.Binary.FactorTwo.Defs
import StochasticToDeterministicLatents.Binary.Symmetry
import StochasticToDeterministicLatents.SparseLimit

/-!
# Orienting a binary table

The row swap, the column swap, and the transpose act on binary tables without
changing either optimum.  `Binary.Symmetry` already transports the stochastic
optimum; this module adds the deterministic one, and then uses the group to
normalize an arbitrary law.

Every binary law is carried by a symmetry to one whose determinant is
nonnegative and whose diagonal and off-diagonal entries are each ordered.  A
multiplicative `T`/`tau` bound therefore only has to be proved on that
normalized region: the last theorem here removes the orientation and, through
the sparse-law transfer, the full-support hypothesis as well.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-! ## Deterministic-score transport -/

/-- Conditional mutual information is symmetric in its two arguments. -/
private theorem condMutualInfo_comm {Ω A B C : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] {p : Ω → ℝ} (hp : IsPMF p)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    condMutualInfo f g h p = condMutualInfo g f h p := by
  have htriple : entropyOf (fun w => (f w, g w, h w)) p
      = entropyOf (fun w => (g w, f w, h w)) p :=
    (entropyOf_equiv hp (fun w => (f w, g w, h w))
      ({ toFun := fun z : A × B × C => (z.2.1, z.1, z.2.2)
         invFun := fun z : B × A × C => (z.2.1, z.1, z.2.2)
         left_inv := by rintro ⟨a, b, c⟩; rfl
         right_inv := by rintro ⟨b, a, c⟩; rfl } : A × B × C ≃ B × A × C)).symm
  simp only [entropyOf] at htriple
  unfold condMutualInfo stoch_to_det.condMI
  rw [htriple]
  ring

/-- A product relabeling of the two binary coordinates preserves the score of
the transported code. -/
private theorem detScore_pushforward_prodCongr (ex ey : Bit ≃ Bit)
    {p : RealTable} (hp : IsPMF p) (g : BinaryCode) :
    detScore (pushforward (Equiv.prodCongr ex ey) p)
        (transportCode (Equiv.prodCongr ex ey) g) = detScore p g := by
  have hmi := condMutualInfo_congr_equiv hp ex ey
    (Equiv.refl (Fin (Fintype.card Cell))) Prod.fst Prod.snd g
  have hx := condEntropy_congr_equiv hp (Equiv.refl (Fin (Fintype.card Cell)))
    ex g Prod.fst
  have hy := condEntropy_congr_equiv hp (Equiv.refl (Fin (Fintype.card Cell)))
    ey g Prod.snd
  simp only [Equiv.refl_apply] at hmi hx hy
  have hf : Prod.fst ∘ ⇑(Equiv.prodCongr ex ey) = fun w : Cell => ex (Prod.fst w) := rfl
  have hs : Prod.snd ∘ ⇑(Equiv.prodCongr ex ey) = fun w : Cell => ey (Prod.snd w) := rfl
  have hg : transportCode (Equiv.prodCongr ex ey) g ∘ ⇑(Equiv.prodCongr ex ey) = g := by
    funext z
    exact congrArg g (Equiv.symm_apply_apply _ z)
  unfold detScore
  rw [condMutualInfo_pushforward, condEntropy_pushforward, condEntropy_pushforward,
    hf, hs, hg, hmi, hx, hy]

/-- The transpose preserves the score of the transported code. -/
private theorem detScore_pushforward_transpose {p : RealTable} (hp : IsPMF p)
    (g : BinaryCode) :
    detScore (pushforward transposeCell p) (transportCode transposeCell g)
      = detScore p g := by
  have hf : Prod.fst ∘ ⇑transposeCell = (Prod.snd : Cell → Bit) := rfl
  have hs : Prod.snd ∘ ⇑transposeCell = (Prod.fst : Cell → Bit) := rfl
  have hg : transportCode transposeCell g ∘ ⇑transposeCell = g := by
    funext z
    exact congrArg g (Equiv.symm_apply_apply _ z)
  unfold detScore
  rw [condMutualInfo_pushforward, condEntropy_pushforward, condEntropy_pushforward,
    hf, hs, hg, condMutualInfo_comm hp]
  ring

private theorem detScore_pushforward_aux (r : TableSymmetry) :
    ∀ p : RealTable, IsPMF p → ∀ g : BinaryCode,
      detScore (pushforward r.equiv p) (transportCode r.equiv g) = detScore p g := by
  induction r with
  | refl =>
      intro p _ g
      have hid : pushforward (Equiv.refl Cell) p = p := by
        funext z
        rw [pushforward_apply_equiv]
        rfl
      show detScore (pushforward (Equiv.refl Cell) p)
          (transportCode (Equiv.refl Cell) g) = detScore p g
      rw [hid]
      rfl
  | swapRows =>
      intro p hp g
      exact detScore_pushforward_prodCongr bitFlip (Equiv.refl Bit) hp g
  | swapColumns =>
      intro p hp g
      exact detScore_pushforward_prodCongr (Equiv.refl Bit) bitFlip hp g
  | transpose =>
      intro p hp g
      exact detScore_pushforward_transpose hp g
  | comp a b iha ihb =>
      intro p hp g
      show detScore (pushforward (a.equiv.trans b.equiv) p)
          (transportCode (a.equiv.trans b.equiv) g) = detScore p g
      rw [pushforward_trans]
      exact (ihb _ (pushforward_isPMF hp) (transportCode a.equiv g)).trans (iha p hp g)

/-- A binary table symmetry preserves the score of the transported code. -/
theorem detScore_pushforward (r : TableSymmetry) (p : RealTable) (hp : IsPMF p)
    (g : BinaryCode) :
    detScore (pushforward r.equiv p) (transportCode r.equiv g) = detScore p g :=
  detScore_pushforward_aux r p hp g

/-- Binary table symmetries preserve the deterministic optimum. -/
theorem T_pushforward (r : TableSymmetry) (p : RealTable) (hp : IsPMF p) :
    T (pushforward r.equiv p) = T p := by
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg⟩ := exists_optimalCode p
    calc T (pushforward r.equiv p)
        ≤ detScore (pushforward r.equiv p) (transportCode r.equiv g) :=
          T_le_detScore _ _
      _ = detScore p g := detScore_pushforward r p hp g
      _ = T p := hg
  · obtain ⟨g, hg⟩ := exists_optimalCode (pushforward r.equiv p)
    have h := detScore_pushforward r p hp (transportCode r.equiv.symm g)
    rw [transportCode_transportCode] at h
    calc T p ≤ detScore p (transportCode r.equiv.symm g) := T_le_detScore _ _
      _ = detScore (pushforward r.equiv p) g := h.symm
      _ = T (pushforward r.equiv p) := hg

/-! ## Cell and determinant transport

Only three of the eight symmetries are needed to orient a table: the column
swap reverses the sign of the determinant, the transpose exchanges the two
off-diagonal entries, and the anti-transpose exchanges the two diagonal
entries.  Each fixes what the previous one arranged. -/

/-- Reflection in the anti-diagonal: transpose, then exchange both labels. -/
private def antiTranspose : TableSymmetry :=
  .comp .transpose (.comp .swapRows .swapColumns)

private theorem bitFlip_zero : bitFlip 0 = 1 := Equiv.swap_apply_left 0 1

private theorem bitFlip_one : bitFlip 1 = 0 := Equiv.swap_apply_right 0 1

private theorem swapColumns_symm (z : Cell) :
    TableSymmetry.swapColumns.equiv.symm z = (z.1, bitFlip z.2) := rfl

private theorem transpose_symm (z : Cell) :
    TableSymmetry.transpose.equiv.symm z = (z.2, z.1) := rfl

private theorem antiTranspose_symm (z : Cell) :
    antiTranspose.equiv.symm z = (bitFlip z.2, bitFlip z.1) := rfl

private theorem cells_swapColumns (p : RealTable) :
    entryA (pushforward TableSymmetry.swapColumns.equiv p) = entryB p ∧
      entryB (pushforward TableSymmetry.swapColumns.equiv p) = entryA p ∧
      entryC (pushforward TableSymmetry.swapColumns.equiv p) = entryD p ∧
      entryD (pushforward TableSymmetry.swapColumns.equiv p) = entryC p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [entryA, entryB, entryC, entryD, pushforward_apply_equiv,
      swapColumns_symm, bitFlip_zero, bitFlip_one]

private theorem cells_transpose (p : RealTable) :
    entryA (pushforward TableSymmetry.transpose.equiv p) = entryA p ∧
      entryB (pushforward TableSymmetry.transpose.equiv p) = entryC p ∧
      entryC (pushforward TableSymmetry.transpose.equiv p) = entryB p ∧
      entryD (pushforward TableSymmetry.transpose.equiv p) = entryD p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [entryA, entryB, entryC, entryD, pushforward_apply_equiv, transpose_symm]

private theorem cells_antiTranspose (p : RealTable) :
    entryA (pushforward antiTranspose.equiv p) = entryD p ∧
      entryB (pushforward antiTranspose.equiv p) = entryB p ∧
      entryC (pushforward antiTranspose.equiv p) = entryC p ∧
      entryD (pushforward antiTranspose.equiv p) = entryA p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [entryA, entryB, entryC, entryD, pushforward_apply_equiv,
      antiTranspose_symm, bitFlip_zero, bitFlip_one]

private theorem determinant_swapColumns (p : RealTable) :
    determinant (pushforward TableSymmetry.swapColumns.equiv p) = -determinant p := by
  obtain ⟨hA, hB, hC, hD⟩ := cells_swapColumns p
  rw [determinant_eq, determinant_eq, hA, hB, hC, hD]
  ring

private theorem determinant_transpose (p : RealTable) :
    determinant (pushforward TableSymmetry.transpose.equiv p) = determinant p := by
  obtain ⟨hA, hB, hC, hD⟩ := cells_transpose p
  rw [determinant_eq, determinant_eq, hA, hB, hC, hD]
  ring

private theorem determinant_antiTranspose (p : RealTable) :
    determinant (pushforward antiTranspose.equiv p) = determinant p := by
  obtain ⟨hA, hB, hC, hD⟩ := cells_antiTranspose p
  rw [determinant_eq, determinant_eq, hA, hB, hC, hD]
  ring

/-! ## Orienting an arbitrary law

The three steps are taken in the order in which they do not disturb each
other: the column swap fixes the sign of the determinant, the transpose then
orders the off-diagonal without touching the determinant, and the
anti-transpose finally orders the diagonal without touching either. -/

private theorem exists_diagonal_ordered (p : RealTable) (hp : IsPMF p)
    (hpos : FullSupport p) (hdet : 0 ≤ determinant p)
    (hcb : entryC p ≤ entryB p) :
    ∃ q : RealTable, IsPMF q ∧ FullSupport q ∧ 0 ≤ determinant q ∧
      entryD q ≤ entryA q ∧ entryC q ≤ entryB q ∧ tau q = tau p ∧ T q = T p := by
  by_cases hda : entryD p ≤ entryA p
  · exact ⟨p, hp, hpos, hdet, hda, hcb, rfl, rfl⟩
  · obtain ⟨hA, hB, hC, hD⟩ := cells_antiTranspose p
    refine ⟨pushforward antiTranspose.equiv p, pushforward_isPMF hp,
      fun z => pushforward_pos hpos _ z, ?_, ?_, ?_,
      tau_pushforward antiTranspose p hp, T_pushforward antiTranspose p hp⟩
    · rw [determinant_antiTranspose]
      exact hdet
    · rw [hA, hD]
      exact le_of_not_ge hda
    · rw [hB, hC]
      exact hcb

private theorem exists_ordered (p : RealTable) (hp : IsPMF p) (hpos : FullSupport p)
    (hdet : 0 ≤ determinant p) :
    ∃ q : RealTable, IsPMF q ∧ FullSupport q ∧ 0 ≤ determinant q ∧
      entryD q ≤ entryA q ∧ entryC q ≤ entryB q ∧ tau q = tau p ∧ T q = T p := by
  by_cases hcb : entryC p ≤ entryB p
  · exact exists_diagonal_ordered p hp hpos hdet hcb
  · obtain ⟨-, hB, hC, -⟩ := cells_transpose p
    obtain ⟨q, hq, hqpos, hqdet, hda, hqcb, htau, hT⟩ :=
      exists_diagonal_ordered (pushforward TableSymmetry.transpose.equiv p)
        (pushforward_isPMF hp) (fun z => pushforward_pos hpos _ z)
        (by rw [determinant_transpose]; exact hdet)
        (by rw [hB, hC]; exact le_of_not_ge hcb)
    exact ⟨q, hq, hqpos, hqdet, hda, hqcb,
      htau.trans (tau_pushforward .transpose p hp),
      hT.trans (T_pushforward .transpose p hp)⟩

/-- Every fully supported binary law is carried by a symmetry to one with a
nonnegative determinant and both its diagonal and its off-diagonal entries
ordered, at the same pair of optima. -/
private theorem exists_oriented (p : RealTable) (hp : IsPMF p) (hpos : FullSupport p) :
    ∃ q : RealTable, IsPMF q ∧ FullSupport q ∧ 0 ≤ determinant q ∧
      entryD q ≤ entryA q ∧ entryC q ≤ entryB q ∧ tau q = tau p ∧ T q = T p := by
  by_cases hdet : 0 ≤ determinant p
  · exact exists_ordered p hp hpos hdet
  · obtain ⟨q, hq, hqpos, hqdet, hda, hcb, htau, hT⟩ :=
      exists_ordered (pushforward TableSymmetry.swapColumns.equiv p)
        (pushforward_isPMF hp) (fun z => pushforward_pos hpos _ z)
        (by rw [determinant_swapColumns]; exact neg_nonneg.mpr (le_of_not_ge hdet))
    exact ⟨q, hq, hqpos, hqdet, hda, hcb,
      htau.trans (tau_pushforward .swapColumns p hp),
      hT.trans (T_pushforward .swapColumns p hp)⟩

/-! ## Reducing a multiplicative bound to the oriented region -/

/-- A nonnegative multiplicative `T`/`tau` bound proved only on the oriented
region -- full support, nonnegative determinant, both pairs ordered -- holds
for every binary law.  The orientation is removed by the symmetries above and
the full-support hypothesis by the sparse-law transfer. -/
theorem T_le_mul_tau_of_oriented {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ q : RealTable, IsPMF q → FullSupport q → 0 ≤ determinant q →
      entryD q ≤ entryA q → entryC q ≤ entryB q → T q ≤ C * tau q)
    (p : RealTable) (hp : IsPMF p) : T p ≤ C * tau p := by
  refine T_le_mul_tau_of_forall_fullSupport hC ?_ p hp
  intro w hw hwpos
  obtain ⟨q, hq, hqpos, hqdet, hda, hcb, htau, hT⟩ := exists_oriented w hw hwpos
  rw [← htau, ← hT]
  exact h q hq hqpos hqdet hda hcb

end StochasticToDeterministicLatents.Binary
