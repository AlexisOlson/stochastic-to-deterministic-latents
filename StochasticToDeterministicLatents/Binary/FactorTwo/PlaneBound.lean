import StochasticToDeterministicLatents.Binary.FactorTwo.Center
import StochasticToDeterministicLatents.Binary.FactorTwo.Planes
import StochasticToDeterministicLatents.Binary.FactorTwo.Shape

/-!
# The plane bound, as a function of the imbalance

Fix a reference plane and a law on the centre seam: off-diagonal mass `1/8`,
split between the two off-diagonal cells as `(1 + z)/16` and `(1 - z)/16`.
Pairing the plane against that law and feeding the result to
`centerConstantScalar` gives a function of `z` alone, `centerPlaneBound`.  This
module shows it is **concave** on `[0, 1]`, which is what lets four values at
four endpoints cover a whole range of `z`.

The constant fed to `centerConstantScalar` is

```
(7/8) log K - ((1 + z)/16) log L_b - ((1 - z)/16) log L_c
```

for a plane with values `K`, `L_b`, `L_c`, and that is `Real.log 2` times the
pairing of `tangentCert_referencePlane` against
`cellTable (7/16) ((1+z)/16) ((1-z)/16) (7/16)`: the certificate is `logb 2 K`
at both diagonal cells and `-logb 2 L_b`, `-logb 2 L_c` off them, and the
diagonal cells carry `7/16` each.  The signs are read off the certificate, and
`centerConstantScalar` subtracts twice its argument because that argument is
the contact's `Phi` in natural-log units.

Nothing here connects the bound to a margin.  That step needs the pairing
inequality and belongs where the seam is closed.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

variable {z : ℝ}

/-! ## The bound and its two derivatives -/

/-- The constant code's margin at a seam law of imbalance `z`, bounded below
through the plane `P`.  The off-diagonal mass is `1/8` throughout. -/
noncomputable def centerPlaneBound (P : ReferencePlane) (z : ℝ) : ℝ :=
  centerConstantScalar (1 / 8) z
    ((7 / 8) * Real.log P.diagValue
      - ((1 + z) / 16) * Real.log P.offValueB
      - ((1 - z) / 16) * Real.log P.offValueC)

/-- The derivative of `centerPlaneBound` in `z`.  The plane enters only
through the ratio of its two off-diagonal values. -/
private noncomputable def centerPlaneDeriv (P : ReferencePlane) (z : ℝ) : ℝ :=
  (5 / 16) * Real.log ((1 - z) / (1 + z))
    + (3 / 8) * Real.log ((8 + z) / (8 - z))
    + (1 / 8) * (Real.log P.offValueB - Real.log P.offValueC)

/-- The second derivative, which no longer mentions the plane at all: the
plane contributes a term linear in `z`. -/
private noncomputable def centerPlaneDeriv2 (z : ℝ) : ℝ :=
  -5 / (8 * (1 - z ^ 2)) + 6 / (64 - z ^ 2)

/-! ## Regularity -/

private theorem centerPlaneBound_continuous (P : ReferencePlane) :
    Continuous (centerPlaneBound P) := by
  unfold centerPlaneBound centerConstantScalar centerLogEntropy
    centerMarginalEntropy xLogX
  fun_prop

private theorem centerPlaneBound_hasDerivAt (P : ReferencePlane)
    (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (centerPlaneBound P) (centerPlaneDeriv P z) z := by
  rcases hz with ⟨hz0, hz1⟩
  have hp : 0 < (1 + z) / 16 := by nlinarith
  have hm : 0 < (1 - z) / 16 := by nlinarith
  have h8p : 0 < (1 + (1 / 8 : ℝ) * z) / 2 := by nlinarith
  have h8m : 0 < (1 - (1 / 8 : ℝ) * z) / 2 := by nlinarith
  have hJp : HasDerivAt (fun x : ℝ => xLogX ((1 + x) / 16))
      ((1 / 16) * (Real.log ((1 + z) / 16) + 1)) z := by
    unfold xLogX
    convert (Real.hasDerivAt_mul_log hp.ne').comp z
      (((hasDerivAt_id z).const_add 1).div_const 16) using 1
    all_goals first | rfl | ring
  have hJm : HasDerivAt (fun x : ℝ => xLogX ((1 - x) / 16))
      ((-1 / 16) * (Real.log ((1 - z) / 16) + 1)) z := by
    unfold xLogX
    convert (Real.hasDerivAt_mul_log hm.ne').comp z
      (((hasDerivAt_const z 1).sub (hasDerivAt_id z)).div_const 16) using 1
    all_goals first | rfl | ring
  have hRp : HasDerivAt (fun x : ℝ => xLogX ((1 + (1 / 8 : ℝ) * x) / 2))
      ((1 / 16) * (Real.log ((1 + (1 / 8 : ℝ) * z) / 2) + 1)) z := by
    unfold xLogX
    convert (Real.hasDerivAt_mul_log h8p.ne').comp z
      (((hasDerivAt_const z 1).add
        ((hasDerivAt_const z (1 / 8)).mul (hasDerivAt_id z))).div_const 2) using 1
    all_goals first | rfl | ring
  have hRm : HasDerivAt (fun x : ℝ => xLogX ((1 - (1 / 8 : ℝ) * x) / 2))
      ((-1 / 16) * (Real.log ((1 - (1 / 8 : ℝ) * z) / 2) + 1)) z := by
    unfold xLogX
    convert (Real.hasDerivAt_mul_log h8m.ne').comp z
      (((hasDerivAt_const z 1).sub
        ((hasDerivAt_const z (1 / 8)).mul (hasDerivAt_id z))).div_const 2) using 1
    all_goals first | rfl | ring
  have hLb : HasDerivAt (fun x : ℝ => ((1 + x) / 16) * Real.log P.offValueB)
      ((1 / 16) * Real.log P.offValueB) z := by
    convert (((hasDerivAt_const z 1).add (hasDerivAt_id z)).div_const 16).const_mul
      (Real.log P.offValueB) using 1
    all_goals try rfl
    · funext x
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hLc : HasDerivAt (fun x : ℝ => ((1 - x) / 16) * Real.log P.offValueC)
      ((-1 / 16) * Real.log P.offValueC) z := by
    convert (((hasDerivAt_const z 1).sub (hasDerivAt_id z)).div_const 16).const_mul
      (Real.log P.offValueC) using 1
    all_goals try rfl
    · funext x
      simp only [Pi.sub_apply, id_eq]
      ring
    · ring
  have hlin : HasDerivAt
      (fun x : ℝ => (7 / 8) * Real.log P.diagValue
        - ((1 + x) / 16) * Real.log P.offValueB
        - ((1 - x) / 16) * Real.log P.offValueC)
      (-((1 / 16) * Real.log P.offValueB) + (1 / 16) * Real.log P.offValueC) z := by
    convert ((hasDerivAt_const z ((7 / 8) * Real.log P.diagValue)).sub hLb).sub hLc
      using 1
    all_goals first | rfl | ring
  have hconst : HasDerivAt (fun _ : ℝ => -2 * xLogX (7 / 16)) 0 z :=
    hasDerivAt_const z _
  have h := ((((hconst.sub hJp).sub hJm).const_mul 5).sub
      ((hRp.neg.sub hRm).const_mul 6)).sub (hlin.const_mul 2)
  convert h using 1
  all_goals try rfl
  · funext x
    simp only [centerPlaneBound, centerConstantScalar, centerLogEntropy,
      centerMarginalEntropy]
    norm_num
    ring_nf
  · unfold centerPlaneDeriv
    have heq1 : (1 - z) / (1 + z) = ((1 - z) / 16) / ((1 + z) / 16) := by
      field_simp
    rw [heq1, Real.log_div hm.ne' hp.ne']
    have heq : (8 + z) / (8 - z) =
        ((1 + (1 / 8 : ℝ) * z) / 2) / ((1 - (1 / 8 : ℝ) * z) / 2) := by
      field_simp
    rw [heq, Real.log_div h8p.ne' h8m.ne']
    ring

private theorem centerPlaneDeriv_hasDerivAt (P : ReferencePlane)
    (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (centerPlaneDeriv P) (centerPlaneDeriv2 z) z := by
  rcases hz with ⟨hz0, hz1⟩
  have h1m : 1 - z ≠ 0 := by nlinarith
  have h1p : 1 + z ≠ 0 := by nlinarith
  have h8p : 8 + z ≠ 0 := by nlinarith
  have h8m : 8 - z ≠ 0 := by nlinarith
  have hleft : HasDerivAt (fun x : ℝ => Real.log ((1 - x) / (1 + x)))
      ((-1) / (1 - z) - 1 / (1 + z)) z := by
    have hq := ((hasDerivAt_const z 1).sub (hasDerivAt_id z)).div
      ((hasDerivAt_const z 1).add (hasDerivAt_id z)) h1p
    convert (Real.hasDerivAt_log (div_ne_zero h1m h1p)).comp z hq using 1
    all_goals try rfl
    simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    field_simp [h1m, h1p]
    ring
  have hright : HasDerivAt (fun x : ℝ => Real.log ((8 + x) / (8 - x)))
      (1 / (8 + z) + 1 / (8 - z)) z := by
    have hq := ((hasDerivAt_const z 8).add (hasDerivAt_id z)).div
      ((hasDerivAt_const z 8).sub (hasDerivAt_id z)) h8m
    convert (Real.hasDerivAt_log (div_ne_zero h8p h8m)).comp z hq using 1
    all_goals try rfl
    simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    field_simp [h8p, h8m]
    ring
  have h := ((hleft.const_mul (5 / 16)).add (hright.const_mul (3 / 8))).add_const
      ((1 / 8) * (Real.log P.offValueB - Real.log P.offValueC))
  rw [show centerPlaneDeriv P = _ from rfl]
  convert h using 1
  all_goals try rfl
  change -5 / (8 * (1 - z ^ 2)) + 6 / (64 - z ^ 2) = _
  have hs1 : 1 - z ^ 2 ≠ 0 := by nlinarith [mul_pos hz0 (sub_pos.mpr hz1)]
  have hs64 : 64 - z ^ 2 ≠ 0 := by nlinarith [mul_pos hz0 (sub_pos.mpr hz1)]
  field_simp [h1m, h1p, h8p, h8m, hs1, hs64]
  ring

/-! ## Concavity -/

/-- **The plane bound is concave in the imbalance**, on the whole of `[0, 1]`.
The second derivative is `-5 / (8 (1 - z^2)) + 6 / (64 - z^2)`, whose numerator
over the common denominator is negative for every `z` in the interval, so no
positivity of the plane's values is needed. -/
theorem centerPlaneBound_concaveOn (P : ReferencePlane) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (centerPlaneBound P) := by
  refine concaveOn_Icc_of_hasDerivAt2_nonpos 0 1 (centerPlaneBound P)
    (centerPlaneDeriv P) centerPlaneDeriv2 (centerPlaneBound_continuous P).continuousOn
    (fun t ht => centerPlaneBound_hasDerivAt P ht)
    (fun t ht => centerPlaneDeriv_hasDerivAt P ht) ?_
  rintro t ⟨ht0, ht1⟩
  unfold centerPlaneDeriv2
  have hden1 : 0 < 8 * (1 - t ^ 2) := by nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
  have hden2 : 0 < 64 - t ^ 2 := by nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
  rw [div_add_div _ _ hden1.ne' hden2.ne']
  refine div_nonpos_of_nonpos_of_nonneg ?_ ?_
  · nlinarith [sq_nonneg t]
  · positivity

end StochasticToDeterministicLatents.Binary
