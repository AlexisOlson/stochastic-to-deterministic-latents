import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shape lemmas for the chord margins

The two margins of the binary factor-two argument are scalar functions of the
diagonal split `t` along a chord.  This module isolates everything about them
that is pure real analysis: it mentions no probability law, no code, and no
information quantity, and it imports nothing from this library.

Three families live here.

* A **curvature calculus**.  Along the chord the singleton margin has second
  derivative proportional to a fixed combination of reciprocals, which
  `singletonCurvature_neg` shows is negative; the constant margin has second
  derivative proportional to `constantCurvatureNumerator`, a quadratic in the
  diagonal product `t (s - t)` whose sign changes at most once
  (`constantCurvature_sign_switch`).

* Two **transfer lemmas** that turn those sign facts into shape facts:
  `concaveOn_Icc_of_hasDerivAt2_nonpos` and
  `min_endpoints_le_of_curvature_switch`.  A function whose derivative rises
  and then falls attains its minimum on any subinterval at an endpoint.

* The **norm-gate quartic** `normGateQuartic_nonneg`, a scalar nonnegativity
  used where the optimizer's norm gate is discharged.

The four monotonicity helpers and `concaveOn_Icc_of_hasDerivAt2_nonpos` are
thin wrappers over Mathlib's `monotoneOn_of_deriv_nonneg`,
`antitoneOn_of_deriv_nonpos`, and `concaveOn_of_hasDerivWithinAt2_nonpos`.
They contribute no mathematics; their whole content is converting a
`HasDerivAt` hypothesis on the open interval into the `HasDerivWithinAt` form
those lemmas ask for.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-! ## The singleton margin's curvature -/

private theorem reciprocalK_mul_den (t b c : ℝ) (ht : 0 < t) (hb : 0 < b) (hc : 0 < c) :
    t * (t + b) * (t + c) * (t + b + c) *
        (-5 / t + 3 / (t + b) + 3 / (t + c) - 1 / (t + b + c))
      = -(2 * (b + c) * t ^ 2 + (2 * (b + c) ^ 2 + 6 * b * c) * t + 5 * b * c * (b + c)) := by
  field_simp
  ring

private theorem reciprocalE_mul_den (d b c : ℝ) (hd : 0 < d) (hb : 0 < b) (hc : 0 < c) :
    d * (d + b) * (d + c) * (-2 / d + 1 / (d + b) + 1 / (d + c))
      = -((b + c) * d + 2 * b * c) := by
  field_simp
  ring

private theorem reciprocalK_neg (t b c : ℝ) (ht : 0 < t) (hb : 0 < b) (hc : 0 < c) :
    -5 / t + 3 / (t + b) + 3 / (t + c) - 1 / (t + b + c) < 0 := by
  have hp : 0 < t * (t + b) * (t + c) * (t + b + c) := by positivity
  have hn : 0 < 2 * (b + c) * t ^ 2 + (2 * (b + c) ^ 2 + 6 * b * c) * t + 5 * b * c * (b + c) := by
    positivity
  have he := reciprocalK_mul_den t b c ht hb hc
  nlinarith

private theorem reciprocalE_neg (d b c : ℝ) (hd : 0 < d) (hb : 0 < b) (hc : 0 < c) :
    -2 / d + 1 / (d + b) + 1 / (d + c) < 0 := by
  have hp : 0 < d * (d + b) * (d + c) := by positivity
  have hn : 0 < (b + c) * d + 2 * b * c := by positivity
  have he := reciprocalE_mul_den d b c hd hb hc
  nlinarith

/-- The singleton margin's second derivative along the chord is negative.
Here `t` and `d` are the two diagonal cells and `b`, `c` the off-diagonal
cells; the expression is the margin's curvature up to the positive factor
`log 2`. -/
theorem singletonCurvature_neg (t d b c : ℝ) (ht : 0 < t) (hd : 0 < d) (hb : 0 < b)
    (hc : 0 < c) :
    -5 / t - 2 / d + 3 / (t + b) + 3 / (t + c) + 1 / (d + c) + 1 / (d + b)
        - 1 / (t + b + c) < 0 := by
  have hK := reciprocalK_neg t b c ht hb hc
  have hE := reciprocalE_neg d b c hd hb hc
  have hid :
      (-5 / t - 2 / d + 3 / (t + b) + 3 / (t + c) + 1 / (d + c) + 1 / (d + b)
          - 1 / (t + b + c)) =
        (-5 / t + 3 / (t + b) + 3 / (t + c) - 1 / (t + b + c)) +
          (-2 / d + 1 / (d + b) + 1 / (d + c)) := by ring
  rw [hid]
  linarith

/-! ## The constant margin's curvature -/

private theorem pair_reciprocal_eq (t d b : ℝ) (h1 : 0 < t + b) (h2 : 0 < d + b) :
    1 / (t + b) + 1 / (d + b) = (t + d + 2 * b) / (t * d + b * (t + d + b)) := by
  have hprod : t * d + b * (t + d + b) = (t + b) * (d + b) := by ring
  rw [hprod]
  field_simp
  ring

/-- The numerator of the constant margin's second derivative, as a quadratic in
the diagonal product `xi = t (s - t)`. -/
noncomputable def constantCurvatureNumerator (s b c xi : ℝ) : ℝ :=
  -5 * s * (xi + b * (s + b)) * (xi + c * (s + c)) + 3 * (s + 2 * b) * xi * (xi + c * (s + c))
    + 3 * (s + 2 * c) * xi * (xi + b * (s + b))

private theorem constantCurvatureNumerator_expand (s b c xi : ℝ) :
    constantCurvatureNumerator s b c xi = (s + 6 * (b + c)) * xi ^ 2
      + (-2 * s * (b * (s + b) + c * (s + c)) + 6 * (b * (c * (s + c)) + c * (b * (s + b)))) * xi
      + (-5 * s * (b * (s + b)) * (c * (s + c))) := by
  unfold constantCurvatureNumerator
  ring

/-- The constant margin's curvature, in quotient form: a positive denominator
times `constantCurvatureNumerator` at the diagonal product. -/
theorem constantCurvature_eq_numerator_div (t s b c : ℝ) (ht : 0 < t) (hd : 0 < s - t)
    (hb : 0 < b) (hc : 0 < c) :
    -5 * (1 / t + 1 / (s - t)) + 3 * (1 / (t + b) + 1 / (s - t + c))
        + 3 * (1 / (t + c) + 1 / (s - t + b))
      = constantCurvatureNumerator s b c (t * (s - t)) /
        ((t * (s - t)) * (t * (s - t) + b * (s + b)) * (t * (s - t) + c * (s + c))) := by
  have htd : 0 < t * (s - t) := mul_pos ht hd
  have hs : 0 < s := by linarith
  have hB : 0 < t * (s - t) + b * (s + b) := by positivity
  have hC : 0 < t * (s - t) + c * (s + c) := by positivity
  have hsum : t + (s - t) = s := by ring
  have hbase : 1 / t + 1 / (s - t) = s / (t * (s - t)) := by
    field_simp
    ring
  have hbpair := pair_reciprocal_eq t (s - t) b (by positivity) (by positivity)
  have hcpair := pair_reciprocal_eq t (s - t) c (by positivity) (by positivity)
  rw [hsum] at hbpair hcpair
  rw [show -5 * (1 / t + 1 / (s - t)) + 3 * (1 / (t + b) + 1 / (s - t + c)) +
      3 * (1 / (t + c) + 1 / (s - t + b)) =
      -5 * (1 / t + 1 / (s - t)) + 3 * (1 / (t + b) + 1 / (s - t + b)) +
      3 * (1 / (t + c) + 1 / (s - t + c)) by ring]
  rw [hbase, hbpair, hcpair]
  unfold constantCurvatureNumerator
  field_simp [ht.ne', hd.ne', htd.ne', hB.ne', hC.ne']

private theorem quadratic_cross (a b c x y : ℝ) :
    x * (a * y ^ 2 + b * y + c) - y * (a * x ^ 2 + b * x + c) = (y - x) * (a * x * y - c) := by
  ring

/-- An upward quadratic with a negative value at zero keeps its sign to the
right: once it is nonnegative it stays nonnegative, and where it is nonpositive
it was nonpositive to the left. -/
private theorem quadratic_sign_propagation (a b c x y : ℝ) (ha : 0 < a) (hc : c < 0)
    (hx : 0 < x) (hxy : x ≤ y) :
    (0 ≤ a * x ^ 2 + b * x + c → 0 ≤ a * y ^ 2 + b * y + c) ∧
      (a * y ^ 2 + b * y + c ≤ 0 → a * x ^ 2 + b * x + c ≤ 0) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hpos : 0 < a * x * y - c := by nlinarith [mul_pos (mul_pos ha hx) hy]
  have hfac : 0 ≤ (y - x) * (a * x * y - c) := mul_nonneg (sub_nonneg.mpr hxy) hpos.le
  have hid := quadratic_cross a b c x y
  constructor <;> intro hsign <;> nlinarith

/-- The diagonal product `t (s - t)` decreases on the upper half of the
diagonal. -/
private theorem diagonalProduct_antitoneOn (s A : ℝ) :
    AntitoneOn (fun t => t * (s - t)) (Set.Icc (s / 2) A) := by
  intro x hx y hy hxy
  have hsxy : 0 ≤ x + y - s := by linarith [hx.1, hy.1]
  have hprod : 0 ≤ (y - x) * (x + y - s) := mul_nonneg (sub_nonneg.mpr hxy) hsxy
  nlinarith

/-- The constant margin's curvature changes sign at most once on the upper half
of the diagonal: it is nonnegative up to some `c0` and nonpositive after it. -/
theorem constantCurvature_sign_switch (s b c A : ℝ) (hs : 0 < s) (hA : s / 2 ≤ A) (hAs : A < s)
    (hb : 0 < b) (hc : 0 < c) :
    ∃ c0 ∈ Set.Icc (s / 2) A,
      (∀ t ∈ Set.Ioo (s / 2) c0, 0 ≤ constantCurvatureNumerator s b c (t * (s - t))) ∧
        (∀ t ∈ Set.Ioo c0 A, constantCurvatureNumerator s b c (t * (s - t)) ≤ 0) := by
  set theta : ℝ → ℝ := fun t => t * (s - t) with htheta
  set kappa : ℝ → ℝ := fun t => constantCurvatureNumerator s b c (theta t) with hkappa
  have ha : 0 < s + 6 * (b + c) := by positivity
  have hprodpos : 0 < s * (b * (s + b)) * (c * (s + c)) := by positivity
  have hgamma : -5 * s * (b * (s + b)) * (c * (s + c)) < 0 := by nlinarith
  have hthetapos : ∀ t ∈ Set.Icc (s / 2) A, 0 < theta t := by
    intro t ht
    simp only [htheta]
    exact mul_pos (by linarith [ht.1]) (by linarith [ht.2])
  have hanti : AntitoneOn theta (Set.Icc (s / 2) A) := diagonalProduct_antitoneOn s A
  have hprop : ∀ x y : ℝ, 0 < x → x ≤ y →
      (0 ≤ constantCurvatureNumerator s b c x → 0 ≤ constantCurvatureNumerator s b c y) ∧
        (constantCurvatureNumerator s b c y ≤ 0 →
          constantCurvatureNumerator s b c x ≤ 0) := by
    intro x y hx hxy
    have hp := quadratic_sign_propagation
      (s + 6 * (b + c))
      (-2 * s * (b * (s + b) + c * (s + c)) + 6 * (b * (c * (s + c)) + c * (b * (s + b))))
      (-5 * s * (b * (s + b)) * (c * (s + c))) x y ha hgamma hx hxy
    simpa only [← constantCurvatureNumerator_expand] using hp
  by_cases hL : kappa (s / 2) ≤ 0
  · refine ⟨s / 2, ⟨le_rfl, hA⟩, ?_, ?_⟩
    · intro t ht
      exact (lt_asymm ht.1 ht.2).elim
    · intro t ht
      exact (hprop (theta t) (theta (s / 2)) (hthetapos t ⟨ht.1.le, ht.2.le⟩)
        (hanti ⟨le_rfl, hA⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le)).2 hL
  · by_cases hR : 0 ≤ kappa A
    · refine ⟨A, ⟨hA, le_rfl⟩, ?_, ?_⟩
      · intro t ht
        exact (hprop (theta A) (theta t) (hthetapos A ⟨hA, le_rfl⟩)
          (hanti ⟨ht.1.le, ht.2.le⟩ ⟨hA, le_rfl⟩ ht.2.le)).1 hR
      · intro t ht
        exact (lt_asymm ht.1 ht.2).elim
    · have hcont : Continuous kappa := by
        simp only [hkappa, htheta, constantCurvatureNumerator]
        fun_prop
      have hzmem : (0 : ℝ) ∈ Set.Icc (kappa A) (kappa (s / 2)) :=
        ⟨le_of_not_ge hR, le_of_not_ge hL⟩
      obtain ⟨c0, hc0, hzero⟩ := (intermediate_value_Icc' hA hcont.continuousOn) hzmem
      refine ⟨c0, hc0, ?_, ?_⟩
      · intro t ht
        refine (hprop (theta c0) (theta t) (hthetapos c0 hc0)
          (hanti ⟨ht.1.le, ht.2.le.trans hc0.2⟩ hc0 ht.2.le)).1 ?_
        exact le_of_eq (by simpa [hkappa] using hzero.symm)
      · intro t ht
        refine (hprop (theta t) (theta c0) (hthetapos t ⟨hc0.1.trans ht.1.le, ht.2.le⟩)
          (hanti hc0 ⟨hc0.1.trans ht.1.le, ht.2.le⟩ ht.1.le)).2 ?_
        exact le_of_eq (by simpa [hkappa] using hzero)

/-! ## From derivative signs to shape

The five lemmas below carry no mathematics of their own: each converts a
`HasDerivAt` hypothesis stated on the open interval into the
`HasDerivWithinAt` or `deriv` form that the corresponding Mathlib lemma
expects.
-/

private theorem monotoneOn_left_of_hasDerivAt_nonneg (L A c0 : ℝ) (g h : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc L A))
    (hgh : ∀ t ∈ Set.Ioo L A, HasDerivAt g (h t) t)
    (hc : c0 ∈ Set.Icc L A) (hleft : ∀ t ∈ Set.Ioo L c0, 0 ≤ h t) :
    MonotoneOn g (Set.Icc L c0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc L c0)
  · exact hg.mono (Set.Icc_subset_Icc_right hc.2)
  · intro t ht
    rw [interior_Icc] at ht
    exact (hgh t ⟨ht.1, ht.2.trans_le hc.2⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hgh t ⟨ht.1, ht.2.trans_le hc.2⟩).deriv]
    exact hleft t ht

private theorem antitoneOn_right_of_hasDerivAt_nonpos (L A c0 : ℝ) (g h : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc L A))
    (hgh : ∀ t ∈ Set.Ioo L A, HasDerivAt g (h t) t)
    (hc : c0 ∈ Set.Icc L A) (hright : ∀ t ∈ Set.Ioo c0 A, h t ≤ 0) :
    AntitoneOn g (Set.Icc c0 A) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc c0 A)
  · exact hg.mono (Set.Icc_subset_Icc_left hc.1)
  · intro t ht
    rw [interior_Icc] at ht
    exact (hgh t ⟨hc.1.trans_lt ht.1, ht.2⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hgh t ⟨hc.1.trans_lt ht.1, ht.2⟩).deriv]
    exact hright t ht

private theorem monotoneOn_of_hasDerivAt_nonneg (L A : ℝ) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc L A))
    (hfg : ∀ t ∈ Set.Ioo L A, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.Ioo L A, 0 ≤ g t) : MonotoneOn f (Set.Icc L A) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc L A) hf
  · intro t ht
    rw [interior_Icc] at ht
    exact (hfg t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hfg t ht).deriv]
    exact hg t ht

private theorem antitoneOn_of_hasDerivAt_nonpos (L A : ℝ) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc L A))
    (hfg : ∀ t ∈ Set.Ioo L A, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.Ioo L A, g t ≤ 0) : AntitoneOn f (Set.Icc L A) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc L A) hf
  · intro t ht
    rw [interior_Icc] at ht
    exact (hfg t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hfg t ht).deriv]
    exact hg t ht

/-- A function whose derivative vanishes at the left endpoint and whose second
derivative is nonnegative then nonpositive attains, on every subinterval, a
value at least the smaller of the two endpoint values. -/
theorem min_endpoints_le_of_curvature_switch (L A c0 : ℝ) (f g h : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc L A)) (hg : ContinuousOn g (Set.Icc L A))
    (hfg : ∀ t ∈ Set.Ioo L A, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Set.Ioo L A, HasDerivAt g (h t) t)
    (hgL : g L = 0) (hc : c0 ∈ Set.Icc L A)
    (hleft : ∀ t ∈ Set.Ioo L c0, 0 ≤ h t)
    (hright : ∀ t ∈ Set.Ioo c0 A, h t ≤ 0) :
    ∀ x y z, x ∈ Set.Icc L A → z ∈ Set.Icc L A → x ≤ y → y ≤ z →
      min (f x) (f z) ≤ f y := by
  have gmono := monotoneOn_left_of_hasDerivAt_nonneg L A c0 g h hg hgh hc hleft
  have ganti := antitoneOn_right_of_hasDerivAt_nonpos L A c0 g h hg hgh hc hright
  intro x y z hx hz hxy hyz
  have hy : y ∈ Set.Icc L A := ⟨hx.1.trans hxy, hyz.trans hz.2⟩
  by_cases hyc : y ≤ c0
  · have fmono : MonotoneOn f (Set.Icc L y) := by
      apply monotoneOn_of_hasDerivAt_nonneg L y f g
      · exact hf.mono (Set.Icc_subset_Icc_right hy.2)
      · intro t ht
        exact hfg t ⟨ht.1, ht.2.trans_le hy.2⟩
      · intro t ht
        have hgt := gmono ⟨le_rfl, hc.1⟩ ⟨ht.1.le, ht.2.le.trans hyc⟩ ht.1.le
        simpa [hgL] using hgt
    exact (min_le_left _ _).trans (fmono ⟨hx.1, hxy⟩ ⟨hy.1, le_rfl⟩ hxy)
  · have hcy : c0 ≤ y := le_of_not_ge hyc
    rcases le_total 0 (g y) with hgy | hgy
    · have fmono : MonotoneOn f (Set.Icc L y) := by
        apply monotoneOn_of_hasDerivAt_nonneg L y f g
        · exact hf.mono (Set.Icc_subset_Icc_right hy.2)
        · intro t ht
          exact hfg t ⟨ht.1, ht.2.trans_le hy.2⟩
        · intro t ht
          by_cases htc : t ≤ c0
          · have hgt := gmono ⟨le_rfl, hc.1⟩ ⟨ht.1.le, htc⟩ ht.1.le
            simpa [hgL] using hgt
          · exact hgy.trans (ganti
              ⟨le_of_not_ge htc, ht.2.le.trans hy.2⟩ ⟨hcy, hy.2⟩ ht.2.le)
      exact (min_le_left _ _).trans (fmono ⟨hx.1, hxy⟩ ⟨hy.1, le_rfl⟩ hxy)
    · have fanti : AntitoneOn f (Set.Icc y A) := by
        apply antitoneOn_of_hasDerivAt_nonpos y A f g
        · exact hf.mono (Set.Icc_subset_Icc_left hy.1)
        · intro t ht
          exact hfg t ⟨hy.1.trans_lt ht.1, ht.2⟩
        · intro t ht
          exact (ganti ⟨hcy, hy.2⟩ ⟨hcy.trans ht.1.le, ht.2.le⟩ ht.1.le).trans hgy
      exact (min_le_right _ _).trans (fanti ⟨le_rfl, hy.2⟩ ⟨hyz, hz.2⟩ hyz)

/-- Concavity on a closed interval from a nonpositive second derivative,
supplied as `HasDerivAt` witnesses on the open interval. -/
theorem concaveOn_Icc_of_hasDerivAt2_nonpos (L A : ℝ) (f g h : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc L A))
    (hfg : ∀ t ∈ Set.Ioo L A, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Set.Ioo L A, HasDerivAt g (h t) t)
    (hneg : ∀ t ∈ Set.Ioo L A, h t ≤ 0) : ConcaveOn ℝ (Set.Icc L A) f := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc L A) hf
  · intro t ht
    exact (hfg t (by simpa [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    exact (hgh t (by simpa [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    exact hneg t (by simpa [interior_Icc] using ht)

/-! ## The norm-gate quartic

The norm gate of the optimizer argument reduces to the nonnegativity of

`A x^4 + 2 A x^3 - 3 V x^2 + 2 E x + E`

for `x >= 0`, under the gate inequality `V^3 <= A E (A + E + 3 V)`.  This is
scalar algebra in `A`, `E`, `V`, `x`; the binary meaning of the three
coefficients is supplied where the gate is discharged.

The proof substitutes cube roots `alpha^3 = A`, `epsilon^3 = E`, `y^3 = x`,
which turns the gate into `V <= alpha epsilon (alpha + epsilon)` and the
quartic into a three-term AM-GM.
-/

private theorem gate_degenerate_V_eq_zero (A E V : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (h : V ^ 3 ≤ A * E * (A + E + 3 * V)) (hzero : A = 0 ∨ E = 0) : V = 0 := by
  rcases hzero with rfl | rfl <;> simp at h
  all_goals
    by_contra hn
    have hp : 0 < V ^ 3 := pow_pos (lt_of_le_of_ne hV (Ne.symm hn)) _
    linarith

private theorem cbrt_pos_and_cube (A : ℝ) (hA : 0 < A) :
    0 < A ^ ((1 : ℝ) / 3) ∧ (A ^ ((1 : ℝ) / 3)) ^ 3 = A := by
  constructor
  · exact Real.rpow_pos_of_pos hA _
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    norm_num

private theorem three_mul_le_sum_cubes (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    3 * p * q * r ≤ p ^ 3 + q ^ 3 + r ^ 3 := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p),
    mul_nonneg (add_nonneg (add_nonneg hp hq) hr)
      (add_nonneg (add_nonneg (sq_nonneg (p - q)) (sq_nonneg (q - r)))
        (sq_nonneg (r - p)))]

private theorem quartic_amgm_bound (a e y : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e) (hy : 0 ≤ y) :
    3 * a * e * (a + e) * y ^ 6 ≤
      a ^ 3 * y ^ 12 + 2 * a ^ 3 * y ^ 9 + 2 * e ^ 3 * y ^ 3 + e ^ 3 := by
  have h1 := three_mul_le_sum_cubes (a * y ^ 4) (e * y) (e * y)
    (mul_nonneg ha (pow_nonneg hy _)) (mul_nonneg he hy) (mul_nonneg he hy)
  have h2 := three_mul_le_sum_cubes (a * y ^ 3) (a * y ^ 3) e
    (mul_nonneg ha (pow_nonneg hy _)) (mul_nonneg ha (pow_nonneg hy _)) he
  ring_nf at h1 h2 ⊢
  nlinarith

/-- Under the gate, `V` is bounded by the symmetric function of the cube
roots. -/
private theorem gate_V_le_symmetric (a e V : ℝ) (ha : 0 < a) (he : 0 < e) (hV : 0 ≤ V)
    (h : V ^ 3 ≤ a ^ 3 * e ^ 3 * (a ^ 3 + e ^ 3 + 3 * V)) :
    V ≤ a * e * (a + e) := by
  let s := a * e * (a + e)
  have hspos : 0 < s := mul_pos (mul_pos ha he) (add_pos ha he)
  by_contra hn
  have hs : s < V := lt_of_not_ge hn
  have hs2 : 4 * a ^ 3 * e ^ 3 ≤ s ^ 2 := by
    dsimp [s]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (a - e)) (sq_nonneg a)) (sq_nonneg e)]
  have hfac : 0 < V ^ 2 + V * s + s ^ 2 - 3 * a ^ 3 * e ^ 3 := by
    have hVs : 0 ≤ V * s := mul_nonneg hV hspos.le
    have hcube : 0 < a ^ 3 * e ^ 3 := mul_pos (pow_pos ha _) (pow_pos he _)
    nlinarith [sq_nonneg V]
  have hprod := mul_pos (sub_pos.mpr hs) hfac
  have hid : V ^ 3 - s ^ 3 - 3 * a ^ 3 * e ^ 3 * (V - s) =
      (V - s) * (V ^ 2 + V * s + s ^ 2 - 3 * a ^ 3 * e ^ 3) := by ring
  have hscube : s ^ 3 = a ^ 3 * e ^ 3 * (a ^ 3 + e ^ 3 + 3 * s) := by
    dsimp [s]
    ring
  nlinarith

private theorem normGateQuartic_nonneg_of_pos (A E V x : ℝ) (hA : 0 < A) (hE : 0 < E)
    (hV : 0 ≤ V) (h : V ^ 3 ≤ A * E * (A + E + 3 * V)) (hx : 0 ≤ x) :
    0 ≤ A * x ^ 4 + 2 * A * x ^ 3 - 3 * V * x ^ 2 + 2 * E * x + E := by
  let a := A ^ ((1 : ℝ) / 3)
  let e := E ^ ((1 : ℝ) / 3)
  let y := x ^ ((1 : ℝ) / 3)
  obtain ⟨ha, hacube⟩ := cbrt_pos_and_cube A hA
  obtain ⟨he, hecube⟩ := cbrt_pos_and_cube E hE
  have hy : 0 ≤ y := Real.rpow_nonneg hx _
  have hycube : y ^ 3 = x := by
    dsimp [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hgate : V ^ 3 ≤ a ^ 3 * e ^ 3 * (a ^ 3 + e ^ 3 + 3 * V) := by
    rw [hacube, hecube]
    exact h
  have hVs := gate_V_le_symmetric a e V ha he hV hgate
  have hpoly := quartic_amgm_bound a e y ha.le he.le hy
  rw [← hacube, ← hecube, ← hycube]
  ring_nf at hpoly ⊢
  nlinarith [pow_nonneg hy 6]

/-- The norm-gate quartic is nonnegative on the nonnegative reals whenever the
gate inequality `V ^ 3 <= A * E * (A + E + 3 * V)` holds. -/
theorem normGateQuartic_nonneg (A E V : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (h : V ^ 3 ≤ A * E * (A + E + 3 * V)) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ A * x ^ 4 + 2 * A * x ^ 3 - 3 * V * x ^ 2 + 2 * E * x + E := by
  rcases eq_or_lt_of_le hA with hAz | hApos
  · have hVz := gate_degenerate_V_eq_zero A E V hA hE hV h (Or.inl hAz.symm)
    subst A
    subst V
    have hx1 : 0 ≤ x ^ 3 := pow_nonneg hx _
    nlinarith [mul_nonneg hE hx, mul_nonneg hE hx1]
  rcases eq_or_lt_of_le hE with hEz | hEpos
  · have hVz := gate_degenerate_V_eq_zero A E V hA hE hV h (Or.inr hEz.symm)
    subst E
    subst V
    have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx _
    have hx4 : 0 ≤ x ^ 4 := pow_nonneg hx _
    nlinarith [mul_nonneg hA hx3, mul_nonneg hA hx4]
  exact normGateQuartic_nonneg_of_pos A E V x hApos hEpos hV h hx

end StochasticToDeterministicLatents.Binary
