import StochasticToDeterministicLatents.Binary.FactorTwo.CenterMajorant

/-!
# Four reference planes

`CenterMajorant` bounds `Phi` at a chord's centre by the pairing with the
contact plane of any other chord domain.  This module supplies four such laws,
with every entry an explicit rational, and evaluates their planes in closed
form.

Each plane is fixed by three rational numbers -- `certDiagonal` at the two
diagonal cells and `certOffDiagonal` in the two orders off it -- so its four
values are the logarithms of those three, and the bound a plane gives is a
rational combination of them, with no reference to the optimum of the law being
bounded.  The four are chosen to cover the imbalance
`z` in four ranges; which one applies where is a later module's business, and
nothing here mentions a range.

The reference law of the argument is a plane's **contact**, not the plane's own
law: a law whose diagonal product is exactly the square of its top root fails
`Nonconstant`, so it is never a chord domain.  The laws below are chord
domains; the certificates are taken at their contacts.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
Selected follow-on working material is adapted with public names and
module boundaries; it is unpublished and supplies no verification evidence.
-/

namespace StochasticToDeterministicLatents.Binary

/-! ## An explicit table -/

/-- The binary table with the four given cells, in row-major order.  The tree
writes this pattern inline wherever it builds a table from cells; it is named
here because the four reference laws below all need it. -/
noncomputable def cellTable (a b c d : ℝ) : RealTable := fun z =>
  if z = (0, 0) then a else if z = (0, 1) then b else if z = (1, 0) then c else d

/-! ## The planes -/

/-- An explicit law together with its top root and the three rational values
its contact's tangent certificate takes. -/
structure ReferencePlane where
  /-- The law, which is a chord domain at `root`. -/
  law : RealTable
  /-- The top root of the law's cubic. -/
  root : ℝ
  /-- The common value of `certDiagonal` at the two diagonal cells. -/
  diagValue : ℝ
  /-- The value of `certOffDiagonal` at the cell `(0,1)`. -/
  offValueB : ℝ
  /-- The value of `certOffDiagonal` at the cell `(1,0)`. -/
  offValueC : ℝ

/-- The four reference planes. -/
noncomputable def referencePlanes : Fin 4 → ReferencePlane :=
  ![⟨cellTable (119 / 270) (8 / 135) (8 / 135) (119 / 270),
      28 / 135, 375 / 343, 8 / 375, 8 / 375⟩,
    ⟨cellTable (4635 / 10642) (1029 / 10642) (343 / 10642) (4635 / 10642),
      2205 / 10642, 190304 / 172125, 5831 / 120192, 5831 / 903944⟩,
    ⟨cellTable (1665 / 3806) (441 / 3806) (35 / 3806) (1665 / 3806),
      315 / 1903, 2941 / 2640, 1078 / 14013, 154 / 249985⟩,
    ⟨cellTable (6345 / 14324) (3249 / 28648) (19 / 28648) (6345 / 14324),
      855 / 7162, 640999 / 576000, 2888 / 32229, 152 / 114738821⟩]

/-! ## Each is a chord domain -/

/-- **Every reference law is a chord domain at its root.**  Each of the seven
conditions is a rational inequality in four explicit cells. -/
theorem chordDomain_referencePlane (i : Fin 4) :
    ChordDomain (referencePlanes i).law (referencePlanes i).root := by
  have hpos : FullSupport (referencePlanes i).law := by
    intro z
    rcases z with ⟨x, y⟩
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      norm_num [referencePlanes, cellTable]
  have hu : 0 < (referencePlanes i).root := by
    fin_cases i <;> norm_num [referencePlanes]
  have hroot : cubic (referencePlanes i).law (referencePlanes i).root = 0 := by
    fin_cases i <;>
      norm_num [referencePlanes, cellTable, cubic, offDiagonalMass,
        offDiagonalProduct_eq, diagonalMass, entryA, entryB, entryC, entryD]
  refine ⟨⟨fun z => (hpos z).le, ?_⟩, hpos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stoch_to_det.mass, sum_cells]
    fin_cases i <;> norm_num [referencePlanes, cellTable]
  · fin_cases i <;>
      norm_num [referencePlanes, cellTable, determinant_eq, entryA, entryB, entryC,
        entryD]
  · refine isTopRoot_of_pos_root ?_ ?_ hu hroot
    · fin_cases i <;>
        norm_num [referencePlanes, cellTable, offDiagonalProduct_eq, entryB, entryC]
    · fin_cases i <;>
        norm_num [referencePlanes, cellTable, diagonalMass, entryA, entryD]
  · rw [Nonconstant, show (referencePlanes i).root
      = |(referencePlanes i).root| from (abs_of_pos hu).symm, ← Real.sqrt_sq_eq_abs,
      Real.sqrt_lt_sqrt_iff (by positivity)]
    fin_cases i <;>
      norm_num [referencePlanes, cellTable, diagonalProduct_eq, entryA, entryD]
  · fin_cases i <;> norm_num [referencePlanes, cellTable, entryA, entryD]
  · fin_cases i <;> norm_num [referencePlanes, cellTable, entryB, entryC]

/-! ## Each plane in closed form -/

/-- The three rational constants are the closed forms of `CertValues` at the
reference law's contact. -/
private theorem cert_referencePlane (i : Fin 4) :
    certDiagonal (diagonalMass (contactAt (referencePlanes i).law
        (referencePlanes i).root)) (referencePlanes i).root
      = (referencePlanes i).diagValue
    ∧ certOffDiagonal (entryB (contactAt (referencePlanes i).law
        (referencePlanes i).root)) (entryC (contactAt (referencePlanes i).law
        (referencePlanes i).root)) (referencePlanes i).root
      = (referencePlanes i).offValueB
    ∧ certOffDiagonal (entryC (contactAt (referencePlanes i).law
        (referencePlanes i).root)) (entryB (contactAt (referencePlanes i).law
        (referencePlanes i).root)) (referencePlanes i).root
      = (referencePlanes i).offValueC := by
  have hs : ∀ i : Fin 4, diagonalMass (contactAt (referencePlanes i).law
      (referencePlanes i).root) = diagonalMass (referencePlanes i).law := by
    intro i
    simp only [diagonalMass, entryA, entryD, contactAt]
    norm_num
    ring
  have hb : ∀ i : Fin 4, entryB (contactAt (referencePlanes i).law
      (referencePlanes i).root) = entryB (referencePlanes i).law := by
    intro i; simp [entryB, contactAt]
  have hc : ∀ i : Fin 4, entryC (contactAt (referencePlanes i).law
      (referencePlanes i).root) = entryC (referencePlanes i).law := by
    intro i; simp [entryC, contactAt]
  rw [hs i, hb i, hc i]
  refine ⟨?_, ?_, ?_⟩ <;>
    · fin_cases i <;>
        norm_num [referencePlanes, cellTable, certDiagonal, certOffDiagonal,
          diagonalMass, entryA, entryB, entryC, entryD]

/-- **The tangent certificate at each reference plane's contact, cell by
cell.**  Three rational numbers, and the two diagonal cells share one. -/
theorem tangentCert_referencePlane (i : Fin 4) :
    tangentCert (contactAt (referencePlanes i).law (referencePlanes i).root) (0, 0)
        = Real.logb 2 (referencePlanes i).diagValue
      ∧ tangentCert (contactAt (referencePlanes i).law (referencePlanes i).root) (1, 1)
        = Real.logb 2 (referencePlanes i).diagValue
      ∧ tangentCert (contactAt (referencePlanes i).law (referencePlanes i).root) (0, 1)
        = -Real.logb 2 (referencePlanes i).offValueB
      ∧ tangentCert (contactAt (referencePlanes i).law (referencePlanes i).root) (1, 0)
        = -Real.logb 2 (referencePlanes i).offValueC := by
  have h := chordDomain_referencePlane i
  have hu := topRoot_pos h.isPMF h.fullSupport h.topRoot
  obtain ⟨v00, v11, v01, v10⟩ := tangentCert_contact_values
    (isPMF_contactAt h.isPMF h.fullSupport hu h.nonconstant)
    (contactAt_pos h.fullSupport hu h.nonconstant) hu
    (chordTop_mul_chordBottom h)
    (by rw [← chordAt_chordTop, cubic_chordAt]; exact h.topRoot.2.1)
  obtain ⟨eK, eB, eC⟩ := cert_referencePlane i
  exact ⟨by rw [v00, eK], by rw [v11, eK], by rw [v01, eB], by rw [v10, eC]⟩

end StochasticToDeterministicLatents.Binary
