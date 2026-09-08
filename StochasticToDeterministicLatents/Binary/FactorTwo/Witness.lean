/-
Adapted from `DLorell/stoch_to_det` (Apache-2.0).  The statement and its
argument are this tree's own; two short proof scripts follow the upstream
repository's, one of them restated here without the probability hypothesis
it carries there.
-/
import StochasticToDeterministicLatents.Binary.FactorTwo
import StochasticToDeterministicLatents.Binary.FactorTwo.Orientation

/-!
# Five codes suffice for the factor-two bound

`T_le_two_mul_tau` bounds an infimum over the whole code space.  The claim it
settles says more: on full support one of **five** named codes -- the constant
code, or one of the four singletons -- already has deterministic score at most
twice the stochastic optimum.  This module states that.  It narrows the code
space; it is not a sharpness claim, and nothing here says the bound is met
with equality.

Almost all of it was already there.  Bounding an infimum from above meant
exhibiting a competitor, and the chord argument's competitors are the constant
code and the code isolating the last cell; `chordMargin_witness` is that step
with the codes kept rather than discarded.  Two things had to be added.

**The constant code's score.**  `T_le_psi_sub_phi` bounds `T` by the mutual
information through the constant *latent*, and names no code.
`detScore_constantCode` computes the constant *code* directly:
conditioning on a constant changes no entropy, so its two conditional entropy
terms vanish and its conditional mutual information is the plain mutual
information `Psi - Phi`.

**Why the statement carries four singletons.**  The chord argument runs on the
oriented region, and a general law reaches it through the table symmetries.  A
bound on `T` and `tau` survives that passage by itself, since both are
invariant; a named code does not, and has to be carried back.  Pulling a code
back along a relabelling of the cells sends the constant code to itself and the
singleton at `c` to the singleton at the preimage of `c`, so the five-code set
is closed under the group and the transport goes through.  That closure is what
makes four singletons *sufficient*.  Nothing here shows they are necessary: no
declaration states that a smaller set of codes would fail.

The full-support hypothesis is the claim's own.  It is not removed by the
sparse-law transfer, which preserves the two optima but not a code.
-/

namespace StochasticToDeterministicLatents.Binary

variable {p : RealTable}

/-! ## The constant code's score -/

private theorem hvar_pair_const {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (k : B) :
    stoch_to_det.Hvar (fun w => (f w, k)) m = stoch_to_det.Hvar f m :=
  le_antisymm
    (stoch_to_det.Hvar_comp_le hm f (fun a => (a, k)))
    (stoch_to_det.Hvar_comp_le hm (fun w => (f w, k)) Prod.fst)

private theorem hvar_const_pair {Ω A B : Type*} [Fintype Ω]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → A) (k : B) :
    stoch_to_det.Hvar (fun w => (k, f w)) m = stoch_to_det.Hvar f m :=
  le_antisymm
    (stoch_to_det.Hvar_comp_le hm f (fun a => (k, a)))
    (stoch_to_det.Hvar_comp_le hm (fun w => (k, f w)) Prod.snd)

private theorem hvar_const {Ω B : Type*} [Fintype Ω]
    [Fintype B] [DecidableEq B] {m : Ω → ℝ} (hm : IsPMF m) (k : B) :
    stoch_to_det.Hvar (fun _ : Ω => k) m = 0 := by
  have hsum : ∑ z, m z = 1 := by simpa [stoch_to_det.mass] using hm.total
  have hunit : stoch_to_det.Hvar (fun _ : Ω => ()) m = 0 := by
    simp [stoch_to_det.Hvar, stoch_to_det.H, stoch_to_det.push,
      stoch_to_det.mass, hsum]
  refine le_antisymm ?_ (entropy_nonneg (pushforward_isPMF hm))
  calc stoch_to_det.Hvar (fun _ : Ω => k) m
      ≤ stoch_to_det.Hvar (fun _ : Ω => ()) m :=
        stoch_to_det.Hvar_comp_le hm (fun _ : Ω => ()) (fun _ => k)
    _ = 0 := hunit

private theorem hvar_id {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (m : Ω → ℝ) :
    stoch_to_det.Hvar (fun w : Ω => w) m = stoch_to_det.H m := by
  have hpush : stoch_to_det.push (fun w : Ω => w) m = m := by
    funext a
    simp [stoch_to_det.push, Finset.filter_eq']
  rw [stoch_to_det.Hvar, hpush]

private theorem hvar_triple_const {B : Type*} [Fintype B] [DecidableEq B]
    (hp : IsPMF p) (k : B) :
    stoch_to_det.Hvar (fun z : Cell => (z.1, z.2, k)) p = stoch_to_det.H p := by
  have hid : stoch_to_det.Hvar (fun z : Cell => z) p = stoch_to_det.H p := hvar_id p
  refine le_antisymm ?_ ?_
  · calc stoch_to_det.Hvar (fun z : Cell => (z.1, z.2, k)) p
        ≤ stoch_to_det.Hvar (fun z : Cell => z) p :=
          stoch_to_det.Hvar_comp_le hp (fun z : Cell => z)
            (fun w : Cell => (w.1, w.2, k))
      _ = stoch_to_det.H p := hid
  · calc stoch_to_det.H p
        = stoch_to_det.Hvar (fun z : Cell => z) p := hid.symm
      _ ≤ stoch_to_det.Hvar (fun z : Cell => (z.1, z.2, k)) p :=
          stoch_to_det.Hvar_comp_le hp (fun z : Cell => (z.1, z.2, k))
            (fun w => (w.1, w.2.1))

/-- **The constant code scores the law's own mutual information.**  Its two
conditional entropy terms vanish and its conditional mutual information is the
plain one, because conditioning on a constant changes no entropy.  Upstream
bounds `T` by the same quantity through the constant *latent*; this names the
code. -/
theorem detScore_constantCode (hp : IsPMF p) :
    detScore p constantCode = Psi p - Phi p := by
  have hconst : (constantCode : BinaryCode) = fun _ => (constantCode cell00) := by
    funext z; rfl
  show stoch_to_det.condMI Prod.fst Prod.snd constantCode p
      + stoch_to_det.condH constantCode Prod.fst p
      + stoch_to_det.condH constantCode Prod.snd p = Psi p - Phi p
  rw [hconst, stoch_to_det.condMI, stoch_to_det.condH, stoch_to_det.condH,
    hvar_pair_const hp (fun z : Cell => z.1) (constantCode cell00),
    hvar_pair_const hp (fun z : Cell => z.2) (constantCode cell00),
    hvar_const_pair hp (fun z : Cell => z.1) (constantCode cell00),
    hvar_const_pair hp (fun z : Cell => z.2) (constantCode cell00),
    hvar_const hp (constantCode cell00),
    hvar_triple_const hp (constantCode cell00)]
  show stoch_to_det.H (stoch_to_det.mX p) + stoch_to_det.H (stoch_to_det.mY p)
      - stoch_to_det.H p - 0 + (stoch_to_det.H (stoch_to_det.mX p)
        - stoch_to_det.H (stoch_to_det.mX p))
      + (stoch_to_det.H (stoch_to_det.mY p) - stoch_to_det.H (stoch_to_det.mY p))
    = (2 * stoch_to_det.H p - stoch_to_det.H (stoch_to_det.mX p)
        - stoch_to_det.H (stoch_to_det.mY p))
      - (3 * stoch_to_det.H p - 2 * stoch_to_det.H (stoch_to_det.mX p)
        - 2 * stoch_to_det.H (stoch_to_det.mY p))
  ring

/-! ## The five codes -/

/-- The constant code, or one of the four singletons. -/
def IsWitnessCode (g : BinaryCode) : Prop :=
  g = constantCode ∨ ∃ c : Cell, g = singletonCode c

/-- Pulling a witness code back along a relabelling of the cells gives a
witness code: the constant code is fixed, and the singleton at `c` becomes the
singleton at the preimage of `c`.  Closure of the five-code set under this
action is what lets the oriented bound transport to a general law. -/
private theorem isWitnessCode_comp {g : BinaryCode} (e : Cell ≃ Cell)
    (hg : IsWitnessCode g) : IsWitnessCode (fun z => g (e z)) := by
  rcases hg with rfl | ⟨c, rfl⟩
  · exact Or.inl (by funext z; rfl)
  · refine Or.inr ⟨e.symm c, ?_⟩
    funext z
    simp only [singletonCode]
    rcases eq_or_ne (e z) c with h | h
    · rw [if_pos h, if_pos (by rw [← h, Equiv.symm_apply_apply])]
    · rw [if_neg h, if_neg (fun hcon => h (by rw [hcon, Equiv.apply_symm_apply]))]

/-! ## The witness -/

/-- **One of five named codes witnesses the factor-two bound.**  For every fully
supported binary law, the constant code or one of the four singleton codes has
deterministic score at most twice the stochastic optimum.

This is the clause of the factor-two claim that `T_le_two_mul_tau` does not
state: that theorem bounds the infimum over the whole code space, and this one
exhibits the code. -/
theorem exists_witnessCode (hp : IsPMF p) (hpos : FullSupport p) :
    ∃ g : BinaryCode, IsWitnessCode g ∧ detScore p g ≤ 2 * tau p := by
  refine of_oriented
    (P := fun q => ∃ g : BinaryCode, IsWitnessCode g ∧ detScore q g ≤ 2 * tau q)
    ?_ ?_ p hp hpos
  · -- carrying a code back along one symmetry
    rintro r q hq ⟨g, hshape, hle⟩
    refine ⟨fun z => g (r.equiv z), isWitnessCode_comp r.equiv hshape, ?_⟩
    have hback : transportCode r.equiv (fun z => g (r.equiv z)) = g := by
      funext z
      simp [transportCode]
    have hscore := detScore_pushforward r q hq (fun z => g (r.equiv z))
    rw [hback] at hscore
    rw [← hscore]
    rwa [tau_pushforward r q hq] at hle
  · -- the oriented region
    intro q hq hqpos hqdet hda hcb
    obtain ⟨htop, hbranch⟩ := tau_eq_at_topRoot hq hqpos hqdet
    rcases hbranch with ⟨hnc, _⟩ | ⟨_, htau⟩
    · have hdet := determinant_pos_of_nonconstant hq hqpos hqdet htop hnc
      have hdom : ChordDomain q (cubicRoot q) := ⟨hq, hqpos, hdet, htop, hnc, hda, hcb⟩
      have hpt : ∀ t ∈ Set.Icc (chordMidpoint q) (chordTop q (cubicRoot q)),
          0 ≤ constantMargin q (cubicRoot q) t
            ∨ 0 ≤ singletonMargin q (cubicRoot q) t := by
        rcases gates_of_chordDomain hdom with hg | ⟨hm, he⟩ | ⟨t, ht, hm, hd, h0⟩
        · exact chordMargin_of_constantCentre hdom hg
        · exact chordMargin_of_singletonEnds hdom hm he
        · exact chordMargin_of_crossover hdom t ht hm hd h0
      rcases chordMargin_witness hdom hpt with h0 | hD
      · exact ⟨constantCode, Or.inl rfl, by rw [detScore_constantCode hq]; exact h0⟩
      · exact ⟨singletonCode cell11, Or.inr ⟨cell11, rfl⟩, hD⟩
    · refine ⟨constantCode, Or.inl rfl, ?_⟩
      rw [detScore_constantCode hq, ← htau]
      linarith [tau_nonneg q]

end StochasticToDeterministicLatents.Binary
