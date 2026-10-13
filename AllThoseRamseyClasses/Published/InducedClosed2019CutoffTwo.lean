import AllThoseRamseyClasses.Published.ExactWeakTwoVertex2019
import AllThoseRamseyClasses.Published.InducedClosed2019UnrestrictedInitial

/-!
# A fully constructed corrected Ramsey theorem at local cutoff at most TWO

The unrestricted initial closed Picture is already available (PR #121).
The direct two-vertex theorem supplies ALL exact weak local tests, not
just native two-active-line tests. Applying the actual corrected local
completion axiom and B-copywise transfer now gives a K-Ramsey witness.

The original control may be nonclosed, the local cutoff is fixed before
constructing the Picture, and no rank-increment constructor is assumed.
This does not settle the unrestricted theorem, whose local cutoff can
be arbitrary. In particular cardinal cutoff two is not a closed rank-two
invariant and is not claimed to start the general closed-rank induction.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- The coordinated 2019 Ramsey conclusion for an arbitrary (possibly
nonclosed) control whenever the genuine local-completion cutoff is at
most two. Every small test is the original exact weak induced source. -/
theorem coordinated2019_cutoff_two_unrestricted_induced
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UA VB P : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hKB : K B) (hC0 : C0.Irreducible)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (T : RelStructure L X),
      K T → T.Irreducible)
    (n : ℕ) (hn : n ≤ 2)
    (hLocal : InducedClosedULocalCompletionAt K rules B C0 n)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C0 κ) :
    ∃ (Y : Type v) (_ : Finite Y) (Target : RelStructure L Y),
      K Target ∧ StructuralRamsey.Arrow A B Target κ := by
  obtain ⟨Y, hY, C, hRamsey, hClosed, hPart, hCover⟩ :=
    StructuralRamsey.Partite.Induced.closed_ramsey_unrestricted
      A B C0 hA hB κ hArrow
  letI : Finite Y := hY
  have hCovered : CorrectedUIrreduciblesIn K rules C.toRelStructure :=
    ClosedUIrreduciblesIn.toCorrectedInduced
      (ClosedUIrreduciblesIn.of_copy_coverage
        hHer B hKB C.toRelStructure hCover)
  have hSmall : ∀ S : Finset Y, S.card ≤ n →
      HasInducedClosedUKCompletion K rules
        (C.toRelStructure.induce (↑S : Set Y)) := by
    intro S hS
    exact inducedClosed2019_exact_weak_card_le_two_completion
      C.toRelStructure B hClosed hKB hStrong hHer hKIrr hCover S
      (hS.trans hn)
  have hCopywise : HasCopywiseCompletion K B C.toRelStructure :=
    hLocal C.toRelStructure hClosed
      ⟨hC0, C.part,
        IsClosedUHomomorphismEmbedding.toInducedClosed hPart⟩
      hCovered hSmall
  exact arrow_of_BCopywiseCompletion_inClass hRamsey hCopywise

end AllThoseRamseyClasses.Published
