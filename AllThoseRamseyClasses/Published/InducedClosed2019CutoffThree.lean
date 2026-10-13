import AllThoseRamseyClasses.Published.ExactWeakThreeVertex2019
import AllThoseRamseyClasses.Published.InducedClosed2019UnrestrictedInitial

/-!
# Constructed corrected 2019 Ramsey endpoint at local cutoff at most THREE

Use the actual unrestricted initial Picture, complete EVERY original
weak induced test on at most three vertices, apply the fixed-cutoff
local completion axiom, then transfer the B-copywise Ramsey arrow.
The original Ramsey control may be nonclosed. No sparse-witness,
rank-increment, or selected-native-history constructor is assumed.

This is a cardinal-cutoff endpoint, not the unrestricted main theorem
and not a closed generating-rank-three Picture invariant.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- The complete Ramsey witness construction when the genuine fixed
local-completion cutoff is at most three, even for a nonclosed control. -/
theorem coordinated2019_cutoff_three_unrestricted_induced
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
    (hKIrr : ∀ {X : Type v} (T : RelStructure L X), K T → T.Irreducible)
    (n : ℕ) (hn : n ≤ 3)
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
    exact inducedClosed2019_exact_weak_card_le_three_completion
      C.toRelStructure B hClosed hKB hStrong hHer hKIrr hCover S (hS.trans hn)
  have hCopywise : HasCopywiseCompletion K B C.toRelStructure :=
    hLocal C.toRelStructure hClosed
      ⟨hC0, C.part, IsClosedUHomomorphismEmbedding.toInducedClosed hPart⟩
      hCovered hSmall
  exact arrow_of_BCopywiseCompletion_inClass hRamsey hCopywise

end AllThoseRamseyClasses.Published
