import AllThoseRamseyClasses.Published.FunctionalWithParts2019IrreducibleTestsAutomatic
import AllThoseRamseyClasses.Published.FunctionalWithParts2019GeneratedClosedTests
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureWeakRankDichotomy
import PartiteConstruction.Relational.FreeAmalgamationClass

/-!
# Track C: exact weak rank cut without a fixed B-cover

The verified 2019 rank dichotomy says that a weak test S of size
at most j+1 in a U-closed candidate C is either completable
from the rank-j closed completion invariant, or S has maximal
intrinsic U-size and EVERY vertex subset of S is relatively U-closed.

The older weak-cut completion theorem supplied the ordinary
irreducible case using a strong FIXED B-cover premise. That is
not part of corrected 2019 clause (4b). Here the already verified
canonical genuine H-target lemma instead handles ordinary
irreducible induced S using exactly corrected (4b), with a
possibly different H-member for every test.

Consequently any still-uncompletable weak S with |S|<=j+1
admits a PROPER free decomposition into two weak sides with
relative U-closed ranges in S, each having at most j vertices.
No assertion is made that their common weak root is U-closed
or belongs to canonical K(H): this is the separate protected
boundary condition needed to glue the two side completions.

This exact dichotomy is the geometric input for the remaining
higher-rank completion step. It does not assert the original
closed-vertex local-finiteness axiom implies rank-j completion
control, or that independent completions have a common boundary.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Under actual corrected (4b), any j+1-small exact ambient
OLD weak test is H-relatively completable OR admits a proper
free split into sides of at most j vertices, both with relative
U-closed ranges. Unlike the older fixed-B-cover theorem, the
irreducible case uses a canonical H target depending on S.

This is an OR theorem: neither a canonical closed common root
nor side completability is postulated or inferred from the cut. -/
theorem genuineTagged2019_weakSmall_complete_or_relativeFreeCut
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hKIrr : ∀ {X : Type w}
      (Target : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H Target → Target.Irreducible)
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    (S : Finset V) (hCard : S.card ≤ j + 1) :
    HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)) ∨
    ∃ d : ProperFreeDecomposition (C.induce (↑S : Set V)),
      IsUSubstructure ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set V)) (Set.range d.leftIn) ∧
      IsUSubstructure ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set V)) (Set.range d.rightIn) ∧
      Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  -- Explicitly fix the universe-polymorphic carrier argument of K.
  let K : ∀ {X : Type w},
      RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X → Prop :=
    canonicalGenuineTagged2019Class H
  have hClosedRankK : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ j →
      HasClosedUKCompletion K rules (C.induce T) := by
    intro T hFinite hTClosed hTRank
    have hRelative :
        HasGenuinePartiteTagged2019RelativeCompletion H
          (C.induce T) := hRank T hTClosed hTRank
    have hInduced :
        HasInducedClosedUKCompletion K rules (C.induce T) :=
      (canonicalGenuineTagged2019_KCompletion_iff_relative
        H (C.induce T)).mpr hRelative
    exact inducedClosedKCompletion_iff_abstract_2019.mp hInduced
  rcases weak_test_complete_or_maximal_independent
    C hClosed j hClosedRankK S hCard with
    hComplete | ⟨hExact, hMaxRank, hEveryRelative⟩
  · left
    have hInduced : HasInducedClosedUKCompletion
        K rules (C.induce (↑S : Set V)) :=
      inducedClosedKCompletion_iff_abstract_2019.mpr hComplete
    exact (canonicalGenuineTagged2019_KCompletion_iff_relative
      H (C.induce (↑S : Set V))).mp hInduced
  by_cases hIrred : (C.induce (↑S : Set V)).Irreducible
  · left
    exact genuineTagged2019_weakIrred_has_relativeCompletion
      H C hClosed hCovered hKIrr (↑S : Set V) hIrred
  · right
    obtain ⟨d⟩ := properFreeDecomposition_of_not_irreducible hIrred
    letI : Finite d.Left :=
      Finite.of_injective d.leftIn d.leftIn.injective
    letI : Finite d.Right :=
      Finite.of_injective d.rightIn d.rightIn.injective
    letI : Fintype d.Left := Fintype.ofFinite d.Left
    letI : Fintype d.Right := Fintype.ofFinite d.Right
    have hCardS : Fintype.card (↑S : Set V) = S.card := by simp
    have hLeftCard :
        Fintype.card d.Left < Fintype.card (↑S : Set V) :=
      Fintype.card_lt_of_injective_not_surjective
        d.leftIn d.leftIn.injective d.leftProper
    have hRightCard :
        Fintype.card d.Right < Fintype.card (↑S : Set V) :=
      Fintype.card_lt_of_injective_not_surjective
        d.rightIn d.rightIn.injective d.rightProper
    have hSmallLeft : Nat.card d.Left ≤ j := by
      rw [Nat.card_eq_fintype_card]
      omega
    have hSmallRight : Nat.card d.Right ≤ j := by
      rw [Nat.card_eq_fintype_card]
      omega
    exact ⟨d, hEveryRelative (Set.range d.leftIn),
      hEveryRelative (Set.range d.rightIn),
      hSmallLeft, hSmallRight⟩

/-- Contrapositive presentation for an adversarial higher-rank
argument. A genuinely NONcompletable exact weak test is never
ordinary irreducible under corrected (4b), and its free sides
have strictly smaller vertex cardinalities and relative U-closed
ranges. Nothing says that the common root is a K-member. -/
theorem genuineTagged2019_badWeakSmall_has_relativeFreeCut
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hKIrr : ∀ {X : Type w}
      (Target : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H Target → Target.Irreducible)
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    (S : Finset V) (hCard : S.card ≤ j + 1)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V))) :
    ∃ d : ProperFreeDecomposition (C.induce (↑S : Set V)),
      IsUSubstructure ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set V)) (Set.range d.leftIn) ∧
      IsUSubstructure ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set V)) (Set.range d.rightIn) ∧
      Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j := by
  rcases genuineTagged2019_weakSmall_complete_or_relativeFreeCut
      H C hClosed hCovered hKIrr j hRank S hCard with hGood | hSplit
  · exact (hBad hGood).elim
  · exact hSplit

end AllThoseRamseyClasses.Published
