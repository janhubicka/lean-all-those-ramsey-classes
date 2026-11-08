import AllThoseRamseyClasses.Published.FunctionalWithParts2019ExactLocalRestriction
import PartiteConstruction.Ramsey.ClosureGeneratedHullRank

/-!
# Track C: a sufficient closed-generator-rank test condition for exact weak tests

The corrected 2019 local-completion axiom tests the AMBIENT induced
OLD structure on each exact finite S of at most n vertices. Such an
induced test need not itself be U-closed, even when C is U-closed.

Here we replace a hypothetical COMPLETION OF THE EXACT WEAK S by a
strictly stronger premise: ALL U-closed induced tagged substructures
of U-size at most n have genuine H-valued ambient-relative
completions. The U-closure hull of S is one of these rank-bounded
closed substructures. It can have MORE THAN n vertices, but its
minimum generating support has size at most |S|≤n.

The previously checked relative-completion restriction theorem then
restricts the hull's completion to the ORIGINAL exact S, without
altering its ambient OLD domain-mask bits, adding a vertex or
changing the canonical H-target.

This proves a sufficient candidate-wise small-test interface and
its correct logical local-class implication direction. It DOES NOT
assert that the printed native local-finiteness definition, which
tests genuinely closed substructures on at most n vertices, implies
this stronger closed-RANK premise. The converse weak-to-hull
completion extension is known false in general.

Neither this theorem nor the generated-rank dictionary supplies an
independent sparse-witness argument for the stronger rank premise.
The repaired ambient 2019 theorem stays the validated route.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Z : Type w}

/-- A strong closed-RANK premise on an arbitrary U-closed candidate
implies ALL original exact small weak OLD tests admit the required
genuine H-valued ambient-relative completion.

Both tests use the SAME cutoff n. The hull cardinality is never
substituted for its U-generating rank. -/
theorem genuineTagged2019_ambientSmall_of_closedRankSmall
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmallClosedRank :
      ∀ (T : Set V) [Fintype T],
        IsUClosed
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce T) →
        USize
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce T) ≤ n →
        HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T)) :
    ∀ (S : Finset V), S.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑S : Set V)) := by
  classical
  intro S hSize
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let T : Set V := UClosureHull rules C (↑S : Set V)
  letI : Fintype T := Fintype.ofFinite T
  have hTClosed : IsUClosed rules (C.induce T) :=
    hClosed.induce_UClosureHull (↑S : Set V)
  have hTRank : USize rules (C.induce T) ≤ n := by
    exact (USize_induce_UClosureHull_le rules C S).trans hSize
  have hHull : HasGenuinePartiteTagged2019RelativeCompletion H
      (C.induce T) := hSmallClosedRank T hTClosed hTRank
  exact genuineTagged2019_relativeCompletion_induce_of_hull
    H C (↑S : Set V) hHull

/-- Fixed-cutoff corrected class-local implication using strong
closed RANK-bounded tests instead of arbitrary exact weak tests.
The corrected (4b) membership and the protected control map
remain explicit, and the two ambient B,C0 carriers are independent.

The new condition is logically WEAKER as a class-local implication
than the original ambient-all-weak test condition, because its
small-test antecedent is stronger. This does not turn it into a
sufficient assumption for the existing sparse Ramsey witness. -/
def GenuinePartiteTagged2019ClosedRankLocalCompletionAt
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) : Prop :=
  ∀ {X : Type w} [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
    IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C →
    (C0.Irreducible ∧ ∃ p : X → Z,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p) →
    CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C →
    (∀ (T : Set X) [Fintype T],
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce T)) →
    HasCopywiseCompletion
      (canonicalGenuineTagged2019Class H) B C

/-- Preserve the logical polarity of the class-local implication:
the original same-n all-weak local axiom entails the corresponding
closed-rank-premise local axiom. Its converse is NOT claimed. -/
theorem genuineTagged2019_closedRankLocal_of_ambientLocal
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ)
    (hLocal : GenuinePartiteTagged2019LocalCompletionAt H B C0 n) :
    GenuinePartiteTagged2019ClosedRankLocalCompletionAt H B C0 n := by
  intro X hFinite C hClosed hControl hCovered hSmall
  apply hLocal C hClosed hControl hCovered
  exact genuineTagged2019_ambientSmall_of_closedRankSmall
    H C hClosed n hSmall

end AllThoseRamseyClasses.Published
