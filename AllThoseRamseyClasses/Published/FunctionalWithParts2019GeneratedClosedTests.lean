import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedHullRank
import PartiteConstruction.Ramsey.ClosureClosedCompletionRank

/-!
# Track C: generator-bounded CLOSED tests imply all weak small-test completions

The corrected 2019 relational local (4c) hypothesis tests every
induced exact weak S of at most n vertices. To get those completions
from genuinely U-closed H-completion tests, it is necessary to
control GENERATED closed hulls of small seeds, not merely closed
substructures having at most n TOTAL vertices.

Here is the positive direction, with all quantifiers explicit:

For any finite U-closed tagged C, if EVERY induced U-closed T whose
minimum U-generating rank is at most n has a genuine H-valued
relative completion, THEN every exact induced weak S with |S|≤n
has an H-valued relative completion.

The proof does NOT enlarge S before returning the conclusion.
Internally it first takes the U-hull T of the n-element seed S
and applies the completed abstract 2019 hull-rank lemma. Even if
|T|>n, USize(C|T)≤n, so the assumption covers T. Its completion
then restricts to the original exact S with exactly the same
target; no functional embedding into the weak source is asserted.

This theorem is a bridge of candidate-level SMALL-TEST premises.
It is NOT the original printed local-finiteness axiom: that tests
genuine closed substructures whose number of VERTICES is ≤n,
a strictly narrower demand than all closed structures generated
by ≤n vertices. Nor does it manufacture the stronger rank premise
for the sparse witnesses used by the relational Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- The general 2019 rank bridge, specialized to canonical genuine
Option(Set) H-completions. This keeps the SAME fixed integer n.
The class K(H), the OLD tagged candidate C, and every test carrier
remain unchanged in all existential witnesses. -/
theorem genuineTagged2019_allSmallWeak_of_closedUSize
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T)) :
    ∀ S : Finset V, S.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce (↑S : Set V)) := by
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hKRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ n →
      HasClosedUKCompletion
        (canonicalGenuineTagged2019Class H) rules (C.induce T) := by
    intro T hFinite hTClosed hTSize
    have hRelative :
        HasGenuinePartiteTagged2019RelativeCompletion H
          (C.induce T) :=
      hRank T hTClosed hTSize
    have hInduced :
        HasInducedClosedUKCompletion
          (canonicalGenuineTagged2019Class H) rules (C.induce T) :=
      (canonicalGenuineTagged2019_KCompletion_iff_relative
        H (C.induce T)).mpr hRelative
    exact (inducedClosedKCompletion_iff_abstract_2019).mp hInduced
  intro S hSize
  have hClosedCompletion :
      HasClosedUKCompletion (canonicalGenuineTagged2019Class H)
        rules (C.induce (↑S : Set V)) :=
    HasClosedUKCompletion.of_closed_USize
      rules C hC n hKRank S hSize
  have hInduced :
      HasInducedClosedUKCompletion
        (canonicalGenuineTagged2019Class H)
        rules (C.induce (↑S : Set V)) :=
    (inducedClosedKCompletion_iff_abstract_2019).mpr
      hClosedCompletion
  exact (canonicalGenuineTagged2019_KCompletion_iff_relative
    H (C.induce (↑S : Set V))).mp hInduced

/-- Candidate-level copywise conclusion from the familiar corrected
2019 local class axiom and a *stronger* tested premise: all closed
substructures of generator rank at most n have genuine H-relative
completions. No extra target, rank shift, or change to the candidate
C appears in the conclusion.

This does NOT assert that the 2019 sparse witness automatically has
the stronger closed-rank premise. This implication merely makes the
admissible route explicit if a construction or an application can
supply such a premise separately. -/
theorem genuineTagged2019_copywise_of_local_and_closedUSize
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ)
    (hLocal : GenuinePartiteTagged2019LocalCompletionAt H B C0 n)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hControl : C0.Irreducible ∧
      ∃ p : V → Z,
        IsInducedClosedUHomomorphismEmbedding
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          C C0 p)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T)) :
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C := by
  apply hLocal C hC hControl hCovered
  exact genuineTagged2019_allSmallWeak_of_closedUSize
    H C hC n hRank

end AllThoseRamseyClasses.Published
