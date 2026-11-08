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

/-- A candidate-level "all-weak-small" premise follows from the
corresponding generator-bounded closed-test premise with NO shift
in n and with no need to assume source (4b) or global H membership.
Only U-closedness of the ambient tagged candidate is used here.

Corrected (4b), irreducibility coverage and the original control
map remain necessary elsewhere in the class-local Ramsey theorem;
they are not silently supplied by this small-test lemma. -/
theorem genuineTagged2019_smallWeakPremise_of_generatedClosedPremise
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hGeneratedClosed : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T)) :
    ∀ S : Finset V, S.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce (↑S : Set V)) :=
  genuineTagged2019_allSmallWeak_of_closedUSize
    H C hC n hGeneratedClosed

end AllThoseRamseyClasses.Published
