import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedCoveredValueCoherence
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeProtectedBridge
import AllThoseRamseyClasses.Published.FunctionalWithParts2019OriginalHypothesesRamsey

/-!
# Track C: a corrected native local CLASS axiom sufficient for the 2019 theorem

The genuine local-completion transfer has a CONTRAVARIANT direction:
ambient-relative small-test completions sit in an antecedent, so they
must be converted to the native functional test notion used there.

The previous corrected (4b) lemmas eliminate all of:
  - arbitrary source part labels (singleton U-hull);
  - spurious OLD domain/value records (canonical weak test);
  - root tag normality and complete value uniqueness (common input hull).

Thus a genuine ambient-relative H-completion of C.induce S yields,
without additional source normalization axioms, an H-valued ORIGINAL
PARTIAL homomorphism of the exact intrinsic whole-fibre weak decoder,
and full protection of each canonical closed U-irreducible embedded
test with the same local map and original part assignment.

The functional local axiom packaged below intentionally protects
CANONICAL CLOSED OLD test copies, not arbitrary intrinsic irreducible
whole-weak source pieces. The two notions are demonstrably different
when function outputs escape S. This theorem is a valid sufficient
replacement for the still-unresolved *literal original intrinsic*
local-finiteness hypothesis; it does not claim they are equivalent.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- A corrected class-local axiom whose every exact small test is
completed into the ORIGINAL genuine partial-function H class,
preserving whole source-defined values, every unary vertex part and
all canonically represented closed U-irreducible protected copies.
Global control/coverage and copywise conclusions are still the exact
corrected 2019 tagged forms on the SAME candidate C. -/
def GenuinePartiteIntrinsicCanonicalProtectedLocalCompletionAt
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) (Fin 1))
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) (Fin 1))
    (n : ℕ) : Prop :=
  ∀ {X : Type w} [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (hClosed : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C),
    (C0.Irreducible ∧ ∃ p : X → Fin 1,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p) →
    ∀ (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C),
      (∀ S : Finset X, S.card ≤ n →
        HasGenuineIntrinsicWeakCanonicalProtectedCompletion
          H C (genuineTagged2019_correctedCoveredPart
            H C hClosed hCovered) (↑S : Set X)) →
      HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C

end AllThoseRamseyClasses.Published
