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

variable {W Z : Type w}

/-- A corrected class-local axiom whose every exact small test is
completed into the ORIGINAL genuine partial-function H class,
preserving whole source-defined values, every unary vertex part and
all canonically represented closed U-irreducible protected copies.
Global control/coverage and copywise conclusions are still the exact
corrected 2019 tagged forms on the SAME candidate C. -/
def GenuinePartiteIntrinsicCanonicalProtectedLocalCompletionAt
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) : Prop :=
  ∀ {X : Type w} [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (hClosed : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hControl : C0.Irreducible ∧ ∃ p : X → Z,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C),
      (∀ S : Finset X, S.card ≤ n →
        HasGenuineIntrinsicWeakCanonicalProtectedCompletion
          H C (genuineTagged2019_correctedCoveredPart
            H C hClosed hCovered) (↑S : Set X)) →
      HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C

/-- The exact needed contravariant direction: corrected native
functional exact-weak H-completion hypotheses imply the ambient
relative OLD local-completion axiom. There is NO extra value
coherence, global part-map or fixed B-cover hypothesis:
all are derived from actual (4b) and positive function arity. -/
theorem genuinePartiteTagged2019_localCompletion_of_intrinsicCanonicalProtected
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) (hPos : L.PositiveFuncArity)
    (hNative :
      GenuinePartiteIntrinsicCanonicalProtectedLocalCompletionAt
        H B C0 n) :
    GenuinePartiteTagged2019LocalCompletionAt H B C0 n := by
  intro X hX C hClosed hControl hCovered hSmall
  apply hNative C hClosed hControl hCovered
  intro S hSize
  exact correctedCovered_relative_implies_intrinsicWeakCanonicalProtected
    H C hClosed hCovered
    (genuineTagged2019_correctedCovered_uniqueCompleteValues
      H C hClosed hCovered hPos)
    (↑S : Set X) (hSmall S hSize)

/-- Full Ramsey conclusion in the ORIGINAL genuine Option(Set)
part-preserving function language, assuming a corrected native
canonical-protected weak-local class axiom, instead of the ambient
tagged local axiom as a separate premise.

This is a corrected SUFFICIENT functional hypothesis. It does not
assert equivalence to a stronger/literal notion protecting every
intrinsic whole-fibre weak irreducible test or total-fibre projection.
-/
theorem genuinePartite2019_ramsey_of_intrinsicCanonicalProtectedLocalCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R E → E.Irreducible)
    (hSub : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → R E)
    (hPos : L.PositiveFuncArity)
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hLocalNative : ∀ {X Y : Type w} [Finite X] [Finite Y]
      (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
      (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      canonicalGenuineTagged2019Class H B → R C0 →
      ∃ n : ℕ, GenuinePartiteIntrinsicCanonicalProtectedLocalCompletionAt
        H B C0 n) :
    GenuinePartite2019FiniteRamsey H := by
  apply genuinePartite2019_ramsey_of_original_functional_hypotheses
    H R hR hRIrred hSub hPos hHer hStrong hIso
  intro X Y hX hY B C0 hB hC0
  obtain ⟨n, hNative⟩ := hLocalNative B C0 hB hC0
  exact ⟨n,
    genuinePartiteTagged2019_localCompletion_of_intrinsicCanonicalProtected
      H B C0 n hPos hNative⟩

end AllThoseRamseyClasses.Published
