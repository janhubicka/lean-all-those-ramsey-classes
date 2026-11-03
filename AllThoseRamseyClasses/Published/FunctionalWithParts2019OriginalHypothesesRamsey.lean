import AllThoseRamseyClasses.Published.FunctionalWithParts2019AssembledRamsey
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKIso

/-!
# Corrected 2019 Ramsey theorem entirely in the original functional H language

The previously verified assembled theorem retained an explicit
isomorphism-invariance premise for the CANONICAL TAGGED K class.
But the tagged image K is constructed from the original genuinely
partial partite Option(Set) class H, whose original full part-preserving
isomorphism invariance is exactly enough.

The checked full-tagged same-carrier pullback theorem transfers H's
isomorphism invariance to K. Hence the corrected 2019 two-pass
partite Ramsey theorem now has no independent K-target
canonicality or K-isomorphism-invariance hypothesis.

The remaining local-finiteness premise is the explicit
ambient-relative tagged completion implication on EACH exact
weak induced test. The need to derive that from any differently
defined original functional locally finite class assumption is
NOT hidden or discharged. Part-preserving strong amalgamation,
original function-closed hereditariness, positive primitive arity,
and an irreducible relational Ramsey ambient class stay explicit.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- All genuine functional class properties are stated on the
ORIGINAL part-labelled Option(Set) objects, including isomorphism
closure, not on an arbitrary unrelated relational K. Only the
ambient R and the ambient-relative exact weak completion
implication use the canonical tagged relational language. -/
theorem genuinePartite2019_ramsey_of_original_functional_hypotheses
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
    (hLocal : ∀ {X Y : Type w} [Finite X] [Finite Y]
      (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
      (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      canonicalGenuineTagged2019Class H B → R C0 →
      ∃ n : ℕ, GenuinePartiteTagged2019LocalCompletionAt H B C0 n) :
    GenuinePartite2019FiniteRamsey H := by
  have hIsoK : IsomorphismClosed2019
      (canonicalGenuineTagged2019Class H) :=
    canonicalGenuineTagged2019Class_isomorphismClosed H hIso
  apply genuinePartite2019_ramsey_of_original_class_data
    (L := L) (Parts := Parts)
    H R hR hRIrred hSub hPos hHer hStrong
  · exact hIsoK
  · exact hLocal

end AllThoseRamseyClasses.Published
