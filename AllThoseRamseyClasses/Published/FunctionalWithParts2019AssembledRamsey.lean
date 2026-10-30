import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKStrongAmalgamation
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RamseyDescent

/-!
# An assembled corrected 2019 genuine-function Ramsey theorem

The original functional class H consists of finite genuinely partial
Option(Set) structures with actual vertex parts and transversal
output-value sets. Its canonical tagged K image is now constructed
rather than assumed to represent genuine functions.

Use the verified 2019 two-pass sparse Ramsey theorem for a relational
irreducible Ramsey ambient class R. All the K-side class hypotheses
are derived from their genuine functional counterparts, except for:
 - isomorphism invariance of the canonical K-image, stated explicitly
   until the separate faithful pullback transport theorem is integrated;
 - a locally finite completion assumption on EVERY exact ambient-
   induced semi-closed OLD weak test, whose target is an actual H member.
   The verified relative-completion iff translates this to the
   necessary 2019 K-local axiom with the SAME cutoff n.

The conclusion is an actual genuine partial-function FULL
part-preserving Ramsey class statement on original H structures,
not merely a Ramsey class of relational encodings. No strict
functional Hales--Jewett mixed-tree step is used, and no unsupported
"arbitrary weak test is canonical" claim appears.

This theorem exposes rather than proves the remaining original-
functional local-completion implication; that is precisely where
the witnessed ambient-domain obstruction must be addressed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The 2019 theorem in the true original genuine partial-function
PARTITE language, under the exact corrected relative weak completion
hypothesis and explicit isomorphism closure of its canonical tagged K.

All original native class conditions are on H, except the ambient
relational Ramsey class R and its inclusion predicate, and the
unresolved local relative completion. -/
theorem genuinePartite2019_ramsey_of_original_class_data
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
    (hIso : IsomorphismClosed2019 (canonicalGenuineTagged2019Class H))
    (hLocal : ∀ {X Y : Type w} [Finite X] [Finite Y]
      (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
      (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      canonicalGenuineTagged2019Class H B → R C0 →
      ∃ n : ℕ, GenuinePartiteTagged2019LocalCompletionAt
        H B C0 n) :
    GenuinePartite2019FiniteRamsey H := by
  let K : StructureClass.{max u v,w}
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts) :=
    canonicalGenuineTagged2019Class H
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hInd : InducedClosed2019MultiamalgamationClass R K rules := {
    subset := hSub
    finite := canonicalGenuineTagged2019Class_finite H
    closed := canonicalGenuineTagged2019Class_closed H
    hereditary := canonicalGenuineTagged2019Class_inducedClosedHereditary
      H hHer hPos
    strong := canonicalGenuineTagged2019Class_strongAmalgamation
      H hStrong
    localCompletion := by
      intro X Y hX hY B C0 hB hC0
      obtain ⟨n, hn⟩ := hLocal B C0 hB hC0
      exact ⟨n, (canonicalGenuineTagged2019_localCompletion_iff_relative
        H B C0 n).mpr hn⟩
  }
  let hClass : IsCoordinated2019MultiamalgamationClass R K rules :=
    ⟨hInd, hIso⟩
  exact genuinePartite2019_ramsey_of_canonicalCoordinated2019
    H R hR hRIrred hClass

end AllThoseRamseyClasses.Published
