import AllThoseRamseyClasses.Published.FunctionalWithParts2019TotalUnaryWeakGap
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKClass

/-!
# Track C: the total-unary gap survives ACTUAL corrected (4b)

The genuine two-point all-defined unary function source is not merely
an arbitrary ambient OLD graph. Its canonical tagged expansion is in
the original finite class K(H), is U-closed, and satisfies actual
corrected (4b) membership on EVERY induced closed U-irreducible
substructure. This uses the original H-closed-hereditary theorem, not
an assumed arbitrary K-class closure axiom.

Thus even a candidate meeting exactly the source-side hypotheses of
the corrected local-finiteness test can have an intrinsic whole-weak
singleton that cannot FULLY embed in ANY H target.

The obstruction is to the naive local certificate transfer requiring
FULL intrinsic weak embeddings, not a refutation of the complete
class-local axiom, which has an additional global copywise implication.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

private def totalUnaryPart : Fin 2 → Fin 2 := id

private def totalUnaryTagged :
    RelStructure
      ((exampleLanguage.withParts (Fin 2)).wholeMaskTagLanguage (Fin 2))
      (Fin 2) :=
  wholeMaskTagExpansion
    (withPartsWholeMaskOld totalUnaryToy totalUnaryPart)

theorem totalUnaryToy_tagged_in_K :
    canonicalGenuineTagged2019Class totalUnaryPartiteH
      totalUnaryTagged :=
  canonicalGenuineTagged2019Class_mem
    totalUnaryPartiteH totalUnaryToy totalUnaryPart
    totalUnaryToy_mem totalUnaryToy_transversal

theorem totalUnaryToy_tagged_UClosed :
    IsUClosed
      ((exampleLanguage.withParts (Fin 2)).wholeMaskClosureRules (Fin 2))
      totalUnaryTagged :=
  canonicalGenuineTagged2019Class_closed
    totalUnaryPartiteH totalUnaryTagged totalUnaryToy_tagged_in_K

private theorem totalUnaryLanguage_positive :
    exampleLanguage.PositiveFuncArity := by
  intro F
  cases F
  decide

/-- Actual corrected membership clause (4b), not an axiom:
every U-closed U-irreducible exact induced subtest of this canonical
source belongs to the original class K(totalUnaryPartiteH). -/
theorem totalUnaryToy_tagged_correctedCovered :
    CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class totalUnaryPartiteH)
      ((exampleLanguage.withParts (Fin 2)).wholeMaskClosureRules (Fin 2))
      totalUnaryTagged := by
  intro S hS _
  exact (canonicalGenuineTagged2019Class_inducedClosedHereditary
      totalUnaryPartiteH
      totalUnaryPartiteH_closedHereditary
      totalUnaryLanguage_positive)
    totalUnaryTagged totalUnaryToy_tagged_in_K S hS

end AllThoseRamseyClasses.Published
