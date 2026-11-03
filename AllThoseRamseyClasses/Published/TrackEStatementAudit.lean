import AllThoseRamseyClasses.Published.FunctionalWithParts2019OriginalHypothesesRamsey
import AllThoseRamseyClasses.Published.FunctionalWithParts2019ActualHSparseWitness
import AllThoseRamseyClasses.Published.FunctionalWithParts2019OriginalKMembership

/-!
# Appendix A Track E: same-witness H and local-completion contracts

The exact 2019 functional K,H transfer has TWO logically separate clauses:
  - H membership of an actual decoded finite partial-function target;
  - for every exact ambient tagged weak test S of size <= n, an actual
    ambient-relative completion into some (possibly S-dependent) H target.

The latter is not the assertion H C and does not imply it without the
class-level local-completion hypothesis. Crucially, the S and the OLD
ambient domain-mask structure C.induce S must not be replaced by
intrinsic wholeWeakInduce, a closed hull, or a different candidate.

This is a statement audit, not a new unconditional Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Published.TrackEStatementAudit

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {X Y Z : Type w}

/-- Every exact finite ambient OLD weak test S has its own genuine H target.
One fixed cutoff n and one fixed ambient C are retained. -/
def AllExactAmbientWeakHCompletions
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (n : ℕ) : Prop :=
  ∀ S : Finset X, S.card ≤ n →
    HasGenuinePartiteTagged2019RelativeCompletion H
      (C.induce (↑S : Set X))

/-- Same-C, same-S, same-n equivalence: H-valued ambient OLD relative
completions are the canonical K U-completions for the exact SAME test. -/
theorem allExactHCompletions_iff_allExactCanonicalKCompletions
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (n : ℕ) :
    AllExactAmbientWeakHCompletions H C n ↔
    ∀ S : Finset X, S.card ≤ n →
      HasInducedClosedUKCompletion
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set X)) := by
  constructor
  · intro h S hSize
    exact (canonicalGenuineTagged2019_KCompletion_iff_relative
      H (C.induce (↑S : Set X))).mpr (h S hSize)
  · intro h S hSize
    exact (canonicalGenuineTagged2019_KCompletion_iff_relative
      H (C.induce (↑S : Set X))).mp (h S hSize)

/-- The H-valued OLD-relative class-local axiom uses the same candidate
and exact weak tests. This is a CONDITIONAL endgame: no local axiom
is inferred from the existence of the sparse candidate. -/
theorem sameWitness_localAxiom_yields_copywiseCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ)
    (hLocal : GenuinePartiteTagged2019LocalCompletionAt H B C0 n)
    [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (hClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hProj : C0.Irreducible ∧ ∃ p : X → Z,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hTests : AllExactAmbientWeakHCompletions H C n) :
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C := by
  exact hLocal C hClosed hProj hCovered hTests

/-- Final ACTUAL H membership is equivalent to K membership of the exact
canonical tagged representation of that SAME functional structure and
part map. The equivalence does NOT mention local test completions. -/
theorem sameCarrier_Hmembership_iff_exactCanonicalKMembership
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    [Finite X] (C : PartialSetStructure L X)
    (part : X → Parts) (hTr : FibreTransversal C part) :
    H C part ↔
    canonicalGenuineTagged2019Class H
      (wholeMaskTagExpansion (withPartsWholeMaskOld C part)) := by
  exact (canonicalGenuineTagged2019Class_mem_iff H C part hTr).symm

end AllThoseRamseyClasses.Published.TrackEStatementAudit
