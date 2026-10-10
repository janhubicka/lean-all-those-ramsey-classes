import AllThoseRamseyClasses.Published.CorrectedMainTheoremContract
import AllThoseRamseyClasses.Published.OrderedAmbientRamsey

/-!
# Literal 2019 Theorem 2.18: counterexample assembly contract

This is the UNCORRECTED printed theorem, not the preferred repair.

All original hypotheses except strong amalgamation are fully
proved for the finite paired-equivalence class:
  * members are finite, with exactly the printed U-closure;
  * hereditary only for U-closed full substructures;
  * every B,C0 admits printed local completion for n = 1;
  * ambient R is Ramsey and ordinarily irreducible;
  * K is NOT Ramsey (explicit A=XY, B=XYX two-colouring).

Strong amalgamation is an explicit last premise. Consequently
this file proves a CONDITIONAL refutation of the printed theorem
and makes precise the remaining theorem-level gap. The actual
strong-amalgamation theorem is NOT yet proved; finite exhaustive
regression is not a replacement for it.

No new axioms or weakened embeddings are used.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Literal printed Definition 2.17: intrinsic membership tests in
(4b), not the corrected closed-test membership clause. -/
structure LiteralMultiamalgamationClass
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) : Prop where
  subset : ∀ {X : Type v} (C : RelStructure L X), K C → R C
  finite : ∀ {X : Type v} (C : RelStructure L X), K C → Finite X
  closed : ∀ {X : Type v} (C : RelStructure L X),
    K C → IsUClosed rules C
  hereditary : ClosedUHereditary K rules
  strong : HasFiniteStrongAmalgamation K
  localCompletion :
    ∀ {X Y : Type v} [Finite X] [Finite Y]
      (B : RelStructure L X) (C0 : RelStructure L Y),
      K B → R C0 →
      ∃ n : ℕ, LiteralULocalCompletionAt K rules B C0 n

/-- The literal printed Theorem 2.18, as a TARGET proposition,
not an assumption inserted as a new Lean axiom. -/
def LiteralTheorem218Target : Prop :=
  ∀ (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L),
    FiniteRamseyClass R →
    (∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible) →
    LiteralMultiamalgamationClass R K rules →
    FiniteRamseyClass K

end AllThoseRamseyClasses.Published

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The original (4b) condition is vacuous whenever a finite
paired structure contains a vertex: no singleton lies in K.
The local completion implication therefore holds for EVERY
finite B in K and EVERY original control C0, at cutoff n = 1. -/
theorem finitePairedClass_literal_local_all
    {VB P : Type} [Finite VB] [Finite P]
    (Base : RelStructure Lang VB)
    (Control : RelStructure Lang P)
    (hBase : finitePairedClass Base) :
    LiteralULocalCompletionAt
      finitePairedClass mateRules Base Control 1 := by
  have hNo :
      ∀ {X : Type} [Nonempty X] [Subsingleton X]
        (D : RelStructure Lang X), ¬ finitePairedClass D := by
    intro X _ _ D hD
    exact no_singleton_member D hD.2
  intro X hX C _ _ hAll _
  exact copywiseCompletion_of_intrinsic_tests_mem_of_no_singletons
    (K := finitePairedClass) Base hBase C hNo hAll

/-- The full class K is not Ramsey, not merely the failure of
one particular finite witness C. -/
theorem finitePairedClass_notRamsey :
    ¬ FiniteRamseyClass finitePairedClass := by
  intro h
  obtain ⟨Z, hZ, C, hK, hArrow⟩ :=
    h A B finiteA_mem finiteB_mem Bool
  exact finitePairedClass_has_no_B_Ramsey_witness
    ⟨Z, hZ, C, hK, hArrow⟩

/-- The class fulfils ALL literal printed multiamalgamation
conditions PROVIDED its still-open strong AP is supplied.
This sharply isolates the remaining proof obligation. -/
theorem finitePaired_literal_multiamalgamation_of_strong
    (hStrong : HasFiniteStrongAmalgamation finitePairedClass) :
    LiteralMultiamalgamationClass
      orderedAmbientClass finitePairedClass mateRules := by
  refine {
    subset := ?_
    finite := ?_
    closed := ?_
    hereditary := finitePairedClass_closedUHereditary
    strong := hStrong
    localCompletion := ?_
  }
  · intro X C hC
    exact finitePairedClass_subset_orderedAmbient C hC
  · intro X C hC
    exact hC.1
  · intro X C hC
    exact finitePairedClass_isUClosed C hC
  · intro X Y hX hY Base Control hBase _
    exact ⟨1, finitePairedClass_literal_local_all Base Control hBase⟩

/-- If the UNCORRECTED printed main theorem held for all classes,
then the paired-equivalence class COULD NOT have strong AP.
The preceding finite computations suggest precisely the opposite.
The missing strong AP theorem is NOT silently asserted here. -/
theorem literalTheorem218_implies_not_pairedStrong
    (hPublished : LiteralTheorem218Target.{0, 0} (L := Lang)) :
    ¬ HasFiniteStrongAmalgamation finitePairedClass := by
  intro hStrong
  have hPackage : LiteralMultiamalgamationClass
      orderedAmbientClass finitePairedClass mateRules :=
    finitePaired_literal_multiamalgamation_of_strong hStrong
  have hK : FiniteRamseyClass finitePairedClass :=
    hPublished orderedAmbientClass finitePairedClass mateRules
      orderedAmbient_isRamsey
      (fun C hC => orderedAmbient_irreducible C hC) hPackage
  exact finitePairedClass_notRamsey hK

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
