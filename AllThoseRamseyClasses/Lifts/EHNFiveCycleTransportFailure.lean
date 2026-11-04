import AllThoseRamseyClasses.Lifts.EHNFiveCycleNoInjectiveReplacement
import AllThoseRamseyClasses.Lifts.EHNWeakImageIrreducibleTestLifting
import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre
import AllThoseRamseyClasses.Lifts.EHNWeakImageExistentialTransport

/-!
# Track D: concrete failure of weak-image forbidden-copy transport

The printed family-level tuple-image closure is sufficient to
produce a FULL forbidden substructure of the SOURCE-GENERATED
weak quotient Q. It is NOT sufficient to make the weak inclusion
Q → Target an EHN map on that forbidden substructure.

For the fully certified five-cycle image-closed family and the
three-point target with an extra ternary relation, the original
five-cycle colouring gives a genuine noninjective EHN forbidden
witness. If the forbidden substructures of its generated quotient
transported as EHN maps, the already proved conditional
source-support replacement would give an injective forbidden
EHN map into the target, contradicting the concrete no-injective
replacement theorem.

Thus local forbidden-copy transport fails in the example.
The stronger requirement that all irreducible tests of those
forbidden copies lift to the original source also fails.
The source function-input test cover (vacuous here) does not
make target relation tuples covered: the extra ternary relation
is an explicit witness.

These conclusions are about an ARBITRARY target, which is NOT
a free amalgam of two forbidden-free maximal-lift witnesses.
This module does not assert a contradiction to the printed
maximal-lift strong-amalgamation theorem. The exact missing
special-geometric transport/root-collision obligation remains open.
-/

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-- The actual forbidden-source native EHN map in the
three-point target, retaining finite source carrier and family
membership as explicit dependent fields. -/
def cycle5ForbiddenEHNWitness :
    ForbiddenEHNWitness fiveCycleImageFamily triangleExtraTernary where
  Carrier := Fin 5
  finiteCarrier := inferInstance
  source := cycle5
  forbidden := cycle5_mem_imageFamily
  toTarget := weakColor
  homEmbedding := weakColor_nativeEHN

/-- The generated weak-image inclusion is NOT automatically
EHN on every full forbidden substructure of the quotient,
even though the source family satisfies the printed
tuple-surjective image-closure assumption. -/
theorem fiveCycle_weakImage_forbiddenTransport_fails :
    ¬ ForbiddenFullWeakImagePiecesTransport
      fiveCycleImageFamily triangleExtraTernary
      cycle5ForbiddenEHNWitness := by
  intro hTransport
  have hFinite :
      ∀ {X : Type} (P : Structure language X),
        fiveCycleImageFamily P → Finite X :=
    fun P hP => finite_of_fiveCycleImageFamily P hP
  obtain ⟨replacement, hInjective, _⟩ :=
    forbiddenWeakImage_injectiveReplacement_of_localTransport
      fiveCycleImageFamily hFinite
      fiveCycleImageFamily_printedImageClosed
      triangleExtraTernary
      (∅ : Set (Fin 3))
      cycle5ForbiddenEHNWitness hTransport
  exact
    (fiveCycleImageFamily_noInjectiveEHN
      replacement.source replacement.forbidden
      replacement.toTarget replacement.homEmbedding)
      hInjective

/-- The counterexample rules out even the WEAKER
existential transportable-copy condition: no full forbidden
substructure P of the generated weak quotient has an EHN
inclusion into the target. Otherwise the support-preserving
existential replacement theorem produces an impossible
injective forbidden EHN witness. -/
theorem fiveCycle_weakImage_noTransportableForbiddenCopy :
    ¬ HasTransportableForbiddenWeakImageCopy
      fiveCycleImageFamily triangleExtraTernary
      cycle5ForbiddenEHNWitness := by
  intro hCopy
  have hFinite :
      ∀ {X : Type} (P : Structure language X),
        fiveCycleImageFamily P → Finite X :=
    fun P hP => finite_of_fiveCycleImageFamily P hP
  obtain ⟨replacement, hInjective, _⟩ :=
    forbiddenWeakImage_injectiveReplacement_of_existsTransportableCopy
      fiveCycleImageFamily hFinite
      triangleExtraTernary
      (∅ : Set (Fin 3))
      cycle5ForbiddenEHNWitness hCopy
  exact
    (fiveCycleImageFamily_noInjectiveEHN
      replacement.source replacement.forbidden
      replacement.toTarget replacement.homEmbedding)
      hInjective

/-- The source-side irreducible-test lifting hypothesis is
a genuine EXTRA premise: it implies forbidden transport and
therefore also fails for this finite example. -/
theorem fiveCycle_weakImage_irreducibleSourceTestsDoNotLift :
    ¬ ForbiddenWeakImageIrreducibleTestsLift
      fiveCycleImageFamily triangleExtraTernary
      cycle5ForbiddenEHNWitness := by
  intro hLift
  exact fiveCycle_weakImage_forbiddenTransport_fails
    (forbiddenWeakImage_localTransport_of_irreducibleTestLifting
      fiveCycleImageFamily triangleExtraTernary
      cycle5ForbiddenEHNWitness hLift)

/-- The extra old-language ternary tuple is present in the
entire full target range but absent from every source tuple.
Thus source irreducible FUNCTION-input coverage alone cannot
yield RELATION-tuple coverage of the induced target image. -/
theorem fiveCycle_sourceRelationTupleCoverage_fails :
    ¬ SourceRelationTuplesCoveredOnRange
      cycle5 triangleExtraTernary weakColor := by
  intro h
  obtain ⟨ys, hy, _⟩ :=
    h true (fun i : Fin 3 => i)
      (fun i => weakColor_surjective i)
      target_has_extra_ternary
  exact source_has_no_ternary ys hy

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
