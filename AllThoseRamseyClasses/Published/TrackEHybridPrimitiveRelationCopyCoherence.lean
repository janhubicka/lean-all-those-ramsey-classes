import AllThoseRamseyClasses.Published.TrackEHybridPositiveOutputSound
import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical

/-!
# Track E2: synchronize both primitive relation copies in the hybrid language

The combined hybrid language has TWO independently named copies
of each ORIGINAL primitive relation R:

* the original-OLD complete-mask/tag component, and
* the per-output-part singleton-pattern/tag component.

They agree in a canonical genuine native functional partite System,
but in an ARBITRARY relational hybrid target their interpretations
need not agree. The previously established value/domain/mask and
inner-tag normality invariants do not force this cross-component
relational equality. Without it, no NATIVE re-encoding can recover
the whole hybrid language from the decoded original Structure.

This module isolates the independent necessary target-normality
guard, for every primitive relation, every tuple and every arity.
Rather than repeat the same free-amalgam localization proof twice,
we reuse the already checked positive tuple-to-root implication
`TupleImpliesRoot` with identity coordinate selection. Both
directions are exact-weak hereditary and TRUE FULL free-stable.

The theorem is source-valid, and no U-closure, finite carrier,
positive function arity, new vertex or function value is assumed.
It does NOT assert that the two-pass sparse Ramsey construction
preserves the synchronization law, or that the entire hybrid
target is already its canonical native re-encoding.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The OLD and split nested tag components carry distinct
syntactic copies of the original R relation symbol. -/
private def primitiveOldSymbol (R : L.RelSymbol) :
    (L.splitMaskHybrid Parts).Symbol :=
  .inl (.inl (.inl R))

/-- The exact SAME primitive relation in the singleton
output-part indexed pattern-tag component. -/
private def primitiveSplitSymbol (R : L.RelSymbol) :
    (L.splitMaskHybrid Parts).Symbol :=
  .inr (.inl (.inl (.inl (ULift.up R))))

/-- For every ORIGINAL relation, the two tagged hybrid components
must display exactly the same tuples. We encode this as both
directions of the already verified tuple-to-tuple implication,
using the IDENTITY map of coordinates. -/
def HybridPrimitiveRelationCopiesAgree
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ R : L.RelSymbol,
    TupleImpliesRoot E (primitiveOldSymbol (Parts := Parts) R)
      (primitiveSplitSymbol (Parts := Parts) R) id ∧
    TupleImpliesRoot E (primitiveSplitSymbol (Parts := Parts) R)
      (primitiveOldSymbol (Parts := Parts) R) id

/-- The two primitive relation copies are literally equivalent
at each tuple (not merely up to homomorphism or copy selection). -/
theorem HybridPrimitiveRelationCopiesAgree.rel_iff
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridPrimitiveRelationCopiesAgree E)
    (R : L.RelSymbol) (t : Fin (L.relArity R) → V) :
    E.rel (primitiveOldSymbol (Parts := Parts) R) t ↔
      E.rel (primitiveSplitSymbol (Parts := Parts) R) t := by
  constructor
  · intro ht
    simpa only [Function.comp_id] using (h R).1 t ht
  · intro ht
    simpa only [Function.comp_id] using (h R).2 t ht

/-- Every genuine native functional partite source records
both relation copies using precisely A.rel, including
repeated vertices and nullary primitive relation symbols. -/
theorem canonicalHybrid_primitiveRelationCopiesAgree
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridPrimitiveRelationCopiesAgree A.splitMaskHybrid := by
  intro R
  constructor
  · intro t ht
    simpa only [Function.comp_id] using ht
  · intro t ht
    simpa only [Function.comp_id] using ht

/-- The exact ambient weak cut retains both named primitive
relation copies, so it preserves their agreement without
regenerating any primitive or functional relation tuple. -/
theorem HybridPrimitiveRelationCopiesAgree.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridPrimitiveRelationCopiesAgree E)
    (S : Set V) :
    HybridPrimitiveRelationCopiesAgree (E.induce S) := by
  intro R
  exact ⟨(h R).1.induce S, (h R).2.induce S⟩

/-- A true FULL free amalgam of compatible hybrid pictures
preserves exact equality of the two primitive relation copies.
Every primitive relation tuple comes wholly from one side;
the identity-coordinate implications map it to the other
copy of the SAME tuple on that side, hence in the amalgam. -/
theorem HybridPrimitiveRelationCopiesAgree.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridPrimitiveRelationCopiesAgree Left)
    (hRight : HybridPrimitiveRelationCopiesAgree Right) :
    HybridPrimitiveRelationCopiesAgree Whole := by
  intro R
  constructor
  · exact TupleImpliesRoot.freeAmalgam hFree
      (primitiveOldSymbol (Parts := Parts) R)
      (primitiveSplitSymbol (Parts := Parts) R)
      id (hLeft R).1 (hRight R).1
  · exact TupleImpliesRoot.freeAmalgam hFree
      (primitiveSplitSymbol (Parts := Parts) R)
      (primitiveOldSymbol (Parts := Parts) R)
      id (hLeft R).2 (hRight R).2

end StructuralRamsey.RelStructure
