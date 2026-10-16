import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceOriginalRelations

/-!
# A concrete old/new sort collision in the unmarked incidence language

The paper's incidence lift introduces genuinely NEW vertices for
positive tuples. Without a unary predicate distinguishing original
vertices from newly introduced incidence vertices, a full embedding
of functional incidence lifts need NOT restrict to an embedding
of their original relational reducts.

This module verifies the smallest obstruction: one unary symbol R,
a one-point source with R false, and a one-point target with R true.
The source lift has only its one original vertex; the target lift
has both the positive original vertex and a new incidence vertex.
Sending the source old vertex to the TARGET NEW incidence vertex
is a full embedding for all original relation symbols and ALL
set-valued incidence functions; nevertheless NO full relational
embedding exists between the original one-point shadows.

This does NOT refute the theorem that totally ordered relations are
Ramsey. It identifies a requirement for the proposed proof: the
auxiliary incidence language needs to preserve the original-vs-new
vertex sort (for example by unary predicates) if copies are to
be forgotten back to original structures using arbitrary full
embeddings of the lift.

The total vertex orders in this one-point example are trivial on
the source and old-first on the target, so the same issue persists
when the paper's order relation is included.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

/-- One unary relation symbol. -/
abbrev unaryTinyLanguage : RelLanguage where
  Symbol := PUnit
  arity := fun _ => 1

/-- One original vertex, with the unary relation ALWAYS absent. -/
def negativeOnePoint : TotalOrderData unaryTinyLanguage PUnit where
  base := ⟨fun _ _ => False⟩
  vertexLE := fun _ _ => True
  tupleLE := fun _ _ _ => False

/-- One original vertex, with the unary relation ALWAYS present. -/
def positiveOnePoint : TotalOrderData unaryTinyLanguage PUnit where
  base := ⟨fun _ _ => True⟩
  vertexLE := fun _ _ => True
  tupleLE := fun _ _ _ => True

/-- The unique positive incidence vertex of the target lift. -/
def positiveOnePointTag :
    Sigma fun r : unaryTinyLanguage.Symbol =>
      {t : Fin (unaryTinyLanguage.arity r) → PUnit //
        positiveOnePoint.base.rel r t} :=
  ⟨(), ⟨fun _ => (), trivial⟩⟩

/-- A map that sends every source vertex (necessarily original)
to the NEW incidence vertex of the positive target. -/
def originalToNewMap :
    IncidenceCarrier negativeOnePoint →
      IncidenceCarrier positiveOnePoint :=
  fun _ => .inr positiveOnePointTag

/-- This map is injective since the negative source lift has only
one vertex. A tagged incidence source vertex would require
a proof of a false unary relation. -/
theorem originalToNewMap_injective :
    Function.Injective originalToNewMap := by
  intro x y _
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          cases x
          cases y
          rfl
      | inr y =>
          exact False.elim y.2.2
  | inr x =>
      exact False.elim x.2.2

/-- The negative original one-point relational structure cannot
embed fully into the positive original one-point structure. -/
theorem noOriginalRelationalEmbedding :
    ¬ Nonempty (RelStructure.Embedding
      negativeOnePoint.base positiveOnePoint.base) := by
  rintro ⟨e⟩
  have h := e.map_rel_iff () (fun _ : Fin 1 => ())
  change True ↔ False at h
  exact h.mp trivial

/-- Despite the failure for original shadows, the old-to-new map
IS a full embedding of both the actual inherited relational shadow
and the entire set-valued incidence-function table. -/
def originalToNew_fullFunctionalEmbedding :
    Structure.Embedding
      (incidenceOriginalAndFunctional negativeOnePoint)
      (incidenceOriginalAndFunctional positiveOnePoint) where
  toFun := originalToNewMap
  injective := originalToNewMap_injective
  map_rel_iff := by
    intro r t
    change liftedOriginalRel positiveOnePoint r
        (originalToNewMap ∘ t) ↔
      liftedOriginalRel negativeOnePoint r t
    constructor
    · rintro ⟨old, hOld, _⟩
      have h := hOld 0
      change Sum.inr positiveOnePointTag = Sum.inl (old 0) at h
      cases h
    · rintro ⟨old, _, hFalse⟩
      exact False.elim hFalse
  map_func := by
    intro r t
    change originalToNewMap '' fullIncidenceFibre negativeOnePoint r t =
      fullIncidenceFibre positiveOnePoint r (originalToNewMap ∘ t)
    ext y
    constructor
    · rintro ⟨x, ⟨old, _, hx⟩, _⟩
      have hSome : (incidenceValue negativeOnePoint r old).isSome := by
        change some x = incidenceValue negativeOnePoint r old at hx
        rw [← hx]
        rfl
      have hFalse : negativeOnePoint.base.rel r old :=
        (incidenceValue_isSome_iff negativeOnePoint r old).mp hSome
      exact False.elim hFalse
    · rintro ⟨old, hOld, _⟩
      have h := hOld 0
      change Sum.inr positiveOnePointTag = Sum.inl (old 0) at h
      cases h

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
