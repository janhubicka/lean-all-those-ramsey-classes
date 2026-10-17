import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceWeakOldProjection
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceDecodedPositiveOrder

/-!
# Decode the Old part of a weak functional incidence witness

The freely ordered EHN witness used in manuscript thm:TO belongs only to
the weak orphan-tolerant incidence-law auxiliary class, NOT necessarily
to the exact image of a canonical incidence lift.

We build the original relational L-reduct on exactly its Old-marked
vertices. The induced original vertex comparison is the RESTRICTION of
the EXTERNAL Ramsey witness linear order, never the unconstrained
internal binary comparison predicate.  For each relation symbol, its
positive instances are ordered by their singleton forward-output tag,
and then by the complete old input tuple to resolve collisions.

The resulting TotalOrderData has genuinely supported tuple comparisons
and actual linearly ordered positive-tuple carriers. Nullary symbols
and colliding tags are included. This is the honest target-object
construction needed for direct copywise thm:TO transfer; the global
arrow theorem is deliberately not asserted here.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- Turn a positive tuple of Old vertices into the corresponding positive
tuple of the arbitrary weak auxiliary structure, retaining the full input
coordinates. -/
def weakOldPositiveTuple
    {L : RelLanguage.{u}} {W : Type v}
    (C : Structure (markedIncidencePaperLanguage L) W)
    (r : L.Symbol)
    (t : Fin (L.arity r) → WeakOldVertices C)
    (ht : (weakOldRelStructure C).rel r t) :
    WeakPositiveTuples C r :=
  ⟨fun i => (t i).val, ht⟩

/-- Decode a weak marked incidence structure with an external linear
vertex order to old relational data with valid orders of positive
relation instances. Tag collisions are resolved by the complete tuple
as an injective secondary key. -/
noncomputable def weakDecodedTotalOrderData
    {L : RelLanguage.{u}} {W : Type v}
    [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C) :
    TotalOrderData L (WeakOldVertices C) where
  base := weakOldRelStructure C
  vertexLE := fun x y => x.val ≤ y.val
  tupleLE := fun r t s =>
    ∃ (ht : (weakOldRelStructure C).rel r t)
      (hs : (weakOldRelStructure C).rel r s),
      @LE.le (WeakPositiveTuples C r)
        (weakPositiveTuplesLinearOrder hC r).toLE
        (weakOldPositiveTuple C r t ht)
        (weakOldPositiveTuple C r s hs)

/-- Exact source-matched support: no tuple comparisons are introduced
between negative relation instances, even when a tag is orphaned. -/
theorem weakDecoded_tupleOrdersSupported
    {L : RelLanguage.{u}} {W : Type v}
    [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C) :
    TupleOrdersSupported (weakDecodedTotalOrderData C hC) := by
  intro r t s h
  rcases h with ⟨ht, hs, _⟩
  exact ⟨ht, hs⟩

/-- On positive tuples the decoded relation is total. Its two possible
directions use precisely the genuine linear order on positive tags/tuples
constructed in the previous application module. -/
theorem weakDecoded_tupleOrder_total_of_positive
    {L : RelLanguage.{u}} {W : Type v}
    [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol)
    (t s : Fin (L.arity r) → WeakOldVertices C)
    (ht : (weakDecodedTotalOrderData C hC).base.rel r t)
    (hs : (weakDecodedTotalOrderData C hC).base.rel r s) :
    (weakDecodedTotalOrderData C hC).tupleLE r t s ∨
      (weakDecodedTotalOrderData C hC).tupleLE r s t := by
  letI : LinearOrder (WeakPositiveTuples C r) :=
    weakPositiveTuplesLinearOrder hC r
  rcases le_total (weakOldPositiveTuple C r t ht)
    (weakOldPositiveTuple C r s hs) with hle | hle
  · exact Or.inl ⟨ht, hs, hle⟩
  · exact Or.inr ⟨hs, ht, hle⟩

/-- Restriction of the external vertex order, with no claim that the
unrestricted internal order relation in the auxiliary language is valid. -/
theorem weakDecoded_vertexLE_iff
    {L : RelLanguage.{u}} {W : Type v}
    [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (x y : WeakOldVertices C) :
    (weakDecodedTotalOrderData C hC).vertexLE x y ↔ x.val ≤ y.val :=
  Iff.rfl

/-- The old-reduct of a finite auxiliary witness is finite, including
when some orphan new vertices are completely unrelated to the old part. -/
theorem weakOldVertices_finite
    {L : RelLanguage.{u}} {W : Type v}
    [Finite W]
    (C : Structure (markedIncidencePaperLanguage L) W) :
    Finite (WeakOldVertices C) :=
  Finite.of_injective Subtype.val Subtype.val_injective

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
