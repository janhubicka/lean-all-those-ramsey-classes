import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceDecodedOldData

/-!
# The actual source language of finite totally ordered relations

An ordinary totally ordered relational L-structure consists of:

* an L-structure on a linearly ordered vertex type;
* for each relation symbol r, a separate genuine LinearOrder on the subtype
  of POSITIVE r-tuples, not on all tuples of the same arity.

The earlier TotalOrderData structure was intentionally unconstrained data:
it records raw predicates, not proofs that those predicates are genuine
orders. This module supplies a source-matched bundled object and encodes it
faithfully in TotalOrderData, with the vertex and relation-instance orders
supported by construction.

The subtype approach handles empty positive relations and zero-arity
symbols. No finite-carrier assumption is required to define these data.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- Genuine orders on the original vertex set and each relation's
positive instances, exactly the source objects in manuscript thm:TO. -/
structure OrderedRelations
    (L : RelLanguage.{u}) (V : Type v) [LinearOrder V] where
  base : RelStructure L V
  positiveOrders : (r : L.Symbol) →
    LinearOrder {t : Fin (L.arity r) → V // base.rel r t}

/-- Interpret a genuine instance-ordered relational structure as the
fully recorded order predicates used by the 2019 incidence encoding.
Comparisons of negative tuples are always false. -/
noncomputable def OrderedRelations.toTotalOrderData
    {L : RelLanguage.{u}} {V : Type v} [LinearOrder V]
    (A : OrderedRelations L V) : TotalOrderData L V where
  base := A.base
  vertexLE := (· ≤ ·)
  tupleLE := fun r t s =>
    ∃ (ht : A.base.rel r t) (hs : A.base.rel r s),
      @LE.le _ (A.positiveOrders r).toLE
        (⟨t, ht⟩ : {q // A.base.rel r q})
        (⟨s, hs⟩ : {q // A.base.rel r q})

/-- Original vertex comparison is literally the actual linear order. -/
theorem OrderedRelations.vertexLE_iff
    {L : RelLanguage.{u}} {V : Type v} [LinearOrder V]
    (A : OrderedRelations L V) (x y : V) :
    A.toTotalOrderData.vertexLE x y ↔ x ≤ y :=
  Iff.rfl

/-- Relation-instance comparison is literally the supplied linear
order restricted to the positive r-tuple subtype. -/
theorem OrderedRelations.positiveTupleLE_iff
    {L : RelLanguage.{u}} {V : Type v} [LinearOrder V]
    (A : OrderedRelations L V)
    (r : L.Symbol)
    (t s : {q : Fin (L.arity r) → V // A.base.rel r q}) :
    A.toTotalOrderData.tupleLE r t.1 s.1 ↔
      @LE.le _ (A.positiveOrders r).toLE t s := by
  constructor
  · rintro ⟨ht, hs, hle⟩
    exact hle
  · intro hle
    exact ⟨t.2, s.2, hle⟩

/-- The original comparison relation never compares a negative tuple.
This is intrinsic to ordering relation INSTANCES, not an extra class axiom. -/
theorem OrderedRelations.tupleOrdersSupported
    {L : RelLanguage.{u}} {V : Type v} [LinearOrder V]
    (A : OrderedRelations L V) :
    TupleOrdersSupported A.toTotalOrderData := by
  intro r t s h
  exact ⟨h.1, h.2.1⟩

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
