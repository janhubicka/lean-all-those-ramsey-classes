import AllThoseRamseyClasses.Applications.TotallyOrderedRelationsSource
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceCanonicalOrderCompatibility

/-!
# Source-side canonical incidence order for genuinely ordered relations

The 2019 `thm:TO` source has an honest total vertex order and, for
each relation symbol, an honest total order of its *positive tuples*.
It is not an arbitrary `TotalOrderData` record.

The canonical incidence lift has an **external** EHN order obtained by
putting old vertices first and ordering the new tags by their relation
symbol and their positive-tuple order. The compatibility theorem below
shows that this external order is *exactly* the paper's intrinsic
`paperIncidenceLE`, on all four Old/New configurations.

These theorems discharge the source-order assumptions of the already
checked `totallyOrderedRelations_arrow_of_canonical_orders`. They do
not assume that the unconstrained internal order of a weak auxiliary
Ramsey target is genuine, nor do they claim a final class-level
Ramsey theorem here. In particular, the source may have empty or
nullary positive relations.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- The *genuine* source incidence lift order, old vertices first and
then positive tags ordered by symbol and their given tuple orders.
This is a Lean `LinearOrder`, not a raw binary relation. -/
noncomputable def OrderedRelations.canonicalIncidenceOrder
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} [LinearOrder V]
    (A : OrderedRelations L V) :
    LinearOrder (IncidenceCarrier A.toTotalOrderData) :=
  canonicalIncidenceExternalLinearOrder
    A.toTotalOrderData A.positiveOrders

/-- The paper's literal incidence order agrees *on every vertex pair*
with the external EHN order canonically induced by the genuine source
orders. No additional totality or support assumption is required. -/
theorem OrderedRelations.canonicalIncidenceOrder_agrees
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} [LinearOrder V]
    (A : OrderedRelations L V)
    (x y : IncidenceCarrier A.toTotalOrderData) :
    paperIncidenceLE A.toTotalOrderData x y ↔
      @LE.le (IncidenceCarrier A.toTotalOrderData)
        A.canonicalIncidenceOrder.toLE x y := by
  exact canonicalIncidenceExternalLinearOrder_agrees
    A.toTotalOrderData A.positiveOrders
    (by intro a b; exact A.vertexLE_iff a b)
    (by intro r a b; exact A.positiveTupleLE_iff r a b) x y

/-- The genuine source also satisfies the exact positive-instance
support condition: negative relation tuples carry no comparisons. -/
theorem OrderedRelations.source_tupleOrdersSupported
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} [LinearOrder V]
    (A : OrderedRelations L V) :
    TupleOrdersSupported A.toTotalOrderData :=
  A.tupleOrdersSupported

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
