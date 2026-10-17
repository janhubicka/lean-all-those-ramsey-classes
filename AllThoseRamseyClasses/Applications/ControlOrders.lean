import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic

/-!
# Reusable lexicographic control orders for finite and ordered applications

Two related constructions occur repeatedly in the examples of the 2019 paper:

1. A finite UNORDERED carrier has a map to an ordered control, possibly
   identifying vertices.  Arbitrary distinct finite indices break ties and
   yield an order in which all strictly increasing control pairs stay ordered.
   Both poset and Steiner weak completions use this exact construction.
2. An ALREADY ORDERED carrier has a type/label map to another ordered type.
   Stable sorting by (label, original position) produces a new order.
   Loop-first digraphs and general one-point-type admissible orders use it.

The first is an existential order-extension lemma and does not pick a new
canonical order.  The second is a specified stable sorted order that retains
the original comparisons between vertices of equal type.

The existing researcher-facing `exists_linearOrder_strictOn_controlIncrease`
declaration is preserved in the same namespace; only its source module changes.
-/

namespace AllThoseRamseyClasses.Applications

universe u v

/-- On a finite carrier, extend the strict control-value comparisons
to a total vertex order without assuming the control map is injective. -/
theorem exists_linearOrder_strictOn_controlIncrease
    {V : Type u} {D : Type v} [Finite V] [LinearOrder D]
    (f : V → D) :
    ∃ (o : LinearOrder V),
      ∀ x y : V, f x < f y →
        @LT.lt V o.toLT x y := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let key : V → D ×ₗ Fin (Fintype.card V) :=
    fun x => toLex (f x, Fintype.equivFin V x)
  have hKeyInj : Function.Injective key := by
    intro x y hxy
    apply (Fintype.equivFin V).injective
    exact congrArg (fun z => (ofLex z).2) hxy
  let o : LinearOrder V := LinearOrder.lift' key hKeyInj
  refine ⟨o, ?_⟩
  intro x y hxy
  change key x < key y
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hxy)

namespace ControlOrders

/-- Sort an ALREADY ordered carrier by a possibly noninjective control
label, retaining the original strict order within each label fibre. -/
noncomputable def stableSortLinearOrder
    {V : Type u} {D : Type v}
    [LinearOrder V] [LinearOrder D]
    (label : V → D) : LinearOrder V := by
  classical
  exact LinearOrder.lift'
    (fun x => toLex ((label x, x) : D × V))
    (by
      intro x y h
      exact congrArg Prod.snd
        (congrArg (ofLex : Lex (D × V) → D × V) h))

/-- The exact lexicographic comparison of the stable sorted order:
labels first and the original order on vertices only on ties. -/
theorem stableSortLinearOrder_lt_iff
    {V : Type u} {D : Type v}
    [LinearOrder V] [LinearOrder D]
    (label : V → D) (x y : V) :
    (letI := stableSortLinearOrder label; x < y) ↔
      label x < label y ∨
        (label x = label y ∧ x < y) := by
  change toLex ((label x, x) : D × V) <
    toLex ((label y, y) : D × V) ↔ _
  exact Prod.Lex.toLex_lt_toLex

end ControlOrders
end AllThoseRamseyClasses.Applications
