import AllThoseRamseyClasses.Applications.TotallyOrderedIncidencePaperOrder
import Mathlib.Order.Sigma
import Mathlib.Order.Sum.Order

/-!
# A genuine canonical external linear order on an incidence lift

The paper orders original vertices and, separately for each relation symbol,
the set of positive tuples of that relation. The finite functional EHN Ramsey
theorem instead needs one EXTERNAL total vertex order on the entire incidence
carrier of original vertices and tags.

Given the original vertex LinearOrder and a family of LinearOrders on the
positive tuple subtypes, the canonical external order is the linear sum:
  Old vertices, followed by New_r tags sorted by symbol r and positive tuple.

It is built using Mathlib's actual lexicographic Sigma and Sum orders, with
an explicit two-sided decoding inverse. It does not require the carrier or
language to be finite, and it does not silently assume any arbitrary
TotalOrderData order predicates are already well-formed.

The compatibility of this order with the paper's intrinsic incidenceLE is
a separate source-matched theorem depending on equality of the original
predicates with the supplied linear orders.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- The dependent Sigma-lex order using EXACTLY the supplied
source-positive-tuple orders, rather than an unrelated synthesized
instance on the tagged subtype. This named instance is used by the
whole incidence carrier order and by the compatibility proof. -/
noncomputable def incidenceTagLexLinearOrder
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} (A : TotalOrderData L V)
    (tupleOrders : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t}) :
    LinearOrder (Lex (IncidenceTag A)) := by
  classical
  letI : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t} :=
    tupleOrders
  infer_instance

/-- Literal injection of old vertices and positive-tag vertices into the
lexicographic sum used for the canonical external EHN order. -/
def canonicalIncidenceOrderKey
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) :
    IncidenceCarrier A → Lex (V ⊕ Lex (IncidenceTag A))
  | .inl x => toLex (Sum.inl x)
  | .inr tag => toLex (Sum.inr (toLex tag))

/-- The original incidence carrier can be recovered by simply
unwrapping the two lexicographic sum wrappers. -/
theorem canonicalIncidenceOrderKey_injective
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) :
    Function.Injective (canonicalIncidenceOrderKey A) := by
  let recover : Lex (V ⊕ Lex (IncidenceTag A)) → IncidenceCarrier A :=
    fun z =>
      match (ofLex z : V ⊕ Lex (IncidenceTag A)) with
      | .inl x => .inl x
      | .inr t => .inr (ofLex t)
  have recover_key (x : IncidenceCarrier A) :
      recover (canonicalIncidenceOrderKey A x) = x := by
    cases x <;> rfl
  intro x y h
  calc
    x = recover (canonicalIncidenceOrderKey A x) := (recover_key x).symm
    _ = recover (canonicalIncidenceOrderKey A y) := congrArg recover h
    _ = y := recover_key y

/-- Build the canonical OLD-first, symbol-first total external order of
the full incidence carrier from genuine original and positive-tuple orders.
No injectivity of any induced closure function is assumed or needed. -/
noncomputable def canonicalIncidenceExternalLinearOrder
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} [LinearOrder V]
    (A : TotalOrderData L V)
    (tupleOrders : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t}) :
    LinearOrder (IncidenceCarrier A) := by
  classical
  letI : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t} :=
    tupleOrders
  letI : LinearOrder (Lex (IncidenceTag A)) :=
    incidenceTagLexLinearOrder A tupleOrders
  exact LinearOrder.lift'
    (canonicalIncidenceOrderKey A)
    (canonicalIncidenceOrderKey_injective A)

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
