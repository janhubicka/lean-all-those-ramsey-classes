import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderGraph

/-!
# Track F: decode the exact first-order graph back to native full function fibres

Mathlib's first-order directed limit is relational in the
function-graph encoding of the original global maximal lift. To
obtain the intended original native functional structure, decode
each first-order graph relation, including complete function-value
relations of arity n+1, back into a set-valued function fibre.

This file proves that encoding and decoding are inverse ON ALL
RELATION TABLES and ON EVERY COMPLETE FUNCTION-VALUE FIBRE.
It handles nullary old functions, empty/undefined fibres,
multiple outputs and repeated inputs without any weak
homomorphism-embedding or closure-hull substitutions.

These round-trip properties are distinct from proving that an
arbitrary first-order graph embedding is a FULL native embedding.
That still requires closedness of its image (merged Track F #848).
No infinite Fraisse limit, homogeneous reduct or unrestricted
Section 3 shadow avoidance is asserted.

The frozen ramsey.tex remains unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u v

/-- Decode an arity-indexed first-order *relational* structure
back into the original StructuralRamsey relational structure,
without identifying any two symbols of different arities. -/
def firstOrderRelGraphDecode
    {R : RelLanguage.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage R).Structure V) :
    RelStructure R V where
  rel S xs :=
    h.RelMap
      (⟨S, rfl⟩ :
        (firstOrderRelGraphLanguage R).Relations (R.arity S)) xs

/-- Decoding the first-order encoding of an actual relation
table recovers that table, including negative, repeated-entry
and arity-zero information. -/
theorem firstOrderRelGraphDecode_encode_rel_iff
    {R : RelLanguage.{u}} {V : Type v}
    (A : RelStructure R V)
    (S : R.Symbol)
    (xs : Fin (R.arity S) → V) :
    (firstOrderRelGraphDecode
      (firstOrderRelGraphStructure A)).rel S xs ↔
      A.rel S xs := by
  rfl

/-- Encoding a decoded first-order relational structure
recovers every original first-order relation truth value. -/
theorem firstOrderRelGraph_encode_decode_rel_iff
    {R : RelLanguage.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage R).Structure V)
    (n : ℕ)
    (S : (firstOrderRelGraphLanguage R).Relations n)
    (xs : Fin n → V) :
    (firstOrderRelGraphStructure
      (firstOrderRelGraphDecode h)).RelMap S xs ↔
      h.RelMap S xs := by
  rcases S with ⟨S, hArity⟩
  cases hArity
  rfl

/-- Decode the relational graph of any native set-valued
partial-functional structure as the original native
Structure: every (n+1)-ary function incidence is read as
membership of the output vertex in the ENTIRE fibre. -/
def firstOrderNativeGraphDecode
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V) :
    Structure L V :=
  Structure.ofGraph (firstOrderRelGraphDecode h)

/-- The decoded native structure has exactly the original
relation table, including nullary symbols and negative
incidences on repeated-entry tuples. -/
theorem firstOrderNativeGraph_decode_encode_rel_iff
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (S : L.RelSymbol)
    (xs : Fin (L.relArity S) → V) :
    (firstOrderNativeGraphDecode
      (firstOrderNativeGraphStructure A)).rel S xs ↔
      A.rel S xs := by
  rfl

/-- The decoded native structure has EXACTLY the complete
original partial/set-valued function fibre over any input
tuple. This includes a nullary symbol, an empty output
set, and multiple outputs. -/
theorem firstOrderNativeGraph_decode_encode_func_iff
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (S : L.FuncSymbol)
    (xs : Fin (L.funcArity S) → V)
    (y : V) :
    y ∈ (firstOrderNativeGraphDecode
      (firstOrderNativeGraphStructure A)).func S xs ↔
      y ∈ A.func S xs := by
  change A.graph.rel (.inr S) (Structure.funcTuple xs y) ↔
    y ∈ A.func S xs
  exact Structure.graph_func_snoc A S xs y

/-- Full fibre equality: decoding/encoding does not silently
retain only positive images or drop additional target outputs.
This is the signature semantics required by the subsequent
direct-limit construction. -/
theorem firstOrderNativeGraph_decode_encode_wholeFibre
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (S : L.FuncSymbol)
    (xs : Fin (L.funcArity S) → V) :
    (firstOrderNativeGraphDecode
      (firstOrderNativeGraphStructure A)).func S xs =
      A.func S xs := by
  ext y
  exact firstOrderNativeGraph_decode_encode_func_iff A S xs y

end AllThoseRamseyClasses.Lifts
