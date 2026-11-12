import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderNativeDecodeIdentity

/-!
# Track F: exact first-order equivalence of native decoded graphs and original graph models

The graph of the native set-valued functional decoder of any
pure first-order complete function-graph model is propositionally
equivalent to the ORIGINAL first-order model on the same carrier.
The identity-vertex embedding was isolated earlier.

This file strengthens the comparison to a genuine FIRST-ORDER
STRUCTURE EQUIVALENCE with the identity vertex bijection, not
merely a homomorphism of positive relation incidences.

In the eventual back-and-forth, the original Mathlib quotient
has its inherited first-order graph structure, while the
surjective graph-to-FULL conversion requires the graph of its
decoded native structure. The equivalence below is the exact
bridge between those two first-order structures; it eliminates
any temptation to assume they are definitionally equal.

All relation symbols, nullaries, repeated entries, and the
complete graph relations of partial/multivalued function
fibres are reflected, including negative incidences.
This is unconditional algebraic semantics; no original
Fraïssé input, global shadow avoidance, homogeneity or
2019 Ramsey conclusion is used. The numbered manuscript
is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u v

/-- Genuine first-order equivalence between the EXACT
re-encoded native decoder and its original first-order
function-graph model. Both vertex maps are identity.
The full bidirectional relation law is supplied by the
already verified decoder identity embedding. -/
def firstOrderNativeGraphDecode_id_equiv
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V) :
    @FirstOrder.Language.Equiv
      (firstOrderRelGraphLanguage L.graph) V V
      (firstOrderNativeGraphStructure (firstOrderNativeGraphDecode h))
      h := by
  refine @FirstOrder.Language.Equiv.mk
    (firstOrderRelGraphLanguage L.graph) V V
    (firstOrderNativeGraphStructure (firstOrderNativeGraphDecode h)) h
    (Equiv.refl V) ?_ ?_
  · intro n f xs
    exact nomatch f.down
  · intro n s xs
    -- There are two distinct structure instances on the same
    -- carrier.  Fix the relation goal before using the
    -- checked identity-vertex decoder embedding.
    change h.RelMap s xs ↔
      (firstOrderNativeGraphStructure
        (firstOrderNativeGraphDecode h)).RelMap s xs
    -- Apply the checked bridge's *structure-valued field* with
    -- both source and target model instances specified explicitly.
    -- The two models share the same carrier and Lean's inferred
    -- instance is otherwise ambiguous here.
    have hRel :=
      @FirstOrder.Language.Embedding.map_rel'
        (firstOrderRelGraphLanguage L.graph) V V
        (firstOrderNativeGraphStructure (firstOrderNativeGraphDecode h))
        h
        (firstOrderNativeGraphDecode_id_embedding h)
        n s xs
    have hFunction :
        (firstOrderNativeGraphDecode_id_embedding h).toFun ∘ xs = xs := by
      funext i
      exact firstOrderNativeGraphDecode_id_embedding_apply h (xs i)
    rw [hFunction] at hRel
    exact hRel

end AllThoseRamseyClasses.Lifts
