import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderEmbeddingBridge
import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderGraphDecode
import PartiteConstruction.Functional.Closed

/-!
# Track F: identity first-order embedding between decoded and original graph models

The actual first-order directed limit of the complete
relationalized function graphs is decoded to a native
Structure with partial/set-valued function fibres. Re-encoding
that native model produces a first-order graph structure on
the SAME carrier, but it need not be DEFINITIONALLY EQUAL
to the original first-order structure: relation equivalence
is a theorem, not necessarily a reduction rule.

This file constructs the explicit identity-vertex first-order
EMBEDDING from the encoded decoded model to the original
first-order graph model, for any relational graph language
and any native set-valued functional language. It uses the
verified decode/encode relation equivalence plus the genuine
closed graph-ofGraph embedding.

This is the semantic interface needed before the final
native-limit lift can compose a Mathlib first-order
direct-limit embedding with an exact graph embedding and
then invoke the merged surjective graph-to-FULL bridge.
No carrier quotient is silently identified, and no
arbitrary graph embedding is asserted FULL without closure.

The results are unconditional algebraic decoder lemmas.
No Claim 2, original finite-age input, homogeneity or 2019
Ramsey theorem is assumed. Numbered manuscript unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u v

/-- Decoding a purely relational first-order structure and
re-encoding its relational table gives a first-order
structure EMBEDDING back to the original model, whose
underlying vertex function is literally identity.

The relation equivalence follows from exact arity-indexed
decode/encode, not definitional equality of structures. -/
def firstOrderRelGraphDecode_id_embedding
    {R : RelLanguage.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage R).Structure V) :
    @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage R) V V
      (firstOrderRelGraphStructure (firstOrderRelGraphDecode h))
      h := by
  exact {
    toFun := id
    inj' := Function.injective_id
    map_fun' := by
      intro n f xs
      exact nomatch f.down
    map_rel' := by
      intro n s xs
      change h.RelMap s xs ↔
        (firstOrderRelGraphStructure
          (firstOrderRelGraphDecode h)).RelMap s xs
      exact (firstOrderRelGraph_encode_decode_rel_iff h n s xs).symm
  }

/-- For any native set-valued functional graph language,
the complete first-order graph model of the genuine decoded
native structure embeds into the ORIGINAL first-order model,
via the identity on vertices.

The proof does not identify the graph of Structure.ofGraph R
with R definitionally: it uses the verified graph-ofGraph closed
embedding and the separately proved first-order decode/encode
embedding. Both steps preserve and reflect every graph
incidence, including the exact full set of outputs. -/
def firstOrderNativeGraphDecode_id_embedding
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V) :
    @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V
      (firstOrderNativeGraphStructure (firstOrderNativeGraphDecode h))
      h :=
  (firstOrderRelGraphDecode_id_embedding h).comp
    (firstOrderRelGraphEmbedding
      (Structure.graphOfGraphClosed
        (R := firstOrderRelGraphDecode h)).toEmbedding)

/-- The decoded-model-to-original-model first-order bridge
has exactly the SAME underlying vertex map, namely identity. -/
theorem firstOrderNativeGraphDecode_id_embedding_apply
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (x : V) :
    firstOrderNativeGraphDecode_id_embedding h x = x := by
  rfl

end AllThoseRamseyClasses.Lifts
