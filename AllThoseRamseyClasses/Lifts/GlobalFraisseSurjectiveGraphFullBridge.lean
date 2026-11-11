import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderEmbeddingBridge

/-!
# Track F: surjective first-order graph embeddings are FULL native embeddings

A first-order embedding of the complete relational graph of a
partial/set-valued functional language is not necessarily FULL:
the target can have additional outputs outside the embedded source.

However, if the first-order graph embedding is SURJECTIVE on
vertices, every target output has a source preimage. Reflection
of the exact function-graph relation then proves closure of the
source image for the entire function fibre. Hence the existing
closed-graph reconstruction produces a genuine FULL native
functional embedding with the SAME vertex map.

This elementary bridge is useful at the END of back-and-forth:
a coherent surjective first-order graph embedding obtained by a
direct-limit lift becomes a full native embedding, without
assuming arbitrary relational copies are function-closed.

This is independent of original shadow avoidance, the finite
Fraisse age, source reducibility and all section-3 Claim 2
proof obligations. Includes nullary, partial and multivalued
functions, and all negative relation incidences.

The numbered manuscript is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w

/-- A surjective first-order embedding of complete native
function-graph relationalizations has function-closed image.
Every target function output over old inputs is the image
of a source output; no value or definedness is lost. -/
theorem firstOrderNativeGraphEmbedding_closed_of_surjective
    {L : Language.{u}}
    {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V W
      (firstOrderNativeGraphStructure A)
      (firstOrderNativeGraphStructure B))
    (he : Function.Surjective e) :
    A.ClosedMap B e := by
  intro S xs y hy
  obtain ⟨z, hz⟩ := he y
  have hTuple :
      e ∘ Structure.funcTuple xs z =
        Structure.funcTuple (e ∘ xs) (e z) := by
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [Structure.funcTuple, Function.comp_apply]
    · simp [Structure.funcTuple, Function.comp_apply]
  have hyB : e z ∈ B.func S (e ∘ xs) := by
    rw [hz]
    exact hy
  have hGraphB :
      (firstOrderNativeGraphStructure B).RelMap
        (⟨Sum.inr S, rfl⟩ :
          (firstOrderRelGraphLanguage L.graph).Relations
            (L.funcArity S + 1))
        (e ∘ Structure.funcTuple xs z) := by
    rw [hTuple]
    exact (firstOrderNativeGraph_func_iff B S (e ∘ xs) (e z)).mpr hyB
  have hGraphA :
      (firstOrderNativeGraphStructure A).RelMap
        (⟨Sum.inr S, rfl⟩ :
          (firstOrderRelGraphLanguage L.graph).Relations
            (L.funcArity S + 1))
        (Structure.funcTuple xs z) :=
    (e.map_rel _ (Structure.funcTuple xs z)).mp hGraphB
  exact ⟨z,
    (firstOrderNativeGraph_func_iff A S xs z).mp hGraphA, hz⟩

/-- Every SURJECTIVE first-order graph embedding reconstructs
a genuine FULL native functional embedding of the same
underlying vertex types; no independent closure hypothesis. -/
def firstOrderNativeGraphEmbedding_toFull_of_surjective
    {L : Language.{u}}
    {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V W
      (firstOrderNativeGraphStructure A)
      (firstOrderNativeGraphStructure B))
    (he : Function.Surjective e) :
    Structure.Embedding A B :=
  firstOrderNativeGraphEmbedding_toFull e
    (firstOrderNativeGraphEmbedding_closed_of_surjective e he)

/-- The reconstructed FULL map has precisely the original
first-order graph map on vertices. -/
theorem firstOrderNativeGraphEmbedding_toFull_of_surjective_apply
    {L : Language.{u}}
    {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V W
      (firstOrderNativeGraphStructure A)
      (firstOrderNativeGraphStructure B))
    (he : Function.Surjective e)
    (v : V) :
    firstOrderNativeGraphEmbedding_toFull_of_surjective e he v = e v := by
  rfl

end AllThoseRamseyClasses.Lifts
