import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderGraph
import PartiteConstruction.Structure.Relationalize
import Mathlib.ModelTheory.Basic

/-!
# Track F: exact first-order relational embeddings and native FULL closures

The first-order graph encoding preserves every relation tuple and
each complete value set of an original set-valued partial function
by a pure relation of arity one higher.

This module bridges the EMBEDDING semantics, which is essential
before using Mathlib's first-order direct-limit library:

* Any native FULL embedding induces an ordinary first-order
  embedding of the complete relationalized graphs.
* Conversely, a first-order relational graph embedding
  reconstructs a native functional graph embedding.
* It reconstructs a FULL native functional embedding ONLY with
  the original function-value closure condition: every target
  output over an image input tuple must come from a source output.

This is precisely the condition that ordinary first-order
relational embeddings do not enforce automatically. We do not
claim that the standard first-order age of arbitrary induced
subsets is already the desired functional age.

All statements include nullary relations and functions, repeated
arguments, partiality and multi-valued functions. No weak
homomorphism-embedding or finite-stage image quotient occurs.

The numbered 2019 manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u v w

/-- A genuine relational embedding is a first-order embedding
for the exact arity-indexed relational language. No extra
closure hypothesis is needed in the purely relational case. -/
def firstOrderRelGraphEmbedding
    {R : RelLanguage.{u}}
    {V : Type v} {W : Type w}
    {A : RelStructure R V} {B : RelStructure R W}
    (e : RelStructure.Embedding A B) :
    @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage R) V W
      (firstOrderRelGraphStructure A)
      (firstOrderRelGraphStructure B) where
  toFun := e
  inj' := e.injective
  map_fun' := by
    intro n f xs
    exact nomatch f.down
  map_rel' := by
    intro n s xs
    change B.rel s.1
      (e ∘ (fun i => xs (Fin.cast s.2 i))) ↔
      A.rel s.1 (fun i => xs (Fin.cast s.2 i))
    exact e.map_rel_iff s.1
      (fun i => xs (Fin.cast s.2 i))

/-- Recover the genuine relational embedding of the exact
graph language from any first-order relational embedding,
without changing the underlying function on vertices. -/
def firstOrderRelGraphEmbedding_toRel
    {R : RelLanguage.{u}}
    {V : Type v} {W : Type w}
    {A : RelStructure R V} {B : RelStructure R W}
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage R) V W
      (firstOrderRelGraphStructure A)
      (firstOrderRelGraphStructure B)) :
    RelStructure.Embedding A B where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro s xs
    have h := e.map_rel
      (⟨s, rfl⟩ :
        (firstOrderRelGraphLanguage R).Relations (R.arity s)) xs
    change B.rel s (e ∘ xs) ↔ A.rel s xs at h
    exact h

/-- A native FULL set-valued functional embedding induces an
ordinary first-order embedding of its exact complete graph
relationalization. Both old and added relation symbols are
preserved and reflected. -/
def firstOrderNativeGraphEmbedding
    {L : Language.{u}}
    {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : Structure.Embedding A B) :
    @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V W
      (firstOrderNativeGraphStructure A)
      (firstOrderNativeGraphStructure B) :=
  firstOrderRelGraphEmbedding e.graph

/-- A first-order embedding of native function graphs does
not yet imply FULL native embedding. With the exact
complete-fibre closed-map condition, the existing
relationalization theorem reconstructs it genuinely. -/
def firstOrderNativeGraphEmbedding_toFull
    {L : Language.{u}}
    {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V W
      (firstOrderNativeGraphStructure A)
      (firstOrderNativeGraphStructure B))
    (hClosed : A.ClosedMap B e) :
    Structure.Embedding A B :=
  Structure.Embedding.ofGraphClosed
    (firstOrderRelGraphEmbedding_toRel e) hClosed

/-- The image of every genuinely FULL native embedding is
function-value closed. This is why the forward conversion
loses no semantic information about the function fibres. -/
theorem firstOrderNativeGraphEmbedding_closed
    {L : Language.{u}}
    {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : Structure.Embedding A B) :
    A.ClosedMap B (firstOrderNativeGraphEmbedding e) := by
  exact e.isHomomorphism.closedMap

end AllThoseRamseyClasses.Lifts
