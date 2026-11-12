import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderNativeDecodeEquiv
import AllThoseRamseyClasses.Lifts.GlobalFraisseSurjectiveGraphFullBridge
import AllThoseRamseyClasses.Lifts.GlobalSurjectiveFullEmbeddingInverse

/-!
# Track F: bijective first-order graph self-embeddings yield FULL native automorphisms

Let h be a genuine first-order model of the complete
relationalized graph language of a set-valued native
functional signature, and let N be its decoded native model.

A first-order self-embedding e:h↪h is not immediately a
FULL native structural embedding: the first-order instances
on the quotient and its decoded native graph need not be
definitionally the same. The verified identity-vertex
FIRST-ORDER EQUIVALENCE between them resolves this mismatch.

Conjugating e by that genuine model equivalence gives a
first-order embedding of the exact complete graph of N
into itself. If e is SURJECTIVE, so is this conjugate.
The already verified surjective graph-to-FULL theorem
then produces a genuinely FULL set-valued-functional
embedding N↪N on the SAME underlying vertex map.

The existing verified inverse-of-surjective-FULL-embedding
library provides its FULL inverse. All old/new relations,
negative/positive function graph incidences, nullary
symbols, undefined and multi-valued complete fibres are
preserved and reflected.

This is UNCONDITIONAL algebraic model-theoretic semantics.
It does not assume the original finite Fraïssé input,
unrestricted shadow avoidance, Claim 2 or homogeneity.
The numbered 2019 manuscript is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

/-- Conjugate a first-order self-embedding of an original
complete function-graph model by the identity-on-vertices
first-order equivalence with its decoded native graph. The
result is a genuine embedding between the same native
complete function-graph models. -/
def firstOrderNativeGraphDecode_transport_selfEmbedding
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V h h) :
    @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V
      (firstOrderNativeGraphStructure (firstOrderNativeGraphDecode h))
      (firstOrderNativeGraphStructure (firstOrderNativeGraphDecode h)) :=
  (((firstOrderNativeGraphDecode_id_equiv h).symm.toEmbedding).comp e).comp
    (firstOrderNativeGraphDecode_id_equiv h).toEmbedding

/-- The complete native-graph self-embedding has precisely
the underlying vertex function of the original e:h↪h,
because BOTH comparison maps are the literal identity. -/
theorem firstOrderNativeGraphDecode_transport_selfEmbedding_apply
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V h h)
    (x : V) :
    firstOrderNativeGraphDecode_transport_selfEmbedding h e x = e x := by
  simp only [firstOrderNativeGraphDecode_transport_selfEmbedding,
    FirstOrder.Language.Embedding.comp_apply,
    firstOrderNativeGraphDecode_id_equiv_apply,
    firstOrderNativeGraphDecode_id_equiv_symm_apply]

/-- Surjectivity of the original quotient first-order
embedding transfers to its exact native graph encoding. -/
theorem firstOrderNativeGraphDecode_transport_selfEmbedding_surjective
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V h h)
    (he : Function.Surjective e) :
    Function.Surjective
      (firstOrderNativeGraphDecode_transport_selfEmbedding h e) := by
  intro y
  obtain ⟨x, hx⟩ := he y
  refine ⟨x, ?_⟩
  rw [firstOrderNativeGraphDecode_transport_selfEmbedding_apply]
  exact hx

/-- Every SURJECTIVE first-order self-embedding of the
original complete graph model yields a genuinely FULL
native set-valued-functional embedding of its decoded
native structure, with no added closure hypothesis. -/
def firstOrderNativeGraphDecode_surjectiveSelf_toFull
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V h h)
    (he : Function.Surjective e) :
    Structure.Embedding (firstOrderNativeGraphDecode h)
      (firstOrderNativeGraphDecode h) :=
  firstOrderNativeGraphEmbedding_toFull_of_surjective
    (firstOrderNativeGraphDecode_transport_selfEmbedding h e)
    (firstOrderNativeGraphDecode_transport_selfEmbedding_surjective
      h e he)

/-- The FULL reconstructed native map is literally the
original first-order self-embedding on vertices. -/
theorem firstOrderNativeGraphDecode_surjectiveSelf_toFull_apply
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V h h)
    (he : Function.Surjective e)
    (x : V) :
    firstOrderNativeGraphDecode_surjectiveSelf_toFull h e he x = e x := by
  change firstOrderNativeGraphDecode_transport_selfEmbedding h e x = e x
  exact firstOrderNativeGraphDecode_transport_selfEmbedding_apply h e x

/-- The native FULL map is surjective: its vertex function
is exactly the original surjective first-order map. -/
theorem firstOrderNativeGraphDecode_surjectiveSelf_toFull_surjective
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V h h)
    (he : Function.Surjective e) :
    Function.Surjective
      (firstOrderNativeGraphDecode_surjectiveSelf_toFull h e he) := by
  intro y
  obtain ⟨x, hx⟩ := he y
  refine ⟨x, ?_⟩
  rw [firstOrderNativeGraphDecode_surjectiveSelf_toFull_apply]
  exact hx

/-- An actual FULL inverse of the bijective native
self-embedding, using the already verified inverse-FULL
bridge rather than a merely set-theoretic inverse. -/
noncomputable def firstOrderNativeGraphDecode_surjectiveSelf_fullInverse
    {L : Language.{u}} {V : Type v}
    (h : (firstOrderRelGraphLanguage L.graph).Structure V)
    (e : @FirstOrder.Language.Embedding
      (firstOrderRelGraphLanguage L.graph) V V h h)
    (he : Function.Surjective e) :
    Structure.Embedding (firstOrderNativeGraphDecode h)
      (firstOrderNativeGraphDecode h) :=
  fullEmbeddingInverseOfSurjective
    (firstOrderNativeGraphDecode_surjectiveSelf_toFull h e he)
    (firstOrderNativeGraphDecode_surjectiveSelf_toFull_surjective h e he)

end AllThoseRamseyClasses.Lifts
