import AllThoseRamseyClasses.Lifts.FullComplementClosedOuterRoot

/-!
# Exact functoriality of generated native functional closure

A FULL embedding of genuine set-valued functional structures
preserves whole function-value fibres, not just positive
homomorphism incidences. Consequently it transports the full
generated function closure EXACTLY:

  Cl_B(e[S]) = e[Cl_A(S)].

Both inclusions are essential. The forward direction uses
closedness of the image of Cl_A(S); the reverse uses the full
embedding's closed-preimage property. The proof works also for
nullary functions, whose values may belong to every closed set.

This is the correct functional bridge for transporting generated
component boundaries after a contextual Claim 2 source flip.
Graph-neighbourhood preservation is a SEPARATE condition:
full embeddings alone do not reflect a Gaifman edge witnessed
by a tuple with other vertices outside their image. The exterior
free-amalgam geometry must supply that condition independently.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}}

/-- A full native functional embedding commutes EXACTLY with
generated function closure of EVERY vertex subset. No language
arity restriction, finiteness, or target-map injectivity needed. -/
theorem functionalEmbedding_functionClosure_image
    {V : Type v} {W : Type w}
    (A : Structure L V) (B : Structure L W)
    (e : Structure.Embedding A B) (S : Set V) :
    B.functionClosure (e '' S) =
      e '' (A.functionClosure S) := by
  apply Set.Subset.antisymm
  · have hClosed : B.IsClosed (e '' (A.functionClosure S)) :=
      functionalEmbedding_image_closed A B e
        (A.functionClosure S) (A.functionClosure_isClosed S)
    have hSeed : e '' S ⊆ e '' (A.functionClosure S) := by
      rintro z ⟨a, ha, rfl⟩
      exact ⟨a, A.subset_functionClosure S ha, rfl⟩
    intro z hz
    exact hz (e '' (A.functionClosure S)) hClosed hSeed
  · rintro z ⟨a, ha, rfl⟩
    let U : Set W := B.functionClosure (e '' S)
    have hUClosed : B.IsClosed U :=
      B.functionClosure_isClosed (e '' S)
    have hPullback : A.IsClosed (e ⁻¹' U) :=
      functionalEmbedding_preimage_closed A B e U hUClosed
    have hSeed : S ⊆ e ⁻¹' U := by
      intro x hx
      exact B.subset_functionClosure (e '' S) ⟨x, hx, rfl⟩
    exact ha (e ⁻¹' U) hPullback hSeed

/-- A vertex belongs to the generated closure of an embedded
source set iff it is the actual image of a vertex in the
source generated closure. In particular the ambient closure
cannot create NEW vertices outside the closed embedding range. -/
theorem functionalEmbedding_mem_functionClosure_image_iff
    {V : Type v} {W : Type w}
    (A : Structure L V) (B : Structure L W)
    (e : Structure.Embedding A B) (S : Set V) (y : W) :
    y ∈ B.functionClosure (e '' S) ↔
      ∃ x : V, x ∈ A.functionClosure S ∧ e x = y := by
  rw [functionalEmbedding_functionClosure_image A B e S]
  rfl

/-- Generated external boundary closures are transported exactly
once the FULL source side also reflects the relevant complete
Gaifman neighbourhood. This hypothesis is intentionally explicit:
it does not hold for arbitrary induced relational embeddings, but
the private-side free-amalgam locality lemma supplies it. -/
theorem functionalEmbedding_generatedBoundary_image
    {V : Type v} {W : Type w}
    (A : Structure L V) (B : Structure L W)
    (e : Structure.Embedding A B) (C : Set V)
    (hNeighbour :
      gaifmanNeighborhood B.graph (e '' C) =
        e '' gaifmanNeighborhood A.graph C) :
    B.functionClosure
      (gaifmanNeighborhood B.graph (e '' C)) =
      e '' (A.functionClosure (gaifmanNeighborhood A.graph C)) := by
  rw [hNeighbour]
  exact functionalEmbedding_functionClosure_image A B e
    (gaifmanNeighborhood A.graph C)

end AllThoseRamseyClasses.Lifts
