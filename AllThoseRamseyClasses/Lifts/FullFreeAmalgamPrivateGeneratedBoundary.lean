import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateBoundary
import AllThoseRamseyClasses.Lifts.FullEmbeddingGeneratedClosure

/-!
# Exact generated functional boundaries of unchanged private components

The contextual Claim 2 flip replaces one side of a literal full
functional free amalgam while preserving the complete other side.

Previously verified:
* a private subset C of Right has EXACTLY the same external
  Gaifman neighborhood after full embedding into Whole (#662);
* generated function closure commutes EXACTLY with every
  FULL functional embedding (#661).

Combining these shows that the WHOLE generated boundary of C
in Whole is the image of its entire genuine boundary in Right.
This includes all function-value fibres, arbitrary arities and
nullary operations, not just immediate graph neighbors.

For two different FULL left-hand replacements over the SAME right
side, both generated boundaries are thus transported from a
single unchanged right-side source set. Even if weak maps from
forbidden structures to another target are noninjective, the
actual SOURCE boundaries in the two free amalgams coincide
coordinatewise via their FULL right embeddings.

This establishes exact exterior generated-boundary preservation.
It does NOT claim the transported outer closed context is
connected, its separator root minimal, or its all-test
Myhill--Nerode incompatibility profile unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L W}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- The native generated boundary of a set of right-private source
vertices is EXACTLY the full right embedding's image of its
unchanged native generated boundary. -/
theorem fullFreeAmalgam_private_generatedBoundary_eq_image
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR C : Set F)
    (hRootR : ∀ r : H, sR r ∈ SR)
    (hPrivate : C ⊆ {b : F | b ∉ SR}) :
    Whole.functionClosure
      (gaifmanNeighborhood Whole.graph (iR '' C)) =
    iR '' (Right.functionClosure
      (gaifmanNeighborhood Right.graph C)) := by
  apply functionalEmbedding_generatedBoundary_image
    Right Whole iR C
  exact fullFreeAmalgam_rightPrivate_neighborhood_eq_image
    hFree SR C hRootR hPrivate

/-- Every COMPLETE component after deleting a root-containing
right subset is private, hence enjoys exact generated boundary
transport. This supplies a directly usable component theorem. -/
theorem fullFreeAmalgam_private_component_generatedBoundary_eq_image
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR : Set F) (hRootR : ∀ r : H, sR r ∈ SR)
    (x : {b : F // b ∉ SR}) :
    Whole.functionClosure
      (gaifmanNeighborhood Whole.graph
        (iR '' componentFrom Right.graph SR x)) =
    iR '' (Right.functionClosure
      (gaifmanNeighborhood Right.graph
        (componentFrom Right.graph SR x))) := by
  apply fullFreeAmalgam_private_generatedBoundary_eq_image
    hFree SR (componentFrom Right.graph SR x) hRootR
  intro b hb
  exact hb.1

/-- The generated boundaries of one retained right-private
component in TWO literal free amalgams with the SAME full right
source are transported from exactly the SAME unchanged set.

The new and old carriers and left-hand replacement pieces may
differ. This is an equality of native SOURCE boundaries, never
of images of an arbitrary weak forbidden map into a target. -/
theorem fullFreeAmalgam_replacement_privateBoundary_pair
    {H E₁ E₂ F W₁ W₂ : Type v}
    {Root : Structure L H}
    {OldLeft : Structure L E₁}
    {NewLeft : Structure L E₂}
    {Right : Structure L F}
    {OldWhole : Structure L W₁}
    {NewWhole : Structure L W₂}
    {sOldL : Structure.Embedding Root OldLeft}
    {sNewL : Structure.Embedding Root NewLeft}
    {sR : Structure.Embedding Root Right}
    {iOldL : Structure.Embedding OldLeft OldWhole}
    {iOldR : Structure.Embedding Right OldWhole}
    {iNewL : Structure.Embedding NewLeft NewWhole}
    {iNewR : Structure.Embedding Right NewWhole}
    (hOld : Structure.IsFreeAmalgam sOldL sR iOldL iOldR)
    (hNew : Structure.IsFreeAmalgam sNewL sR iNewL iNewR)
    (SR : Set F) (hRootR : ∀ r : H, sR r ∈ SR)
    (x : {b : F // b ∉ SR}) :
    let T := Right.functionClosure
      (gaifmanNeighborhood Right.graph
        (componentFrom Right.graph SR x))
    (OldWhole.functionClosure
       (gaifmanNeighborhood OldWhole.graph
         (iOldR '' componentFrom Right.graph SR x)) = iOldR '' T) ∧
    (NewWhole.functionClosure
       (gaifmanNeighborhood NewWhole.graph
         (iNewR '' componentFrom Right.graph SR x)) = iNewR '' T) := by
  exact ⟨
    fullFreeAmalgam_private_component_generatedBoundary_eq_image
      hOld SR hRootR x,
    fullFreeAmalgam_private_component_generatedBoundary_eq_image
      hNew SR hRootR x⟩

end AllThoseRamseyClasses.Lifts
