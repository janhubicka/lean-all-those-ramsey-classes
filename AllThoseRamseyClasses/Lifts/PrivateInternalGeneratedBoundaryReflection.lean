import AllThoseRamseyClasses.Lifts.PrivateRootComponentExact
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGeneratedBoundary

/-!
# Reflect the entire generated boundary of a private component into its own side

Let Whole = Left +_Root Right be an ACTUAL FULL native functional
free amalgam. A selected vertex x private to Right has one component
C in Right after deleting the entire common root U. The verified
private-component theorem (#794) identifies its image EXACTLY with
the corresponding whole-source component, without a boundary
assumption. The verified private generated-boundary theorem then
transports the ENTIRE native function-generated neighbourhood of C.

Consequently, if the whole-source component has complete boundary
iRight(U), its right-side internal component already has boundary U.
This implication is proved by injectivity of the FULL right embedding,
and is NOT a circular appeal to the desired internal boundary.

The result works for original relations and all native set-valued
partial functions, including nullary operations and higher-arity
incidence tuples. Neither forbidden-image injectivity nor root
comparability is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A complete generated boundary equality in the WHOLE source
reflects to the component's own full native right side, provided
the cut is the exact complete common root of a free amalgam.

The internal boundary is the conclusion, not an assumption.
The external boundary is about a genuine whole-source component
whose equality to the image of the right component is derived
from full-amalgam geometry, with no hypotheses on its boundary. -/
theorem fullFreeAmalgam_privateInternalBoundary_of_wholeBoundary
    {H E B W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L B}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (x : {b : B // b ∉ Set.range sR})
    (hWholeBoundary :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph (iR '' Set.range sR)
            (fullFunctionalEmbedding_outsideCut iR
              (Set.range sR) x))) =
        iR '' Set.range sR) :
    Right.functionClosure
      (gaifmanNeighborhood Right.graph
        (componentFrom Right.graph (Set.range sR) x)) =
      Set.range sR := by
  let C : Set B :=
    componentFrom Right.graph (Set.range sR) x
  have hExactComponent :=
    fullFreeAmalgam_rightPrivateRoot_component_eq hFree x
  have hFullBoundary :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph (iR '' C)) =
      iR '' (Right.functionClosure
        (gaifmanNeighborhood Right.graph C)) :=
    fullFreeAmalgam_private_component_generatedBoundary_eq_image
      hFree (Set.range sR)
      (fun r => ⟨r, rfl⟩) x
  have hImageEq :
      iR '' (Right.functionClosure
        (gaifmanNeighborhood Right.graph C)) =
      iR '' Set.range sR := by
    rw [hExactComponent] at hWholeBoundary
    exact hFullBoundary.symm.trans hWholeBoundary
  apply Set.Subset.antisymm
  · intro z hz
    have hzImage :
        iR z ∈ iR '' (Right.functionClosure
          (gaifmanNeighborhood Right.graph C)) :=
      ⟨z, hz, rfl⟩
    rw [hImageEq] at hzImage
    obtain ⟨r, hr, hEq⟩ := hzImage
    have hRZ : r = z := iR.injective hEq
    exact hRZ ▸ hr
  · intro z hz
    have hzImage : iR z ∈ iR '' Set.range sR :=
      ⟨z, hz, rfl⟩
    rw [← hImageEq] at hzImage
    obtain ⟨r, hr, hEq⟩ := hzImage
    have hRZ : r = z := iR.injective hEq
    exact hRZ ▸ hr

end AllThoseRamseyClasses.Lifts
