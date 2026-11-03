import AllThoseRamseyClasses.Lifts.PrivateInternalGeneratedBoundaryReflection
import AllThoseRamseyClasses.Lifts.GeometricRetainedInteriorPath

/-!
# The unchanged complement of a selected geometric source has its own full root boundary

Let A have one genuine geometric minimal-separator piece d over
the complete closed functional root U, with distinguished
components D_left and D_right after deleting U. The original
source is a FULL native functional free amalgam of U ∪ D_left
and its unchanged closed complement.

The second original minimal-separator boundary equation states
Cl_A(N_A(D_right)) = U. The right distinguished vertex belongs
to the complete complement carrier, and it is private to the
full gluing root. The exact private-root component theorem (#794)
then identifies D_right as the FULL image of its original
complement-internal component, without using any boundary
premise. Reflection of generated neighbourhood closures (#797)
therefore gives the complete INTERNAL complement root boundary.

This is the second independent source-side input of the two-private-
boundary geometric reconstruction (#786) for the actual literal
canonical replacement. It does not assume anything about the new
replacement Q, its rooted profile, or a weak forbidden target map.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type} {n : ℕ}

/-- The unchanged complete complement of EVERY original genuine
geometric source piece has a private component whose entire
NATIVE function-generated external boundary is exactly its
complete induced Fin n root. No extra boundary hypothesis
is made on the complement. -/
theorem geometricGlobalComplement_internalBoundary_eq_root
    (A : Structure L V)
    (d : GeometricFunctionalPieceData A n) :
    let C := geometricGlobalComplementChart A d
    ∃ x : {b : C.Carrier // b ∉ Set.range C.rootEmbedding},
      C.str.functionClosure
        (gaifmanNeighborhood C.str.graph
          (componentFrom C.str.graph
            (Set.range C.rootEmbedding) x)) =
      Set.range C.rootEmbedding := by
  let C := geometricGlobalComplementChart A d
  let P := geometricGlobalFunctionalChart A d
  let iC : Structure.Embedding C.str A :=
    functionalComponentComplementEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let iP : Structure.Embedding P.ext.str A :=
    functionalComponentEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  have hrNotLeft :
      d.right.1 ∉ componentFrom A.graph (Set.range d.roots) d.left := by
    intro hInLeft
    have hInRight :
        d.right.1 ∈ componentFrom A.graph (Set.range d.roots) d.right :=
      componentFrom_root A.graph (Set.range d.roots) d.right
    exact (Set.disjoint_left.mp
      (geometricPiece_components_disjoint A d)) hInLeft hInRight
  let q : C.Carrier := ⟨d.right.1, hrNotLeft⟩
  have hqNot : q ∉ Set.range C.rootEmbedding := by
    rintro ⟨i, hi⟩
    have hCoord : d.roots i = d.right.1 :=
      congrArg (fun z : C.Carrier => z.1) hi
    exact d.right.2 ⟨i, hCoord⟩
  let x : {b : C.Carrier // b ∉ Set.range C.rootEmbedding} :=
    ⟨q, hqNot⟩
  have hRootImage :
      iC '' Set.range C.rootEmbedding = Set.range d.roots :=
    geometricGlobalSource_innerRoot_range_eq A d
  let xWhole :=
    fullFunctionalEmbedding_outsideCut iC
      (Set.range C.rootEmbedding) x
  have hOldC :
      componentFrom A.graph (iC '' Set.range C.rootEmbedding)
        xWhole =
      componentFrom A.graph (Set.range d.roots) d.right :=
    sourceGaifmanComponent_eq_of_cut_eq
      A hRootImage xWhole d.right rfl
  have hWholeBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph
            (iC '' Set.range C.rootEmbedding) xWhole)) =
      iC '' Set.range C.rootEmbedding := by
    rw [hOldC, hRootImage]
    exact geometricPiece_right_boundary_closure A d
  have hFree :
      Structure.IsFreeAmalgam
        P.ext.rootEmbedding C.rootEmbedding iP iC :=
    geometricGlobalSource_freeDiagram A d
  refine ⟨x, ?_⟩
  exact fullFreeAmalgam_privateInternalBoundary_of_wholeBoundary
    hFree x hWholeBoundary

end AllThoseRamseyClasses.Lifts
