import AllThoseRamseyClasses.Lifts.PrivateInternalGeneratedBoundaryReflection
import AllThoseRamseyClasses.Lifts.GeometricRetainedInteriorPath
import AllThoseRamseyClasses.Lifts.FullFunctionalFreeAmalgamSwap

/-!
# A genuine selected geometric forbidden piece has an internal full-root boundary

A genuine geometric piece in a finite forbidden source A is the
complete closed separating cut U together with ONE connected
Gaifman component D of A outside U. The original geometric
minimal-separator proposition proves Cl_A(N_A(D)) = U in A.

The actual full native source free diagram (over the entire Fin n
root) identifies A as the free amalgam of that selected piece and
the closed complement. The verified exact private-root component
theorem and internal-boundary reflection transport the original
whole-source equation BACK into the induced selected piece.

Thus an actual selected geometric rooted extension has a vertex
outside the whole ordered root whose component's entire
function-generated external boundary is precisely that root.
No equation about the internal boundary is assumed.

This is the missing source-side prerequisite for transporting the
same selected replacement Q through a rooted full isomorphism
and constructing its private component in the literal flipped
forbidden source. No forbidden target-map injectivity is involved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type} {n : ℕ}

/-- Every ACTUAL geometric piece, in its full native Fin n root chart,
has a genuinely connected inner-private component with generated
neighbourhood boundary equal to the COMPLETE ordered root.

The internal conclusion is derived from the already proved
whole-source minimal-separator equation and exact full-amalgam
component equality, not assumed. -/
theorem geometricGlobalSelectedPiece_internalBoundary_eq_root
    (A : Structure L V)
    (d : GeometricFunctionalPieceData A n) :
    let P := geometricGlobalFunctionalChart A d
    ∃ x : {e : P.ext.Carrier // e ∉ Set.range P.ext.rootEmbedding},
      P.ext.str.functionClosure
        (gaifmanNeighborhood P.ext.str.graph
          (componentFrom P.ext.str.graph
            (Set.range P.ext.rootEmbedding) x)) =
      Set.range P.ext.rootEmbedding := by
  let P := geometricGlobalFunctionalChart A d
  let T := geometricGlobalComplementChart A d
  let iP : Structure.Embedding P.ext.str A :=
    functionalComponentEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let iT : Structure.Embedding T.str A :=
    functionalComponentComplementEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let p : P.ext.Carrier :=
    ⟨d.left.1, Or.inr
      (componentFrom_root A.graph (Set.range d.roots) d.left)⟩
  have hpNot : p ∉ Set.range P.ext.rootEmbedding := by
    rintro ⟨i, hi⟩
    have hCoord : d.roots i = d.left.1 :=
      congrArg (fun z : P.ext.Carrier => z.1) hi
    exact d.left.2 ⟨i, hCoord⟩
  let x : {e : P.ext.Carrier // e ∉ Set.range P.ext.rootEmbedding} :=
    ⟨p, hpNot⟩
  have hRootImage :
      iP '' Set.range P.ext.rootEmbedding = Set.range d.roots := by
    ext z
    constructor
    · rintro ⟨e, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨P.ext.rootEmbedding i, ⟨i, rfl⟩, rfl⟩
  let xWhole :=
    fullFunctionalEmbedding_outsideCut iP
      (Set.range P.ext.rootEmbedding) x
  have hOldC :
      componentFrom A.graph (iP '' Set.range P.ext.rootEmbedding)
        xWhole =
      componentFrom A.graph (Set.range d.roots) d.left :=
    sourceGaifmanComponent_eq_of_cut_eq
      A hRootImage xWhole d.left rfl
  have hWholeBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph
            (iP '' Set.range P.ext.rootEmbedding) xWhole)) =
      iP '' Set.range P.ext.rootEmbedding := by
    rw [hOldC, hRootImage]
    exact geometricPiece_left_boundary_closure A d
  have hFree :
      Structure.IsFreeAmalgam
        P.ext.rootEmbedding T.rootEmbedding iP iT :=
    geometricGlobalSource_freeDiagram A d
  have hSwapped :
      Structure.IsFreeAmalgam
        T.rootEmbedding P.ext.rootEmbedding iT iP :=
    fullFunctionalFreeAmalgam_swap hFree
  refine ⟨x, ?_⟩
  exact fullFreeAmalgam_privateInternalBoundary_of_wholeBoundary
    hSwapped x hWholeBoundary

end AllThoseRamseyClasses.Lifts
