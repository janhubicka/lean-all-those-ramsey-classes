import AllThoseRamseyClasses.Lifts.GeometricPieceCutRestriction

/-!
# Track C: an inner shared-root component's complete boundary lies inside the old outer piece

This is a source-geometric invariant that holds WITHOUT requiring
the current forbidden EHN witness to minimize A-exclusive support.

Let P = R ∪ C be any genuine geometric minimal-separator piece
of a native functional source A. If B is ANY subset of the
selected component C, then every external Gaifman neighbour
of B belongs to P. The whole functional closure of that
neighbourhood also belongs to P, since P is genuinely closed
under ALL original partial/set-valued functions.

In particular let S be the closed preimage of the shared target
root, containing R. Any S-component rooted at a vertex of C is
contained in C. Its full generated boundary T=Cl_A(N(B))
therefore lies in S ∩ P, even if R and T are incomparable.
No global A-minimality, mixed-piece minimality, partner existence,
bounded function arity or root-image injectivity enters.

This is a necessary localization for constructing a proper
B-only geometric subpiece inside the transported outer piece.
It DOES NOT prove that T is a minimal separator or has an
opposite boundary partner; the positive-B-rank successor gap
remains open for general-width T.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The entire generated external boundary of ANY subset of the
selected component of an actual geometric piece lies inside
that closed piece. Native full function closure, not graph-only
or immediate-neighbourhood approximation, is used. -/
theorem geometricPiece_subcomponent_generatedBoundary_inside
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (B : Set V)
    (hB : B ⊆ functionalComponentFrom A
      (Set.range P.roots) P.left) :
    A.functionClosure (gaifmanNeighborhood A.graph B) ⊆
      geometricPieceVertices A P := by
  let R : Set V := Set.range P.roots
  let C : Set V := functionalComponentFrom A R P.left
  have hClosed : A.IsClosed (geometricPieceVertices A P) :=
    functionalComponentUnion_isClosed
      A (Set.range P.roots) P.minimal.1 P.left
  have hSeed :
      gaifmanNeighborhood A.graph B ⊆
        geometricPieceVertices A P := by
    intro y hy
    by_cases hyC : y ∈ C
    · exact Or.inr hyC
    · have hyBoundary : y ∈ gaifmanNeighborhood A.graph C := by
        obtain ⟨_hyNotB, b, hb, hEdge⟩ := hy
        exact ⟨hyC, b, hB hb, hEdge⟩
      exact Or.inl
        (gaifmanNeighborhood_component_subset_cut
          A.graph (Set.range P.roots) P.left hyBoundary)
  intro y hy
  exact hy (geometricPieceVertices A P) hClosed hSeed

/-- A component after deleting a LARGER cut S containing the
original geometric root R remains inside the old selected
R-component as long as its selected vertex lies there.

This is a plain path statement, independent of any EHN map. -/
theorem geometricPiece_innerComponent_subset_outerComponent
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hRS : Set.range P.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxOld : x.1 ∈ functionalComponentFrom
      A (Set.range P.roots) P.left) :
    componentFrom A.graph S x ⊆
      functionalComponentFrom A (Set.range P.roots) P.left := by
  have hSmall :=
    componentFrom_subset_of_cut_subset A.graph hRS x
  intro z hz
  have hzOld :=
    hSmall hz
  exact ⟨hzOld.1, hxOld.2.trans hzOld.2⟩

/-- The full native generated boundary T of any S-component
INSIDE an old geometric piece lies in the intersection S ∩ P,
provided S is function-closed and contains the entire old root.

This is exactly the source-side containment required before
attempting a genuine proper B-only replacement. It does not
assume the intermediate source map remains left-support-minimal,
and it does not assert a boundary partner or new geometric
minimality. -/
theorem geometricPiece_innerComponent_generatedBoundary_insideCut
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V) (hSclosed : A.IsClosed S)
    (hRS : Set.range P.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxOld : x.1 ∈ functionalComponentFrom
      A (Set.range P.roots) P.left) :
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
      ⊆ S ∩ geometricPieceVertices A P := by
  have hComponent :=
    geometricPiece_innerComponent_subset_outerComponent
      A P S hRS x hxOld
  have hInsideP :=
    geometricPiece_subcomponent_generatedBoundary_inside
      A P (componentFrom A.graph S x) hComponent
  have hInsideS :=
    functionalClosure_neighborhood_subset_cut A S hSclosed x
  exact fun z hz => ⟨hInsideS hz, hInsideP hz⟩

end AllThoseRamseyClasses.Lifts
