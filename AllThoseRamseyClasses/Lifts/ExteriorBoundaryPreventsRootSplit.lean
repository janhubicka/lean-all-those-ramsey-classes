import AllThoseRamseyClasses.Lifts.GeneralOldRootSplitObstruction
import AllThoseRamseyClasses.Lifts.ClosedBoundaryUnion

/-!
# Exterior boundary prevents splitting the old root across new components

The original Section 3 Claim 2 chooses an OLD minimal
function-closed separator R with its genuine component C.
The opposite OLD component D, selected by the second
distinguished vertex, has complete generated boundary R:
  R = Cl(N(D)).
This is the verified forward half of Proposition prop:sep.

Let U be the root of a SECOND genuine geometric source piece
Q, with U contained in the ENTIRE old piece R ∪ C.
Since D is disjoint from R ∪ C, the whole connected component
D is disjoint from U. Every old D-path therefore survives
deleting U, so D lies in one connected component D_U of
Source minus U.

Now every Gaifman neighbour of D either belongs to U or to
D_U. The union U ∪ D_U is function-closed (verified cut lemma),
so the entire generated boundary R=Cl(N(D)) also lies in
U ∪ D_U. Thus ALL old root vertices surviving U lie in
ONE new component. If Q.left captures one of them, it captures
every surviving old root vertex. In particular Q.right
CANNOT capture a different old root point.

The resulting conditional lemma rules out the split-old-root obstruction
identified in #665 WHEN the new separator lies in the old
geometric piece, without ANY singleton, clique, injectivity
or external-target quotient restriction.

This is a source-only lemma. The remaining Claim 2 steps
include construction of the appropriate new auxiliary
separator entirely inside the old piece in all cases,
the proper B-only flip, contextual profile congruence and
possible root-image collisions of an EHN target map.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- If an entire OLD Gaifman component D is disjoint from
a new vertex cut U, then D lies in the new U-component
containing its old distinguished root. Every original
D-path can be transported edge-by-edge through the new
cut, even though U need not be a subset of the OLD cut. -/
theorem gaifmanComponent_subset_after_disjointCut
    (A : RelStructure L.graph V)
    (R U : Set V)
    (d : {z : V // z ∉ R})
    (hDisjoint : Disjoint (componentFrom A R d) U) :
    let dU : {z : V // z ∉ U} :=
      ⟨d.1, (Set.disjoint_left.mp hDisjoint)
        (componentFrom_root A R d)⟩
    componentFrom A R d ⊆ componentFrom A U dU := by
  let D : Set V := componentFrom A R d
  have hAvoid : ∀ z : V, z ∈ D → z ∉ U := by
    intro z hz
    exact (Set.disjoint_left.mp hDisjoint) hz
  let dU : {z : V // z ∉ U} :=
    ⟨d.1, hAvoid d.1 (componentFrom_root A R d)⟩
  have hLift :
      ∀ (b : {z : V // z ∉ R}),
        ReachOutside A R d b →
          ∃ hb : b.1 ∉ U,
            ReachOutside A U dU ⟨b.1, hb⟩ := by
    intro b hp
    induction hp with
    | refl =>
        exact ⟨dU.2, Relation.ReflTransGen.refl⟩
    | @tail a b hpath hedge ih =>
        obtain ⟨haU, hpU⟩ := ih
        have hbD : b.1 ∈ D :=
          ⟨b.2, hpath.tail hedge⟩
        have hbU : b.1 ∉ U := hAvoid b.1 hbD
        refine ⟨hbU, ?_⟩
        exact hpU.tail hedge
  intro z hz
  obtain ⟨hzU, hpU⟩ := hLift ⟨z, hz.1⟩ hz.2
  exact ⟨hzU, hpU⟩

/-- Any connected source subset D contained in one component
outside a function-closed cut U has its ENTIRE generated
Gaifman-neighbourhood closure inside U together with that
one component. Generated root vertices need not be immediate
neighbours of D; this is why function-closedness matters. -/
theorem generatedBoundary_subset_cut_union_component
    (Source : Structure L V)
    (U D : Set V) (hUclosed : Source.IsClosed U)
    (d : {z : V // z ∉ U})
    (hD : D ⊆ componentFrom Source.graph U d) :
    Source.functionClosure (gaifmanNeighborhood Source.graph D) ⊆
      U ∪ componentFrom Source.graph U d := by
  let C : Set V := componentFrom Source.graph U d
  have hSeed : gaifmanNeighborhood Source.graph D ⊆ U ∪ C := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · obtain ⟨_, y, hyD, hyz⟩ := hz
      exact Or.inr
        (componentFrom_step Source.graph U d
          (hD hyD) hzU hyz)
  have hClosed : Source.IsClosed (U ∪ C) :=
    functionalComponentUnion_isClosed Source U hUclosed d
  intro z hz
  exact hz (U ∪ C) hClosed hSeed

/-- **No split of old separator roots** when the NEW root U is
contained in the OLD genuine piece P and the new left component
contains at least one OLD root vertex.

The proof uses the OPPOSITE old component D, whose COMPLETE
generated external boundary equals the old separating root R.
D avoids the new root and stays connected, so all surviving
old root vertices lie in one Q-component. The conclusion
permits old root vertices to lie in U itself; it does not
assume the two roots are disjoint or graph-irreducible. -/
theorem geometricOldRoot_survivors_capturedLeft_of_innerRoot
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices Source P)
    (hCaptured : ∃ r : V,
      r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left) :
    Set.range P.roots ⊆
      Set.range Q.roots ∪
        functionalComponentFrom Source
          (Set.range Q.roots) Q.left := by
  let R : Set V := Set.range P.roots
  let C : Set V := componentFrom Source.graph R P.left
  let D : Set V := componentFrom Source.graph R P.right
  let U : Set V := Set.range Q.roots
  have hDR : Disjoint D R :=
    componentFrom_disjoint_cut Source.graph R P.right
  have hDC : Disjoint D C :=
    (geometricPiece_components_disjoint Source P).symm
  have hDU : Disjoint D U := by
    apply Set.disjoint_left.mpr
    intro z hzD hzU
    rcases hQrootInsideP hzU with hzR | hzC
    · exact (Set.disjoint_left.mp hDR) hzD hzR
    · exact (Set.disjoint_left.mp hDC) hzD hzC
  let dU : {z : V // z ∉ U} :=
    ⟨P.right.1, (Set.disjoint_left.mp hDU)
      (componentFrom_root Source.graph R P.right)⟩
  have hDsub : D ⊆ componentFrom Source.graph U dU :=
    gaifmanComponent_subset_after_disjointCut
      Source.graph R U P.right hDU
  have hUclosed : Source.IsClosed U := Q.minimal.1
  have hRootSubset :
      R ⊆ U ∪ componentFrom Source.graph U dU := by
    rw [← geometricPiece_right_boundary_closure Source P]
    exact generatedBoundary_subset_cut_union_component
      Source U D hUclosed dU hDsub
  obtain ⟨r, hrOld, hrLeft⟩ := hCaptured
  have hrD : r ∈ componentFrom Source.graph U dU :=
    (hRootSubset hrOld).resolve_left hrLeft.1
  have hLeftToD : ReachOutside Source.graph U Q.left dU := by
    have hDR : ReachOutside Source.graph U
        dU ⟨r, hrD.1⟩ := hrD.2
    have hRD : ReachOutside Source.graph U
        ⟨r, hrLeft.1⟩ dU :=
      reachOutside_symm Source.graph U hDR
    exact hrLeft.2.trans hRD
  intro z hzOld
  rcases hRootSubset hzOld with hzU | hzD
  · exact Or.inl hzU
  · exact Or.inr ⟨hzD.1, hLeftToD.trans hzD.2⟩

/-- With the same geometric INSIDE-root hypothesis, the
opposite Q component can NEVER contain an old P-root vertex
once Q.left captures one such vertex. This rules out the
two-root split of #665 under a natural piece-local condition. -/
theorem geometricOldRoot_noOppositeCapture_of_innerRoot
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices Source P)
    (hCaptured : ∃ r : V,
      r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left) :
    Disjoint (Set.range P.roots)
      (functionalComponentFrom Source
        (Set.range Q.roots) Q.right) := by
  have hOldRoot :=
    geometricOldRoot_survivors_capturedLeft_of_innerRoot
      Source P Q hQrootInsideP hCaptured
  apply Set.disjoint_left.mpr
  intro z hzOld hzRight
  rcases hOldRoot hzOld with hzU | hzLeft
  · exact hzRight.1 hzU
  · exact (Set.disjoint_left.mp
      (geometricPiece_components_disjoint Source Q))
      hzLeft hzRight

/-- This is the actual source locality step needed for
arbitrary-width Claim 2: once the new auxiliary separator
lies wholly inside the old genuine piece and its left
component captures one old root point, its opposite
component cannot ESCAPE the old selected nonroot component.

No root-width, old-root clique, full target-root injection,
forbidden family or image quotient assumption is needed. -/
theorem geometricPiece_opposite_localized_of_innerCutRootCapture
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices Source P)
    (hCaptured : ∃ r : V,
      r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left) :
    functionalComponentFrom Source
      (Set.range Q.roots) Q.right ⊆
    functionalComponentFrom Source
      (Set.range P.roots) P.left := by
  have hNoRootRight :
      Disjoint (Set.range P.roots)
        (functionalComponentFrom Source
          (Set.range Q.roots) Q.right) :=
    geometricOldRoot_noOppositeCapture_of_innerRoot
      Source P Q hQrootInsideP hCaptured
  let Qswap : GeometricFunctionalPieceData Source m := {
    roots := Q.roots
    roots_injective := Q.roots_injective
    left := Q.right
    right := Q.left
    minimal := minimalClosedSeparator_swap
      Source (Set.range Q.roots) Q.left Q.right Q.minimal
  }
  by_contra hEscape
  obtain ⟨r, hrOld, hrQRight⟩ :=
    geometricPiece_escapingComponent_capturesOldRoot
      Source P Qswap hQrightOld hEscape
  exact (Set.disjoint_left.mp hNoRootRight)
    hrOld hrQRight

end AllThoseRamseyClasses.Lifts
