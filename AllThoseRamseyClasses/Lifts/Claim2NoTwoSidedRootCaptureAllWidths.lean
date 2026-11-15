import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.RootRetentionLocalization

/-!
# No two-sided OLD-root capture by a smaller genuine minimal separator

This addresses the remaining higher-width split-root obstruction
in original 2019 Claim 2. Let P and d be GENUINE functional
minimal closed separating cuts of the SAME original source, and
assume the ENTIRE smaller root d.root lies in the old selected
outer piece P.root ∪ component(P.left).

The old OPPOSITE component component(P.right) is disjoint from
the entire old selected piece, hence disjoint from d.root.
It therefore survives inside one component C of the complement
of d.root, the one containing P.right.

The full GENERATED boundary of the OLD opposite component
is EXACTLY the complete old P.root, by the verified minimal
closed-separator boundary theorem. Since d.root is closed and
C is its complete surviving Gaifman component, the union
d.root ∪ C is FULLY CLOSED. Its source Gaifman neighborhood
contains the old opposite-component boundary seed. Therefore
the old FULL root P.root lies in d.root ∪ C.

Consequently EVERY old P-root SOURCE vertex not in d.root
lies in the SAME d-component C. In particular, one old root
cannot be captured in d.left's component while another is
captured in d.right's distinct component.

This uses the exact full functional closure (including arities)
rather than ordinary graph minimal-cut adjacency. No root-width
bound, target-map injectivity, target image quotient, original
A-minimality, or forbidden-family assumption is required.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every old P-root vertex outside the COMPLETE NEW closed cut
d.root can be reached from the OLD OPPOSITE P.right component
without crossing d.root, provided d.root is inside the
old selected root+P.left piece.

The source root in the conclusion is the SAME P.right actual
vertex, with a proof of avoiding d.root. -/
theorem geometric_oldRoot_reachable_from_oldOpposite_after_innerCut
    {V : Type}
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hDRootInOldPiece :
      Set.range d.roots ⊆ geometricPieceVertices Source P) :
    ∃ (hOldRightOutsideNew : P.right.1 ∉ Set.range d.roots),
      ∀ (r : V) (hrOld : r ∈ Set.range P.roots)
        (hrNew : r ∉ Set.range d.roots),
        ReachOutside Source.graph (Set.range d.roots)
          (⟨P.right.1, hOldRightOutsideNew⟩ :
            {v : V // v ∉ Set.range d.roots})
          (⟨r, hrNew⟩ : {v : V // v ∉ Set.range d.roots}) := by
  classical
  let R : Set V := Set.range P.roots
  let S : Set V := Set.range d.roots
  let OldOpposite : Set V :=
    functionalComponentFrom Source R P.right
  have hOldComponentsDisjoint :=
    geometricPiece_components_disjoint Source P
  have hOppositeAvoidS : ∀ z : V, z ∈ OldOpposite → z ∉ S := by
    intro z hzOpp hzS
    have hzOldPiece : z ∈ geometricPieceVertices Source P :=
      hDRootInOldPiece hzS
    rcases hzOldPiece with hzOldRoot | hzOldLeft
    · exact hzOpp.1 hzOldRoot
    · exact (Set.disjoint_left.mp hOldComponentsDisjoint)
        hzOldLeft hzOpp
  have hPrightAvoidS : P.right.1 ∉ S :=
    hOppositeAvoidS P.right.1
      (componentFrom_root Source.graph R P.right)
  let pRightS : {v : V // v ∉ S} :=
    ⟨P.right.1, hPrightAvoidS⟩
  let NewOpposite : Set V :=
    componentFrom Source.graph S pRightS
  have hOldOppositeInsideNew : OldOpposite ⊆ NewOpposite := by
    have hLift :
        ∀ (v : {z : V // z ∉ R}),
          ReachOutside Source.graph R P.right v →
          v.1 ∈ NewOpposite := by
      intro v hPath
      induction hPath with
      | refl =>
          exact componentFrom_root Source.graph S pRightS
      | @tail a b hab hedge ih =>
          have hbOldOpposite : b.1 ∈ OldOpposite :=
            ⟨b.2, hab.tail hedge⟩
          have hbOutsideS : b.1 ∉ S :=
            hOppositeAvoidS b.1 hbOldOpposite
          exact componentFrom_step Source.graph S pRightS
            ih hbOutsideS hedge
    intro v hv
    exact hLift ⟨v, hv.1⟩ hv.2
  have hSclosed : Source.IsClosed S := d.minimal.1
  have hClosed :
      Source.IsClosed (S ∪ NewOpposite) :=
    functionalComponentUnion_isClosed
      Source S hSclosed pRightS
  have hSeed :
      gaifmanNeighborhood Source.graph OldOpposite ⊆
        S ∪ NewOpposite := by
    intro v hv
    obtain ⟨_hvOutsideOpp, z, hzOpp, hEdge⟩ := hv
    by_cases hvS : v ∈ S
    · exact Or.inl hvS
    · exact Or.inr
        (componentFrom_step Source.graph S pRightS
          (hOldOppositeInsideNew hzOpp) hvS hEdge)
  have hOldOppositeBoundary :
      Source.functionClosure
        (gaifmanNeighborhood Source.graph OldOpposite) = R :=
    geometricPiece_right_boundary_closure Source P
  have hOldRootLocalization : R ⊆ S ∪ NewOpposite := by
    intro r hrR
    have hrClosure :
        r ∈ Source.functionClosure
          (gaifmanNeighborhood Source.graph OldOpposite) := by
      rw [hOldOppositeBoundary]
      exact hrR
    exact hrClosure (S ∪ NewOpposite) hClosed hSeed
  refine ⟨hPrightAvoidS, ?_⟩
  intro r hrOld hrNew
  have hrInNew : r ∈ NewOpposite := by
    rcases hOldRootLocalization hrOld with hrS | hrC
    · exact False.elim (hrNew hrS)
    · exact hrC
  exact hrInNew.2

/-- At ANY old root width, an actual smaller minimal CLOSED
separator whose complete root is inside the old selected
outer source piece CANNOT capture old P-root vertices in
BOTH its selected left and opposite right components.

Proof: every old P-root source vertex outside d.root lies
in one SAME new-cut component containing P.right; two
different components d.left and d.right cannot both
intersect that single component. -/
theorem geometric_no_twoSidedOldRootCapture_of_newRoot_inside_oldPiece
    {V : Type}
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hDRootInOldPiece :
      Set.range d.roots ⊆ geometricPieceVertices Source P)
    (hLeftCapture :
      ∃ r : V, r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left)
    (hRightCapture :
      ∃ s : V, s ∈ Set.range P.roots ∧
        s ∈ functionalComponentFrom Source
          (Set.range d.roots) d.right) : False := by
  obtain ⟨hPrightOutsideNew, hReachOldRoot⟩ :=
    geometric_oldRoot_reachable_from_oldOpposite_after_innerCut
      Source P d hDRootInOldPiece
  obtain ⟨r, hrOld, hrLeft⟩ := hLeftCapture
  obtain ⟨s, hsOld, hsRight⟩ := hRightCapture
  have hrFromOldOpposite :
      ReachOutside Source.graph (Set.range d.roots)
        (⟨P.right.1, hPrightOutsideNew⟩ :
          {v : V // v ∉ Set.range d.roots})
        (⟨r, hrLeft.1⟩ :
          {v : V // v ∉ Set.range d.roots}) :=
    hReachOldRoot r hrOld hrLeft.1
  have hsFromOldOpposite :
      ReachOutside Source.graph (Set.range d.roots)
        (⟨P.right.1, hPrightOutsideNew⟩ :
          {v : V // v ∉ Set.range d.roots})
        (⟨s, hsRight.1⟩ :
          {v : V // v ∉ Set.range d.roots}) :=
    hReachOldRoot s hsOld hsRight.1
  have hBetween :
      ReachOutside Source.graph (Set.range d.roots)
        d.left d.right :=
    hrLeft.2.trans
      ((reachOutside_symm Source.graph (Set.range d.roots)
          hrFromOldOpposite).trans
        (hsFromOldOpposite.trans
          (reachOutside_symm Source.graph (Set.range d.roots)
            hsRight.2)))
  exact d.minimal.2.1 hBetween

end AllThoseRamseyClasses.Lifts
