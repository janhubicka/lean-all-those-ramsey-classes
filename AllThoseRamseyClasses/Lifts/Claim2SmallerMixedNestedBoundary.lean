import AllThoseRamseyClasses.Lifts.Claim2SmallerRootNoCaptureGeometricFlip
import AllThoseRamseyClasses.Lifts.Claim2OuterLocalBoundaryRestriction

/-!
# A noncapturing smaller mixed piece is genuinely nested and inherits B-boundary injection

The smaller-root branch of the original Claim 2 can have an A-mixed
selected source component. This does NOT invalidate the source
nesting argument provided that the new component captures NO
vertex of the old outer geometric root.

With the entire new native closed root inside the old outer piece
and both distinguished endpoints in the old selected component,
absence of old-root capture makes the entire smaller geometric
piece a PROPER source subset of the old outer piece. Consequently
the precise LOCAL injectivity hypothesis on complete B-active
generated boundaries restricts to the smaller piece.

No assumption that the smaller component is A-free; it may be
mixed. This is a source-nesting / local-invariant transfer lemma,
not an inner flip or a proof of existence of a noncapturing cut.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The original positive-rank local B-active boundary invariant
restricts to an ACTUAL proper smaller geometric source piece when
its selected component captures no old outer-root vertex. The
smaller source component may contain A-exclusive vertices. -/
theorem claim2_smallerRoot_noCapture_proper_and_localBoundaryInj
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hNewRootInOldPiece :
      Set.range d.roots ⊆ geometricPieceVertices Source P)
    (hDleftInOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hDrightInOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hNoOldRootCapture :
      ∀ r : V, r ∈ Set.range P.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.left)
    (Target : Structure L UT) (f : V → UT)
    (X : Structure L UX) (Left : Structure L UA)
    (Right : Structure L UB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hOldLocalInjection :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
    geometricPieceVertices Source d ⊂
      geometricPieceVertices Source P ∧
      (∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source d →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) := by
  classical
  have hDcomponentInsideP :
      functionalComponentFrom Source
        (Set.range d.roots) d.left ⊆
      functionalComponentFrom Source
        (Set.range P.roots) P.left := by
    by_contra hEscape
    obtain ⟨r, hrOldRoot, hrCaptured⟩ :=
      geometricPiece_escapingComponent_capturesOldRoot
        Source P d hDleftInOld hEscape
    exact hNoOldRootCapture r hrOldRoot hrCaptured
  have hInnerInside :
      geometricPieceVertices Source d ⊆
      geometricPieceVertices Source P := by
    intro z hz
    rcases hz with hRoot | hComp
    · exact hNewRootInOldPiece hRoot
    · exact Or.inr (hDcomponentInsideP hComp)
  have hRightNotInD :
      d.right.1 ∉ geometricPieceVertices Source d := by
    intro hz
    rcases hz with hR | hC
    · exact d.right.2 hR
    · have hRSubtype :
          (⟨d.right.1, hC.1⟩ :
            {z : V // z ∉ Set.range d.roots}) = d.right :=
          Subtype.ext rfl
      exact d.minimal.2.1
        (by simpa only [hRSubtype] using hC.2)
  have hProper :
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hInnerInside, ?_⟩
    intro hEqual
    have hRightOld :
        d.right.1 ∈ geometricPieceVertices Source P :=
      Or.inr hDrightInOld
    exact hRightNotInD (hEqual.symm ▸ hRightOld)
  refine ⟨hProper, ?_⟩
  intro x hxD hxRight
  exact hOldLocalInjection x (hProper.subset hxD) hxRight

end AllThoseRamseyClasses.Lifts
