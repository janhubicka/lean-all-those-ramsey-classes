import AllThoseRamseyClasses.Lifts.OuterGeneratedBoundaryFromSelectedQ
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamOuterOldRootCriterion

/-!
# Recover a TRUE transported older geometric piece after a genuine Q flip

The original 2019 Claim 2 argument needs an actual geometric
minimal-closed-separator piece rooted at the OLD outer cut T
in the new forbidden source, not merely an equivalent abstract
rooted context. The existing old-root criterion recovers such a
piece exactly when BOTH the preserved exterior and the new
opposite interior components have complete generated
boundaries T.

The exterior component and its boundary are certified purely
inside the unchanged full complement. Our new selected-Q
boundary theorem obtains the OPPOSITE boundary from genuine
Q-private inner component geometry, retained paths, and full
source function-closure transport, without assuming it.

The new component is necessarily different from the preserved
exterior one: its root is a private vertex of the inserted
left side, and the free-amalgam overlap certificate forbids
its image from belonging to the unchanged complement.

Thus a finite literal new source contains a genuine geometric
minimal separator with FULL transported root T. Its global
rooted incompatibility-profile agreement with the old outer
piece is a separate nested full-diagram theorem (Track B),
as is the source-support descent (Track C).
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Under explicit original outer-context exterior and old
interior geometry, replacing a selected inner piece by a
genuinely generated-root Q yields an ACTUAL new outer
minimal-closed-separator geometric source piece with exact
transported OLD root, not just a conditionally equivalent
rooted extension.

The new source is finite as for original forbidden sources.
Neither all-test profile congruence nor local B-support
strict decrease is claimed here. -/
theorem fullFreeAmalgam_outerGeometricPiece_from_selectedInnerBoundary
    {H E E' B W W' : Type v} [Finite W']
    {Root : Structure L H}
    {OldInner : Structure L E}
    {NewInner : Structure L E'}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sOldInner : Structure.Embedding Root OldInner}
    {sNewInner : Structure.Embedding Root NewInner}
    {sComp : Structure.Embedding Root Complement}
    {iOldInner : Structure.Embedding OldInner Old}
    {iOldComp : Structure.Embedding Complement Old}
    {iNewInner : Structure.Embedding NewInner New}
    {iNewComp : Structure.Embedding Complement New}
    (hOld : Structure.IsFreeAmalgam
      sOldInner sComp iOldInner iOldComp)
    (hNew : Structure.IsFreeAmalgam
      sNewInner sComp iNewInner iNewComp)
    (T : Set B) (hTclosed : Complement.IsClosed T)
    (dOld : {w : W // w ∉ iOldComp '' Set.range sComp})
    (hdOldInner : dOld.1 ∈ Set.range iOldInner)
    (hOldPrivateInD :
      ∀ e : E, e ∉ Set.range sOldInner →
        iOldInner e ∈ componentFrom Old.graph
          (iOldComp '' Set.range sComp) dOld)
    (xOld : {w : W // w ∉ iOldComp '' T})
    (hxOld :
      xOld.1 ∈ componentFrom Old.graph
        (iOldComp '' Set.range sComp) dOld)
    (hRootOld :
      ∀ r : H, sComp r ∉ T →
        iOldComp (sComp r) ∈
          componentFrom Old.graph (iOldComp '' T) xOld)
    (hOldBoundary :
      Old.functionClosure
        (gaifmanNeighborhood Old.graph
          (componentFrom Old.graph (iOldComp '' T) xOld)) =
        iOldComp '' T)
    (xExterior : {b : B // b ∉ T})
    (hExteriorPrivate :
      componentFrom Complement.graph T xExterior ⊆
        {b : B | b ∉ Set.range sComp})
    (hExteriorBoundary :
      Complement.functionClosure
        (gaifmanNeighborhood Complement.graph
          (componentFrom Complement.graph T xExterior)) = T)
    (dNew : {e : E' // e ∉ Set.range sNewInner})
    (hNewInnerBoundary :
      NewInner.functionClosure
        (gaifmanNeighborhood NewInner.graph
          (componentFrom NewInner.graph
            (Set.range sNewInner) dNew)) =
        Set.range sNewInner) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData New m),
      Set.range d.roots = iNewComp '' T ∧
      d.left.1 = iNewComp xExterior.1 ∧
      d.right.1 = iNewInner dNew.1 ∧
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph
            (Set.range d.roots) d.left)) =
        iNewComp '' T := by
  obtain ⟨xNew, hxNew, hNewBoundary⟩ :=
    fullFreeAmalgam_outerBoundary_from_selectedInnerBoundary
      hOld hNew T hTclosed
      dOld hdOldInner hOldPrivateInD
      xOld hxOld hRootOld hOldBoundary
      dNew hNewInnerBoundary
  have hNewPrivate : xNew.1 ∉ Set.range iNewComp := by
    rintro ⟨b, hbImage⟩
    have hOver : iNewInner dNew.1 = iNewComp b :=
      hxNew.symm.trans hbImage.symm
    obtain ⟨r, hrInner, _hrComp⟩ :=
      (hNew.overlap dNew.1 b).mp hOver
    exact dNew.2 ⟨r, hrInner.symm⟩
  have hOpposite :
      xNew.1 ∉
        iNewComp '' componentFrom Complement.graph T xExterior := by
    rintro ⟨b, _, hbImage⟩
    exact hNewPrivate ⟨b, hbImage⟩
  obtain ⟨m, d, hRoot, hLeft, hRight, hBoundary⟩ :=
    finite_outerOldRoot_hasGeometricPiece_of_oppositeBoundary
      hNew T hTclosed xExterior
      hExteriorPrivate hExteriorBoundary
      xNew hOpposite hNewBoundary
  refine ⟨m, d, hRoot, hLeft, ?_, hBoundary⟩
  exact hRight.trans hxNew

end AllThoseRamseyClasses.Lifts
