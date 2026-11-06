import AllThoseRamseyClasses.Lifts.FullFreeAmalgamOuterContextCarrier
import AllThoseRamseyClasses.Lifts.OuterGeneratedBoundaryFromSelectedQ

/-!
# Derive exact outer context carrier from an inserted full-root component

This composes the verified full native functional free-amalgam
geometry with the generic exact carrier equation of
FullFreeAmalgamOuterContextCarrier.

The OLD geometric assumptions are the same as those already
required by the merged exact older-boundary theorem: a true
old selected inner component, the root-attached older cut, and
a real old outer T-component. The inserted Q has ONE actual
private component with complete generated boundary U, plus
the stronger condition that EVERY Q-private vertex lies in
that same component (proved independently from ACTUAL
geometric selection in the #881 source).

The inserted-component theorem #822 constructs a genuine
new T-component containing the inserted Q component, with
every surviving shared-root vertex U \ T attached. The
already verified ALL-retained equivalence #793 then accounts
for every retained old component vertex, root and nonroot.

Thus the whole transported context is exactly the transported
older root united with ONE new older T-component. This proof
does not assume new outer boundary equality or minimality; the
separate #830/#834 geometry supplies those for genuine nested
sources. It also does not identify any source vertex via weak
forbidden target maps.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- The full transported context carrier becomes the old cut
plus one actual new connected T-component, once the
*entire* newly selected private side belongs to its
single internally full-root-generating component.

All older root attachment and retained component equations
are proved for the literal new source by the merged
#822 and #793 component theorems. No new minimal-cut
or canonical-profile assumption occurs in this statement. -/
theorem fullFreeAmalgam_outerContext_eq_of_selectedComponent
    {H E E' B W W' : Type v}
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
    (dNew : {e : E' // e ∉ Set.range sNewInner})
    (hNewInnerBoundary :
      NewInner.functionClosure
        (gaifmanNeighborhood NewInner.graph
          (componentFrom NewInner.graph
            (Set.range sNewInner) dNew)) =
        Set.range sNewInner)
    (hAllNewPrivate : ∀ e : E',
      e ∉ Set.range sNewInner →
        e ∈ componentFrom NewInner.graph
          (Set.range sNewInner) dNew) :
    ∃ xNew : {w : W' // w ∉ iNewComp '' T},
      xNew.1 = iNewInner dNew.1 ∧
      (iNewInner '' (Set.univ : Set E') ∪
        iNewComp '' {b : B | iOldComp b ∈
          (iOldComp '' T) ∪
          componentFrom Old.graph
            (iOldComp '' T) xOld}) =
       (iNewComp '' T) ∪
          componentFrom New.graph
            (iNewComp '' T) xNew := by
  obtain ⟨xNew, hxNew, hInserted, hRootNew,
      _hRootBoundary⟩ :=
    fullFreeAmalgam_insertedComponent_outerCut_attaches
      hNew T hTclosed dNew hNewInnerBoundary
  have hxNewInLeft : xNew.1 ∈ Set.range iNewInner :=
    ⟨dNew.1, hxNew.symm⟩
  have hRetained : ∀ b : B, b ∉ T →
      (iOldComp b ∈
        componentFrom Old.graph (iOldComp '' T) xOld ↔
       iNewComp b ∈
        componentFrom New.graph (iNewComp '' T) xNew) := by
    intro b hbNotT
    exact fullFreeAmalgam_allRetainedOuterComponent_iff
      hOld hNew T dOld hdOldInner hOldPrivateInD
      xOld hxOld xNew hxNewInLeft hRootOld hRootNew
      b hbNotT
  have hPrivateInserted : ∀ e : E',
      e ∉ Set.range sNewInner →
        iNewInner e ∈ componentFrom New.graph
          (iNewComp '' T) xNew := by
    intro e he
    exact hInserted ⟨e, hAllNewPrivate e he, rfl⟩
  refine ⟨xNew, hxNew, ?_⟩
  exact fullFreeAmalgam_nestedOuterContext_carrier_eq
    hNew T xOld xNew hRetained hRootNew hPrivateInserted

end AllThoseRamseyClasses.Lifts
