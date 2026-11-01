import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateOuterComponentIff

/-!
# ALL retained complement vertices preserve old/new outer-component membership

The verified Track A private-component equivalence (#759) already
handles every vertex of the retained complete complement outside
the common INNER gluing root. The only missing retained vertices
lie in that common root. Their membership is exactly the
old/new root-attachment invariant already explicit in #759.

Combining these two cases gives an old/new component-membership
equivalence for EVERY retained complement vertex outside the
older cut T. This is the complete `hRetained` input of the
generated opposite-boundary theorem (#763), with no artificial
assumption that each retained vertex is private.

The inner and outer cuts need not be nested. Every map here is
a full native functional SOURCE embedding; a forbidden weak
target map need not be injective.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Every retained vertex outside T lies in the intended old
outer component iff its image lies in the corresponding new
outer component, under the same source geometry and root
attachment inputs as the private-component theorem #759.

In particular this handles ALL common-inner-root vertices, not
merely vertices private to the unchanged complement. -/
theorem fullFreeAmalgam_allRetainedOuterComponent_iff
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
    (T : Set B)
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
    (xNew : {w : W' // w ∉ iNewComp '' T})
    (hxNew : xNew.1 ∈ Set.range iNewInner)
    (hRootOld :
      ∀ r : H, sComp r ∉ T →
        iOldComp (sComp r) ∈
          componentFrom Old.graph (iOldComp '' T) xOld)
    (hRootNew :
      ∀ r : H, sComp r ∉ T →
        iNewComp (sComp r) ∈
          componentFrom New.graph (iNewComp '' T) xNew)
    (b : B) (hbNotT : b ∉ T) :
    iOldComp b ∈ componentFrom Old.graph (iOldComp '' T) xOld ↔
      iNewComp b ∈ componentFrom New.graph (iNewComp '' T) xNew := by
  by_cases hbRoot : b ∈ Set.range sComp
  · obtain ⟨r, hr⟩ := hbRoot
    have hrNotT : sComp r ∉ T := by
      intro hrT
      exact hbNotT (hr ▸ hrT)
    constructor
    · intro _
      rw [← hr]
      exact hRootNew r hrNotT
    · intro _
      rw [← hr]
      exact hRootOld r hrNotT
  · exact fullFreeAmalgam_privateOuterComponent_iff
      hOld hNew T dOld hdOldInner hOldPrivateInD
      xOld hxOld xNew hxNew hRootOld hRootNew
      b hbRoot hbNotT

end AllThoseRamseyClasses.Lifts
