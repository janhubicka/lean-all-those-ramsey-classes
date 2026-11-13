import AllThoseRamseyClasses.Lifts.Claim2RetainedCutBoundaryPair
import AllThoseRamseyClasses.Lifts.FullFunctionalFreeAmalgamSwap
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# Actual B-exclusive active-boundary injection through a B-to-A source flip

The paired full-source theorem proves local generated-boundary injectivity
persists when no NEW source vertex in the inserted Q piece belongs to the
specified target Active region. This is not an additional premise for
an actual selected-Q RIGHT-to-LEFT flip: its entire NEW Q side maps
into the target LEFT witness, which is disjoint from the B-exclusive
target region.

Consequently an actual native source flip with the SAME complete
unchanged E complement, full source free-amalgam diagrams, and exact
old/new weak target-coordinate agreement on E transports injection
on ALL B-active generated boundaries. It does not demand injection
on all common-root preimages after the flip. This theorem is
conditional on the source-specific previous active-boundary
injection, not on target root reflection.

Source vertices and full native function-generated boundaries
are used; no weak-image quotient or image-cardinality counting.
The remaining smaller-root mixed-component selection is separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the exact old/new full-native source replacement diagrams
and opposite-side Q factorization, injectivity on ALL old B-exclusive
generated boundaries entails injection on ALL NEW such boundaries,
even if the full new seam preimage has Q-only image collisions.

The inserted Q side is eliminated from the B-active region using
only the TRUE target full free-amalgam overlap and LEFT factorization. -/
theorem fullNativeRightToLeftFlip_allBActiveBoundaries_injection_transfer
    {H E₁ E₂ F W₁ W₂ UX UA UB UT : Type}
    {Root : Structure L H}
    {OldQ : Structure L E₁}
    {NewQ : Structure L E₂}
    {E : Structure L F}
    {OldSource : Structure L W₁}
    {NewSource : Structure L W₂}
    {sOldQ : Structure.Embedding Root OldQ}
    {sNewQ : Structure.Embedding Root NewQ}
    {sE : Structure.Embedding Root E}
    {iOldQ : Structure.Embedding OldQ OldSource}
    {iOldE : Structure.Embedding E OldSource}
    {iNewQ : Structure.Embedding NewQ NewSource}
    {iNewE : Structure.Embedding E NewSource}
    (hOld : Structure.IsFreeAmalgam sOldQ sE iOldQ iOldE)
    (hNew : Structure.IsFreeAmalgam sNewQ sE iNewQ iNewE)
    {X : Structure L UX}
    {Left : Structure L UA}
    {Right : Structure L UB}
    {Target : Structure L UT}
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (f : W₁ → UT) (g : W₂ → UT)
    (hSameE : ∀ e : F, g (iNewE e) = f (iOldE e))
    (hOldGluedRootSeam : ∀ r : H,
      f (iOldE (sE r)) ∈ Set.range (jLeft.comp iLeft))
    (hNewQIntoLeft : ∀ q : E₂, ∃ a : UA, g (iNewQ q) = jLeft a)
    (hOldBActiveInjective :
      ∀ (e : F)
        (heActive : f (iOldE e) ∈
          fullFreeRightExclusiveTarget iRight jRight)
        (heOutside :
          f (iOldE e) ∉ Set.range (jLeft.comp iLeft)),
        Set.InjOn f
          (OldSource.functionClosure
            (gaifmanNeighborhood OldSource.graph
              (componentFrom OldSource.graph
                (f ⁻¹' Set.range (jLeft.comp iLeft))
                (⟨iOldE e, heOutside⟩ :
                  {w : W₁ // w ∉ f ⁻¹' Set.range (jLeft.comp iLeft)}))))) :
    ∀ (y : W₂)
      (hyActive : g y ∈ fullFreeRightExclusiveTarget iRight jRight)
      (hyOutside : g y ∉ Set.range (jLeft.comp iLeft)),
      Set.InjOn g
        (NewSource.functionClosure
          (gaifmanNeighborhood NewSource.graph
            (componentFrom NewSource.graph
              (g ⁻¹' Set.range (jLeft.comp iLeft))
              (⟨y, hyOutside⟩ :
                {w : W₂ // w ∉ g ⁻¹' Set.range (jLeft.comp iLeft)})))) := by
  let Seam : Set UT := Set.range (jLeft.comp iLeft)
  let BOnly : Set UT := fullFreeRightExclusiveTarget iRight jRight
  have hNewRootSeam : ∀ r : H, g (iNewE (sE r)) ∈ Seam := by
    intro r
    rw [hSameE (sE r)]
    exact hOldGluedRootSeam r
  have hNoNewB : ∀ q : E₂, g (iNewQ q) ∉ BOnly := by
    intro q
    obtain ⟨a, hLeft⟩ := hNewQIntoLeft q
    rw [hLeft]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iRight iLeft jRight jLeft
      (fullFunctionalFreeAmalgam_swap hTargetFree) a
  exact fullNativeReplacement_allActiveSeamBoundaries_injection_transfer
    hOld hNew f g Seam BOnly
    hSameE hOldGluedRootSeam hNewRootSeam
    hNoNewB hOldBActiveInjective

end AllThoseRamseyClasses.Lifts
