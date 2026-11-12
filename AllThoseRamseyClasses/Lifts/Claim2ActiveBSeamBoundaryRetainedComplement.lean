import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGeneratedBoundary
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.Claim2SeamCollisionNewSideLocalization

/-!
# Active B-only components and their whole generated boundaries remain in E

A successful native B-to-A source flip constructs New as a TRUE full
functional amalgam Q +_Root E. The Q source map into Target factors
through the LEFT target side. Hence every B-exclusive SOURCE vertex
(and its entire connected component after deleting the TARGET shared
root preimage) lies in the retained E side, irrespective of any NEW
root-image collisions inside Q.

The Q/E overlap is mapped into the target common seam by exact root
coordinates. Thus the B-only component lies in E PRIVATE to the
gluing root. The verified full-native private-side theorem identifies
its entire function-GENERATED external boundary as the embedding of
the unchanged E boundary, with no newly introduced Q-only vertices.

If the original source map was injective on its COMPLETE old seam
preimage, complete complement target-coordinate agreement makes
the NEW B-component's generated boundary injective, even when
the NEW map COLLIDES elsewhere on its complete new seam preimage.
This avoids assuming that a replacement Q automatically reflects
the common root. It does NOT produce an eligible inner geometric
one-sided piece in the smaller-mixed-root branch, nor prove all
successor state conditions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For a real full-native Q+E source, with all Q target images in
the LEFT target side, the full generated boundary of ANY selected
B-exclusive component after deleting the target common seam lies
inside the retained native full E image.

No injectivity of the NEW weak map, even on the entire seam, is
assumed. -/
theorem fullNativeFlip_rightComponent_generatedBoundary_in_retainedComplement
    {R E Q W UX UA UB UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {New : Structure L W}
    {X : Structure L UX} {Left : Structure L UA}
    {Right : Structure L UB} {Target : Structure L UT}
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (flip : W → UT)
    (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    (gQ : Q → UA)
    (hFlipQ : ∀ q : Q, flip (iNewQ q) = jLeft (gQ q))
    (hQRootSeam : ∀ r : R,
      iNewQ (qRoot r) ∈
        weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
    (x : {w : W // w ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) flip})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) flip) :
    New.functionClosure
      (gaifmanNeighborhood New.graph
        (componentFrom New.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) x))
      ⊆ Set.range iNewE := by
  classical
  let S : Set W :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) flip
  let C : Set W := componentFrom New.graph S x
  let CE : Set E := iNewE ⁻¹' C
  have hCinsideE : C ⊆ Set.range iNewE := by
    intro w hw
    have hwB : w ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) flip :=
      weakFreePartition_component_right
        hTargetFree flip hFlip.1 x hxRight hw
    rcases hNewFree.covers w with ⟨q, hq⟩ | ⟨e, he⟩
    · have hAtLeft : flip w = jLeft (gQ q) :=
        (congrArg flip hq).trans (hFlipQ q)
      exact False.elim
        ((weakFreeRightPart_not_left hTargetFree flip hwB (gQ q))
          hAtLeft)
    · exact ⟨e, he.symm⟩
  have hCimage : C = iNewE '' CE := by
    apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨e, he⟩ := hCinsideE hw
      refine ⟨e, ?_, he⟩
      simpa only [he] using hw
    · rintro w ⟨e, he, hEq⟩
      exact hEq ▸ he
  have hCEprivate : CE ⊆ {e : E | e ∉ Set.range eRoot} := by
    intro e he heRoot
    obtain ⟨r, hr⟩ := heRoot
    have hOverlap : iNewQ (qRoot r) = iNewE (eRoot r) :=
      (hNewFree.overlap (qRoot r) (eRoot r)).mpr
        ⟨r, rfl, rfl⟩
    have hAtSeam : iNewE (eRoot r) ∈ S := by
      rw [← hOverlap]
      exact hQRootSeam r
    exact he.1 (by simpa only [hr] using hAtSeam)
  have hBoundaryImage :
      New.functionClosure
        (gaifmanNeighborhood New.graph C) =
      iNewE '' (Complement.functionClosure
        (gaifmanNeighborhood Complement.graph CE)) := by
    rw [hCimage]
    exact fullFreeAmalgam_private_generatedBoundary_eq_image
      hNewFree (Set.range eRoot) CE
      (fun r => ⟨r, rfl⟩) hCEprivate
  intro z hz
  change z ∈ New.functionClosure
    (gaifmanNeighborhood New.graph C) at hz
  rw [hBoundaryImage] at hz
  obtain ⟨e, _he, hMap⟩ := hz
  exact ⟨e, hMap⟩

/-- The ONLY old injectivity needed for a future B-component
boundary is injectivity of the weak map on seam-valued vertices of
the RETAINED complement E; fresh Q-side seam collisions elsewhere
need not be excluded. -/
theorem fullNativeFlip_rightComponent_generatedBoundary_inj_of_retainedSeamInj
    {R E Q V W UX UA UB UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    {X : Structure L UX} {Left : Structure L UA}
    {Right : Structure L UB} {Target : Structure L UT}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (f : V → UT) (flip : W → UT)
    (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    (gQ : Q → UA)
    (hFlipQ : ∀ q : Q, flip (iNewQ q) = jLeft (gQ q))
    (hQRootSeam : ∀ r : R,
      iNewQ (qRoot r) ∈
        weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e))
    (hOldRetainedSeamInjective :
      ∀ e₁ e₂ : E,
        f (iOldE e₁) ∈ Set.range (jLeft.comp iLeft) →
        f (iOldE e₂) ∈ Set.range (jLeft.comp iLeft) →
        f (iOldE e₁) = f (iOldE e₂) →
        e₁ = e₂)
    (x : {w : W // w ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) flip})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) flip) :
    Set.InjOn flip
      (New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) x))) := by
  let S : Set W :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) flip
  let T : Set W := New.functionClosure
    (gaifmanNeighborhood New.graph
      (componentFrom New.graph S x))
  have hTinsideE : T ⊆ Set.range iNewE :=
    fullNativeFlip_rightComponent_generatedBoundary_in_retainedComplement
      iNewE iNewQ qRoot eRoot hNewFree
      iLeft iRight jLeft jRight hTargetFree
      flip hFlip gQ hFlipQ hQRootSeam x hxRight
  have hSclosed : New.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft) flip hFlip.1
  have hTinsideS : T ⊆ S :=
    functionalClosure_neighborhood_subset_cut New S hSclosed x
  intro u hu v hv huv
  obtain ⟨eu, heu⟩ := hTinsideE hu
  obtain ⟨ev, hev⟩ := hTinsideE hv
  have hSeamU : flip (iNewE eu) ∈
      Set.range (jLeft.comp iLeft) := by
    have hU := hTinsideS hu
    change flip u ∈ Set.range (jLeft.comp iLeft) at hU
    exact heu.symm ▸ hU
  have hSeamV : flip (iNewE ev) ∈
      Set.range (jLeft.comp iLeft) := by
    have hV := hTinsideS hv
    change flip v ∈ Set.range (jLeft.comp iLeft) at hV
    exact hev.symm ▸ hV
  have hOldSeamU : f (iOldE eu) ∈
      Set.range (jLeft.comp iLeft) := by
    rw [← hSameComplement eu]
    exact hSeamU
  have hOldSeamV : f (iOldE ev) ∈
      Set.range (jLeft.comp iLeft) := by
    rw [← hSameComplement ev]
    exact hSeamV
  have hOldEqual : f (iOldE eu) = f (iOldE ev) := by
    calc
      f (iOldE eu) = flip (iNewE eu) := (hSameComplement eu).symm
      _ = flip (iNewE ev) := by simpa only [heu, hev] using huv
      _ = f (iOldE ev) := hSameComplement ev
  have hEqE : eu = ev :=
    hOldRetainedSeamInjective eu ev hOldSeamU hOldSeamV hOldEqual
  calc
    u = iNewE eu := heu.symm
    _ = iNewE ev := congrArg iNewE hEqE
    _ = v := hev

/-- Backwards-compatible corollary: full old-seam injectivity implies
injectivity on the old retained complement, hence on each new active
B-component boundary. The stronger retained-E theorem is enough even
when the old full-seam map is not injective elsewhere. -/
theorem fullNativeFlip_rightComponent_generatedBoundary_inj_of_oldSeamInj
    {R E Q V W UX UA UB UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    {X : Structure L UX} {Left : Structure L UA}
    {Right : Structure L UB} {Target : Structure L UT}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (f : V → UT) (flip : W → UT)
    (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    (gQ : Q → UA)
    (hFlipQ : ∀ q : Q, flip (iNewQ q) = jLeft (gQ q))
    (hQRootSeam : ∀ r : R,
      iNewQ (qRoot r) ∈
        weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e))
    (hOldSeamInjective :
      Set.InjOn f (f ⁻¹' Set.range (jLeft.comp iLeft)))
    (x : {w : W // w ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) flip})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) flip) :
    Set.InjOn flip
      (New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) x))) := by
  have hRetainedInjective :
      ∀ e₁ e₂ : E,
        f (iOldE e₁) ∈ Set.range (jLeft.comp iLeft) →
        f (iOldE e₂) ∈ Set.range (jLeft.comp iLeft) →
        f (iOldE e₁) = f (iOldE e₂) →
        e₁ = e₂ := by
    intro e₁ e₂ h₁ h₂ hEq
    exact iOldE.injective (hOldSeamInjective h₁ h₂ hEq)
  exact fullNativeFlip_rightComponent_generatedBoundary_inj_of_retainedSeamInj
    iOldE iNewE iNewQ qRoot eRoot hNewFree
    iLeft iRight jLeft jRight hTargetFree
    f flip hFlip gQ hFlipQ hQRootSeam
    hSameComplement hRetainedInjective x hxRight

end AllThoseRamseyClasses.Lifts
