import AllThoseRamseyClasses.Lifts.Claim2SelectedOuterActiveBoundaryAnchor
import AllThoseRamseyClasses.Lifts.Claim2ActualOuterStatePersistence

/-!
# Same-witness complete inductive eligibility for a selected inner flip

A successful selected-Q B-to-A native source replacement can preserve
ALL of the following on one genuine new outer geometric separator piece:

* strict decrease of B-exclusive SOURCE support inside the outer piece;
* old global canonical piece symbol and ordered target coordinates;
* all-target SOURCE support counts outside that piece;
* B-active full generated-boundary local injectivity on that piece;
* one A-exclusive actual SOURCE anchor with exactly preserved target;
* outer ordered-root containment in the full target common seam;
* outer-piece functional no-escape relative to that seam;
* injectivity of the entire ordered outer target-root coordinate map.

The last property is conditional on the corresponding OLD root
coordinate injection. This theorem never upgrades the arbitrary weak
EHN map into a global injection. It is an eligibility-persistence step
for a chosen one-sided inner piece, not the existence of a flippable
piece in every mixed/captured-root configuration.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The general positive-rank state successor preserves the A-anchor,
local full B-boundary injection, entire outer target seam root and
functional no-escape on the SAME new native source, without any
outer target-root image injectivity assumption. -/
theorem geometricGlobalRightFlip_actualOuterPiece_withSeamAndNoEscape
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Old : Structure L V)
    (hFinite : Finite V) (hOld : F Old)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hm : 0 < m) (hn : 0 < n)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (inner.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (anchor : V)
    (hAnchorOuter : anchor ∈ geometricPieceVertices Old outer)
    (hAnchorA : f anchor ∈ fullFreeLeftExclusiveTarget iLeft jLeft)
    (hOldLocalInjection :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Old outer →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Old.functionClosure
            (gaifmanNeighborhood Old.graph
              (componentFrom Old.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) 
    (hOuterRootInSeam : Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (hFiniteNew : Finite V') (flip : V' → UT)
      (newOuter : GeometricFunctionalPieceData New n),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ i : Fin n, flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old hFinite hOld outer hn =
        geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet}) ∧
      (∀ (y : {w : V' //
          w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
        y.1 ∈ geometricPieceVertices New newOuter →
        y.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) y)))) ∧
      ∃ anew : V',
        anew ∈ geometricPieceVertices New newOuter ∧
        flip anew = f anchor ∧
        flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft ∧
        Set.range newOuter.roots ⊆
          weakFreeRootPart (sL := iLeft) (iL := jLeft) flip ∧
        FunctionalContextNoEscapeOutsideSeam New
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
          (geometricPieceVertices New newOuter) := by
  obtain ⟨V', New, hNew, hFiniteNew, flip, newOuter,
      hFlip, hCoords, hSymbol, hStrictB, hExterior,
      hLocalInjection, anew, haOuter, haSame, haA⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withActiveBoundaryInjAndAAnchor
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
      anchor hAnchorOuter hAnchorA hOldLocalInjection
  obtain ⟨hNewRootSeam, hNoEscape⟩ :=
    geometricOuterRootSeam_noEscape_of_targetCoordinates
      Old New outer newOuter Target X Left iLeft jLeft
      f flip hCoords hOuterRootInSeam
  exact ⟨V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hCoords, hSymbol, hStrictB, hExterior,
    hLocalInjection, anew, haOuter, haSame, haA,
    hNewRootSeam, hNoEscape⟩

/-- Optional ordered outer-root target injection persistence. The
general state theorem above has NO such additional hypothesis. -/
theorem geometricGlobalRightFlip_actualOuterPiece_withFullInductionInvariants
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Old : Structure L V)
    (hFinite : Finite V) (hOld : F Old)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hm : 0 < m) (hn : 0 < n)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (inner.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (anchor : V)
    (hAnchorOuter : anchor ∈ geometricPieceVertices Old outer)
    (hAnchorA : f anchor ∈ fullFreeLeftExclusiveTarget iLeft jLeft)
    (hOldLocalInjection :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Old outer →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Old.functionClosure
            (gaifmanNeighborhood Old.graph
              (componentFrom Old.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) 
    (hOuterRootInSeam : Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hOuterRootImageInjective :
      Function.Injective (fun i : Fin n => f (outer.roots i))) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (hFiniteNew : Finite V') (flip : V' → UT)
      (newOuter : GeometricFunctionalPieceData New n),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ i : Fin n, flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old hFinite hOld outer hn =
        geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet}) ∧
      (∀ (y : {w : V' //
          w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
        y.1 ∈ geometricPieceVertices New newOuter →
        y.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) y)))) ∧
      ∃ anew : V',
        anew ∈ geometricPieceVertices New newOuter ∧
        flip anew = f anchor ∧
        flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft ∧
        Set.range newOuter.roots ⊆
          weakFreeRootPart (sL := iLeft) (iL := jLeft) flip ∧
        FunctionalContextNoEscapeOutsideSeam New
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
          (geometricPieceVertices New newOuter) ∧
        Function.Injective (fun i : Fin n => flip (newOuter.roots i)) := by
  obtain ⟨V', New, hNew, hFiniteNew, flip, newOuter,
      hFlip, hCoords, hSymbol, hStrictB, hExterior,
      hLocalInjection, anew, haOuter, haSame, haA,
      hNewRootSeam, hNoEscape⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withSeamAndNoEscape
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
      anchor hAnchorOuter hAnchorA hOldLocalInjection
      hOuterRootInSeam
  have hNewRootInjective :
      Function.Injective (fun i : Fin n => flip (newOuter.roots i)) :=
    geometricOuterRoot_imageInjective_of_targetCoordinates
      Old New outer newOuter f flip hCoords hOuterRootImageInjective
  exact ⟨V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hCoords, hSymbol, hStrictB, hExterior,
    hLocalInjection, anew, haOuter, haSame, haA,
    hNewRootSeam, hNoEscape, hNewRootInjective⟩

end AllThoseRamseyClasses.Lifts
