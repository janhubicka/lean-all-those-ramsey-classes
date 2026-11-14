import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.Claim2PieceScopedActiveBoundaryTransfer
import AllThoseRamseyClasses.Lifts.Claim2OuterLocalBoundaryRestriction

/-!
# Same-selected-Q actual geometric successor preserves B-active boundaries

The original 2019 Claim 2 descent needs not only a strict decrease
of the B-exclusive SOURCE count but preservation of the local
generated-boundary injectivity hypothesis used to select the next
step. This module assembles those properties for ONE SAME actual
selected-Q functional source replacement and ONE genuine new outer
geometric minimal-separator piece.

The old hypothesis is precisely the piece-scoped B-active injection
assumption of the verified positive-rank dichotomy (#1106).
The actual same-Q selected source theorem supplies (a) old/new
full native free-amalgam diagrams over the exact Fin m inner root;
(b) literal equality of the new outer carrier with all selected Q
and retained E vertices of the old outer carrier;
(c) agreement of the weak target map on ALL retained E vertices;
(d) no B-exclusive source vertex on Q.

The verified piece-scoped paired-native-boundary transport theorem
then preserves the local injection condition on the new outer piece.
Both source counts are genuine Nat.card, not target-image cardinalities.

This is a CONDITIONAL one-step theorem, not selection after mixed
smaller-root cuts or a proof of the terminal original Claim 2 exit.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One selected-Q geometric B-to-A source flip strictly decreases
the B-only SOURCE count while preserving the ENTIRE generated
B-active boundary injection invariant on the SAME new outer piece.

No global injectivity of f or flip is assumed, and the old local
injection hypothesis is required only INSIDE the current outer piece.
The exported result retains the original global piece symbol,
ordered target root coordinates and exterior source counts. -/
theorem geometricGlobalRightFlip_actualOuterPiece_withActiveBoundaryInj
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
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
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
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) y)))) := by
  let iOldE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  have hOldFree :
      Structure.IsFreeAmalgam
        (geometricGlobalFunctionalChart Old inner).ext.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding
        (functionalComponentEmbedding Old
          (Set.range inner.roots) inner.minimal.1 inner.left)
        iOldE := geometricGlobalSource_freeDiagram Old inner
  obtain ⟨V', New, hNew, Q, _hSelected, iQ, iE, hNewFree,
      flip, hFlip, hFiniteNew, newOuter, _hRoot,
      hQNoRight, hEAgree, _hOldRootCoords,
      hCarrier, hCoords, hSymbol, hStrictB, hExterior,
      _hProfile⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExteriorAndAllTests_withNoNewRight
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  have hOldRootSeam :
      ∀ r : Fin m,
        f (iOldE ((geometricGlobalComplementChart Old inner).rootEmbedding r))
          ∈ Set.range (jLeft.comp iLeft) := by
    intro r
    change f (inner.roots r) ∈ Set.range (jLeft.comp iLeft)
    exact hInnerRoots ⟨r, rfl⟩
  have hNewCarrier :
      geometricPieceVertices New newOuter ⊆
        Set.range iQ ∪
          iE '' (iOldE ⁻¹' geometricPieceVertices Old outer) := by
    intro w hw
    have hwUnion :
        w ∈ iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Old outer inner) := by
      rw [hCarrier]
      exact hw
    simpa only [Set.image_univ, oldOuterContextInInnerComplement, iOldE]
      using hwUnion
  have hOldScoped :=
    claim2_outerBActiveBoundaryInjection_restrict_to_retainedComplement
      iOldE iLeft iRight jLeft jRight f
      (geometricPieceVertices Old outer) hOldLocalInjection
  have hTransport :=
    fullNativeReplacement_pieceScoped_activeBoundaryInj_transfer
      hOldFree hNewFree f flip
      (Set.range (jLeft.comp iLeft))
      (fullFreeRightExclusiveTarget iRight jRight)
      (geometricPieceVertices Old outer)
      (geometricPieceVertices New newOuter)
      hEAgree hOldRootSeam hNewCarrier hQNoRight hOldScoped
  have hRootTargetAgree :
      ∀ r : UX, jRight (iRight r) = jLeft (iLeft r) := by
    intro r
    exact ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  have hNewLocalInjection :
      ∀ (y : {w : V' //
          w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
        y.1 ∈ geometricPieceVertices New newOuter →
        y.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) y))) := by
    intro y hyPart hyRight
    have hyRightSwapped :
        y.1 ∈ weakFreeLeftPart
          (sL := iRight) (iL := jRight) flip := by
      refine ⟨hyRight.1, ?_⟩
      intro hyRootR
      obtain ⟨r, hr⟩ := hyRootR
      apply hyRight.2
      exact ⟨r, (hRootTargetAgree r).symm.trans hr⟩
    have hyActive :
        flip y.1 ∈ fullFreeRightExclusiveTarget iRight jRight :=
      (weakFreeLeftPart_iff_targetExclusive
        iRight jRight flip y.1).mp hyRightSwapped
    exact hTransport y.1 hyPart hyActive y.2
  exact ⟨V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hCoords, hSymbol, hStrictB, hExterior,
    hNewLocalInjection⟩

end AllThoseRamseyClasses.Lifts
