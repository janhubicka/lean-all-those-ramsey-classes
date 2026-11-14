import AllThoseRamseyClasses.Lifts.Claim2SelectedQGlobalAMinimalIff
import AllThoseRamseyClasses.Lifts.Claim2SelectedOuterActiveBoundaryAnchor
import AllThoseRamseyClasses.Lifts.Claim2ActualOuterStatePersistence

/-!
# A-neutral selected Q: genuine full original Claim 2 successor state

A successful right-to-left selected-Q replacement of an eligible
B-only inner source component already preserves the actual ordered
outer target-root, global canonical symbol, strict B-SOURCE rank
descent, every exterior SOURCE count, a real A-only anchor, and
LOCAL B-active full generated-boundary injectivity.

The additional ORIGINAL A-global-minimality invariant is retained
IF the selected Q witness itself has NO A-active nonroot SOURCE
vertex. This is the exact neutrality criterion identified by the
source-support cost proof, and must be certified ON THE VERY SAME
selected Q / forbidden source / weak target map as the B-flip.

Here that missing selection condition is an EXPLICIT uniform
assumption on selected-Q free source witnesses with the exact old
E-complement target-map agreement. No independent existence
witness is conjoined or reselected. The proof constructs one Q
from the actual #1120 geometric successor and carries all the
invariants through one exact native replacement.

Crucially this theorem DOES NOT prove that the available
canonical selected-Q construction satisfies the uniform
neutrality hypothesis; the unproved existence/selection of an
A-neutral Q is still the core iteration gap of original
2019 Claim 2. The initial state and higher-width root-capture
geometry remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If one can certify A-neutrality of every selected-Q replacement
candidate with actual full complement agreement, a genuinely
eligible B-only source flip produces ONE forbidden new outer
geometric source state with strict B-rank decrease, original
global A-source minimality, preserved A-anchor, full local
B-generated-boundary injectivity, exact ordered target-root
coordinates, common-seam containment/no-escape, global canonical
symbol, and all-target exterior SOURCE count invariance.

This is the explicit missing conditional induction interface,
NOT a proof of existence of neutral selected Q. -/
theorem geometricGlobalRightFlip_actualOuterPiece_AneutralFullSuccessor
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
    (hOldGlobalAMin : ∀ {Z : Type}
      (Candidate : Structure L Z) (hCandidate : F Candidate)
      (g : Z → UT),
      Candidate.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {z : Z //
        g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft})
    (hSelectedQNeutral :
      ∀ {W : Type} (SelectedNew : Structure L W)
        (hSelectedNew : F SelectedNew)
        (SelectedQ : FunctionalRootExtension
          (geometricGlobalFunctionalChart Old inner).root)
        (hSelected :
          (FunctionalRootExtension.toEnumeratedRootedPattern
            (geometricGlobalFunctionalChart Old inner).root
            (Equiv.refl (Fin m)) SelectedQ) ∈
              forbiddenGeometricFunctionalPieces F m)
        (jQ : Structure.Embedding SelectedQ.str SelectedNew)
        (jE : Structure.Embedding
          (geometricGlobalComplementChart Old inner).str SelectedNew)
        (selectedMap : W → UT),
        SelectedNew.IsEHNHomomorphismEmbedding Target selectedMap →
        (∀ e : (geometricGlobalComplementChart Old inner).Carrier,
          selectedMap (jE e) = f e.1) →
        ∀ q : SelectedQ.Carrier,
          q ∉ Set.range SelectedQ.rootEmbedding →
          selectedMap (jQ q) ∉
            fullFreeLeftExclusiveTarget iLeft jLeft) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (hFiniteNew : Finite V') (flip : V' → UT)
      (newOuter : GeometricFunctionalPieceData New n),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {w : V' //
          flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) ∧
      Set.range newOuter.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) flip ∧
      FunctionalContextNoEscapeOutsideSeam New
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
        (geometricPieceVertices New newOuter) ∧
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
        flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft := by
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
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
      hFiniteNew, flip, newOuter, hFlip,
      hQNoRight, hEAgree, hCarrier, hCoords,
      hSymbol, hStrictB, hExterior,
      anew, haOuterNew, haSame, haNewA⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withExteriorAnchorAndNoNewRight
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
      anchor hAnchorOuter hAnchorA
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
  have hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      f z ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro z hz hzA
    exact hInnerNoLeft z hz
      ((weakFreeLeftPart_iff_targetExclusive iLeft jLeft f z).mpr hzA)
  have hQNonrootNoA :
      ∀ q : Q.Carrier,
        q ∉ Set.range Q.rootEmbedding →
        flip (iQ q) ∉ fullFreeLeftExclusiveTarget iLeft jLeft :=
    hSelectedQNeutral New hNew Q hSelected iQ iE flip
      hFlip hEAgree
  have hNewGlobalAMin :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {w : V' //
          flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft} :=
    (geometricSelectedQ_globalAMinimum_iff_nonrootAfree
      F Old hOld inner Q New hNew hFiniteNew iQ iE hNewFree
      Target f hf flip hFlip
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      hOldInnerNoA hEAgree hOldGlobalAMin).mpr hQNonrootNoA
  obtain ⟨hNewRootSeam, hNoEscape⟩ :=
    geometricOuterRootSeam_noEscape_of_targetCoordinates
      Old New outer newOuter Target X Left iLeft jLeft
      f flip hCoords hOuterRootInSeam
  exact ⟨V', New, hNew, hFiniteNew, flip, newOuter,
    hFlip, hNewGlobalAMin, hNewRootSeam, hNoEscape,
    hCoords, hSymbol, hStrictB, hExterior,
    hNewLocalInjection, anew, haOuterNew, haSame, haNewA⟩

end AllThoseRamseyClasses.Lifts
