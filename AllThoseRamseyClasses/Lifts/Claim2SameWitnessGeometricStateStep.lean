import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStepAnchor
import AllThoseRamseyClasses.Lifts.Claim2ActualGeometricPieceBoundaryTransfer

/-!
# One same-selected-Q actual geometric step carrying ALL Claim 2 state invariants

The genuine nested selected-Q source flip already constructs one
actual finite forbidden new source and geometric outer piece,
strictly decreases its B-exclusive SOURCE rank, preserves the
original global selected symbol and all exterior SOURCE counts,
and retains an A-exclusive source anchor.

Here that SAME construction also preserves the two independent
injectivity requirements needed for a later terminal argument:
(1) injection of the old ordered outer root's target image;
(2) injection of all generated B-exclusive component boundaries
    INSIDE the chosen actual outer geometric piece.

No global full common-seam injection or source-image quotient is
required. Both injectivity properties have explicit OLD premises;
the theorem does NOT construct an eligible inner one-sided piece,
rule out smaller-root A-mixed/root-capture obstructions, or show
that an initial original minimizer has those properties.

Source counts count literal source vertices. The original numbered
2019 manuscript remains untouched.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The complete one-step *conditional* original Claim 2 state
invariant, witnessed by one concrete same-Q native free-amalgam
source, one target map, one geometric outer carrier and one A anchor.

Positive strict B-source descent and exterior counts are genuine,
while all original root/boundary injection requirements are explicit.
No unrestricted positive successor or final contradiction is claimed. -/
theorem geometricGlobalRightFlip_actualOuterPiece_withExteriorAnchorRootAndBoundaryInj
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
    (hOldOuterRootTargetInj :
      Function.Injective (fun i : Fin n => f (outer.roots i)))
    (hOldActiveBoundaryInj :
      ∀ (x : {v : V // v ∉
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Old outer →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Old.functionClosure
            (gaifmanNeighborhood Old.graph
              (componentFrom Old.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Old inner).root)
      (hSelected :
        (FunctionalRootExtension.toEnumeratedRootedPattern
          (geometricGlobalFunctionalChart Old inner).root
          (Equiv.refl (Fin m)) Q) ∈
            forbiddenGeometricFunctionalPieces F m)
      (iQ : Structure.Embedding Q.str New)
      (iE : Structure.Embedding
        (geometricGlobalComplementChart Old inner).str New)
      (hNewFree : Structure.IsFreeAmalgam Q.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding iQ iE)
      (hFiniteNew : Finite V') (flip : V' → UT)
      (newOuter : GeometricFunctionalPieceData New n),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ q : Q.Carrier,
        flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight) ∧
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1) ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter ∧
      (∀ i : Fin n, flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn =
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
      ∃ anew : V',
        anew ∈ geometricPieceVertices New newOuter ∧
        flip anew = f anchor ∧
        flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft ∧
      Function.Injective (fun i : Fin n => flip (newOuter.roots i)) ∧
      (∀ (y : V')
        (hyPart : y ∈ geometricPieceVertices New newOuter)
        (hyB : flip y ∈ fullFreeRightExclusiveTarget iRight jRight)
        (hyOutside : flip y ∉ Set.range (jLeft.comp iLeft)),
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (flip ⁻¹' Set.range (jLeft.comp iLeft))
                (⟨y, hyOutside⟩ :
                  {w : V' // w ∉ flip ⁻¹' Set.range (jLeft.comp iLeft)}))))) := by
  -- All invariants are certified for ONE literal selected-Q new source.
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
      hFiniteNew, flip, newOuter, hFlip, hQNoB,
      hEAgree, hCarrier, hTargetCoords, hSymbol,
      hRank, hExterior, anew, haOuter, haSame, haNewA⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withExteriorAnchorAndNoNewRight
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
      anchor hAnchorOuter hAnchorA
  -- Old target-root tuple injectivity is a genuine separate input,
  -- and is conserved by the checked old/new exact root coordinates.
  have hNewOuterRootInj :
      Function.Injective (fun i : Fin n => flip (newOuter.roots i)) :=
    geometricOuterRoot_imageInjective_of_targetCoordinates
      Old New outer newOuter f flip hTargetCoords
      hOldOuterRootTargetInj
  -- This boundary invariant belongs to the SAME selected Q/new outer.
  -- The source-free-amalgam and context-preimage premises are supplied
  -- by the actual old geometric inner piece, not by an abstract state.
  have hNewBoundaryInj :
      ∀ (y : V')
        (hyPart : y ∈ geometricPieceVertices New newOuter)
        (hyB : flip y ∈ fullFreeRightExclusiveTarget iRight jRight)
        (hyOutside : flip y ∉ Set.range (jLeft.comp iLeft)),
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (flip ⁻¹' Set.range (jLeft.comp iLeft))
                (⟨y, hyOutside⟩ :
                  {w : V' // w ∉ flip ⁻¹' Set.range (jLeft.comp iLeft)})))) :=
    geometricSelectedQ_actualOuter_preserves_BActive_boundary_inj
      Old New outer inner Q iQ iE hNewFree newOuter
      Target f flip X Left Right iLeft iRight jLeft jRight
      hInnerRoots hEAgree hCarrier hQNoB hOldActiveBoundaryInj
  exact ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
    hFiniteNew, flip, newOuter, hFlip, hQNoB, hEAgree,
    hCarrier, hTargetCoords, hSymbol, hRank, hExterior,
    anew, haOuter, haSame, haNewA, hNewOuterRootInj,
    hNewBoundaryInj⟩

end AllThoseRamseyClasses.Lifts
