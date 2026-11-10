import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol

/-!
# Track A/C: original outer target relation in the same genuine selected-Q B-flip

The verified same-Q actual geometric step preserves the old outer
GLOBAL canonical symbol, exact ordered root target coordinates,
strict B-exclusive SOURCE rank, and all SOURCE counts outside the
actual outer piece. A weak EHN map of the NEW forbidden source
realizes its own original GLOBAL canonical relation on an
injectively mapped ordered root. The equality of full GLOBAL
piece symbols and exact coordinates then transfers that relation
to the ORIGINAL older symbol in the SAME target.

The target injectivity of the OLD OUTER root is an explicit extra
hypothesis. It does **not** follow from injectivity of the inner
selected root under the weak map. Track D must address potential
outer collisions. This theorem is only a faithful composition of
the already validated geometric and target-relation interfaces,
not a proof of the unrestricted Claim 2 iteration or strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One selected right-to-left geometric replacement, with strict
B-exclusive SOURCE support descent and all exterior SOURCE counts
conserved, also realizes the *original* outer globally indexed
canonical relation in the target, assuming injectivity of the old
outer root's TARGET coordinates. This is a target-side certificate
for the SAME replacement Q, New and flip as the source descent. -/
theorem geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior_andOldRelation
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
    (hOuterRootTargetInjective : Function.Injective
      (fun i : Fin n => f (outer.roots i))) :
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
        (geometricGlobalComplementChart Old inner).rootEmbedding
        iQ iE)
      (flip : V' → UT)
      (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
      (hFiniteNew : Finite V')
      (newOuter : GeometricFunctionalPieceData New n),
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1) ∧
      (∀ i : Fin n,
        newOuter.roots i =
          iE (⟨outer.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)) ∧
      (∀ i : Fin n,
        flip (newOuter.roots i) = f (outer.roots i)) ∧
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
          f v ∈ TargetSet})
       ∧
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn))
        (fun i : Fin n => f (outer.roots i))
 := by
  letI : Finite V := hFinite
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
      flip, hFlip, hFiniteNew, newOuter, hEAgree,
      hRootCoords, hTargetCoords, hSymbol, hRank, hExterior⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  letI : Finite V' := hFiniteNew
  have hNewRootTargetInjective :
      Function.Injective (fun i : Fin n => flip (newOuter.roots i)) := by
    intro i j hij
    apply hOuterRootTargetInjective
    calc
      f (outer.roots i) = flip (newOuter.roots i) :=
        (hTargetCoords i).symm
      _ = flip (newOuter.roots j) := hij
      _ = f (outer.roots j) := hTargetCoords j
  have hNewRelation :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn))
        (fun i : Fin n => flip (newOuter.roots i)) :=
    geometricGlobalCanonicalRelation_of_weak
      F New hFiniteNew hNew newOuter hn
      Target flip hFlip hNewRootTargetInjective
  let OldSelected : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F Old hFinite hOld outer
  let NewSelected : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F New hFiniteNew hNew newOuter
  have hClass :
      (Quotient.mk (globalFunctionalPieceSetoid F n) OldSelected :
        GlobalFunctionalPieceClass F n) =
      Quotient.mk (globalFunctionalPieceSetoid F n) NewSelected := by
    have hPair :
        (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
          OldSelected⟩ : GlobalFunctionalPieceSymbol F) =
        (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
          NewSelected⟩ : GlobalFunctionalPieceSymbol F) := by
      exact hSymbol
    exact eq_of_heq ((Sigma.mk.inj_iff.mp hPair).2)
  have hOldRelationAtNewCoordinates :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn))
        (fun i : Fin n => flip (newOuter.roots i)) := by
    obtain ⟨hChosenInj, Chosen, hChosenClass, hChosenReal⟩ :=
      (globalFunctionalCanonicalRelation_iff F Target
        (geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn)
        (fun i : Fin n => flip (newOuter.roots i))).mp hNewRelation
    apply (globalFunctionalCanonicalRelation_iff F Target
      (geometricGlobalPieceSymbol F Old
        hFinite hOld outer hn)
      (fun i : Fin n => flip (newOuter.roots i))).mpr
    refine ⟨hChosenInj, Chosen, ?_, hChosenReal⟩
    exact hChosenClass.trans hClass.symm
  have hOldCoordinates :
      (fun i : Fin n => flip (newOuter.roots i)) =
        (fun i : Fin n => f (outer.roots i)) :=
    funext hTargetCoords
  have hOriginalOuterRelation :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn))
        (fun i : Fin n => f (outer.roots i)) := by
    rw [← hOldCoordinates]
    exact hOldRelationAtNewCoordinates
  exact ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
    flip, hFlip, hFiniteNew, newOuter, hEAgree, hRootCoords,
    hTargetCoords, hSymbol, hRank, hExterior, hOriginalOuterRelation⟩

end AllThoseRamseyClasses.Lifts
