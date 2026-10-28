import AllThoseRamseyClasses.Lifts.InteriorMinimalClosedSeparatorSelection
import AllThoseRamseyClasses.Lifts.MinimumMixedAuxiliaryRootCapture
import AllThoseRamseyClasses.Lifts.InteriorAuxiliaryProperRightFlip
import AllThoseRamseyClasses.Lifts.GlobalOneSidedCollisionObstruction
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# Unconditional auxiliary-root collision OR a proper B-only flip

This isolates the exact remaining root-image issue in the genuine
2019 original-global Section 3 Claim 2, without pretending that
the weak EHN forbidden-source map is injective.

Fix any LEFT-exclusive-SOURCE-support-minimal finite connected
forbidden weak EHN witness inside an actual full native free amalgam
with a common FULL original canonical lift. Choose an arbitrary
smallest mixed geometric source piece P rooted inside the common-root
preimage S. Pick actual A-exclusive and B-exclusive source vertices
a,b in the same selected nonroot component of P.

The verified closed interior-cut selection constructs an ACTUAL
positive-width geometric separator Q separating a,b whose WHOLE
functional root lies in S ∩ P. For this automatically selected Q:

* If its ordered TARGET root images collide, we have isolated an
  explicit genuine source minimal-separator piece exhibiting the
  obstruction to the published naive HE-image injectivization.
* Otherwise, the EHN root images are injective. Minimum mixed-piece
  size forces Q.left either B-free or capturing an old P-root
  vertex. The B-free case contradicts the verified original global
  Claim 1 at the LEFT-support minimum. Old-root capture and the
  no-splitting theorem produce a genuine proper B-only sub-piece
  at ARBITRARY old-root width, and the full original common lift
  gives a literal B→A forbidden flip with strict RIGHT source
  support decrease.

Thus NO auxiliary cut, boundary partner, root-capture, root-width
restriction, or map injectivity is assumed. The output is a TRUE
disjunction: a concrete colliding piece root OR a true forbidden
B→A replacement source with strict right support drop.

This is the strongest source-geometric reduction presently known,
NOT the unrestricted strong-amalgamation conclusion. Collisions
are not eliminated, and a B→A flip may increase LEFT support.
To complete Claim 2 one needs collision repair and a repeated
contextual flip preserving genuine outer minimal-separator geometry
and its entire rooted incompatibility profile.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For EVERY minimum genuine mixed geometric source piece P of
a LEFT-support-minimal actual forbidden EHN witness in a genuine
original-global common FULL lift, an automatically selected
positive-width auxiliary source piece Q has its complete root
inside the old piece and S, and yields the following dichotomy:

1. Q's TARGET root tuple is NOT injective;
2. a genuine proper B-only geometric sub-piece can be flipped
   into a new forbidden EHN source with strictly lower RIGHT
   SOURCE support.

No injectivity assumption on S or the entire weak map. This is
a conditional *either/or* result, not a proof that (1) never happens. -/
theorem minimalLeftMixedPiece_auxiliaryCollision_or_properRightFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMinLeft : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft))
    (P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget))
    (hMinP : ∀ Q : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      P.nonrootCount ≤ Q.nonrootCount) :
    ∃ (m : ℕ) (Q : GeometricFunctionalPieceData w.source m),
      0 < m ∧
      Set.range Q.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget ∩
        geometricPieceVertices w.source P.data ∧
      (¬ Function.Injective
        (fun i : Fin m => w.toTarget (Q.roots i)) ∨
        ∃ Qright : GeometricFunctionalPieceData w.source m,
          geometricPieceVertices w.source Qright ⊂
            geometricPieceVertices w.source P.data ∧
          (∀ z : w.Carrier,
            z ∈ functionalComponentFrom w.source
              (Set.range Qright.roots) Qright.left →
            z ∉ weakFreeLeftPart
              (sL := iLeft) (iL := jLeft) w.toTarget) ∧
          ∃ (V' : Type) (New : Structure L V'),
            F New ∧
            ∃ flip : V' → UT,
              New.IsEHNHomomorphismEmbedding Target flip ∧
              Nat.card {v : V' //
                flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
              Nat.card {v : w.Carrier //
                w.toTarget v ∈ fullFreeRightExclusiveTarget
                  iRight jRight}) := by
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  obtain ⟨a, haOld, haA⟩ := P.left_mixed
  obtain ⟨b, hbOld, hbB⟩ := P.right_mixed
  let aS : {v : w.Carrier // v ∉ S} := ⟨a, haA.2⟩
  let bS : {v : w.Carrier // v ∉ S} := ⟨b, hbB.2⟩
  have hSclosed : w.source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft)
      w.toTarget w.homEmbedding.1
  have hSeparated : ¬ ReachOutside w.source.graph S aS bS :=
    weakFreePartition_root_separates_exclusive
      hFree w.toTarget w.homEmbedding.1 haA hbB
  have hConnectedPath : ReachOutside w.source.graph
      (∅ : Set w.Carrier)
      (⟨a, by simp⟩ : {v : w.Carrier // v ∉ ∅})
      (⟨b, by simp⟩ : {v : w.Carrier // v ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 a b)
  obtain ⟨m, Q, hm, hInside, hQL, hQR⟩ :=
    finite_geometricPiece_selectPositiveInteriorCut
      w.source P.data S hSclosed P.roots_in_common
      aS bS haOld hSeparated hConnectedPath
  refine ⟨m, Q, hm, hInside, ?_⟩
  have hRootsS : Set.range Q.roots ⊆ S := by
    intro z hz
    exact (hInside hz).1
  have hRootsP :
      Set.range Q.roots ⊆ geometricPieceVertices w.source P.data := by
    intro z hz
    exact (hInside hz).2
  have hQA : Q.left.1 ∈ AOnly := by
    rw [hQL]
    exact haA
  have hQB : Q.right.1 ∈ BOnly := by
    rw [hQR]
    exact hbB
  have hQleftOld :
      Q.left.1 ∈ functionalComponentFrom w.source
        (Set.range P.data.roots) P.data.left := by
    rw [hQL]
    exact haOld
  have hQrightOld :
      Q.right.1 ∈ functionalComponentFrom w.source
        (Set.range P.data.roots) P.data.left := by
    rw [hQR]
    exact hbOld
  by_cases hRootInjective :
      Function.Injective (fun i : Fin m => w.toTarget (Q.roots i))
  · rcases minimumMixed_auxiliaryLeft_oneSided_or_oldRootCapture
        w.source S AOnly BOnly P hMinP Q hm
        hRootsS hQleftOld hQrightOld hQA with
      hOneSided | hCaptured
    · have hFalse : False :=
        minimalGlobalWitness_noOneSidedPiece_of_rootInjective
          F hFiniteF Target Left Right jLeft jRight
          X iLeft iRight hFree hCommon w hMinLeft
          Q hm hRootsS hOneSided hQA hRootInjective
      exact False.elim hFalse
    · obtain ⟨Qright, hProper, hNoLeft,
        V', New, hNew, flip, hFlip, hStrict⟩ :=
        minimalMixedInteriorRootCapture_hasProperRightFlip
          F hFiniteF Target Left Right jLeft jRight
          X iLeft iRight hFree hCommon w P hMinP
          Q hm hCaptured hRootsS hRootsP
          hQleftOld hQrightOld hQB hRootInjective
      exact Or.inr ⟨Qright, hProper, hNoLeft,
        V', New, hNew, flip, hFlip, hStrict⟩
  · exact Or.inl hRootInjective

end AllThoseRamseyClasses.Lifts
