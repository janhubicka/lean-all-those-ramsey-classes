import AllThoseRamseyClasses.Lifts.InteriorMinimalClosedSeparatorSelection
import AllThoseRamseyClasses.Lifts.MinimumMixedAuxiliaryRootCapture
import AllThoseRamseyClasses.Lifts.InteriorAuxiliaryProperRightFlip
import AllThoseRamseyClasses.Lifts.GlobalOneSidedCollisionObstruction
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# Every minimum mixed piece has a genuine proper B-only flip (root-injective case)

This completes a substantial SOURCE-GEOMETRIC portion of the printed
Section 3 Claim 2 without a preselected auxiliary cut, a boundary
partner, a singleton/clique old root, or a postulated old-root capture.

Take a finite connected forbidden weak EHN source at a minimum of
LEFT-exclusive SOURCE support, with the original common FULL canonical
lift on the two free-amalgam sides. Suppose the source weak map is
injective ONLY on the preimage S of their common root. Choose ANY
smallest genuinely mixed geometric source piece P rooted inside S.

1. Select A-exclusive and B-exclusive source vertices a,b from the
   same selected component of P; they are S-separated by the actual
   free-amalgam witness, but connected in the full forbidden source.
2. The verified closed interior-cut selection produces an ACTUAL
   positive-width geometric piece Q separating a,b whose whole
   function-closed root lies in S and in the old piece P.
3. Minimum mixed-piece size forces Q.left either to be B-free or
   to capture an old root vertex (verified auxiliary dichotomy).
4. The B-free alternative contradicts the already verified original
   global Claim 1: Q has an A-exclusive selected vertex and its
   ORDERED target root image is injective by the stated InjOn S.
5. Old-root capture, plus the verified opposite exterior-boundary
   no-split theorem, gives a genuine PROPER B-only sub-piece
   (including its entire native closed root), even for arbitrary
   reducible old-root width.
6. The original FULL quotient-indexed canonical lift executes a
   literal B-to-A forbidden-source flip, strictly lowering GLOBAL
   right-exclusive SOURCE support without injecting the whole
   forbidden EHN map.

This removes the separate auxiliary-cut/root-capture assumptions
of #677 under InjOn S. It does NOT prove that the resulting
transported outer context remains a genuine minimum mixed piece,
nor that one can iterate B-only flips while preserving the complete
rooted incompatibility profile. A successful B-to-A flip may
INCREASE LEFT-exclusive support, so its RIGHT support drop alone
cannot contradict the original LEFT-support minimization.
Also, arbitrary EHN maps need not be InjOn S in the printed theorem;
that collision case remains unresolved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- **One-step source-geometric Claim 2 at arbitrary old-root width.**

For every globally smallest mixed genuine source piece P in a
LEFT-support-minimal forbidden weak witness, assuming ONLY injectivity
on the exact full common-root PREIMAGE S, there is an ACTUAL
proper B-only geometric sub-piece and a literal B-to-A forbidden
replacement weak witness with strictly lower RIGHT-exclusive
SOURCE support.

There is no auxiliary separator, root-capture, boundary partner,
root-width, or additional flip-availability premise. The new
forbidden map may be noninjective away from the root preimage. -/
theorem minimalLeftMixedPiece_hasProperRightFlip_of_rootInjOn
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
    (hInjOnRoot : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
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
    ∃ (m : ℕ) (Qright : GeometricFunctionalPieceData w.source m),
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
              iRight jRight} := by
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
  have hRootInj : Function.Injective
      (fun i : Fin m => w.toTarget (Q.roots i)) := by
    intro i j hij
    apply Q.roots_injective
    exact hInjOnRoot
      (hRootsS ⟨i, rfl⟩) (hRootsS ⟨j, rfl⟩) hij
  rcases minimumMixed_auxiliaryLeft_oneSided_or_oldRootCapture
      w.source S AOnly BOnly P hMinP Q hm
      hRootsS hQleftOld hQrightOld hQA with
    hOneSided | hCaptured
  · have hContradiction : False :=
      minimalGlobalWitness_noOneSidedPiece_of_rootInjective
        F hFiniteF Target Left Right jLeft jRight
        X iLeft iRight hFree hCommon w hMinLeft
        Q hm hRootsS hOneSided hQA hRootInj
    exact False.elim hContradiction
  · obtain ⟨Qright, hProper, hNoLeft,
      V', New, hNew, flip, hFlip, hStrict⟩ :=
      minimalMixedInteriorRootCapture_hasProperRightFlip
        F hFiniteF Target Left Right jLeft jRight
        X iLeft iRight hFree hCommon w P hMinP
        Q hm hCaptured hRootsS hRootsP
        hQleftOld hQrightOld hQB hRootInj
    exact ⟨m, Qright, hProper, hNoLeft,
      V', New, hNew, flip, hFlip, hStrict⟩

end AllThoseRamseyClasses.Lifts
