import AllThoseRamseyClasses.Lifts.GlobalSharedSelectedGeometricFlip
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftPieceFlip

/-!
# Same selected geometric Q for one original B-only -> A source flip

The right-to-left FULL common-lift flip must retain its exact
genuinely selected Q witness, not merely a profile-equivalent
root extension. This is the one and the same literal new forbidden
source and weak map used by the original right-to-left flip.

This supplies the essential selected-Q connectivity and boundary
premise to the future one-witness local right-support decrease
and actual outer geometric context identification.
The two distinguished original roots need not be nested.

No support-count decrease or arbitrary weak-image injection
is asserted here; the existing strict support proof can consume
this exact same flip certificate. The source is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A genuine B-only source-piece flip from a common FULL lift,
retaining its selected-geometric witness on the SAME new Q. -/
theorem geometricGlobalCommonFullLiftFlip_rightToLeft_selected
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (d : GeometricFunctionalPieceData Forbidden n) (hn : 0 < n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hRootInjective : Function.Injective
      (fun i : Fin n => f (d.roots i))) :
    let P := geometricGlobalSelectedChart F Forbidden
      hFinite hForbidden d
    let T := geometricGlobalComplementChart Forbidden d
    ∃ Q : FunctionalRootExtension P.1.root,
      (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
      (FunctionalRootExtension.toEnumeratedRootedPattern
        P.1.root (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n ∧
      ∃ g : Q.Carrier → UA,
        Q.str.IsEHNHomomorphismEmbedding Left g ∧
        ∃ (V' : Type) (New : Structure L V'),
          F New ∧
          ∃ (iQ : Structure.Embedding Q.str New)
            (iT : Structure.Embedding T.str New),
            Structure.IsFreeAmalgam Q.rootEmbedding T.rootEmbedding
              iQ iT ∧
            ∃ flip : V' → UT,
              New.IsEHNHomomorphismEmbedding Target flip ∧
              (∀ a : Q.Carrier, flip (iQ a) = jLeft (g a)) ∧
              (∀ b : T.Carrier, flip (iT b) = f b.1) := by
  have hTargetAgreeR : ∀ x : UX,
      jRight (iRight x) = jLeft (iLeft x) := by
    intro x
    exact ((hFree.overlap (iLeft x) (iRight x)).mpr
      ⟨x, rfl, rfl⟩).symm
  have hRootsRight : Set.range d.roots ⊆
      weakFreeRootPart (sL := iRight) (iL := jRight) f := by
    intro z hz
    obtain ⟨x, hx⟩ := hRoots hz
    exact ⟨x, (hTargetAgreeR x).trans hx⟩
  let hCommonSwapped :
      CommonGlobalCanonicalLift F X Right Left iRight iLeft := {
    lifted := hCommon.lifted
    shadow_eq := hCommon.shadow_eq
    intoA := hCommon.intoB
    intoB := hCommon.intoA
    intoA_verts := hCommon.intoB_verts
    intoB_verts := hCommon.intoA_verts
  }
  obtain ⟨pRight, hpRight, hPieceMap⟩ :=
    weakGeometricPiece_factor_right_if_no_left
      hFree f hf d hRoots hNoLeft
  have hpRight' : Structure.IsEHNHomomorphismEmbedding
      ((geometricGlobalFunctionalChart Forbidden d).ext.str)
      Right pRight := hpRight
  have hPieceMap' : ∀ z :
      (geometricGlobalFunctionalChart Forbidden d).ext.Carrier,
      jRight (pRight z) = f z.1 := hPieceMap
  obtain ⟨xsX, hRootRight⟩ :=
    geometricPiece_commonRootCoordinates
      Forbidden d Target f X Right
      iRight jRight pRight hPieceMap' hRootsRight
  obtain ⟨Q, hEq, hSelected, g, hg, _hRootQ,
      V', New, hNew, iQ, iT, hNewFree,
      flip, hFlip, hQImage, hTImage⟩ :=
    geometricGlobalSharedLiftFlip_selected
      F Forbidden hFinite hForbidden d hn
      Target f hf
      Right Left jRight jLeft
      X iRight iLeft
      (hCommonSwapped.agreeOn F) hTargetAgreeR
      pRight hpRight' hPieceMap' xsX hRootRight hRootInjective
  exact ⟨Q, hEq, hSelected, g, hg, V', New, hNew,
    iQ, iT, hNewFree, flip, hFlip, hQImage, hTImage⟩

end AllThoseRamseyClasses.Lifts
