import AllThoseRamseyClasses.Lifts.GeometricPieceRightFactor
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates
import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport

/-!
# Actual strict RIGHT-exclusive source-support drop under a B-to-A flip

The 2019 Claim 2 proof repeatedly attempts to eliminate B-only
components from a globally smallest mixed geometric source piece.

The already checked common-full-lift flip strictly decreases
LEFT-exclusive source support when a genuine A-only one-sided
piece is moved to B. Its theorem applies symmetrically:

* Use the verified full right-side EHN factorization for a
  genuine one-sided source geometric piece.
* Swap the two original full witness embeddings and their
  shared full canonical lifted root (no assumption that only
  the old shadows agree).
* Invoke the already certified exact support-counting flip,
  with its "left" role played by the ORIGINAL RIGHT side.

The result is a literal new member of the forbidden family
with a native EHN target map whose number of SOURCE vertices
mapped to the ORIGINAL B-exclusive region is strictly smaller.
No source map is assumed globally injective. Only the selected
ordered ROOT images are assumed injective.

This gives a genuine natural-number decreasing parameter for
SUCCESSFUL B-to-A flips, not a proof that every B-component
admits such a flip or that the selected mixed piece remains
minimal under repeated flips. The original Section 3 theorem
is still open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- The exact exclusive-RIGHT target region in an original
functional amalgam, expressed using the existing symmetric
exclusive-side definition. -/
def fullFreeRightExclusiveTarget
    {UX UB UT : Type}
    {X : Structure L UX} {Right : Structure L UB}
    {Target : Structure L UT}
    (iRight : Structure.Embedding X Right)
    (jRight : Structure.Embedding Right Target) : Set UT :=
  fullFreeLeftExclusiveTarget iRight jRight

/-- An actual successful B-to-A flip of a positive-width
genuine forbidden geometric piece strictly decreases the
number of SOURCE vertices mapped into B minus the common
full root, even when the original source-to-target map
has collisions outside the selected injective ROOT.

The NEW forbidden source may have a different carrier type.
This is source-cardinality descent, not a statement that
all target-image vertices were distinct. -/
theorem geometricGlobalCommonFullLiftFlip_strict_rightSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
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
    (hRootImageInjective : Function.Injective
      (fun i : Fin n => f (d.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ flip : V' → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {v : V' //
          flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
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
  have hvRightSwapped :
      oldVertex ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hvRight.1, ?_⟩
    intro hRootR
    obtain ⟨x, hx⟩ := hRootR
    apply hvRight.2
    exact ⟨x, (hTargetAgreeR x).symm.trans hx⟩
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
  exact geometricGlobalCommonFullLiftFlip_strict_leftSupport
    F hFiniteF Forbidden hFinite hForbidden d hn
    Target f hf
    Right Left jRight jLeft
    X iRight iLeft hFree.swap hCommonSwapped
    pRight hpRight' hPieceMap' xsX hRootRight
    hRootImageInjective oldVertex hvComponent hvRightSwapped

end AllThoseRamseyClasses.Lifts
