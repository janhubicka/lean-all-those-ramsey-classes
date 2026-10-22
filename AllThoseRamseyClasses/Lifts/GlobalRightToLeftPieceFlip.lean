import AllThoseRamseyClasses.Lifts.GeometricPieceRightFactor
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates
import AllThoseRamseyClasses.Lifts.CommonFullGlobalPieceFlip

/-!
# Actual right-to-left flip of a one-sided geometric forbidden piece

The certified original 2019 quotient-indexed global-lift flip
was written from the left witness into the right witness.
The paper's Claim 2 also needs the OPPOSITE direction when
a genuine B-only sub-piece is eliminated.

For a real finite forbidden source with an actual positive-width
minimal function-closed separator piece, suppose its ordered
target root images are injective, its root lies in the common
full functional seam, and its selected component has NO
left-exclusive vertex. The previously verified geometric
right-factorization constructs a weak EHN map of the entire
piece into Right, including all original function fibres.
Recover the exact root coordinates and then apply the original
global full-lift flip with its two full witness sides exchanged.

This constructs a literal forbidden replacement source, a
genuine full native functional free-amalgam diagram, and an
EHN map to the SAME target. Its new piece is mapped into Left;
the map is EXACTLY unchanged on the old complementary side.

The proof assumes a common FULL global canonical lifted root,
a genuine free-amalgam target, positive root width, and injective
TARGET root images; these do NOT follow automatically from
arbitrary weak HE maps. Nothing here proves the remaining
multicomponent minimality descent or unrestricted shadow avoidance.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- An actual B-only forbidden geometric source piece can be
flipped from the RIGHT witness into the LEFT witness of the
same native functional free amalgam, provided its root tuple
has injective target images and the witnesses have their
required common FULL original canonical lift.

The new forbidden source is real (not an incidence-generated
weak image) and the old complement map remains literal.
No global injectivity of the original forbidden-source map. -/
theorem geometricGlobalCommonFullLiftFlip_rightToLeft
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
  obtain ⟨Q, hEq, g, hg, _hRootQ,
      V', New, hNew, iQ, iT, hNewFree,
      flip, hFlip, hQImage, hTImage⟩ :=
    geometricGlobalCommonFullLiftFlip
      F Forbidden hFinite hForbidden d hn
      Target f hf
      Right Left jRight jLeft
      X iRight iLeft
      hCommonSwapped hTargetAgreeR
      pRight hpRight' hPieceMap' xsX hRootRight hRootInjective
  exact ⟨Q, hEq, g, hg, V', New, hNew,
    iQ, iT, hNewFree, flip, hFlip, hQImage, hTImage⟩

end AllThoseRamseyClasses.Lifts
