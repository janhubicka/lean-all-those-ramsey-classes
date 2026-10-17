import AllThoseRamseyClasses.Lifts.WeakSingleRightComponentPiece
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates
import AllThoseRamseyClasses.Lifts.FoldedCommonFlipStrictSupport

/-!
# First minimality contradiction when the opposite exclusive region is connected

This theorem assembles the already proved noninjective geometry into
the auxiliary FOLDED global piece-lift flip:
* a connected source pair mapped to opposite exclusive sides gives a
  positive-width minimal CLOSED separator contained in the root preimage;
* if all right-exclusive source vertices are connected in the
  complement of that root preimage, the chosen left component contains
  no right-exclusive vertices, so the FULL selected left piece has a
  genuine weak EHN factorization through the left witness;
* its ordered common-root coordinate tuple is automatically recovered
  from the complete embeddings of X and Left, even if the weak
  forbidden-source map identifies several source roots;
* the conditional common-folded-lift flip produces a literal forbidden
  replacement source, preserving the old complement map exactly,
  with strictly fewer left-exclusive SOURCE vertices.

The hypotheses still include a common FULL FOLDED lifted X and the
single-right-component condition. Neither follows in the general
published Section 3 theorem; no strong-amalgamation theorem is
asserted. There is NO root-image or global-map injectivity hypothesis.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine, conditional, noninjective Claim 1 for the auxiliary
folded lift, in the important case when the opposite right-exclusive
source region has a single Gaifman component outside the root preimage.

The selected geometric piece, its positive root width, its weak EHN
factorization into Left and its ordered X-root coordinates are
constructed, rather than assumed as separate flip prerequisites. -/
theorem foldedFirstMinimality_of_connectedRightRegion
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonFoldedGlobalCanonicalLift
      F X Left Right iLeft iRight)
    (x y : V)
    (hx : x ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hy : y ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hConnected : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y, by simp⟩ : {z : V // z ∉ ∅}))
    (hAllRight : ∀ z : V,
      (hz : z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f) →
      ReachOutside Forbidden.graph
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
        ⟨y, hy.2⟩ ⟨z, hz.2⟩) :
    ∃ (W : Type) (New : Structure L W),
      F New ∧
      ∃ flip : W → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {w : W //
          flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
        Nat.card {v : V //
          f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  letI : Finite V := hFinite
  obtain ⟨n, d, hRoots, hLeft, hRight,
      pLeft, hpLeft, hPieceMap⟩ :=
    weakFreePartition_leftFactor_of_rightConnected
      hTargetFree f hf x y hx hy hAllRight
  have hPathD : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨d.left.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    simpa only [hLeft, hRight] using hConnected
  have hn : 0 < n :=
    geometricPiece_positiveWidth_of_emptyCut_path
      Forbidden d hPathD
  have hPieceMap' :
      ∀ z : (geometricGlobalFunctionalChart Forbidden d).ext.Carrier,
        jLeft (pLeft z) = f z.1 := hPieceMap
  have hpLeft' :
      (geometricGlobalFunctionalChart Forbidden d).ext.str.IsEHNHomomorphismEmbedding
        Left pLeft := hpLeft
  obtain ⟨xsX, hRootLeft⟩ :=
    geometricPiece_commonRootCoordinates
      Forbidden d Target f X Left iLeft jLeft
      pLeft hPieceMap' hRoots
  have hComponent :
      x ∈ functionalComponentFrom Forbidden (Set.range d.roots) d.left := by
    rw [← hLeft]
    exact functionalComponentFrom_root Forbidden (Set.range d.roots) d.left
  exact geometricFoldedCommonFullLiftFlip_strict_leftSupport
    F hFiniteF Forbidden hFinite hForbidden d hn
    Target f hf Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon
    pLeft hpLeft' hPieceMap' xsX hRootLeft
    x hComponent hx

end AllThoseRamseyClasses.Lifts
