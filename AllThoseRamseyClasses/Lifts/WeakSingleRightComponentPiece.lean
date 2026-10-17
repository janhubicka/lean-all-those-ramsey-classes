import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart
import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy

/-!
# A genuine one-sided forbidden piece when the opposite region is connected

The first minimality claim in the 2019 lift argument needs a genuine
minimal-separator piece whose selected component maps entirely into
one ambient free-amalgam side. Arbitrary minimal separators for one
left and one right source vertex do NOT automatically have this
property: their component can meet other opposite-side components.

Here is a useful exact special case. Suppose ALL right-exclusive
source vertices lie in ONE Gaifman component after deleting the
function-closed common-root preimage S. A minimal closed separator
R ⊆ S between a chosen left and right vertex has its selected
left component disjoint from the ENTIRE right-exclusive region.
Otherwise a Gaifman path from that right vertex to the chosen right
root survives the smaller deleted cut R, contradicting separation.

Thus the actual left geometric piece maps wholly to the left
ambient side, with a genuine EHN weak piece factorization when the
original map is a homomorphism-embedding. This is a mathematically
substantive SPECIAL CASE of Claim 1, not the general case with
several opposite-side components, which requires further geometry.
No weak-map injectivity is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- If every right-exclusive vertex is joined to the chosen right
witness by a path avoiding the common-root preimage, then the
minimal-cut piece on the left side obtained from the weak source
partition has no right-exclusive vertex in its chosen component. -/
theorem weakFreePartition_leftOnlyPiece_of_rightConnected
    [Finite U]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    (x y : U)
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (hAllRight : ∀ z : U,
      (hz : z ∈ weakFreeRightPart
        (sL := sL) (iL := iL) (iR := iR) f) →
      ReachOutside Source.graph
        (weakFreeRootPart (sL := sL) (iL := iL) f)
        ⟨y, hy.2⟩ ⟨z, hz.2⟩) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      Set.range d.roots ⊆
        weakFreeRootPart (sL := sL) (iL := iL) f ∧
      d.left.1 = x ∧ d.right.1 = y ∧
      ∀ z : U,
        z ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left →
        z ∉ weakFreeRightPart
          (sL := sL) (iL := iL) (iR := iR) f := by
  obtain ⟨n, d, hRoots, hLeft, hRight⟩ :=
    weakFreePartition_hasMinimalGeometricChart
      hfree f hf x y hx hy
  refine ⟨n, d, hRoots, hLeft, hRight, ?_⟩
  intro z hzComponent hzRight
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  let R : Set U := Set.range d.roots
  let yS : {z : U // z ∉ S} := ⟨y, hy.2⟩
  let zS : {v : U // v ∉ S} := ⟨z, hzRight.2⟩
  have hPath :
      ReachOutside Source.graph R
        (outsideCutMap hRoots yS)
        (outsideCutMap hRoots zS) :=
    reachOutside_of_cut_subset
      Source.graph hRoots yS zS (hAllRight z hzRight)
  have hY : d.right = outsideCutMap hRoots yS := by
    apply Subtype.ext
    exact hRight
  have hZ :
      (⟨z, hzComponent.1⟩ : {v : U // v ∉ R}) =
        outsideCutMap hRoots zS := by
    apply Subtype.ext
    rfl
  have hPathRight :
      ReachOutside Source.graph R
        d.right ⟨z, hzComponent.1⟩ := by
    rw [hY, hZ]
    exact hPath
  have hPathLeftRight :
      ReachOutside Source.graph R d.left d.right :=
    hzComponent.2.trans (reachOutside_symm
      Source.graph R hPathRight)
  exact d.minimal.2.1 hPathLeftRight

/-- Consequently the genuine minimal geometric LEFT piece weakly
factors through the FULL left target side whenever the original
forbidden-source map is EHN. This is valid even when all root images
collide; it is purely a side-containment/geometry theorem. -/
theorem weakFreePartition_leftFactor_of_rightConnected
    [Finite U]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x y : U)
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (hAllRight : ∀ z : U,
      (hz : z ∈ weakFreeRightPart
        (sL := sL) (iL := iL) (iR := iR) f) →
      ReachOutside Source.graph
        (weakFreeRootPart (sL := sL) (iL := iL) f)
        ⟨y, hy.2⟩ ⟨z, hz.2⟩) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      Set.range d.roots ⊆
        weakFreeRootPart (sL := sL) (iL := iL) f ∧
      d.left.1 = x ∧ d.right.1 = y ∧
      ∃ pLeft : geometricPieceVertices Source d → E,
        (geometricFunctionalPiece Source d).IsEHNHomomorphismEmbedding
          Left pLeft ∧
        ∀ z, iL (pLeft z) = f z.1 := by
  obtain ⟨n, d, hRoots, hLeft, hRight, hNoRight⟩ :=
    weakFreePartition_leftOnlyPiece_of_rightConnected
      hfree f hf.1 x y hx hy hAllRight
  obtain ⟨pLeft, hMap, hAgree⟩ :=
    weakGeometricPiece_factor_left_if_no_right
      hfree f hf d hRoots hNoRight
  exact ⟨n, d, hRoots, hLeft, hRight,
    pLeft, hMap, hAgree⟩

end AllThoseRamseyClasses.Lifts
