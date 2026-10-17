import AllThoseRamseyClasses.Lifts.FoldedGeneralFirstMinimality
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# Genuine positive-width mixed forbidden piece in a minimum folded witness

Combining the closed-root/Gaifman separator construction with the
general first minimality claim for a shared auxiliary FOLDED lift:
any actual finite forbidden weak EHN witness minimizing A-only
SOURCE support, whose source contains an A-only and a B-only
vertex joined by a Gaifman path, contains a genuine
positive-width minimal CLOSED separator piece rooted entirely
inside the inverse image of the common root, with selected
component meeting BOTH exclusive source regions.

This proves the existence premise of the printed Section 3
"Choose P' minimal mixed non-root vertices" step in the auxiliary
folded setting, with no source map/root-image injectivity.

The output includes membership in the ACTUAL forbidden piece
family, rather than an arbitrary rooted candidate. Selection
of the SMALLEST eligible piece is a separate finite minimum
lemma, and the proper-subpiece contradiction (Claim 2) remains
unproved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A finite minimum-support forbidden weak witness under a
common full FOLDED lift and a connected crossing source pair
contains a positive-width TRUE mixed forbidden geometric piece.
Its root lies entirely in the exact common-root preimage; its
selected nonroot component contains both an A-only vertex and
a B-only vertex, even if the B-only part has many components. -/
theorem minimalFoldedForbiddenWitness_has_mixed_piece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonFoldedGlobalCanonicalLift
      F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMinimal : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft))
    (x y : w.Carrier)
    (hx : x ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (hy : y ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight)
      w.toTarget)
    (hConnected : ReachOutside w.source.graph
      (∅ : Set w.Carrier)
      (⟨x, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨y, by simp⟩ : {z : w.Carrier // z ∉ ∅})) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n),
      0 < n ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft)
          w.toTarget ∧
      d.left.1 = x ∧ d.right.1 = y ∧
      x ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left ∧
      (∃ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range d.roots) d.left ∧
        z ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight)
          w.toTarget) ∧
      geometricFunctionalRootedPattern w.source d ∈
        forbiddenGeometricFunctionalPieces F n := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  obtain ⟨n, d, hn, hRoots, hLeft, hRight, hMember⟩ :=
    weakFreePartition_hasPositiveForbiddenGeometricPiece
      F w.forbidden hFree w.toTarget
      w.homEmbedding.1 x y hx hy hConnected
  have hxComponent :
      x ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left := by
    rw [← hLeft]
    exact functionalComponentFrom_root
      w.source (Set.range d.roots) d.left
  have hRightInComponent :
      ∃ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range d.roots) d.left ∧
        z ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight)
          w.toTarget :=
    minimalFoldedForbiddenWitness_piece_meets_right
      F hFiniteF Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      w hMinimal d hn hRoots x hxComponent hx
  exact ⟨n, d, hn, hRoots, hLeft, hRight,
    hxComponent, hRightInComponent, hMember⟩

end AllThoseRamseyClasses.Lifts
