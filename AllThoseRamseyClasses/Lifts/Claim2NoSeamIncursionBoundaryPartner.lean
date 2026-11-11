import AllThoseRamseyClasses.Lifts.UncoveredMinimalMixedOldRootLoss
import AllThoseRamseyClasses.Lifts.FunctionalGaifmanCuts

/-!
# Track C: the precise seam-incursion obstruction to a matched boundary

At a minimal genuinely mixed old geometric piece P, suppose a B-only
component has generated boundary T in the full common-root preimage S
and an actual opposite A-only component is chosen outside T.

The verified uncovered-boundary theorem constructs a smaller-root mixed
piece, but proves that its selected component captures an old P-root.
Since every original P-root lies in S, a STRICTLY smaller rooted mixed
piece necessarily has an INTERNAL common-seam vertex. This is precisely
why the source-minus-S monochromaticity argument cannot automatically be
reapplied after shrinking the geometric root.

The theorem below is a restricted consequence: if every potential
strictly smaller-root chart avoids introducing S inside its selected
nonroot component, there is NO uncovered alternative, and the two FULL
function-generated opposite boundaries agree.

The no-seam-incursion hypothesis is *not* proved generally, and may
fail. This is not an unrestricted Claim 2 successor or a solution
to weak EHN target-root collisions. Source vertices, never weak target
images, are tracked.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuinely minimal mixed old piece cannot have an uncovered right
boundary without a smaller-root mixed piece swallowing an old root,
which is necessarily a vertex of the original common seam S.

Consequently, if every strictly smaller chart with root inside T has a
selected component disjoint from S, the opposite generated boundary
equals T. This obtains an actual complete boundary partner for general
root width, *conditional* on the stated seam-cleanliness hypothesis.
No assertion of image-injectivity or of a subsequent source flip. -/
theorem minimalLeftWitness_noSeamIncursion_forces_matchingBoundary
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
      P.nonrootCount ≤ Q.nonrootCount)
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hxOld : x.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (y : {z : w.Carrier // z ∉ T})
    (hyLeft : y.1 ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (hyOld : y.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left)
    (hNoSeamIncursion :
      ∀ (m : ℕ) (d : GeometricFunctionalPieceData w.source m),
        Set.range d.roots ⊂ T →
        ∀ r : w.Carrier,
          r ∈ weakFreeRootPart
            (sL := iLeft) (iL := jLeft) w.toTarget →
          r ∉ functionalComponentFrom w.source
            (Set.range d.roots) d.left) :
    w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y)) = T := by
  classical
  let U : Set w.Carrier :=
    w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y))
  have hTclosed : w.source.IsClosed T := by
    rw [hT]
    exact w.source.functionClosure_isClosed
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x))
  have hUsub : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut
      w.source T hTclosed y
  have hTsub : T ⊆ U := by
    by_contra hUncovered
    obtain ⟨m, d, r, _hm, _hExactRoot, hProperRoot, _hRootInside,
      _hLeft, _hRight, hrOldRoot, hrCaptured, _hrNotNewRoot⟩ :=
      minimalLeftWitness_uncoveredInsideMinimalMixed_losesOldRoot
        F hFiniteF hConnected
        Target Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        w hMinLeft hInjOnRoot P hMinP
        x hxRight hxOld T hT hTS y hyLeft hyOld hUncovered
    have hrSeam : r ∈ weakFreeRootPart
        (sL := iLeft) (iL := jLeft) w.toTarget :=
      P.roots_in_common hrOldRoot
    exact (hNoSeamIncursion m d hProperRoot r hrSeam) hrCaptured
  exact Set.Subset.antisymm hUsub hTsub

end AllThoseRamseyClasses.Lifts
