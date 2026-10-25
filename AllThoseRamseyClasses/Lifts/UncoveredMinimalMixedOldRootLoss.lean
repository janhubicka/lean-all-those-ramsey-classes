import AllThoseRamseyClasses.Lifts.RootRetentionLocalization
import AllThoseRamseyClasses.Lifts.MinimalLeftUncoveredMixedPiece
import AllThoseRamseyClasses.Lifts.BoundaryPartnerProperSubpiece

/-!
# At a smallest mixed source piece, uncovered-boundary descent LOSES an old root

The original Claim 2 chooses an outer genuine mixed piece P of
minimum NONROOT component size. The recently verified left-support
minimality lemma constructs a NEW mixed source piece Q when the
generated boundary of a right-only component B is not covered
by an opposite left component. Q's root is EXACTLY the generated boundary U of the opposite
component after deleting T=Cl(N(B)), and U is strictly inside T.

When B occurs in P's original selected component, native
closed-component geometry proves T lies inside the FULL old
piece P (including the complete old root). Both Q
distinguished vertices are already in P's old component.

The independent root-retention localization theorem now has
a sharp consequence: Q MUST LOSE at least one original P-root
vertex. Otherwise retaining all old roots would make Q a
genuine proper sub-piece with strictly fewer nonroot vertices,
contradicting the choice of P.

The captured old-root vertex is returned inside Q's selected
nonroot component and OUTSIDE the complete opposite-component
generated boundary U. This makes its precise coverage defect
explicit, without proving that such a defect is impossible.
This is a positive necessary obstruction for the original
Claim 2, NOT a claim that the full canonical lift prevents
the loss of that vertex. Old-root retention remains the
essential missing step for unrestricted strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In a finite connected forbidden weak EHN source, assume
the original LEFT-support minimum, root-preimage injectivity,
and a genuinely smallest mixed old piece P.

If a right-only S-component B inside P has an uncovered
generated boundary T, and the chosen opposite LEFT source
vertex y also belongs to P, the checked construction produces
a smaller-root genuine mixed piece Q with its root still
INSIDE P. The new piece NECESSARILY omits an actual vertex
of P's old separating root.

This distinguishes a strict reduction of root width from the
strict NONROOT-component-size reduction required by the paper. -/
theorem minimalLeftWitness_uncoveredInsideMinimalMixed_losesOldRoot
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
    (hUncovered : ¬ T ⊆ w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y))) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n)
      (r : w.Carrier),
      0 < n ∧
      Set.range d.roots = w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph T y)) ∧
      Set.range d.roots ⊂ T ∧
      Set.range d.roots ⊆ geometricPieceVertices w.source P.data ∧
      d.left.1 = y.1 ∧ d.right.1 = x.1 ∧
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left ∧
      r ∉ w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph T y)) := by
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  obtain ⟨n, d, hn, hQrootExact, hQrootT, hQleft, hQright,
      z, hzComponent, hzRight⟩ :=
    minimalLeftWitness_uncoveredBoundary_hasSmallerRootMixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      w hMinLeft hInjOnRoot
      x hxRight T hT hTS y hyLeft hUncovered
  have hTinside :
      T ⊆ geometricPieceVertices w.source P.data := by
    rw [hT]
    exact componentBoundaryClosure_inside_geometricPiece
      w.source P.data S P.roots_in_common x hxOld
  have hNewRootInside :
      Set.range d.roots ⊆ geometricPieceVertices w.source P.data :=
    hQrootT.subset.trans hTinside
  have hNewRootS : Set.range d.roots ⊆ S :=
    hQrootT.subset.trans hTS
  have hNewLeft : d.left.1 ∈ AOnly := by
    rw [hQleft]
    exact hyLeft
  let Q : MixedGeometricPiece w.source S AOnly BOnly := {
    width := n
    data := d
    positive := hn
    roots_in_common := hNewRootS
    left_mixed := ⟨d.left.1,
      functionalComponentFrom_root w.source (Set.range d.roots) d.left,
      hNewLeft⟩
    right_mixed := ⟨z, hzComponent, hzRight⟩
  }
  have hLeftOld : Q.data.left.1 ∈
      functionalComponentFrom w.source
        (Set.range P.data.roots) P.data.left := by
    change d.left.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left
    rw [hQleft]
    exact hyOld
  have hRightOld : Q.data.right.1 ∈
      functionalComponentFrom w.source
        (Set.range P.data.roots) P.data.left := by
    change d.right.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left
    rw [hQright]
    exact hxOld
  obtain ⟨r, hrOld, hrCaptured⟩ :=
    minimalMixedPiece_otherMixed_capturesOldRoot
      w.source S AOnly BOnly P Q hMinP hLeftOld hRightOld
  have hrUncovered :
      r ∉ w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph T y)) := by
    intro hrU
    exact hrCaptured.1 (by
      rw [hQrootExact]
      exact hrU)
  exact ⟨n, d, r, hn, hQrootExact, hQrootT,
    hNewRootInside, hQleft, hQright, hrOld,
    hrCaptured, hrUncovered⟩

end AllThoseRamseyClasses.Lifts
