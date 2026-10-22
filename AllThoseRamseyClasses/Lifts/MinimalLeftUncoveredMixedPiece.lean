import AllThoseRamseyClasses.Lifts.UncoveredBoundarySmallerRootPiece
import AllThoseRamseyClasses.Lifts.WeakRightBoundaryCoverage
import AllThoseRamseyClasses.Lifts.GlobalOriginalClaim1OneSided
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# A missing opposite boundary at a LEFT-support minimum forces a smaller-root MIXED piece

There is a useful interaction between two independently checked
parts of the printed Section 3 proof:

* A failure of generated boundary coverage produces an ACTUAL
  positive-width minimal-separator source piece rooted strictly
  inside the original generated right-component boundary T.
* At a forbidden EHN witness minimizing LEFT-exclusive SOURCE
  support, the genuine original-global Claim 1 forces any
  left-rooted piece with injective target root images to contain
  a right-exclusive vertex as well.

Consequently, if the weak source map is injective merely on
the full common-root preimage S, an uncovered right-component
boundary gives a smaller-root GENUINELY MIXED source piece.

The new piece's root lies STRICTLY inside T and the original
left/right distinguished source vertices are retained. It is
not asserted to be a proper sub-piece of a previously selected
mixed piece P: the component may enlarge when the final minimal
root is chosen inside T. This remains an essential missing
Claim 2 descent/iteration invariant.

The minimality used here is LEFT support, unlike the
RIGHT-support-minimal collision-or-uncovered dichotomy.
No claim that one witness realizes both minima is made.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under actual left-support minimality and injectivity on the
entire shared-root preimage, an uncovered generated right
component boundary T yields a GENUINE positive-width
geometric piece with root strictly smaller than T whose
selected component contains both exclusive colours.

This does NOT identify that piece with a proper sub-piece of
an old chosen mixed piece or solve the unrestricted Claim 2. -/
theorem minimalLeftWitness_uncoveredBoundary_hasSmallerRootMixedPiece
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
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
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
    (hUncovered : ¬ T ⊆ w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y))) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n),
      0 < n ∧
      Set.range d.roots ⊂ T ∧
      d.left.1 = y.1 ∧
      d.right.1 = x.1 ∧
      ∃ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range d.roots) d.left ∧
        z ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget := by
  letI : Finite w.Carrier := w.finiteCarrier
  obtain ⟨y', hY'a, hSep'⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree w.toTarget w.homEmbedding
      x hxRight T hT hTS y.1 hyLeft
  have hYeq : y' = y := Subtype.ext hY'a
  have hSep : ¬ ReachOutside w.source.graph T
      (outsideCutMap hTS x) y := by
    simpa only [hYeq] using hSep'
  have hTclosed : w.source.IsClosed T := by
    rw [hT]
    exact w.source.functionClosure_isClosed
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x))
  have hPath : ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : w.Carrier // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 x.1 y.1)
  obtain ⟨n, d, hn, hRootProper, hLeftOriginal, hRightOriginal⟩ :=
    finite_uncoveredBoundary_hasSmallerRootGeometricPiece
      w.source T hTclosed (outsideCutMap hTS x) y
      hSep hUncovered hPath
  have hRootsInS : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget := by
    intro z hz
    exact hTS (hRootProper.subset hz)
  have hLeftD : d.left.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget := by
    rw [hLeftOriginal]
    exact hyLeft
  have hRootImageInj :
      Function.Injective (fun i : Fin n => w.toTarget (d.roots i)) := by
    intro i j hij
    apply d.roots_injective
    exact hInjOnRoot
      (hRootsInS ⟨i, rfl⟩) (hRootsInS ⟨j, rfl⟩) hij
  obtain ⟨z, hzComp, hzRight⟩ :=
    minimalGlobalWitness_pieceMeetsRight_of_rootInjective
      F hFiniteF Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      w hMinLeft d hn hRootsInS hLeftD hRootImageInj
  exact ⟨n, d, hn, hRootProper, hLeftOriginal, hRightOriginal,
    z, hzComp, hzRight⟩

end AllThoseRamseyClasses.Lifts
