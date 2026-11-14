import AllThoseRamseyClasses.Lifts.Claim2InitialBoundaryMinimizerAlternative
import AllThoseRamseyClasses.Lifts.EHNPairwiseSourceTestRootInjectivity

/-!
# Track B: initialize original minimizer from pairwise irreducible source tests

The initial Track B state previously required ordered outer-root
target-image injectivity as explicit source input. Track D already
proved this injectivity from the much more structural premise that
every pair of distinct ORIGINAL separator-root source vertices
belongs to some genuinely FULL irreducible embedded source test.

Here we construct the ACTUAL same original forbidden witness as
a preboundary state from that pairwise source-test cover, without
assuming either global weak-map injection or the initial B-generated
boundary injection. The verified collision-or-geometric-descent
dichotomy then applies directly to the SAME initialized witness.

This is a conditional source-test-covered subcase, NOT a claim
that arbitrary forbidden minimal separators are pairwise covered.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Initialize a native preboundary state from one ACTUAL original
forbidden EHN witness and one genuine geometric separator root,
using the checked Track D joint FULL source-test cover to derive
injective ordered TARGET root coordinates.  No arbitrary replacement
or global weak map injection is introduced. -/
def claim2NativePreBoundary_of_pairwiseRootSourceTests
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (original : ForbiddenEHNWitness F Target)
    {n : ℕ}
    (outer : GeometricFunctionalPieceData original.source n)
    (hOuterRootSeam : Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft)
        original.toTarget)
    (anchor : original.Carrier)
    (hAnchorOuter :
      anchor ∈ geometricPieceVertices original.source outer)
    (hAnchorLeft :
      anchor ∈ weakFreeLeftPart
        (sL := iLeft) (iL := jLeft) original.toTarget)
    (hPairwiseRootTests :
      PairwiseIrreducibleSourceTestCover
        original.source (Set.range outer.roots)) :
    Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n :=
  { original := original
    outer := outer
    outerRootInSeam := hOuterRootSeam
    anchor := anchor
    anchorInOuter := hAnchorOuter
    anchorLeft := hAnchorLeft
    outerRootTargetInj :=
      geometricRootImage_injective_of_pairwiseSourceTests
        original.source outer Target original.toTarget
        original.homEmbedding hPairwiseRootTests }

/-- Compact conclusion of the genuine preboundary geometric-state
theorem: local original SOURCE boundary collision, or a finite
selected-Q Claim 2 state chain ending at old-root capture/A-mixedness.
The chain starts with EXACTLY the same native original forbidden
source/map, augmented only with its now verified B-boundary injection
certificate in the second branch. -/
def claim2NativePreBoundaryMinimizerOutcome
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n)
    (initial : Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n) : Prop :=
    initial.hasLocalCollision ∨
      ∃ (hBoundary : initial.boundaryInjected)
        (k : ℕ)
        (terminal : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n),
        ConditionalSelectedQChain
          (claim2NativeGeometricStep F Target Left Right
            jLeft jRight X iLeft iRight hn)
          k (initial.withBoundaryInjection hBoundary) terminal ∧
        claim2NativeOuterProfile F Target Left Right
          jLeft jRight X iLeft iRight hn
          (initial.withBoundaryInjection hBoundary) terminal ∧
        (claim2NativeOldRootCapture terminal ∨
          claim2NativeAMixedRoot terminal) ∧
        k + claim2NativeBSourceRank terminal ≤
          claim2NativeBSourceRank
            (initial.withBoundaryInjection hBoundary)

/-- An ACTUAL globally A-SOURCE-minimal forbidden EHN source with a
pairwise FULL source-test-covered geometric outer root, a real
A-only anchor and a root lying in the target seam either has a
literal local B-boundary SOURCE collision, or a finite full-profile
descent reaches old-root capture / A-mixedness.

The old outer root-target injection is DERIVED, not assumed.
There is NO assertion that either of the remaining outcomes is
impossible in arbitrary forbidden sources. -/
theorem claim2_pairwiseRootSourceTests_minimizer_collision_or_reachableObstruction
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
    (original : ForbiddenEHNWitness F Target)
    (hOriginalMin :
      ∀ v : ForbiddenEHNWitness F Target,
        original.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (outer : GeometricFunctionalPieceData original.source n)
    (hn : 0 < n)
    (hOuterRootSeam : Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft)
        original.toTarget)
    (anchor : original.Carrier)
    (hAnchorOuter :
      anchor ∈ geometricPieceVertices original.source outer)
    (hAnchorLeft :
      anchor ∈ weakFreeLeftPart
        (sL := iLeft) (iL := jLeft) original.toTarget)
    (hPairwiseRootTests :
      PairwiseIrreducibleSourceTestCover
        original.source (Set.range outer.roots)) :
    claim2NativePreBoundaryMinimizerOutcome F Target Left Right
      jLeft jRight X iLeft iRight hn
      (claim2NativePreBoundary_of_pairwiseRootSourceTests
        F Target Left Right jLeft jRight
        X iLeft iRight original outer
        hOuterRootSeam anchor hAnchorOuter
        hAnchorLeft hPairwiseRootTests) := by
  let s :=
    claim2NativePreBoundary_of_pairwiseRootSourceTests
      F Target Left Right jLeft jRight
      X iLeft iRight original outer hOuterRootSeam
      anchor hAnchorOuter hAnchorLeft hPairwiseRootTests
  change s.hasLocalCollision ∨
    ∃ (hBoundary : s.boundaryInjected)
      (k : ℕ)
      (terminal : Claim2NativeGeometricState F Target Left Right
        jLeft jRight X iLeft iRight n),
      ConditionalSelectedQChain
        (claim2NativeGeometricStep F Target Left Right
          jLeft jRight X iLeft iRight hn)
        k (s.withBoundaryInjection hBoundary) terminal ∧
      claim2NativeOuterProfile F Target Left Right
        jLeft jRight X iLeft iRight hn
        (s.withBoundaryInjection hBoundary) terminal ∧
      (claim2NativeOldRootCapture terminal ∨
        claim2NativeAMixedRoot terminal) ∧
      k + claim2NativeBSourceRank terminal ≤
        claim2NativeBSourceRank
          (s.withBoundaryInjection hBoundary)
  have hMin :
      ∀ v : ForbiddenEHNWitness F Target,
        s.original.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro v
    change original.sourceSupportCount
      (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)
    exact hOriginalMin v
  exact claim2NativePreBoundary_minimizer_collision_or_reachableObstruction
    F hFiniteF hConnected Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon hn s hMin

end AllThoseRamseyClasses.Lifts
