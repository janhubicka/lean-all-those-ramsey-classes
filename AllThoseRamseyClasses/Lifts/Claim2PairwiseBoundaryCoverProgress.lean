import AllThoseRamseyClasses.Lifts.Claim2InitialPairwiseTestRootCover

/-!
# Track B: source-test coverage of all active B-generated boundaries

A native EHN source map is FULL on each irreducible embedded
source test. Pairwise joint source-test coverage of the complete
generated boundary of each B-active component therefore derives
the exact injectivity condition needed for the initial full native
selected-Q state. There is no new target map or source replacement.

This is a conditional SOURCE-SIDE sufficient hypothesis, not
an assertion that all original minimizers enjoy the cover.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- Every generated B-active boundary inside the chosen geometric
outer piece is pairwise covered by FULL irreducible source tests. -/
def Claim2NativePreBoundaryState.boundariesPairwiseCovered
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UX UA UB UT : Type}
    {Target : Structure L UT}
    {Left : Structure L UA} {Right : Structure L UB}
    {jLeft : Structure.Embedding Left Target}
    {jRight : Structure.Embedding Right Target}
    {X : Structure L UX}
    {iLeft : Structure.Embedding X Left}
    {iRight : Structure.Embedding X Right}
    {n : ℕ}
    (s : Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n) : Prop :=
  ∀ (x : {v : s.original.Carrier //
      v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft)
        s.original.toTarget}),
    x.1 ∈ geometricPieceVertices s.original.source s.outer →
    x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight)
      s.original.toTarget →
    PairwiseIrreducibleSourceTestCover s.original.source
      (s.original.source.functionClosure
        (gaifmanNeighborhood s.original.source.graph
          (componentFrom s.original.source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft)
              s.original.toTarget) x)))

/-- The verified original EHN full-test clause makes the weak map
injective on every pairwise FULL-test-covered generated boundary. -/
theorem Claim2NativePreBoundaryState.boundaryInjected_of_pairwiseSourceTests
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UX UA UB UT : Type}
    {Target : Structure L UT}
    {Left : Structure L UA} {Right : Structure L UB}
    {jLeft : Structure.Embedding Left Target}
    {jRight : Structure.Embedding Right Target}
    {X : Structure L UX}
    {iLeft : Structure.Embedding X Left}
    {iRight : Structure.Embedding X Right}
    {n : ℕ}
    (s : Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hCovered : s.boundariesPairwiseCovered) :
    s.boundaryInjected := by
  intro x hxPart hxRight
  exact ehn_injOn_of_pairwiseIrreducibleSourceTestCover
    s.original.source Target s.original.toTarget
    s.original.homEmbedding
    (s.original.source.functionClosure
      (gaifmanNeighborhood s.original.source.graph
        (componentFrom s.original.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft)
            s.original.toTarget) x)))
    (hCovered x hxPart hxRight)

/-- Promote the SAME original forbidden source and map, using
SOURCE-only joint irreducible-test coverage, rather than assuming
injectivity of any target generated boundary. -/
def Claim2NativePreBoundaryState.withPairwiseBoundaryTests
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UX UA UB UT : Type}
    {Target : Structure L UT}
    {Left : Structure L UA} {Right : Structure L UB}
    {jLeft : Structure.Embedding Left Target}
    {jRight : Structure.Embedding Right Target}
    {X : Structure L UX}
    {iLeft : Structure.Embedding X Left}
    {iRight : Structure.Embedding X Right}
    {n : ℕ}
    (s : Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hCovered : s.boundariesPairwiseCovered) :
    Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n :=
  s.withBoundaryInjection
    (s.boundaryInjected_of_pairwiseSourceTests hCovered)

/-- The original globally A-SOURCE-minimal forbidden EHN source
with SOURCE-side pairwise-test cover on its active B-boundaries
must reach OLD-ROOT CAPTURE or A-MIXEDNESS under finite genuine
full-invariant B-SOURCE rank descent.

No original target B-boundary injection premise remains. The two
geometric obstruction branches are still open, as is general
pairwise test coverage for arbitrary forbidden geometric pieces. -/
theorem claim2_pairwiseCoveredBoundaries_originalMinimizer_reaches_obstruction
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
    {n : ℕ} (hn : 0 < n)
    (s : Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hOriginalMin :
      ∀ v : ForbiddenEHNWitness F Target,
        s.original.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hCovered : s.boundariesPairwiseCovered) :
    ∃ (k : ℕ)
      (terminal : Claim2NativeGeometricState F Target Left Right
        jLeft jRight X iLeft iRight n),
      ConditionalSelectedQChain
        (claim2NativeGeometricStep F Target Left Right
          jLeft jRight X iLeft iRight hn)
        k (s.withPairwiseBoundaryTests hCovered) terminal ∧
      claim2NativeOuterProfile F Target Left Right
        jLeft jRight X iLeft iRight hn
        (s.withPairwiseBoundaryTests hCovered) terminal ∧
      (claim2NativeOldRootCapture terminal ∨
        claim2NativeAMixedRoot terminal) ∧
      k + claim2NativeBSourceRank terminal ≤
        claim2NativeBSourceRank
          (s.withPairwiseBoundaryTests hCovered) := by
  let initial := s.withPairwiseBoundaryTests hCovered
  have hMin :
      ∀ v : ForbiddenEHNWitness F Target,
        (claim2NativeGeometricState_asForbiddenWitness initial).sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro v
    change s.original.sourceSupportCount
      (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)
    exact hOriginalMin v
  exact claim2NativeOriginalMinimizer_forces_reachable_capture_or_mixed
    F hFiniteF hConnected Target Left Right
    jLeft jRight X iLeft iRight hFree hCommon hn
    initial hMin

end AllThoseRamseyClasses.Lifts
