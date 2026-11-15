import AllThoseRamseyClasses.Lifts.Claim2OriginalMinimizerThreeWayGate

/-!
# Track B: singleton generated B-boundaries initialize genuine Claim 2 descent

An original EHN weak target map can identify distinct source vertices.
It is nevertheless automatically injective on any SOURCE set having
at most one vertex. In particular, if every *complete function-generated*
boundary of a B-active component in the chosen true geometric outer
piece is source-subsingleton, the initial B-boundary injection needed
for the same-Q native descent follows without any irreducible-test
coverage or global weak-map injection.

For root width one the ordered TARGET-root injection is automatic as
well, so a genuine global A-SOURCE-minimal initial forbidden witness
whose B-boundaries are source-subsingleton reaches old-root capture or
A-mixedness under finite actual geometric-state descent.

The source-subsingleton condition is EXPLICIT. Neither width one nor
minimal forbidden witness status alone implies it. No claim of
eliminating the remaining geometric obstructions or proving the
unrestricted 2019 Claim 2 is made.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- Every complete generated boundary of a B-exclusive component
in the actual chosen old geometric outer piece has at most ONE
literal SOURCE vertex, independently of its target image. -/
def Claim2NativePreBoundaryState.hasSubsingletonBActiveBoundaries
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
    ∀ (v w : s.original.Carrier),
      v ∈ s.original.source.functionClosure
        (gaifmanNeighborhood s.original.source.graph
          (componentFrom s.original.source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft)
              s.original.toTarget) x)) →
      w ∈ s.original.source.functionClosure
        (gaifmanNeighborhood s.original.source.graph
          (componentFrom s.original.source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft)
              s.original.toTarget) x)) →
      v = w

/-- A complete B-active generated SOURCE boundary of size at most one
is mapped injectively by ANY weak target map. Uses no assumption
about the images of other seam vertices or about full source tests. -/
theorem Claim2NativePreBoundaryState.boundaryInjected_of_subsingletonBoundaries
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
    (hSmall : s.hasSubsingletonBActiveBoundaries) :
    s.boundaryInjected := by
  intro x hxOuter hxB v hv w hw _hImages
  exact hSmall x hxOuter hxB v w hv hw

/-- The original A-support-minimal forbidden EHN witness is retained
literally when upgrading its one-vertex B-boundary certificate to the
full native geometric iteration state. No extra source-test coverage. -/
theorem claim2NativePreBoundary_smallBoundaries_minimizer_reaches_obstruction
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
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hSmall : s.hasSubsingletonBActiveBoundaries) :
    Claim2NativePreBoundaryState.reachesGeometricObstruction
      F Target Left Right jLeft jRight X iLeft iRight hn s := by
  let hBoundary : s.boundaryInjected :=
    s.boundaryInjected_of_subsingletonBoundaries hSmall
  let initial := s.withBoundaryInjection hBoundary
  have hMin :
      ∀ v : ForbiddenEHNWitness F Target,
        (claim2NativeGeometricState_asForbiddenWitness initial).sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro v
    change s.original.sourceSupportCount
      (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)
    exact hOriginalMin v
  obtain ⟨k, terminal, hChain, hProfile, hObstruction, hBudget⟩ :=
    claim2NativeOriginalMinimizer_forces_reachable_capture_or_mixed
      F hFiniteF hConnected Target Left Right
      jLeft jRight X iLeft iRight hFree hCommon
      hn initial hMin
  exact ⟨hBoundary, k, terminal, hChain,
    hProfile, hObstruction, hBudget⟩

/-- Ordered root-target injection is automatic at width ONE, even
when the original source EHN map collides elsewhere. -/
theorem Claim2NativePreRootState.widthOne_rootTargetInjective
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UX UA UB UT : Type}
    {Target : Structure L UT}
    {Left : Structure L UA} {Right : Structure L UB}
    {jLeft : Structure.Embedding Left Target}
    {jRight : Structure.Embedding Right Target}
    {X : Structure L UX}
    {iLeft : Structure.Embedding X Left}
    {iRight : Structure.Embedding X Right}
    (s : Claim2NativePreRootState F Target Left Right
      jLeft jRight X iLeft iRight 1) :
    Function.Injective
      (fun i : Fin 1 => s.original.toTarget (s.outer.roots i)) := by
  intro i j _
  exact Subsingleton.elim i j

/-- At actual old outer root width one, provided each complete
B-active generated SOURCE boundary has at most one vertex, the
original A-support minimizer enters native finite descent WITHOUT
any initial target-image injectivity or pairwise irreducible-test
cover premise. This gives an eventual REAL old-root-capture or
A-mixed smaller source obstruction; it does NOT exclude either. -/
theorem claim2NativePreRoot_widthOne_smallBoundaries_minimizer_reaches_obstruction
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
    (s : Claim2NativePreRootState F Target Left Right
      jLeft jRight X iLeft iRight 1)
    (hOriginalMin :
      ∀ v : ForbiddenEHNWitness F Target,
        s.original.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hSmall :
      (s.withRootInjection s.widthOne_rootTargetInjective).hasSubsingletonBActiveBoundaries) :
    Claim2NativePreBoundaryState.reachesGeometricObstruction
      F Target Left Right jLeft jRight X iLeft iRight
      (by decide : 0 < 1)
      (s.withRootInjection s.widthOne_rootTargetInjective) := by
  let initial := s.withRootInjection s.widthOne_rootTargetInjective
  have hMin :
      ∀ v : ForbiddenEHNWitness F Target,
        initial.original.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro v
    change s.original.sourceSupportCount
      (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)
    exact hOriginalMin v
  exact claim2NativePreBoundary_smallBoundaries_minimizer_reaches_obstruction
    F hFiniteF hConnected Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    (by decide : 0 < 1) initial hMin hSmall

end AllThoseRamseyClasses.Lifts
