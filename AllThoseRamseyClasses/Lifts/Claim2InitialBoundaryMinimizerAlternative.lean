import AllThoseRamseyClasses.Lifts.Claim2InitialBoundaryCollisionGate

/-!
# Track B: first initialization gate for original minimizer, without B-boundary injection

The first state in the original Claim 2 proof is a GLOBAL minimizer of
literal A-exclusive SOURCE support. Such a minimizer need not have an
injective weak EHN map on complete B-component generated boundaries.

This module stores the genuine initial native forbidden witness, its
geometric outer piece, its chosen A-anchor, and the ordered root-target
injection, but does NOT assume the B-boundary injection invariant.
There is an exact dichotomy:

(1) an actual collision in ONE generated B-component boundary T, with
    two distinct SOURCE vertices in T having the same target image;
(2) B-boundary injection holds, so promote the actual SAME initial
    minimizer to the verified full-invariant heterogeneous state
    and apply the genuine finite selected-Q descent and existing
    terminal minimizer contradiction to obtain a finitely reachable
    old-root-capture or A-mixed smaller geometric obstruction.

This is a more accurate initialization gate, not a proof of automatic
normalization or general 2019 Claim 2. The root-target injectivity and
existence of the initial true geometric outer piece stay explicit.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A real initial original-minimizer state BEFORE proving B-active
generated-boundary injectivity. The source is a full forbidden
EHN witness with variable finite native carrier. -/
structure Claim2NativePreBoundaryState
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (n : ℕ) where
  original : ForbiddenEHNWitness F Target
  outer : GeometricFunctionalPieceData original.source n
  outerRootInSeam :
    Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) original.toTarget
  anchor : original.Carrier
  anchorInOuter :
    anchor ∈ geometricPieceVertices original.source outer
  anchorLeft :
    anchor ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft)
      original.toTarget
  outerRootTargetInj :
    Function.Injective
      (fun i : Fin n => original.toTarget (outer.roots i))

/-- The local generated B-active boundary injection that the
original minimizer may or may not satisfy. -/
def Claim2NativePreBoundaryState.boundaryInjected
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
    x.1 ∈ weakFreeRightPart (sL := iLeft)
      (iL := jLeft) (iR := jRight) s.original.toTarget →
    Set.InjOn s.original.toTarget
      (s.original.source.functionClosure
        (gaifmanNeighborhood s.original.source.graph
          (componentFrom s.original.source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft)
              s.original.toTarget) x)))

/-- A concrete initial local boundary-collision certificate.
It asserts distinct SOURCE vertices, rather than merely failure of
a target-image quotient or a collision somewhere in the whole seam. -/
def Claim2NativePreBoundaryState.hasLocalCollision
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
  ∃ (x : {v : s.original.Carrier //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft)
          s.original.toTarget})
      (T : Set s.original.Carrier),
    x.1 ∈ geometricPieceVertices s.original.source s.outer ∧
    x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight)
      s.original.toTarget ∧
    T = s.original.source.functionClosure
      (gaifmanNeighborhood s.original.source.graph
        (componentFrom s.original.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft)
            s.original.toTarget) x)) ∧
    T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft)
        s.original.toTarget ∩
      geometricPieceVertices s.original.source s.outer ∧
    ∃ v w : s.original.Carrier,
      v ∈ T ∧ w ∈ T ∧ v ≠ w ∧
      s.original.toTarget v = s.original.toTarget w

/-- Upgrade the SAME initial native forbidden minimizer once
the missing B-active boundary injection certificate is supplied.
No new source, weak target map or selected replacement is chosen. -/
def Claim2NativePreBoundaryState.withBoundaryInjection
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
    (hInjection : s.boundaryInjected) :
    Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n :=
  { Carrier := s.original.Carrier
    source := s.original.source
    finite := s.original.finiteCarrier
    forbidden := s.original.forbidden
    outer := s.outer
    f := s.original.toTarget
    hom := s.original.homEmbedding
    outerRootInSeam := s.outerRootInSeam
    anchor := s.anchor
    anchorInOuter := s.anchorInOuter
    anchorLeft := s.anchorLeft
    outerRootTargetInj := s.outerRootTargetInj
    activeBoundaryInj := hInjection }

/-- Actual first-state alternative for an A-support-minimal forbidden
weak EHN witness. A local initial collision is exhibited, OR a finite
CHAIN of real native geometric source states reaches old-root capture
or A-mixedness. The original minimizer is retained LITERALLY in the
success case, with all its exact exterior SOURCE and global selected
symbol invariants preserved throughout the chain.

The old root-target tuple injectivity and initial positive-width
geometric piece are still GIVEN; boundary injection is NOT assumed. -/
theorem claim2NativePreBoundary_minimizer_collision_or_reachableObstruction
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
    (hOriginalMinimal :
      ∀ v : ForbiddenEHNWitness F Target,
        s.original.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    s.hasLocalCollision ∨
      ∃ (hInjection : s.boundaryInjected)
        (k : ℕ)
        (terminal : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n),
        ConditionalSelectedQChain
          (claim2NativeGeometricStep F Target Left Right
            jLeft jRight X iLeft iRight hn)
          k (s.withBoundaryInjection hInjection) terminal ∧
        claim2NativeOuterProfile F Target Left Right
          jLeft jRight X iLeft iRight hn
          (s.withBoundaryInjection hInjection) terminal ∧
        (claim2NativeOldRootCapture terminal ∨
          claim2NativeAMixedRoot terminal) ∧
        k + claim2NativeBSourceRank terminal ≤
          claim2NativeBSourceRank (s.withBoundaryInjection hInjection) := by
  classical
  rcases claim2_initial_activeBoundaryInj_or_localSourceCollision
      s.original.source s.outer Target s.original.toTarget
      s.original.homEmbedding Left Right
      jLeft jRight X iLeft iRight s.outerRootInSeam with
    hInjection | hCollision
  · let initial := s.withBoundaryInjection hInjection
    have hMin :
        ∀ v : ForbiddenEHNWitness F Target,
          (claim2NativeGeometricState_asForbiddenWitness initial).sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          v.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) := by
      intro v
      change s.original.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)
      exact hOriginalMinimal v
    obtain ⟨k, terminal, hChain, hProfile, hObstruction, hBudget⟩ :=
      claim2NativeOriginalMinimizer_forces_reachable_capture_or_mixed
        F hFiniteF hConnected Target Left Right
        jLeft jRight X iLeft iRight hFree hCommon
        hn initial hMin
    exact Or.inr
      ⟨hInjection, k, terminal, hChain, hProfile,
        hObstruction, hBudget⟩
  · exact Or.inl hCollision


/-- A genuine local B-boundary collision in the initial state cannot
be confined to two vertices of the old ordered outer root, because
that root's TARGET image is explicitly injected. Hence at least
one colliding SOURCE vertex lies outside the old outer root.

This does NOT say the nonroot vertex is outside the old geometric
outer piece: by the no-escape certificate BOTH lie INSIDE that piece.
Nor is this a repair of the weak target-map collision. -/
theorem Claim2NativePreBoundaryState.localCollision_has_nonrootVertex
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
    (hCollision : s.hasLocalCollision) :
    ∃ (v w : s.original.Carrier),
      v ≠ w ∧
      s.original.toTarget v = s.original.toTarget w ∧
      (v ∉ Set.range s.outer.roots ∨
       w ∉ Set.range s.outer.roots) := by
  rcases hCollision with ⟨x, T, hx, hB, hT, hTInside,
    v, w, hv, hw, hDifferent, hSame⟩
  refine ⟨v, w, hDifferent, hSame, ?_⟩
  by_cases hvRoot : v ∈ Set.range s.outer.roots
  · right
    rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hvRoot
    have hTargetRootEq :
        s.original.toTarget (s.outer.roots i) =
          s.original.toTarget (s.outer.roots j) := by
      calc
        s.original.toTarget (s.outer.roots i) =
            s.original.toTarget v := congrArg s.original.toTarget hi
        _ = s.original.toTarget w := hSame
        _ = s.original.toTarget (s.outer.roots j) :=
          (congrArg s.original.toTarget hj).symm
    have hij : i = j := s.outerRootTargetInj hTargetRootEq
    apply hDifferent
    calc
      v = s.outer.roots i := hi.symm
      _ = s.outer.roots j := congrArg s.outer.roots hij
      _ = w := hj
  · exact Or.inl hvRoot

end AllThoseRamseyClasses.Lifts
