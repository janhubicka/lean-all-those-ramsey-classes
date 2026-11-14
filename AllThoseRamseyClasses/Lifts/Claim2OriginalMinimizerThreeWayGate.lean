import AllThoseRamseyClasses.Lifts.Claim2InitialPairwiseTestRootCover

/-!
# Track B: exhaustive ORIGINAL minimizer initialization test gaps

The initial original 2019 A-source-support minimizer is a weak EHN
witness. Neither its ordered geometric separator root nor the complete
generated B-active source boundaries are automatically target-injective.

This module removes BOTH injectivity assumptions from the entry
condition of the existing geometric Claim 2 descent, replacing them
by a mathematically precise finite trichotomy:

* an actual collision of distinct old ordered root SOURCE vertices,
  necessarily NOT jointly covered by one FULL irreducible source test;
* an actual collision of distinct source vertices inside ONE complete
  generated B-active boundary, likewise NOT jointly covered by one
  FULL irreducible source test;
* an ACTUAL finite selected-Q geometric B-source-rank descent that
  reaches old-root capture or A-mixedness, preserving the full original
  global symbol, source exterior multiplicities, root coordinates
  and anchor target.

The initial real geometric piece with its root in the target seam,
a real A-exclusive source anchor and ORIGINAL global A-support
minimality remain premises. There is NO claim that the two test gaps
or the two later geometric obstructions are impossible. No quotient
of the non-injective weak map or auxiliary forbidden-source closure.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Original finite forbidden EHN source with a true geometric
outer piece and A-exclusive source anchor, but NO root-target or
B-active generated-boundary injectivity assumptions. -/
structure Claim2NativePreRootState
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

/-- Promote exactly the SAME original native forbidden source,
selected geometric piece and weak EHN map to the preboundary state
when and only when the ordered root has injected target images. -/
def Claim2NativePreRootState.withRootInjection
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
    (s : Claim2NativePreRootState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hRootInj :
      Function.Injective
        (fun i : Fin n => s.original.toTarget (s.outer.roots i))) :
    Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n :=
  { original := s.original
    outer := s.outer
    outerRootInSeam := s.outerRootInSeam
    anchor := s.anchor
    anchorInOuter := s.anchorInOuter
    anchorLeft := s.anchorLeft
    outerRootTargetInj := hRootInj }

/-- A real collision on ONE generated B-component boundary
automatically exhibits an uncovered pair of SOURCE vertices:
no genuine FULL irreducible embedded source test contains both.
The collision itself is retained to preserve its local geometry. -/
def Claim2NativePreBoundaryState.hasLocalFullTestGap
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
  s.hasLocalCollision ∧
  ∃ (v w : s.original.Carrier),
    v ≠ w ∧
    s.original.toTarget v = s.original.toTarget w ∧
    ¬ ∃ (Y : Type) (E : Structure L Y),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E s.original.source,
        ∃ x y : Y, e x = v ∧ e y = w

/-- The local collision certificate is stronger than mere failure
of source-test coverage: it includes two distinct actual SOURCE
vertices in a complete B-active generated boundary inside the OLD
outer geometric piece and common target seam. -/
theorem Claim2NativePreBoundaryState.localCollision_has_fullTestGap
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
    s.hasLocalFullTestGap := by
  rcases hCollision with
    ⟨x, T, hxInOuter, hxRight, hT, hTinside,
      v, w, hvT, hwT, hvw, hSame⟩
  refine ⟨⟨x, T, hxInOuter, hxRight, hT, hTinside,
    v, w, hvT, hwT, hvw, hSame⟩, v, w, hvw, hSame, ?_⟩
  exact ehn_collidingSourcePair_not_in_jointIrreducibleTest
    s.original.source Target s.original.toTarget
    s.original.homEmbedding v w hvw hSame

/-- The actual finite native descent part of the old original
minimizer reduction, separated from the initial collision branch. -/
def Claim2NativePreBoundaryState.reachesGeometricObstruction
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
    (s : Claim2NativePreBoundaryState F Target Left Right
      jLeft jRight X iLeft iRight n) : Prop :=
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
      claim2NativeBSourceRank (s.withBoundaryInjection hBoundary)

/-- A full native ORIGINAL minimizer initialization trichotomy:
(1) an old ordered-root SOURCE collision without a common FULL
irreducible source test; OR (2) a generated B-boundary SOURCE
collision without a common FULL irreducible source test; OR
(3) a real finite native selected-Q descent to old-root capture
or A-mixedness, with original symbol and support profile preserved.

No injectivity is assumed for the initial root or any generated
B-active boundary. The genuine outer piece/root-seam/A-anchor
assumptions are stored in s and global A-support minimality is
explicit. No unrestricted original Claim 2 proof is claimed. -/
theorem claim2NativePreRoot_originalMinimizer_rootGap_or_boundaryGap_or_descent
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
    (s : Claim2NativePreRootState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hOriginalMin :
      ∀ v : ForbiddenEHNWitness F Target,
        s.original.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    (∃ i j : Fin n,
      i ≠ j ∧
      s.original.toTarget (s.outer.roots i) =
        s.original.toTarget (s.outer.roots j) ∧
      ¬ ∃ (Y : Type) (E : Structure L Y),
        E.Irreducible ∧
        ∃ e : Structure.Embedding E s.original.source,
          ∃ x y : Y,
            e x = s.outer.roots i ∧ e y = s.outer.roots j) ∨
    (∃ (hRootInj :
        Function.Injective
          (fun i : Fin n => s.original.toTarget (s.outer.roots i))),
      let initial := s.withRootInjection hRootInj
      initial.hasLocalFullTestGap ∨
        Claim2NativePreBoundaryState.reachesGeometricObstruction
          F Target Left Right jLeft jRight X iLeft iRight
          hn initial) := by
  classical
  rcases geometricRootImage_injective_or_jointIrreducibleTestGap
      s.original.source s.outer Target
      s.original.toTarget s.original.homEmbedding with
    hRootInj | hRootGap
  · let initial := s.withRootInjection hRootInj
    have hMin :
        ∀ v : ForbiddenEHNWitness F Target,
          initial.original.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          v.sourceSupportCount
            (fullFreeLeftExclusiveTarget iLeft jLeft) := by
      intro v
      change s.original.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)
      exact hOriginalMin v
    rcases claim2NativePreBoundary_minimizer_collision_or_reachableObstruction
        F hFiniteF hConnected Target Left Right
        jLeft jRight X iLeft iRight hFree hCommon
        hn initial hMin with
      hLocalCollision | hDescent
    · exact Or.inr ⟨hRootInj,
        Or.inl (initial.localCollision_has_fullTestGap hLocalCollision)⟩
    · exact Or.inr ⟨hRootInj, Or.inr hDescent⟩
  · exact Or.inl hRootGap

/-- At original outer root WIDTH ONE the ordered root TARGET image
is automatically injected, so the ROOT-collision test-gap branch of
the general original-minimizer trichotomy is impossible.

Consequently the only remaining initialization diagnostic is a
genuine generated B-boundary SOURCE collision (with a missing FULL
joint irreducible source test), or the already verified finite
geometric descent to an old-root-capture/A-mixed obstruction.

This makes NO assertion that either remaining branch is impossible;
it does not assume target injection of the entire weak source map. -/
theorem claim2NativePreRoot_widthOne_minimizer_boundaryGap_or_descent
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
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    ∃ (hRootInj :
        Function.Injective
          (fun i : Fin 1 => s.original.toTarget (s.outer.roots i))),
      let initial := s.withRootInjection hRootInj
      initial.hasLocalFullTestGap ∨
        Claim2NativePreBoundaryState.reachesGeometricObstruction
          F Target Left Right jLeft jRight X iLeft iRight
          (by decide : 0 < 1) initial := by
  rcases claim2NativePreRoot_originalMinimizer_rootGap_or_boundaryGap_or_descent
      F hFiniteF hConnected Target Left Right
      jLeft jRight X iLeft iRight hFree hCommon
      (by decide : 0 < 1) s hOriginalMin with
    hGap | hOther
  · obtain ⟨i, j, hij, _hImages, _hNoJointTest⟩ := hGap
    exact False.elim (hij (Subsingleton.elim i j))
  · exact hOther


end AllThoseRamseyClasses.Lifts
