import AllThoseRamseyClasses.Lifts.Claim2SelectedQPositiveRankObstructionDescent
import AllThoseRamseyClasses.Lifts.Claim2OriginalMinimizerThreeWayGate

/-!
# Track B: initialize ORIGINAL minimizer descent with literal selected-Q edges

The earlier original-minimizer root/boundary collision trichotomy
produced an abstract native state chain whose edges conserved the
right source/profile invariants, but whose edge predicate did NOT
store a particular selected forbidden Q native gluing diagram.

Using the independently proven positive-rank eligible-inner source
selector and actual same-Q provenance step, replace the successful
descent by a STRONGER finite chain which retains the literal forbidden
selected Q and full old-complement free-amalgam data at EVERY edge.

The initial weak EHN map need NOT be injective globally. Both missing
initial injectivity premises are diagnosed as genuine original source
FULL irreducible-test gaps: either a pair of distinct old root
SOURCE vertices has the same target image without a joint FULL test,
or one complete B-active generated boundary inside the actual old
outer source piece contains a distinct colliding pair without a
joint FULL test. Under neither gap, the SAME original globally
A-SOURCE-support-minimal witness enters the genuine selected-Q
chain, which must terminate in old-root capture or A-mixedness.

This does not prove those four obstructions impossible, nor does it
construct an initial mixed geometric piece from arbitrary source
data. A width-one old outer root removes the root collision case
without a source-test cover assumption.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- With an injectively mapped old ordered root, an ORIGINAL
A-SOURCE-minimal forbidden EHN source either exhibits an actual
local B-generated-boundary FULL source-test gap, OR the very SAME
original witness starts a finite genuine selected-Q replacement
chain. Every step retains its complete Q+E native source diagram,
and the endpoint exhibits old-root capture or A-mixedness. -/
theorem claim2NativePreBoundary_minimizer_fullTestGap_or_literalSelectedQChain
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
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    s.hasLocalFullTestGap ∨
      ∃ (hBoundary : s.boundaryInjected)
        (k : ℕ)
        (terminal : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n),
        ConditionalSelectedQChain
          (claim2NativeSelectedQProvenanceStep F Target Left Right
            jLeft jRight X iLeft iRight hn)
          k (s.withBoundaryInjection hBoundary) terminal ∧
        claim2NativeOuterProfile F Target Left Right
          jLeft jRight X iLeft iRight hn
          (s.withBoundaryInjection hBoundary) terminal ∧
        (claim2NativeOldRootCapture terminal ∨
          claim2NativeAMixedRoot terminal) ∧
        k + claim2NativeBSourceRank terminal ≤
          claim2NativeBSourceRank (s.withBoundaryInjection hBoundary) := by
  classical
  rcases claim2_initial_activeBoundaryInj_or_localSourceCollision
      s.original.source s.outer Target s.original.toTarget
      s.original.homEmbedding Left Right
      jLeft jRight X iLeft iRight s.outerRootInSeam with
    hBoundary | hCollision
  · let initial := s.withBoundaryInjection hBoundary
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
      exact hOriginalMin v
    obtain ⟨k, terminal, hChain, hProfile, hObstruction, hBudget⟩ :=
      claim2Native_originalAMinimizer_selectedQChain_reaches_obstruction
        F hFiniteF hConnected Target Left Right
        jLeft jRight X iLeft iRight hFree hCommon
        hn initial hMin
    exact Or.inr
      ⟨hBoundary, k, terminal, hChain, hProfile,
        hObstruction, hBudget⟩
  · exact Or.inl (s.localCollision_has_fullTestGap hCollision)

/-- For a genuinely chosen ORIGINAL globally A-source-minimal
forbidden EHN witness, but with NO assumed initial target image
injection on either the separator root or its active boundaries,
there is (1) a colliding original SOURCE root pair with no
joint FULL irreducible native source test, OR (2) an injected
root but a genuine local B-boundary SOURCE collision with no
joint FULL source test, OR (3) a finite chain with a literal
selected forbidden Q+old E diagram on EVERY successful step
ending at old-root capture or A-mixedness.

Root-in-seam, genuine geometric minimal separator, A-only anchor,
target full free amalgam, original canonical lift and global
original A-support minimality remain explicitly required. -/
theorem claim2NativePreRoot_minimizer_rootGap_or_boundaryGap_or_literalSelectedQChain
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
        ∃ (hBoundary : initial.boundaryInjected)
          (k : ℕ)
          (terminal : Claim2NativeGeometricState F Target Left Right
            jLeft jRight X iLeft iRight n),
          ConditionalSelectedQChain
            (claim2NativeSelectedQProvenanceStep F Target Left Right
              jLeft jRight X iLeft iRight hn)
            k (initial.withBoundaryInjection hBoundary) terminal ∧
          claim2NativeOuterProfile F Target Left Right
            jLeft jRight X iLeft iRight hn
            (initial.withBoundaryInjection hBoundary) terminal ∧
          (claim2NativeOldRootCapture terminal ∨
            claim2NativeAMixedRoot terminal) ∧
          k + claim2NativeBSourceRank terminal ≤
            claim2NativeBSourceRank
              (initial.withBoundaryInjection hBoundary)) := by
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
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)
      exact hOriginalMin v
    rcases claim2NativePreBoundary_minimizer_fullTestGap_or_literalSelectedQChain
        F hFiniteF hConnected Target Left Right
        jLeft jRight X iLeft iRight hFree hCommon
        hn initial hMin with hBoundaryGap | hQChain
    · exact Or.inr ⟨hRootInj, Or.inl hBoundaryGap⟩
    · exact Or.inr ⟨hRootInj, Or.inr hQChain⟩
  · exact Or.inl hRootGap

/-- At original old root WIDTH ONE there is no initial root-image
collision, since the domain Fin 1 is subsingleton. Without ANY
other initial target-map injectivity assumption, a globally
A-source-minimal forbidden EHN original witness with a genuine
seam-rooted outer piece therefore has a local generated B-active
boundary FULL-test gap or a literal selected-Q finite chain
ending in old-root capture/A-mixedness. -/
theorem claim2NativePreRoot_widthOne_minimizer_boundaryGap_or_literalQChain
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
        ∃ (hBoundary : initial.boundaryInjected)
          (k : ℕ)
          (terminal : Claim2NativeGeometricState F Target Left Right
            jLeft jRight X iLeft iRight 1),
          ConditionalSelectedQChain
            (claim2NativeSelectedQProvenanceStep F Target Left Right
              jLeft jRight X iLeft iRight
              (by decide : 0 < 1))
            k (initial.withBoundaryInjection hBoundary) terminal ∧
          claim2NativeOuterProfile F Target Left Right
            jLeft jRight X iLeft iRight (by decide : 0 < 1)
            (initial.withBoundaryInjection hBoundary) terminal ∧
          (claim2NativeOldRootCapture terminal ∨
            claim2NativeAMixedRoot terminal) ∧
          k + claim2NativeBSourceRank terminal ≤
            claim2NativeBSourceRank
              (initial.withBoundaryInjection hBoundary) := by
  rcases
      claim2NativePreRoot_minimizer_rootGap_or_boundaryGap_or_literalSelectedQChain
        F hFiniteF hConnected Target Left Right
        jLeft jRight X iLeft iRight hFree hCommon
        (by decide : 0 < 1) s hOriginalMin with
    hGap | hOther
  · obtain ⟨i, j, hij, _hImages, _hNoJointTest⟩ := hGap
    exact False.elim (hij (Subsingleton.elim i j))
  · exact hOther

end AllThoseRamseyClasses.Lifts
