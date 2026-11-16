import AllThoseRamseyClasses.Lifts.Claim2PositiveRankEligibleInnerSelection
import AllThoseRamseyClasses.Lifts.Claim2OriginalMinimizerObstructionReduction

/-!
# Track B: genuine positive-rank selected-Q provenance or smaller-root obstructions

The positive B-exclusive SOURCE-rank boundary selection now returns
a REAL eligible inner minimal-separator piece BEFORE the Q is chosen.
Apply the checked SAME-Q geometric flip to that precise inner piece.
This packages one new finite forbidden source, an actual new outer
geometric piece and the literal selected forbidden Q+E full-native
free-amalgam diagram into the heterogeneous next-state relation.

All original state invariants persist: same old global selected
symbol, exact old target-root coordinates, all exterior SOURCE
multiplicities, surviving A-only anchor, injected ordered new root,
injected complete B-active generated boundaries, and STRICT local
B-exclusive SOURCE-rank descent. An actual smaller-root old-root
capture/A-mixedness remains an explicit alternative.

Unlike the earlier contract-only finite-chain descent, each successful
edge in the NEW relation retains the SAME selected forbidden Q.
The terminal original A-minimizer contradiction then eliminates the
zero-B-rank alternative from any such chain starting at an actually
globally A-source-support-minimal witness.

No unproved existence of a universally eligible inner piece;
no weak-map quotient; no global seam injection; no elimination of
the two genuine smaller-root obstructions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- At positive B-exclusive source rank, the SAME selected-Q
provenance-preserving native source step exists, OR a smaller source
minimal-separator selected component captures an OLD outer root,
OR it is A-mixed. Every successful step stores the literal Q+E
full source diagram, not just a target-map or profile certificate. -/
theorem claim2Native_positiveRank_selectedQStep_or_capture_or_mixed
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
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hPositive : 0 < claim2NativeBSourceRank s) :
    (∃ t : Claim2NativeGeometricState F Target Left Right
        jLeft jRight X iLeft iRight n,
      claim2NativeSelectedQProvenanceStep F Target Left Right
        jLeft jRight X iLeft iRight hn s t) ∨
      claim2NativeOldRootCapture s ∨
      claim2NativeAMixedRoot s := by
  rcases claim2Native_positiveRank_eligibleInner_or_capture_or_mixed
      F hConnected Target Left Right jLeft jRight
      X iLeft iRight hFree s hPositive with
    hInner | hCapture | hMixed
  · obtain ⟨m, inner, hm, hInside, hOldRootOutside,
      hRoots, hNoA, hRootInj, x, hxComp, hxRight⟩ := hInner
    obtain ⟨t, hStep⟩ :=
      claim2Native_eligibleInner_hasSelectedQProvenanceStep
        F hFiniteF Target Left Right jLeft jRight
        X iLeft iRight hFree hCommon hn hm s inner
        hInside hOldRootOutside hRoots hNoA hRootInj
        x hxComp hxRight
    exact Or.inl ⟨t, hStep⟩
  · exact Or.inr (Or.inl hCapture)
  · exact Or.inr (Or.inr hMixed)

/-- The obstruction-sensitive finite descent now iterates ONLY
actual selected-Q native source replacements, preserving the
literal forbidden Q and full old-complement free-amalgam data at
every nontrivial edge of its proof term. Full original selected
symbol and exterior SOURCE support remain invariant. -/
theorem claim2Native_selectedQChain_reaches_zero_or_capture_or_mixed
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
    (initial : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) :
    ∃ (k : ℕ) (terminal : Claim2NativeGeometricState F Target
        Left Right jLeft jRight X iLeft iRight n),
      ConditionalSelectedQChain
        (claim2NativeSelectedQProvenanceStep F Target Left Right
          jLeft jRight X iLeft iRight hn) k initial terminal ∧
      claim2NativeOuterProfile F Target Left Right
        jLeft jRight X iLeft iRight hn initial terminal ∧
      (claim2NativeBSourceRank terminal = 0 ∨
        claim2NativeOldRootCapture terminal ∨
        claim2NativeAMixedRoot terminal) ∧
      k + claim2NativeBSourceRank terminal ≤
        claim2NativeBSourceRank initial := by
  let Step : (Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) →
    (Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) → Prop :=
    claim2NativeSelectedQProvenanceStep F Target Left Right
      jLeft jRight X iLeft iRight hn
  let rank : (Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) → ℕ :=
    claim2NativeBSourceRank
  have hDecrease :
      ∀ ⦃s t : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n⦄,
        Step s t → rank t < rank s := by
    intro s t hStep
    exact hStep.1.2.2.1
  have hPreserves :
      ∀ ⦃s t : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n⦄,
        Step s t → True → True := by
    intro s t _hStep _hValid
    trivial
  have hProgress :
      ∀ s : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n,
        True → 0 < rank s →
          claim2NativeOldRootCapture s ∨
          claim2NativeAMixedRoot s ∨
          ∃ t, Step s t := by
    intro s _hValid hPositive
    rcases claim2Native_positiveRank_selectedQStep_or_capture_or_mixed
        F hFiniteF hConnected Target Left Right
        jLeft jRight X iLeft iRight hFree hCommon
        hn s hPositive with ⟨t, hStep⟩ | hCapture | hMixed
    · exact Or.inr (Or.inr ⟨t, hStep⟩)
    · exact Or.inl hCapture
    · exact Or.inr (Or.inl hMixed)
  obtain ⟨k, terminal, hChain, _hValid, hExit, hBudget⟩ :=
    conditionalSelectedQChain_reaches_zero_or_two_obstructions
      rank (fun _ => True)
      claim2NativeOldRootCapture claim2NativeAMixedRoot
      hDecrease hPreserves hProgress initial trivial
  exact ⟨k, terminal, hChain,
    claim2NativeSelectedQChain_preservesOriginalProfile
      F Target Left Right jLeft jRight X iLeft iRight
      hn initial terminal hChain,
    hExit, hBudget⟩

/-- For an actual initial globally A-SOURCE-support-minimal
forbidden EHN witness already carrying full native geometric
state certificates, the FINITE chain whose every edge stores
one complete actual forbidden selected Q cannot terminate at
zero B-SOURCE rank: the checked original whole-piece A→B
terminal flip would strictly reduce ORIGINAL A-source support.

Therefore the endpoint of this literal same-Q chain exhibits
a concrete old-root capture or an A-mixed smaller component. -/
theorem claim2Native_originalAMinimizer_selectedQChain_reaches_obstruction
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
    (initial : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hOriginalMin :
      ∀ w : ForbiddenEHNWitness F Target,
        (claim2NativeGeometricState_asForbiddenWitness initial).sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    ∃ (k : ℕ) (terminal : Claim2NativeGeometricState F Target
        Left Right jLeft jRight X iLeft iRight n),
      ConditionalSelectedQChain
        (claim2NativeSelectedQProvenanceStep F Target Left Right
          jLeft jRight X iLeft iRight hn) k initial terminal ∧
      claim2NativeOuterProfile F Target Left Right
        jLeft jRight X iLeft iRight hn initial terminal ∧
      (claim2NativeOldRootCapture terminal ∨
        claim2NativeAMixedRoot terminal) ∧
      k + claim2NativeBSourceRank terminal ≤
        claim2NativeBSourceRank initial := by
  obtain ⟨k, terminal, hChain, hProfile, hExit, hBudget⟩ :=
    claim2Native_selectedQChain_reaches_zero_or_capture_or_mixed
      F hFiniteF hConnected Target Left Right
      jLeft jRight X iLeft iRight hFree hCommon hn initial
  rcases hExit with hZero | hCapture | hMixed
  · have hInitialA :
        ∃ v : (claim2NativeGeometricState_asForbiddenWitness initial).Carrier,
          v ∈ geometricPieceVertices initial.source initial.outer ∧
          (claim2NativeGeometricState_asForbiddenWitness initial).toTarget v ∈
            fullFreeLeftExclusiveTarget iLeft jLeft := by
      refine ⟨initial.anchor, initial.anchorInOuter, ?_⟩
      exact (weakFreeLeftPart_iff_targetExclusive
        iLeft jLeft initial.f initial.anchor).mp initial.anchorLeft
    have hOutsideOriginal :
        Nat.card {v : terminal.Carrier //
          v ∉ geometricPieceVertices terminal.source terminal.outer ∧
          terminal.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
        Nat.card {v : (claim2NativeGeometricState_asForbiddenWitness initial).Carrier //
          v ∉ geometricPieceVertices initial.source initial.outer ∧
          (claim2NativeGeometricState_asForbiddenWitness initial).toTarget v ∈
            fullFreeLeftExclusiveTarget iLeft jLeft} := by
      exact hProfile.2.2.1 (fullFreeLeftExclusiveTarget iLeft jLeft)
    exact False.elim
      (claim2_originalMinimizer_contradicted_by_zeroTerminalBSupport
        F hFiniteF Target Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        (claim2NativeGeometricState_asForbiddenWitness initial)
        hOriginalMin
        (geometricPieceVertices initial.source initial.outer)
        hInitialA
        terminal.source terminal.finite terminal.forbidden
        terminal.f terminal.hom terminal.outer hn
        terminal.outerRootInSeam hZero terminal.outerRootTargetInj
        hOutsideOriginal)
  · exact ⟨k, terminal, hChain, hProfile,
      Or.inl hCapture, hBudget⟩
  · exact ⟨k, terminal, hChain, hProfile,
      Or.inr hMixed, hBudget⟩

end AllThoseRamseyClasses.Lifts
