import AllThoseRamseyClasses.Lifts.Claim2HeterogeneousNativeDescent
import AllThoseRamseyClasses.Lifts.Claim2TerminalZeroRightSupport

/-!
# Track B/C: the original left minimizer forces a smaller-root obstruction

The concrete heterogeneous geometric-state descent now has all the
inputs required by the ALREADY verified original Claim 2 zero-B-rank
terminal theorem. In particular it preserves literal exterior
A-exclusive SOURCE support for every step, while each state carries
the full outer-root target injection and its original genuine
geometric outer piece.

If the INITIAL state represents an actual globally left-support-
MINIMAL forbidden EHN witness, any reachable zero-B-rank state
contradicts the original minimizer by the previously verified final
A-to-B full native selected-symbol flip.

Therefore a finite genuine geometric B-rank descent from such an
initial state must encounter one of EXACTLY TWO unresolved source
obstructions: an old outer-root captured inside a smaller selected
component, or an A-exclusive source vertex in that component.

Crucially, this does NOT construct the initial boundary-injective
minimal state, nor rule out either obstruction, nor prove general
strong amalgamation for the 2019 lifting construction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Forget the chosen geometric context, but retain the very SAME
complete native finite forbidden source and EHN target map. -/
def claim2NativeGeometricState_asForbiddenWitness
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
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) :
    ForbiddenEHNWitness F Target :=
  { Carrier := s.Carrier
    finiteCarrier := s.finite
    source := s.source
    forbidden := s.forbidden
    toTarget := s.f
    homEmbedding := s.hom }

/-- A genuine initially MINIMAL forbidden witness carrying the
explicit native geometric/injectivity state cannot descend to
zero B-source rank: the full original A-to-B terminal theorem
supplies a contradiction, not a postulated exit condition. -/
theorem claim2NativeOriginalMinimizer_forces_reachable_capture_or_mixed
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
    (hOriginalMinimal :
      ∀ w : ForbiddenEHNWitness F Target,
        (claim2NativeGeometricState_asForbiddenWitness initial).sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    ∃ (k : ℕ) (terminal : Claim2NativeGeometricState F Target
        Left Right jLeft jRight X iLeft iRight n),
      ConditionalSelectedQChain
        (claim2NativeGeometricStep F Target Left Right
          jLeft jRight X iLeft iRight hn) k initial terminal ∧
      claim2NativeOuterProfile F Target Left Right
        jLeft jRight X iLeft iRight hn initial terminal ∧
      (claim2NativeOldRootCapture terminal ∨
        claim2NativeAMixedRoot terminal) ∧
      k + claim2NativeBSourceRank terminal ≤
        claim2NativeBSourceRank initial := by
  obtain ⟨k, terminal, hChain, hProfile, hExit, hBudget⟩ :=
    claim2NativeGeometricState_reaches_zero_or_capture_or_mixed
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon hn initial
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
        hOriginalMinimal
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
