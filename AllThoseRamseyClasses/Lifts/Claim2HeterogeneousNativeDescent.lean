import AllThoseRamseyClasses.Lifts.Claim2HeterogeneousNativeState
import AllThoseRamseyClasses.Lifts.Claim2ObstructionOrZeroDescent

/-!
# Track B: instantiate finite descent on ACTUAL native geometric source states

The preceding module packages the heterogeneous forbidden source,
genuine geometric outer piece, EHN weak map, A-source anchor and
both local injection invariants, and derives a real step or one of
two smaller-root obstructions from the certified same-Q source flip.

This module now supplies a CONCRETE step/rank/progress instance of the
finite-chain theorem. Every edge of the resulting chain is a native
geometric state transition with strict literal B-SOURCE rank descent,
unchanged original global selected symbol, fixed ordered root target
coordinates and exact exterior SOURCE support counts for EVERY target
set. The reference profile is retained throughout the chain.

At the last state, B-rank is zero OR an old outer-root is captured by
a smaller separator component OR that smaller component is A-mixed.

This is NOT a theorem that either obstruction is impossible, nor a
zero-B terminal contradiction. Initialization still requires a state
with full native generated-boundary injection.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The four fixed-coordinate tests from the original selected-symbol
proof: ordered root targets, entire global selected piece symbol,
every exterior SOURCE-count, and the A-anchor target coordinate.
These tests compare literally different source carrier types. -/
def claim2NativeOuterProfile
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
    (initial t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) : Prop :=
    (∀ i : Fin n,
      t.f (t.outer.roots i) = initial.f (initial.outer.roots i)) ∧
    geometricGlobalPieceSymbol F t.source t.finite t.forbidden t.outer hn =
      geometricGlobalPieceSymbol F initial.source initial.finite
        initial.forbidden initial.outer hn ∧
    (∀ TargetSet : Set UT,
      Nat.card {w : t.Carrier //
        w ∉ geometricPieceVertices t.source t.outer ∧
        t.f w ∈ TargetSet} =
      Nat.card {v : initial.Carrier //
        v ∉ geometricPieceVertices initial.source initial.outer ∧
        initial.f v ∈ TargetSet}) ∧
    t.f t.anchor = initial.f initial.anchor

/-- Complete original selected-symbol profile is inherited by every
genuine step of the concrete geometric state relation. -/
theorem claim2NativeStep_preserves_originalProfile
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
    (initial s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hStep : claim2NativeGeometricStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t)
    (hProfile : claim2NativeOuterProfile F Target Left Right
      jLeft jRight X iLeft iRight hn initial s) :
    claim2NativeOuterProfile F Target Left Right jLeft jRight
      X iLeft iRight hn initial t := by
  rcases hStep with ⟨hCoords, hSymbol, _hRank, hExterior, hAnchor⟩
  rcases hProfile with ⟨hOldCoords, hOldSymbol, hOldExterior, hOldAnchor⟩
  exact ⟨
    (fun i => (hCoords i).trans (hOldCoords i)),
    hSymbol.symm.trans hOldSymbol,
    (fun TargetSet => (hExterior TargetSet).trans (hOldExterior TargetSet)),
    hAnchor.trans hOldAnchor⟩

/-- All source-geometric conditions, root-target coordinates, full
global selected symbol and exterior source multiplicities survive an
arbitrary finite chain of ACTUAL full-invariant native state steps. -/
theorem claim2NativeChain_preserves_originalProfile
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
    (initial t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    {k : ℕ}
    (hChain : ConditionalSelectedQChain
      (claim2NativeGeometricStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k initial t) :
    claim2NativeOuterProfile F Target Left Right jLeft jRight
      X iLeft iRight hn initial t := by
  have hBase : claim2NativeOuterProfile F Target Left Right
      jLeft jRight X iLeft iRight hn initial initial :=
    ⟨(fun _ => rfl), rfl, (fun _ => rfl), rfl⟩
  exact conditionalSelectedQChain_preserves
    (step := claim2NativeGeometricStep F Target Left Right
      jLeft jRight X iLeft iRight hn)
    (good := claim2NativeOuterProfile F Target Left Right
      jLeft jRight X iLeft iRight hn initial)
    (fun _s _t hStep hProfile =>
      claim2NativeStep_preserves_originalProfile F Target
        Left Right jLeft jRight X iLeft iRight hn
        initial _s _t hStep hProfile)
    hChain hBase

/-- Genuine finite geometric-source descent, including the full
original profile at its endpoint. Unconditionally *relative to an
initial full-invariant native state*, every chain produced from the
concrete positive-rank trichotomy reaches ZERO B-SOURCE rank or one
of the TWO real smaller-root obstructions, with exact rank budget.

No third 'seam-image collision' exit is introduced. The terminal
Claim 2 contradiction is still outside this theorem. -/
theorem claim2NativeGeometricState_reaches_zero_or_capture_or_mixed
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
        (claim2NativeGeometricStep F Target Left Right
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
    claim2NativeGeometricStep F Target Left Right
      jLeft jRight X iLeft iRight hn
  let rank : (Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) → ℕ :=
    claim2NativeBSourceRank
  have hDecrease :
      ∀ ⦃s t : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n⦄,
        Step s t → rank t < rank s := by
    intro s t hStep
    exact hStep.2.2.1
  have hPreserve :
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
    intro s _valid hPositive
    rcases claim2NativeGeometricState_step_or_capture_or_mixed
        F hFiniteF hConnected Target Left Right
        jLeft jRight X iLeft iRight hFree hCommon hn
        s hPositive with ⟨t, hStep⟩ | hCapture | hMixed
    · exact Or.inr (Or.inr ⟨t, hStep⟩)
    · exact Or.inl hCapture
    · exact Or.inr (Or.inl hMixed)
  obtain ⟨k, terminal, hChain, _hValid, hExit, hBudget⟩ :=
    conditionalSelectedQChain_reaches_zero_or_two_obstructions
      rank (fun _ => True)
      claim2NativeOldRootCapture claim2NativeAMixedRoot
      hDecrease hPreserve hProgress initial trivial
  exact ⟨k, terminal, hChain,
    claim2NativeChain_preserves_originalProfile F Target Left Right
      jLeft jRight X iLeft iRight hn initial terminal hChain,
    hExit, hBudget⟩

end AllThoseRamseyClasses.Lifts
