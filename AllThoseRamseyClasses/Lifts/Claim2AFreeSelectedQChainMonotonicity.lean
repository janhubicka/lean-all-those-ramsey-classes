import AllThoseRamseyClasses.Lifts.Claim2AFreeSelectedQCostCertificate
import AllThoseRamseyClasses.Lifts.Claim2PositiveRankEligibleInnerSelection
import AllThoseRamseyClasses.Lifts.Claim2SelectedQPositiveRankObstructionDescent
import Mathlib.Tactic

/-!
# Track B: finite actual selected-Q descent with OLD A-freeness on every edge

The stronger source step now preserves the missing certificate that
the removed OLD selected component is A-exclusive-free on the SAME
actual forbidden selected Q+E gluing. The positive-rank source
eligibility theorem proves this exact component condition.

Every successful positive-B-exclusive-SOURCE-rank state therefore
has a FULL A-FREE Q-certified native step, or a literal old-root
capture/A-mixed smaller source component. The finite descent is
instantiated with this stronger relation (not the old weak relation).
We can project to the verified original-state profile and total
B-SOURCE budget while retaining A-freeness on every Q-edge.

Crucially, the exact old/new support identity shows that total
A-exclusive SOURCE support is NONDECREASING on each successful step
and hence on the finite chain. This does NOT imply intermediate
sources remain ORIGINAL globally A-source-minimal: at an original
lexicographic minimum a first successful B-decreasing Q must pay
strict POSITIVE private A-source cost.

No global weak-map injection, Q selection in the captured/mixed
branches, elimination of source-test gaps, or unrestricted Claim 2
is claimed. Frozen 2019 TeX unchanged.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- Actual positive B-SOURCE rank supplies an eligible one-sided
native inner piece and its complete A-free SAME Q replacement,
or exactly the two smaller-root geometric obstructions. -/
theorem claim2Native_positiveRank_AFreeQStep_or_capture_or_mixed
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
      claim2NativeAFreeSelectedQStep F Target Left Right
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
      claim2Native_eligibleInner_hasAFreeSelectedQStep
        F hFiniteF Target Left Right jLeft jRight
        X iLeft iRight hFree hCommon hn hm s inner
        hInside hOldRootOutside hRoots hNoA hRootInj
        x hxComp hxRight
    exact Or.inl ⟨t, hStep⟩
  · exact Or.inr (Or.inl hCapture)
  · exact Or.inr (Or.inr hMixed)


/-- Forget ONLY OLD selected-component A-freeness at every edge
of a finite native Q+E source replacement chain. The selected Q
and all actual state data survive this precise projection. -/
theorem claim2NativeAFreeQChain_toProvenance
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
    {k : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : ConditionalSelectedQChain
      (claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k s t) :
    ConditionalSelectedQChain
      (claim2NativeSelectedQProvenanceStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k s t := by
  induction hChain with
  | nil s =>
      exact ConditionalSelectedQChain.nil s
  | cons hStep hTail ih =>
      exact ConditionalSelectedQChain.cons
        (claim2NativeAFreeSelectedQStep.toSelectedQProvenance
          F Target Left Right jLeft jRight X iLeft iRight hn
          _ _ hStep) ih

/-- The original selected global symbol, ordered root TARGET
coordinates, exterior literal SOURCE counts for ALL target sets,
and the A-anchor TARGET coordinate persist through every
A-free certified SAME-Q native source replacement chain. -/
theorem claim2NativeAFreeQChain_preservesOriginalProfile
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
    (initial terminal : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    {k : ℕ}
    (hChain : ConditionalSelectedQChain
      (claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k initial terminal) :
    claim2NativeOuterProfile F Target Left Right jLeft jRight
      X iLeft iRight hn initial terminal := by
  exact claim2NativeSelectedQChain_preservesOriginalProfile
    F Target Left Right jLeft jRight X iLeft iRight
    hn initial terminal
    (claim2NativeAFreeQChain_toProvenance
      F Target Left Right jLeft jRight X iLeft iRight
      hn hChain)

theorem claim2Native_AFreeQChain_reaches_zero_or_capture_or_mixed
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
        (claim2NativeAFreeSelectedQStep F Target Left Right
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
    claim2NativeAFreeSelectedQStep F Target Left Right
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
    rcases claim2Native_positiveRank_AFreeQStep_or_capture_or_mixed
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
    claim2NativeAFreeQChain_preservesOriginalProfile
      F Target Left Right jLeft jRight X iLeft iRight
      hn initial terminal hChain,
    hExit, hBudget⟩


/-- Literal total A-exclusive SOURCE-vertex count at any genuine
native forbidden source state; source maps need not be injective. -/
noncomputable def claim2NativeTotalASourceCount
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
      jLeft jRight X iLeft iRight n) : ℕ :=
  Nat.card {v : s.Carrier //
    s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft}

/-- ONE same-Q source replacement certified with OLD A-free
selected component cannot DECREASE total A-exclusive SOURCE
count; the new private Q-nonroot A-source count is its exact
nonnegative increase (not an assumed zero). -/
theorem claim2NativeAFreeQStep_totalA_nondecreasing
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
    (s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hStep : claim2NativeAFreeSelectedQStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t) :
    claim2NativeTotalASourceCount s ≤
      claim2NativeTotalASourceCount t := by
  obtain ⟨m, inner, Q, iQ, hExact⟩ :=
    claim2NativeAFreeSelectedQStep_exactACost
      F Target Left Right jLeft jRight
      X iLeft iRight hn s t hStep
  change
    Nat.card {v : s.Carrier //
      s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
    Nat.card {w : t.Carrier //
      t.f w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}
  omega

/-- Every FINITE chain with a literal selected forbidden Q,
native Q+old E full diagram and OLD A-free component certified
on EACH edge makes TOTAL A-exclusive SOURCE support
NONDECREASING. Strict B-source decrease runs in parallel,
but ORIGINAL A-minimality does not persist automatically. -/
theorem claim2NativeAFreeQChain_totalA_nondecreasing
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
    {k : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : ConditionalSelectedQChain
      (claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k s t) :
    claim2NativeTotalASourceCount s ≤
      claim2NativeTotalASourceCount t := by
  have hOneStep :
      ∀ ⦃a b : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n⦄,
        claim2NativeAFreeSelectedQStep F Target Left Right
          jLeft jRight X iLeft iRight hn a b →
        claim2NativeTotalASourceCount a ≤
          claim2NativeTotalASourceCount b := by
    intro a b hStep
    exact claim2NativeAFreeQStep_totalA_nondecreasing
      F Target Left Right jLeft jRight
      X iLeft iRight hn a b hStep
  induction hChain with
  | nil a =>
      exact le_rfl
  | cons hStep hTail ih =>
      exact (hOneStep hStep).trans ih

/-- The exact GLOBAL B-exclusive SOURCE rank budget continues
to hold on A-free selected-Q chains; the ORIGINAL A-source
count is separately proved nondecreasing above. -/
theorem claim2NativeAFreeQChain_globalBBudget
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
    {k : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : ConditionalSelectedQChain
      (claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k s t) :
    k + claim2NativeTotalBSourceCount t ≤
      claim2NativeTotalBSourceCount s := by
  exact claim2NativeSelectedQChain_globalBSourceBudget
    F Target Left Right jLeft jRight X iLeft iRight
    hn
    (claim2NativeAFreeQChain_toProvenance
      F Target Left Right jLeft jRight X iLeft iRight
      hn hChain)

end AllThoseRamseyClasses.Lifts
