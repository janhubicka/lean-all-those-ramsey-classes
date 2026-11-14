import AllThoseRamseyClasses.Lifts.Claim2PositiveRankFullStateObstructions
import AllThoseRamseyClasses.Lifts.Claim2ConditionalFiniteChain

/-!
# Track B: actual heterogeneous native states for original Claim 2

A selected Q-replacement need not have the same carrier as its source.
This state therefore stores a *type* of vertices, the complete native
structure, an actual positive-width geometric outer piece, weak map,
a real A-exclusive source anchor, the ordered outer-root target
injectivity, and the exact native local generated B-boundary injection.

All the data needed to apply the positive-rank full-state trichotomy
are carried by the state, not produced by a hypothetical normalization.

The successful step records original global selected symbol,
ordered target root coordinates, exact exterior SOURCE counts for
every target set, an A-anchor target coordinate and strict B-SOURCE
rank descent. A positive-rank source either has such an ACTUAL step
or witnesses one of the two specific smaller-root obstructions.

This proves no initial state exists and no obstruction is impossible.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Full source-geometric state for the original selected-symbol
Claim 2; its finite source carrier is intentionally heterogeneous. -/
structure Claim2NativeGeometricState
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
  Carrier : Type
  source : Structure L Carrier
  finite : Finite Carrier
  forbidden : F source
  outer : GeometricFunctionalPieceData source n
  f : Carrier → UT
  hom : source.IsEHNHomomorphismEmbedding Target f
  outerRootInSeam :
    Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  anchor : Carrier
  anchorInOuter : anchor ∈ geometricPieceVertices source outer
  anchorLeft : anchor ∈ weakFreeLeftPart
    (sL := iLeft) (iL := jLeft) f
  outerRootTargetInj :
    Function.Injective (fun i : Fin n => f (outer.roots i))
  activeBoundaryInj :
    ∀ (x : {v : Carrier //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
      x.1 ∈ geometricPieceVertices source outer →
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f →
      Set.InjOn f
        (source.functionClosure
          (gaifmanNeighborhood source.graph
            (componentFrom source.graph
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))

/-- A genuine *source*-rank, not cardinality of target-map images. -/
def claim2NativeBSourceRank
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
    v ∈ geometricPieceVertices s.source s.outer ∧
    s.f v ∈ fullFreeRightExclusiveTarget iRight jRight}

/-- A strict local native state transition, including the SAME
original global selected symbol and full all-target exterior
SOURCE-count conservation. This relation is restricted to states
with genuine geometric pieces and built-in local injections. -/
def claim2NativeGeometricStep
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
      jLeft jRight X iLeft iRight n) : Prop :=
    (∀ i : Fin n, t.f (t.outer.roots i) = s.f (s.outer.roots i)) ∧
    geometricGlobalPieceSymbol F s.source s.finite s.forbidden s.outer hn =
      geometricGlobalPieceSymbol F t.source t.finite t.forbidden t.outer hn ∧
    claim2NativeBSourceRank t < claim2NativeBSourceRank s ∧
    (∀ TargetSet : Set UT,
      Nat.card {w : t.Carrier //
        w ∉ geometricPieceVertices t.source t.outer ∧
        t.f w ∈ TargetSet} =
      Nat.card {v : s.Carrier //
        v ∉ geometricPieceVertices s.source s.outer ∧
        s.f v ∈ TargetSet}) ∧
    t.f t.anchor = s.f s.anchor

/-- A certified smaller-root obstruction with a captured OLD outer
root. The selected separator root is genuinely positive and lies in
the old outer piece and the target seam. -/
def claim2NativeOldRootCapture
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
      jLeft jRight X iLeft iRight n) : Prop :=
  ∃ (m : ℕ) (d : GeometricFunctionalPieceData s.source m),
    0 < m ∧
    Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f ∩
        geometricPieceVertices s.source s.outer ∧
    ∃ i : Fin n, s.outer.roots i ∈
      functionalComponentFrom s.source (Set.range d.roots) d.left

/-- The other precise smaller-root obstruction: the selected source
component contains a literal A-exclusive source vertex. -/
def claim2NativeAMixedRoot
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
      jLeft jRight X iLeft iRight n) : Prop :=
  ∃ (m : ℕ) (d : GeometricFunctionalPieceData s.source m),
    0 < m ∧
    Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f ∩
        geometricPieceVertices s.source s.outer ∧
    ∃ z : s.Carrier,
      z ∈ functionalComponentFrom s.source (Set.range d.roots) d.left ∧
      z ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f

/-- Fully native Claim 2 trichotomy on heterogeneous *actual* states.
The witnesses come from the same-source selected-Q construction, not
from an arbitrary weak-image quotient. The two obstructions are real
open branches of the original argument. -/
theorem claim2NativeGeometricState_step_or_capture_or_mixed
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
      claim2NativeGeometricStep F Target Left Right jLeft jRight
        X iLeft iRight hn s t) ∨
    claim2NativeOldRootCapture s ∨
    claim2NativeAMixedRoot s := by
  classical
  rcases
      claim2_positiveRank_fullStateStep_or_oldRootCapture_or_AMixed
        F hFiniteF hConnected s.source s.finite s.forbidden
        s.outer hn
        Target s.f s.hom Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        s.outerRootInSeam s.anchor s.anchorInOuter s.anchorLeft
        hPositive s.activeBoundaryInj s.outerRootTargetInj with
    hStep | hObstruction
  · obtain ⟨m, d, hm, hProper, V', New, hNew, hFiniteNew,
        flip, newOuter, hFlip, hCoords, hSymbol, hRank, hExterior,
        anew, haOuter, haSame, haNewA, hNewRootInj,
        hNewNativeBoundaryInj⟩ := hStep
    have hNewSeam : Set.range newOuter.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) flip := by
      rintro _ ⟨i, rfl⟩
      change flip (newOuter.roots i) ∈ Set.range (jLeft.comp iLeft)
      rw [hCoords i]
      exact s.outerRootInSeam ⟨i, rfl⟩
    have hNewAnchorLeft :
        anew ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) flip :=
      (weakFreeLeftPart_iff_targetExclusive
        iLeft jLeft flip anew).mpr haNewA
    let t : Claim2NativeGeometricState F Target Left Right
        jLeft jRight X iLeft iRight n :=
      { Carrier := V'
        source := New
        finite := hFiniteNew
        forbidden := hNew
        outer := newOuter
        f := flip
        hom := hFlip
        outerRootInSeam := hNewSeam
        anchor := anew
        anchorInOuter := haOuter
        anchorLeft := hNewAnchorLeft
        outerRootTargetInj := hNewRootInj
        activeBoundaryInj := hNewNativeBoundaryInj }
    left
    refine ⟨t, ?_⟩
    change (∀ i : Fin n,
        flip (newOuter.roots i) = s.f (s.outer.roots i)) ∧
      geometricGlobalPieceSymbol F s.source s.finite
        s.forbidden s.outer hn =
        geometricGlobalPieceSymbol F New hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        claim2NativeBSourceRank s ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : s.Carrier //
          v ∉ geometricPieceVertices s.source s.outer ∧
          s.f v ∈ TargetSet}) ∧
      flip anew = s.f s.anchor
    exact ⟨hCoords, hSymbol, hRank, hExterior, haSame⟩
  · obtain ⟨x, T, y, m, d, hxK, hxB, hyA, hT, hm,
        hProper, hRootIn, hdLeft, hdRight, hExact, hCases⟩ :=
        hObstruction
    rcases hCases with hCapture | hMixed
    · exact Or.inr (Or.inl ⟨m, d, hm, hRootIn, hCapture⟩)
    · exact Or.inr (Or.inr ⟨m, d, hm, hRootIn, hMixed⟩)

end AllThoseRamseyClasses.Lifts
