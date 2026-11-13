import AllThoseRamseyClasses.Lifts.Claim2PositiveRankActiveBoundaryDichotomy

/-!
# Claim 2 positive B-rank: actual flip, smaller geometric root, or LOCAL boundary collision

The previous original trichotomy reported a collision anywhere
in the COMPLETE target common-seam preimage. The verified
active-boundary two-way source theorem actually needs only
injectivity on the function-generated boundaries T of
B-exclusive components inside the selected old outer piece P.

This theorem isolates its exact missing premise:
either the same genuine rank-decreasing selected-Q B-to-A
source flip (full original symbol, exterior SOURCE support,
surviving A SOURCE anchor), or an actual smaller positive
geometric separator root, or TWO DISTINCT literal SOURCE
vertices u,v in ONE generated B-component boundary T
with f u = f v. The whole T lies in the old seam preimage.

Thus the last case is a localized source collision witness,
not an arbitrary weak target-seam collision outside the
selected context. No quotient or assumption of injectivity
of the full weak source map is introduced.

This diagnostic does NOT repair the collision, exclude
the mixed smaller-root branch, establish the initial
boundary-injectivity invariant, or close the printed
2019 Claim 2. Its theorem statement is additive:
historical exports and numbered TeX remain unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Positive B-exclusive SOURCE rank has an actual selected-Q strict
source flip, a genuine smaller positive rooted separator, or a
LITERAL local collision on a generated boundary of an eligible
B-exclusive component inside the chosen older geometric piece.

The collision's exact boundary is still closed into the
common-seam PREIMAGE, without requiring its weak target
map to be globally injective. -/
theorem claim2_positiveRank_actualFlip_or_smallerRoot_or_activeBoundaryCollision
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hn : 0 < n)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (a : V)
    (haK : a ∈ geometricPieceVertices Source P)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hPositiveB : 0 < Nat.card {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    (∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      0 < m ∧
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New n),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin n, flip (newOuter.roots i) = f (P.roots i)) ∧
        geometricGlobalPieceSymbol F Source
            hFinite hForbidden P hn =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter hn ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Source P ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
        (∀ TargetSet : Set UT,
          Nat.card {w : V' //
            w ∉ geometricPieceVertices New newOuter ∧
            flip w ∈ TargetSet} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Source P ∧
            f v ∈ TargetSet}) ∧
        (∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f a ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft)) ∨
    (∃ (x : {v : V // v ∉
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
        (T : Set V) (y : {v : V // v ∉ T})
        (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      x.1 ∈ geometricPieceVertices Source P ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      y.1 = a ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      0 < m ∧
      Set.range d.roots ⊂ T ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩
          geometricPieceVertices Source P ∧
      d.left.1 = x.1 ∧ d.right.1 = a ∧
      Set.range d.roots =
        Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph T y))) ∨
    (∃ (x : {v : V // v ∉
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
        (T : Set V),
      x.1 ∈ geometricPieceVertices Source P ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∧
      ∃ u v : V, u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ f u = f v) := by
  classical
  by_cases hActiveBoundaryInjective :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
  · rcases
        (claim2_positiveRank_actualSuccessor_or_smallerRoot_of_activeBoundaryInjective
          F hFiniteF hConnected Source hFinite hForbidden
          P hn Target f hf Left Right jLeft jRight
          X iLeft iRight hFree hCommon hOuterRootInSeam
          a haK haLeft hPositiveB hActiveBoundaryInjective) with
      hFlip | hSmaller
    · exact Or.inl hFlip
    · exact Or.inr (Or.inl hSmaller)
  · push_neg at hActiveBoundaryInjective
    obtain ⟨x, hxP, hxRight, hNotInj⟩ := hActiveBoundaryInjective
    let S : Set V :=
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f
    let T : Set V := Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph S x))
    have hSClosed : Source.IsClosed S :=
      weakFreeRootPart_isClosed
        (sL := iLeft) (iL := jLeft) f hf.1
    have hTinsideS : T ⊆ S :=
      functionalClosure_neighborhood_subset_cut Source S hSClosed x
    have hCollision :
        ∃ u v : V, u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ f u = f v := by
      by_contra hNoCollision
      apply hNotInj
      intro u hu v hv hEq
      by_contra hDistinct
      exact hNoCollision ⟨u, v, hu, hv, hDistinct, hEq⟩
    exact Or.inr (Or.inr
      ⟨x, T, hxP, hxRight, rfl, hTinsideS, hCollision⟩)

end AllThoseRamseyClasses.Lifts
