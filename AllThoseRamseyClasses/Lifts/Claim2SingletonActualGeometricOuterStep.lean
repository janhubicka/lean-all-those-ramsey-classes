import AllThoseRamseyClasses.Lifts.Claim2PartnerActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.WeakSingletonBoundaryPartner

/-!
# Singleton boundary produces an actual strict B-source geometric successor

When the chosen B-only native S-component has a nonempty
ONE-VERTEX function-generated boundary, the pre-existing
singleton-boundary theorem provides its genuine opposite
boundary partner and trivial injectivity ON THAT ROOT.
The new matched-partner theorem then performs ONE selected
canonical B→A source flip and produces a GENUINE new outer
geometric minimal-separator piece, with the entire original
ordered root, global class symbol, and strictly fewer
B-exclusive SOURCE vertices.

This replaces the earlier singleton *closed context* endpoint
with an actual outer geometric piece in its conditional setting.
Positive OUTER root width is explicit for the global symbol.
The full native language and noninjective weak target maps
are retained; no additional root injectivity assumption is made.

The singleton-boundary case does NOT cover general mixed
non-singleton complete boundaries, nor does it imply that
the next state also satisfies a singleton-boundary hypothesis
or that a terminal A-clearing flip exists. Manuscript frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual right-exclusive source component with a nonempty
singleton complete generated boundary yields a proper selected
inner flip, a genuine old-symbol new outer geometric piece,
and a strict drop of its B-only SOURCE-vertex rank. -/
theorem claim2_actualGeometricRightFlip_of_singletonBoundary
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n : ℕ} (P : GeometricFunctionalPieceData Forbidden n)
    (hn : 0 < n)
    (Target : Structure L UT) (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
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
    (x : {v : V // v ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hxOuter : x.1 ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (haOuter : a ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (T : Set V)
    (hT : T = Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
    (hTnonempty : T.Nonempty)
    (hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v)
    (hConnected : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅})) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Forbidden m),
      0 < m ∧
      geometricPieceVertices Forbidden d ⊂
        geometricPieceVertices Forbidden P ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New n),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin n, flip (newOuter.roots i) = f (P.roots i)) ∧
        geometricGlobalPieceSymbol F Forbidden
            hFinite hForbidden P hn =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter hn ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Forbidden P ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  have hSclosed : Forbidden.IsClosed S :=
    weakFreeRootPart_isClosed (sL := iLeft) (iL := jLeft) f hf.1
  have hTS : T ⊆ S := by
    intro z hz
    exact functionalClosure_neighborhood_subset_cut
      Forbidden S hSclosed x
      (by simpa only [hT] using hz)
  obtain ⟨y, _hyVal, hSep, hYBoundary⟩ :=
    weakRightComponent_singletonBoundary_hasPartner
      hFree f hf x hxRight T hT hTS
      hSingleton a haLeft hConnected
  have hInjT : Set.InjOn f T := by
    intro u hu v hv _huv
    exact hSingleton u v hu hv
  exact claim2_actualGeometricRightFlip_of_boundaryPartner
    F hFiniteF Forbidden hFinite hForbidden
    P hn Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    hOuterRootInSeam x hxRight hxOuter
    a haLeft haOuter
    T hT hTS hTnonempty y hSep hYBoundary hInjT

end AllThoseRamseyClasses.Lifts
