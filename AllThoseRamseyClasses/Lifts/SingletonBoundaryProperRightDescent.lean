import AllThoseRamseyClasses.Lifts.WeakSingletonBoundaryPartner
import AllThoseRamseyClasses.Lifts.BoundaryPartnerRightSupportDescent

/-!
# Automatic strict RIGHT-support drop inside a genuine mixed source piece

In the one-root case, all three previously explicit assumptions
in the proper B-only source flip are unnecessary:
* a boundary partner is the actual left-exclusive source vertex a;
* connectedness and separation force the generated boundary
  to be NONEMPTY, hence exactly one vertex;
* any weak EHN map is injective on a singleton boundary.

Combining the constructive source boundary-partner theorem with
the previously verified literal proper-subpiece flip produces
a real forbidden replacement with STRICTLY LESS original
right-exclusive SOURCE support. The source map itself may be
noninjective away from the unique boundary vertex.

This certifies a substantial SINGLETON boundary subcase of the
printed Claim 2. It does not prove that an arbitrary right-only
component of a smallest mixed piece has a singleton boundary,
or that a sequence of flips preserves the chosen outer piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A right-only connected source component inside a real
mixed piece P with generated boundary of cardinality at most
one can always be flipped to the left with a STRICT drop in
right-exclusive source support, provided the original full
canonical lifts of the two witnesses agree.

The complete PROPER sub-piece Q is constructed from the
source, including its full root, and the replacement is an
actual member of the forbidden family with an EHN target map. -/
theorem singletonBoundary_properRightPiece_strictSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
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
    {n : ℕ} (P : GeometricFunctionalPieceData Forbidden n)
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (x : {z : V // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxOld : x.1 ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (T : Set V)
    (hT : T = Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) f)
    (hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v)
    (a : V)
    (haOld : a ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hConnected : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨a, by simp⟩ : {z : V // z ∉ ∅})) :
    ∃ (m : ℕ) (Q : GeometricFunctionalPieceData Forbidden m),
      Set.range Q.roots = T ∧
      geometricPieceVertices Forbidden Q ⊂
        geometricPieceVertices Forbidden P ∧
      ∃ (V' : Type) (New : Structure L V'),
        F New ∧
        ∃ flip : V' → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          Nat.card {v : V' //
            flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : V //
            f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  letI : Finite V := hFinite
  obtain ⟨y, hYa, hSep, hYBoundary⟩ :=
    weakRightComponent_singletonBoundary_hasPartner
      hFree f hf x hxRight T hT hTS
      hSingleton a haLeft hConnected
  have hPathY : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨(outsideCutMap hTS x).1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    change ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})
    simpa only [hYa] using hConnected
  have hTclosed : Forbidden.IsClosed T := by
    rw [hT]
    exact Forbidden.functionClosure_isClosed
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))
  have hMin :
      IsMinimalClosedSeparator Forbidden T
        (outsideCutMap hTS x) y :=
    singletonClosedCut_isMinimal_of_connectedSeparation
      Forbidden T hTclosed hSingleton
      (outsideCutMap hTS x) y hSep hPathY
  have hTnonempty : T.Nonempty :=
    minimalClosedSeparator_nonempty_of_emptyCut_path
      Forbidden T (outsideCutMap hTS x) y hMin hPathY
  have hInjT : Set.InjOn f T := by
    intro u hu v hv _hEq
    exact hSingleton u v hu hv
  exact boundaryPartner_properRightPiece_strictRightSupport
    F hFiniteF Forbidden hFinite hForbidden
    Target f hf Left Right jLeft jRight X iLeft iRight
    hFree hCommon P hRoots x hxOld hxRight
    T hT hTS y hSep hYBoundary
    a haOld haLeft hTnonempty hInjT

end AllThoseRamseyClasses.Lifts
