import AllThoseRamseyClasses.Lifts.Claim2SingletonActualGeometricOuterStep
import AllThoseRamseyClasses.Lifts.Claim2PositiveRankNoEscapeComponent
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece
import AllThoseRamseyClasses.Lifts.ConnectedComponentBoundaryNonempty

/-!
# Positive B-source rank: actual geometric successor under singleton boundaries

Let P be an ACTUAL original outer geometric minimal-separator piece
in a finite CONNECTED forbidden native functional source.
Its entire ordered outer root lies in the full target-root seam S.
Assume that the WHOLE outer geometric context K=vertices(P) has
the source no-escape property relative to S, has a genuine A-only
anchor, and has positive local B-only SOURCE support.

The verified positive-rank component selector picks an ACTUAL B-only
S-component, with its complete generated boundary T contained in
S∩K. Under the separately EXPLICIT hypothesis that ALL such chosen
B-only components have at most singleton generated boundary,
the singleton partner theorem finds the opposite complete boundary
and gives source-root injectivity on T for FREE. The concrete
same-selected-Q B→A source flip now produces an ACTUAL new outer
geometric minimal separator with the SAME original ordered root,
original global canonical relation symbol, and a STRICT decrease
of local B-only SOURCE support inside the entire geometric piece.

Unlike the earlier singleton-boundary closed-context theorem,
this returns an actual geometric successor in the selected
singleton/no-escape subcase; no separate chosen B-only vertex
or matched partner is an input.

This does NOT imply every intermediate state again has
the singleton/no-escape property, and the arbitrary mixed
higher-width boundary case and final A-clearing flip remain open.
Neither source-map injectivity nor an image quotient is asserted.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Positive B-only SOURCE support and an A-only anchor in a
geometric no-escape outer piece yield an actual strict
old-symbol geometric successor, PROVIDED all relevant
generated B-component boundaries contain at most one vertex.

This removes any existential choice of the B-only starting
vertex or opposite complete boundary partner from the input. -/
theorem claim2_positiveRank_singletonBoundary_actualGeometricOuterStep
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
      f v ∈ fullFreeRightExclusiveTarget iRight jRight})
    (hSingletonBoundaries :
      ∀ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        let T : Set V := Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))
        ∀ u v : V, u ∈ T → v ∈ T → u = v) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
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
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  let K : Set V := geometricPieceVertices Source P
  let S : Set V := weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  have hNoEscape : FunctionalContextNoEscapeOutsideSeam Source
      S (geometricPieceVertices Source P) :=
    geometricPiece_noEscapeOutsideContainingSeam
      Source P S hOuterRootInSeam
  have hKclosed : Source.IsClosed K :=
    functionalComponentUnion_isClosed Source
      (Set.range P.roots) P.minimal.1 P.left
  obtain ⟨x, T, hxK, hxRight, _hCompInside,
      hComponentRight, hT, _hTInside⟩ :=
    positiveLocalRightSupport_noEscape_hasInnerComponent
      Source hFinite Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree K hKclosed hNoEscape hPositiveB
  have hxOuter :
      x.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
    rcases hxK with hRoot | hComponent
    · obtain ⟨i, hi⟩ := hRoot
      have hxSeam : x.1 ∈ S := hi ▸
        hOuterRootInSeam ⟨i, rfl⟩
      exact False.elim (x.2 hxSeam)
    · exact hComponent
  have haOuter :
      a ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
    rcases haK with hRoot | hComponent
    · obtain ⟨i, hi⟩ := hRoot
      have haSeam : a ∈ S := hi ▸
        hOuterRootInSeam ⟨i, rfl⟩
      exact False.elim (haLeft.2 haSeam)
    · exact hComponent
  have haNotComponent :
      a ∉ componentFrom Source.graph S x := by
    intro haComponent
    have haRight : a ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
      hComponentRight a haComponent
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree f))
        haLeft haRight
  have hConnectedPath : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach Source
      ((hConnected Source hFinite hForbidden).2 x.1 a)
  have hTnonempty : T.Nonempty := by
    rw [hT]
    exact functionalComponent_generatedBoundary_nonempty_of_emptyCutReach
      Source S x a haNotComponent hConnectedPath
  have hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v := by
    intro u v hu hv
    apply (hSingletonBoundaries x hxK hxRight) u v
    · simpa only [hT] using hu
    · simpa only [hT] using hv
  exact claim2_actualGeometricRightFlip_of_singletonBoundary
    F hFiniteF Source hFinite hForbidden
    P hn Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    hOuterRootInSeam x hxRight hxOuter
    a haLeft haOuter
    T hT hTnonempty hSingleton hConnectedPath

end AllThoseRamseyClasses.Lifts
