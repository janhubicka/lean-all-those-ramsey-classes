import AllThoseRamseyClasses.Lifts.Claim2NoEscapePositiveRankBoundaryAlternative
import AllThoseRamseyClasses.Lifts.Claim2PartnerActualGeometricOuterStepExterior
import AllThoseRamseyClasses.Lifts.ConnectedComponentBoundaryNonempty
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation

/-!
# Track C: positive-rank actual successor OR smaller root with local injection

At an arbitrary intermediate genuine positive-width geometric piece P
inside a finite connected forbidden native functional source, assume
P's ordered root lies in the target common-seam preimage, there is
a real A-exclusive source anchor inside P and a positive B-exclusive
SOURCE count inside P.

Only the COMPLETE generated functional boundaries of B-exclusive
S-components in P must be mapped injectively to Target. The weak map
on the ENTIRE common-seam preimage S may be noninjective.

The checked no-escape source boundary alternative selects the actual
B-only component and its complete generated boundary T, plus a
separated A-only anchor. If the opposite generated boundary matches
T, local injectivity on T suffices for the merged one-selected-Q
source flip, preserving unchanged outer ordered root coordinates,
global canonical relation symbol and all exterior SOURCE counts,
strictly decreasing the B-only SOURCE count inside the new outer
geometric piece, and preserving a real A-only SOURCE anchor in
the same new piece. Otherwise the opposite boundary gives a
genuine smaller positive native separator root inside T; its
selected component can be MIXED and is NOT automatically flippable.

This is a two-branch conditional positive-rank theorem. Neither
global S injectivity nor source-witness A-minimality nor the
smallest-mixed-piece assumption is made. It does NOT resolve the
smaller-root mixed branch, assert arbitrary next-step eligibility,
prove a zero-B-rank terminal contradiction or establish general
2019 strong amalgamation. Full source functional arities are used,
without weak-image quotienting or image-cardinality counting.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under injectivity on all B-active generated boundaries of
an A-anchored genuine positive-rank geometric state, there is
either one actual old-symbol strictly B-rank-decreasing source
replacement or a smaller positive native separator root with
the complete opposite generated boundary.

Neither the full common-seam preimage nor the weak source map
need be injected globally. No original A-support minimizer or
smallest mixed-piece hypothesis is assumed. The smaller-root
branch is not automatically one-sided or flippable. -/
theorem claim2_positiveRank_actualSuccessor_or_smallerRoot_of_activeBoundaryInjective
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
    (hActiveBoundaryInjective :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
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
            (componentFrom Source.graph T y))) := by
  classical
  let K : Set V := geometricPieceVertices Source P
  let S : Set V := weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  have hKclosed : Source.IsClosed K :=
    functionalComponentUnion_isClosed Source
      (Set.range P.roots) P.minimal.1 P.left
  have hNoEscape : FunctionalContextNoEscapeOutsideSeam Source S K :=
    geometricPiece_noEscapeOutsideContainingSeam
      Source P S hOuterRootInSeam
  obtain ⟨x, T, hxK, hxRight, hT, hTInside,
      y, hYa, hAlternative⟩ :=
    positiveLocalRightRank_noEscape_partner_or_smallerRoot
      F hConnected Source hFinite hForbidden
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree
      K hKclosed hNoEscape a haK haLeft hPositiveB
  have hTS : T ⊆ S := fun z hz => (hTInside hz).1
  rcases hAlternative with hPartner |
      ⟨m, d, hm, hProper, hRootIn, hLeft, hRight, hExactRoot⟩
  · have hxOuter : x.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
      rcases hxK with hRoot | hComponent
      · obtain ⟨i, hi⟩ := hRoot
        have hxSeam : x.1 ∈ S := hi ▸
          hOuterRootInSeam ⟨i, rfl⟩
        exact False.elim (x.2 hxSeam)
      · exact hComponent
    have haOuter : a ∈ functionalComponentFrom Source
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
        weakFreePartition_component_right
          hFree f hf.1 x hxRight haComponent
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
    obtain ⟨y', hy'Val, hSeparated'⟩ :=
      weakRightComponent_leftVertex_separatedByBoundary
        hFree f hf x hxRight T hT hTS a haLeft
    have hYeq : y' = y := Subtype.ext (hy'Val.trans hYa.symm)
    have hSeparated : ¬ ReachOutside Source.graph T
        (outsideCutMap hTS x) y := by
      simpa only [hYeq] using hSeparated'
    have hInjT : Set.InjOn f T := by
      rw [hT]
      exact hActiveBoundaryInjective x hxK hxRight
    left
    exact claim2_actualGeometricRightFlip_of_boundaryPartner_withExteriorAndAnchor
      F hFiniteF Source hFinite hForbidden
      P hn Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hOuterRootInSeam x hxRight hxOuter
      a haLeft haOuter
      T hT hTS hTnonempty y hSeparated hPartner hInjT
  · right
    exact ⟨x, T, y, m, d, hxK, hxRight, hYa, hT,
      hm, hProper, hRootIn, hLeft, hRight, hExactRoot⟩


end AllThoseRamseyClasses.Lifts
