import AllThoseRamseyClasses.Lifts.Claim2ActualOppositeColorRootDichotomy
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# Claim 2: positive local B-source support gives a concrete boundary alternative

The original finite connected forbidden-family hypotheses make
the selected A-only and B-only SOURCE vertices path-connected.
The previous Track C lemmas separately proved:

* a positive natural-number B-exclusive SOURCE support count in
  an actual geometric outer piece rooted in the shared target seam
  supplies a real right-exclusive vertex x in its selected component;
* any such x and any connected left-exclusive vertex a in that
  same component automatically determine the generated B-boundary
  T=Cl(N(component(Source minus S,x))) and its opposite a-side
  boundary, with the exhaustive alternative:
    matching boundary partner, or
    strictly smaller positive-width genuine geometric root.

This module composes those results WITHOUT assuming intermediate
A-exclusive support minimality. The whole source may change across
the contextual B-to-A flips; only its current finite forbidden
membership, connectivity, true target free amalgam and actual
weak EHN map enter.

This finishes the source-geometric choice of x,T,y from a
POSITIVE local B-rank. It does not turn the smaller-root
mixed piece into a flippable B-only piece, nor certify the new
outer context as the same genuine geometric selected component.
Both remain essential to the unrestricted 2019 Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An ACTUAL positive local B-only SOURCE count and one A-exclusive
vertex inside a genuine geometric outer piece of any finite
CONNECTED forbidden EHN source force a fully determined
native generated-boundary dichotomy.

The B component x is SELECTED from the positive source count,
its full boundary T is constructed (not an independent argument),
the opposite y is the original A-exclusive source vertex a,
and the smaller-root alternative is genuine and positive-width.

No intermediate left-minimality, chosen partner, weak-map
injectivization, arbitrary smaller-separator oracle, or extra
connectedness assumption beyond the original forbidden source
family is used. -/
theorem claim2_positiveRightCount_partner_or_smallerPositiveRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (haOuter : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (hPositive : 0 < Nat.card {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
      (T : Set V),
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      x.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      ∃ (y : {v : V // v ∉ T}),
        y.1 = a ∧
        (Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph T y)) = T ∨
         ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
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
  letI : Finite V := hFinite
  obtain ⟨x, hxRight, hxOuter⟩ :=
    claim2_positiveLocalRightSupport_hasComponentVertex
      Source Target Left Right jLeft jRight
      X iLeft iRight hFree f P hRootInSeam hPositive
  let T : Set V := Source.functionClosure
    (gaifmanNeighborhood Source.graph
      (componentFrom Source.graph
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))
  have hPath : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach Source
      ((hConnected Source hFinite hForbidden).2 x.1 a)
  obtain ⟨y, hYa, hAlternative⟩ :=
    claim2_actualOppositeColors_partner_or_positiveSmallerRoot
      Source hFinite Target f hf Left Right jLeft jRight
      X iLeft iRight hFree P hRootInSeam
      x hxRight hxOuter a haLeft haOuter hPath T rfl
  exact ⟨x, T, hxRight, hxOuter, rfl, y, hYa, hAlternative⟩

/-- Every positive interior B-exclusive source rank in a connected
forbidden witness exhibits exactly one of three certified
obstructions/actions, WITHOUT intermediate A-support minimality:

1. two distinct vertices of the selected full generated
   boundary T have COLLIDING weak target images;
2. the A-exclusive opposite component has the SAME full
   generated boundary T, and f is INJECTIVE on T, precisely
   the partner/root condition needed by the actual B→A flip;
3. a genuine POSITIVE-width minimal-separator root lies
   strictly inside T and inside the current outer piece.

The middle branch is constructive by the verified partner-based
contextual flip; the third is not assumed B-only. -/
theorem claim2_positiveRightCount_collision_or_flippablePartner_or_smallerRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (haOuter : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (hPositive : 0 < Nat.card {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
      (T : Set V),
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      x.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      ∃ (y : {v : V // v ∉ T}),
        y.1 = a ∧
        ((∃ u v : V, u ∈ T ∧ v ∈ T ∧
            u ≠ v ∧ f u = f v) ∨
         (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph T y)) = T ∧
          Set.InjOn f T) ∨
         ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
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
  obtain ⟨x, T, hxRight, hxOuter, hT, y, hYa, hAlt⟩ :=
    claim2_positiveRightCount_partner_or_smallerPositiveRoot
      F hConnected Source hFinite hForbidden
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree P hRootInSeam
      a haLeft haOuter hPositive
  refine ⟨x, T, hxRight, hxOuter, hT, y, hYa, ?_⟩
  rcases hAlt with hPartner |
    ⟨m, d, hm, hProper, hInside, hDx, hDa, hBoundary⟩
  · by_cases hInj : Set.InjOn f T
    · exact Or.inr (Or.inl ⟨hPartner, hInj⟩)
    · left
      by_contra hNoCollision
      apply hInj
      intro u hu v hv hEq
      by_contra hNe
      exact hNoCollision ⟨u, v, hu, hv, hNe, hEq⟩
  · exact Or.inr (Or.inr
      ⟨m, d, hm, hProper, hInside, hDx, hDa, hBoundary⟩)


end AllThoseRamseyClasses.Lifts
