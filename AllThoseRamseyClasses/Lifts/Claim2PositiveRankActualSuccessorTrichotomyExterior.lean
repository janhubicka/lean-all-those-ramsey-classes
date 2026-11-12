import AllThoseRamseyClasses.Lifts.Claim2NoEscapePositiveRankBoundaryAlternative
import AllThoseRamseyClasses.Lifts.Claim2PartnerActualGeometricOuterStepExterior
import AllThoseRamseyClasses.Lifts.ConnectedComponentBoundaryNonempty
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation

/-!
# Track C: actual positive B-rank successor with ALL exterior SOURCE support invariants

This strengthens the merged-source geometry diagnostic by requiring
the actual source flip, when it exists, to preserve exterior SOURCE
counts of every target subset, especially A-exclusive support. The
companion matched-partner wrapper uses the already verified
same-selected-Q withExterior theorem. This proof still makes no
original A-minimality or minimum mixed-piece assumption.

This is a **genuine full native source** trichotomy for an arbitrary
intermediate geometric state, not just the original A-source-minimizer.

Let P be an actual positive-width geometric outer piece of a finite
connected forbidden source, with its complete old ordered root in
the preimage S of the common target seam. Suppose P contains an
A-exclusive SOURCE anchor and positive B-exclusive SOURCE rank.

Without any source-witness A-support minimality, smallest-mixed-piece
minimality, or assumption that the weak target map is injective,
one of the following must hold:

1. An actual SAME-selected-Q full forbidden source B-to-A flip,
   preserving the original outer ordered target-root coordinates
   and global canonical relation symbol while strictly decreasing
   the B-exclusive count of SOURCE VERTICES inside a genuine
   new outer geometric piece, and exactly conserving SOURCE counts
   OUTSIDE the whole old/new geometric pieces for ALL target sets.
2. A genuine smaller POSITIVE-width native minimal-separator root
   strictly inside the generated B-component boundary, still
   lying in S and in the old geometric outer piece. Its selected
   component can be mixed: this is NOT called a valid next step.
3. The weak target map is noninjective on the entire original
   common-seam preimage S. This is a genuine collision obstruction,
   not an invented quotient or any claim about injectivity.

The nonempty boundary and actual opposite vertex are DERIVED from
source connectedness and full free-amalgam monochromaticity.
No new global 2019 theorem, preservation of next-state eligibility,
or final A-clearing contradiction is claimed. The alternative two
obstructions remain explicit even with exact exterior conservation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In any positive B-rank, A-anchored genuine geometric state,
there is either a real old-symbol rank-decreasing B-to-A source
replacement, a specifically smaller positive native source root
with exact opposite generated boundary, or a weak-map collision
on the COMPLETE common-root preimage.

No minimum original A-source-support witness and no smallest
mixed geometric piece are assumed. The smaller-root branch is
not promoted to a one-sided flippable piece. -/
theorem claim2_positiveRank_actualSuccessorWithExterior_or_smallerRoot_or_seamCollision
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
            f v ∈ TargetSet})) ∨
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
    ¬ Set.InjOn f
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) := by
  classical
  let K : Set V := geometricPieceVertices Source P
  let S : Set V := weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  by_cases hInjS : Set.InjOn f S
  · have hKclosed : Source.IsClosed K :=
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
        intro v hv w hw hvw
        exact hInjS (hTS hv) (hTS hw) hvw
      left
      exact claim2_actualGeometricRightFlip_of_boundaryPartner_withExterior
        F hFiniteF Source hFinite hForbidden
        P hn Target f hf Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        hOuterRootInSeam x hxRight hxOuter
        a haLeft haOuter
        T hT hTS hTnonempty y hSeparated hPartner hInjT
    · right
      left
      exact ⟨x, T, y, m, d, hxK, hxRight, hYa, hT,
        hm, hProper, hRootIn, hLeft, hRight, hExactRoot⟩
  · right
    right
    exact hInjS

end AllThoseRamseyClasses.Lifts
