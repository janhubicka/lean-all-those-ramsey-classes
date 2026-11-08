import AllThoseRamseyClasses.Lifts.ConnectedComponentBoundaryNonempty
import AllThoseRamseyClasses.Lifts.Claim2PositiveRankNoEscapeComponent
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# A positive B-only local SOURCE rank gives a NONEMPTY generated root

The verified no-escape component selector obtains a genuine
B-exclusive source vertex x inside the current closed context K,
its entire monochromatic component C after deleting the full
weak-target common-root preimage S, and the complete native
generated boundary T = Cl(N(C)), with T contained in S∩K.

Previously, subsequent partner/singleton arguments required
T.Nonempty as a separate hypothesis. In a connected forbidden
SOURCE containing an actual A-exclusive anchor a, this is
automatic. The entire S-component C containing x consists
of B-exclusive source vertices, whereas a is A-exclusive,
so a lies outside C. Actual source connectedness supplies a
full Gaifman path from x to a. The verified source-native
boundary lemma forces N(C), and hence its full function-generated
closure T, to be nonempty.

This uses no weak target-map injectivity, no singleton assumption,
no minimality of the current source/context, and no replacement
of set-valued function fibres by partial graph incidence.

The root may still have multiple vertices with colliding TARGET
images. The required opposite matching boundary partner, or
strictly smaller positive root with the right one-sided status,
remains separate mathematical work in the general Claim 2 step.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Positive B-only SOURCE support in a genuine closed no-escape
context K together with an A-exclusive SOURCE anchor, in a finite
connected forbidden source, gives a true B-only S-component with
COMPLETE NONEMPTY function-generated boundary T inside S∩K.

No independent boundary nonemptiness oracle, source support
minimality, singleton/partner condition, target-image root
injectivity, or hypothesis that K itself is geometric occurs. -/
theorem positiveLocalRightSupport_noEscape_has_nonemptyGeneratedBoundary
    (F : ∀ {Z : Type}, Structure L Z → Prop)
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
    (K : Set V) (hKclosed : Source.IsClosed K)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) K)
    (a : V) (haK : a ∈ K)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hPositive :
      0 < Nat.card {v : V //
        v ∈ K ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
      (T : Set V),
      x.1 ∈ K ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      componentFrom Source.graph
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x ⊆ K ∧
      (∀ z : V,
        z ∈ componentFrom Source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x →
        z ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f) ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩ K ∧
      T.Nonempty := by
  let S : Set V := weakFreeRootPart
    (sL := iLeft) (iL := jLeft) f
  obtain ⟨x, T, hxK, hxRight, hComponentInside,
      hComponentRight, hT, hTInside⟩ :=
    positiveLocalRightSupport_noEscape_hasInnerComponent
      Source hFinite Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree K hKclosed hNoEscape hPositive
  have haNotComponent :
      a ∉ componentFrom Source.graph S x := by
    intro haComponent
    have haRight : a ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
      hComponentRight a haComponent
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree f))
        haLeft haRight
  have hFullPath : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach Source
      ((hConnected Source hFinite hForbidden).2 x.1 a)
  have hNonempty : T.Nonempty := by
    rw [hT]
    exact functionalComponent_generatedBoundary_nonempty_of_emptyCutReach
      Source S x a haNotComponent hFullPath
  exact ⟨x, T, hxK, hxRight, hComponentInside,
    hComponentRight, hT, hTInside, hNonempty⟩

end AllThoseRamseyClasses.Lifts
