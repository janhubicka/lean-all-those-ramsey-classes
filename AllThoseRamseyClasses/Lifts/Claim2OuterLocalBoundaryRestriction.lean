import AllThoseRamseyClasses.Lifts.Claim2PositiveRankActiveBoundaryDichotomy

/-!
# Track C: restrict local B-boundary injectivity to the retained source

The verified positive-rank dichotomy assumes source-map injectivity
on complete function-generated boundaries of every B-exclusive
source component in a fixed actual geometric outer piece.

The piece-scoped full-native free-amalgam transfer is stated using
vertices of the complete RETAINED source E whose OLD coordinates
lie in that outer piece. This is not a stronger hypothesis:
every such retained source vertex is already an actual old source
vertex, and its B-exclusive target image gives a genuine B-only
source component root outside the full seam preimage.

This standalone lemma performs the precise conversion, with no
new weak source injection premise, no target quotient and no
source-cardinality assumption. It applies to ANY full old
source embedding of a retained piece, independently of the
selected-Q replacement.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The local injection hypothesis of the positive-rank
geometric Claim 2 step restricts to the full retained E-side
source vertices belonging to the OLD outer geometric piece.

The target B-exclusive membership, expressed using actual
full target images, supplies the genuine source B-component
root required by the original hypothesis. -/
theorem claim2_outerBActiveBoundaryInjection_restrict_to_retainedComplement
    {V E UX UA UB UT : Type}
    {Old : Structure L V} {Complement : Structure L E}
    {X : Structure L UX} {Left : Structure L UA}
    {Right : Structure L UB} {Target : Structure L UT}
    (iOldE : Structure.Embedding Complement Old)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (f : V → UT)
    (OldPart : Set V)
    (hOldLocalInjection :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ OldPart →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Old.functionClosure
            (gaifmanNeighborhood Old.graph
              (componentFrom Old.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
    ∀ (e : E) (heOldPart : iOldE e ∈ OldPart)
      (heRight : f (iOldE e) ∈
        fullFreeRightExclusiveTarget iRight jRight)
      (heOutside : f (iOldE e) ∉
        Set.range (jLeft.comp iLeft)),
      Set.InjOn f
        (Old.functionClosure
          (gaifmanNeighborhood Old.graph
            (componentFrom Old.graph
              (f ⁻¹' Set.range (jLeft.comp iLeft))
              (⟨iOldE e, heOutside⟩ :
                {v : V // v ∉ f ⁻¹' Set.range (jLeft.comp iLeft)})))) := by
  intro e heOldPart heRight heOutside
  have hxOutside :
      iOldE e ∉ weakFreeRootPart
        (sL := iLeft) (iL := jLeft) f := heOutside
  have hxB :
      iOldE e ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
    obtain ⟨⟨b, hb⟩, _⟩ := heRight
    exact ⟨⟨b, hb.symm⟩, hxOutside⟩
  exact hOldLocalInjection ⟨iOldE e, hxOutside⟩ heOldPart hxB

end AllThoseRamseyClasses.Lifts
