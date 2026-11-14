import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# The weak B-only source partition equals the exact right-exclusive target pullback

In the verified 2019 native full target free amalgam, the left and
right images meet ONLY in their exact shared full root. Therefore
the "right and outside the LEFT shared-root preimage" predicate used
by the source Gaifman component lemmas is literally the same as
the original B-exclusive target region used by B-SOURCE rank and
generated-boundary injection transfers.

The right root image and left root image coincide as actual sets
inside Target; no injectivity of the weak SOURCE map is needed.

This statement is the missing source/target predicate alignment
when applying an actual selected-Q same-witness boundary-injection
certificate to the next positive-rank active-boundary state.
No claim that the initial source map is injective.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In an ACTUAL target free amalgam, the B-exclusive weak source
partition is exactly the pullback of the full B-exclusive target
set. The original weak source map may have arbitrary collisions
outside its explicitly injective rooted tests. -/
theorem weakFreeRightPart_iff_fullFreeRightExclusiveTarget
    {U UX UA UB UT : Type}
    {X : Structure L UX}
    {Left : Structure L UA}
    {Right : Structure L UB}
    {Target : Structure L UT}
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (f : U → UT) (x : U) :
    x ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ↔
      f x ∈ fullFreeRightExclusiveTarget iRight jRight := by
  constructor
  · rintro ⟨⟨b, hb⟩, hNotLeftRoot⟩
    constructor
    · exact ⟨b, hb.symm⟩
    · rintro ⟨r, hr⟩
      apply hNotLeftRoot
      refine ⟨r, ?_⟩
      calc
        jLeft (iLeft r) = jRight (iRight r) :=
          (hFree.overlap (iLeft r) (iRight r)).mpr
            ⟨r, rfl, rfl⟩
        _ = f x := hr
  · rintro ⟨⟨b, hb⟩, hNotRightRoot⟩
    refine ⟨⟨b, hb.symm⟩, ?_⟩
    rintro ⟨r, hr⟩
    apply hNotRightRoot
    refine ⟨r, ?_⟩
    calc
      jRight (iRight r) = jLeft (iLeft r) :=
        ((hFree.overlap (iLeft r) (iRight r)).mpr
          ⟨r, rfl, rfl⟩).symm
      _ = f x := hr

end AllThoseRamseyClasses.Lifts
