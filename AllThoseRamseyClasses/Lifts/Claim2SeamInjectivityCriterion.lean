import AllThoseRamseyClasses.Lifts.Claim2SeamCollisionNewSideLocalization

/-!
# A precise sufficient condition for full-seam injectivity after a source flip

An old weak EHN target map may be injective on the complete preimage
of the target common seam even though a new same-Q replacement map
is not. The full native complement is embedded and retained with
exactly the old target values, so the collision-localization theorem
shows that EVERY new seam collision contains a replacement-side
SOURCE vertex outside the retained complement.

Consequently, if every such genuinely fresh Q vertex avoids the
target common seam, the whole NEW weak map is injective on its full
seam preimage. This criterion does not require arbitrary target
injectivity, a target-image quotient, finite source, or an old
A-exclusive support minimizer.

The NO-FRESH-SEAM hypothesis is a separate mathematical input.
The selected-Q canonical replacement theorem does not currently
establish it; this is a conditional continuation criterion for the
source-specific positive-rank iteration, not a completed Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- After a genuine native full free-amalgam source replacement,
old seam injectivity persists provided NO replacement-side
vertex outside the unchanged complement maps into the common
target seam. Any counterexample to new seam injectivity would
produce precisely such a fresh seam vertex by localization. -/
theorem fullNativeReplacement_seamInjective_of_noFreshSeam
    {R E Q V W UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (f : V → UT) (g : W → UT)
    (Seam : Set UT)
    (hOldSeamInj : Set.InjOn f (f ⁻¹' Seam))
    (hSameComplement : ∀ e : E,
      g (iNewE e) = f (iOldE e))
    (hNoFreshSeam : ∀ q : Q,
      iNewQ q ∉ Set.range iNewE →
      g (iNewQ q) ∉ Seam) :
    Set.InjOn g (g ⁻¹' Seam) := by
  intro x hx y hy hxy
  change g x ∈ Seam at hx
  change g y ∈ Seam at hy
  by_contra hDistinct
  rcases fullNativeReplacement_newSeamCollision_hits_replacementOutsideComplement
      iOldE iNewE iNewQ qRoot eRoot hNewFree
      f g Seam hOldSeamInj hSameComplement
      x y hx hy hxy hDistinct with
    ⟨⟨q, hq⟩, hNoE⟩ | ⟨⟨q, hq⟩, hNoE⟩
  · have hFresh : iNewQ q ∉ Set.range iNewE := by
      simpa only [hq] using hNoE
    have hSeam : g (iNewQ q) ∈ Seam := by
      simpa only [hq] using hx
    exact (hNoFreshSeam q hFresh) hSeam
  · have hFresh : iNewQ q ∉ Set.range iNewE := by
      simpa only [hq] using hNoE
    have hSeam : g (iNewQ q) ∈ Seam := by
      simpa only [hq] using hy
    exact (hNoFreshSeam q hFresh) hSeam

end AllThoseRamseyClasses.Lifts
