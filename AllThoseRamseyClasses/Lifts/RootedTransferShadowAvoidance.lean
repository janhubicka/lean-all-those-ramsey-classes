import AllThoseRamseyClasses.Lifts.GenericClosedComponentTransfer
import AllThoseRamseyClasses.Lifts.EHNFullSideFactor
import Mathlib.Data.Set.Card

/-!
# Forbidden-source avoidance under generic closed-component relation transfer

This abstract theorem needs only realization transfer for EVERY
authentic function-closed-root component of one finite source.
It does not require a specific tagged language or a common full
lift interface; those are mechanisms for establishing the transfer
hypothesis.

Suppose D is a full functional free amalgam of Left and Right.
If the source has no weak EHN map to Right, and each weak realization
in Left of an actual native full closed-root component rooted in X
transfers to Right on the same (possibly colliding) root tuple,
then the source has NO weak EHN map into D.

Proof uses finite minimization of A-only source vertices among
all maps of the unchanged source: any A-only component can be
folded into Right using transfer, strictly reducing the count.
At support zero the entire weak map factors through Right,
contradiction. No injective reduction, minimal separating cut,
component connectivity, forbidden quotient, or change of source.

This is a reusable shadow-level avoidance theorem. The original
2019 Section 3 maximal-lift and Ramsey conclusions remain open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A precise conditional source-specific free-amalgam avoidance
theorem for the finite all-component folded lift.

One named finite source does not weakly homomorphism-embed into
D=A⊕_X B if it does not weakly embed into B and there is a
common FULL induced all-component canonical tagged expansion on
X in A and B. The proof never assumes the source map is injective. -/
theorem wholeComponentRootedTransfer_freeAmalgam_avoids_source
    {V UX UA UB UT : Type}
    [Finite V]
    (Source : Structure L V)
    (Target : Structure L UT)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hTransfer : AllClosedComponentRootedTransfer
      Source X Left Right iLeft iRight)
    (hRightAvoid : ∀ g : V → UB,
      ¬ Source.IsEHNHomomorphismEmbedding Right g) :
    ∀ f : V → UT,
      ¬ Source.IsEHNHomomorphismEmbedding Target f := by
  classical
  let AOnly : Set UT :=
    fullFreeLeftExclusiveTarget iLeft jLeft
  let count : (V → UT) → ℕ :=
    fun g => Nat.card {v : V // g v ∈ AOnly}
  let counts : Set ℕ :=
    {n | ∃ g : V → UT,
      Source.IsEHNHomomorphismEmbedding Target g ∧ count g = n}
  by_contra hBad
  push_neg at hBad
  obtain ⟨fBad, hfBad⟩ := hBad
  have hCounts : counts.Nonempty :=
    ⟨count fBad, fBad, hfBad, rfl⟩
  have hMin : sInf counts ∈ counts :=
    Nat.sInf_mem hCounts
  obtain ⟨f, hf, hCountMin⟩ := hMin
  have hMinimal (g : V → UT)
      (hg : Source.IsEHNHomomorphismEmbedding Target g) :
      count f ≤ count g := by
    rw [hCountMin]
    exact Nat.sInf_le (show count g ∈ counts from
      ⟨g, hg, rfl⟩)
  by_cases hA : ∃ x : V, f x ∈ AOnly
  · obtain ⟨x, hxA⟩ := hA
    have hx : x ∈ weakFreeLeftPart
        (sL := iLeft) (iL := jLeft) f :=
      (weakFreeLeftPart_iff_targetExclusive
        iLeft jLeft f x).mpr hxA
    obtain ⟨g, hg, hStrict⟩ :=
      wholeComponent_strict_leftSupport_of_rootedTransfer
        Source Target f hf Left Right
        jLeft jRight X iLeft iRight
        hFree hTransfer x hx
    have hlt : count g < count f := hStrict
    exact (Nat.not_lt_of_ge (hMinimal g hg)) hlt
  · have hImage : ∀ x : V, ∃ y : UB,
        f x = jRight y := by
      intro x
      have hnotA : f x ∉ AOnly := by
        intro hx
        exact hA ⟨x, hx⟩
      rcases hFree.covers (f x) with ⟨a, ha⟩ | ⟨b, hb⟩
      · have hxRoot : f x ∈ Set.range (jLeft.comp iLeft) := by
          by_contra hnotRoot
          apply hnotA
          exact ⟨⟨a, ha.symm⟩, hnotRoot⟩
        obtain ⟨r, hr⟩ := hxRoot
        refine ⟨iRight r, ?_⟩
        calc
          f x = jLeft (iLeft r) := hr.symm
          _ = jRight (iRight r) :=
            (hFree.overlap (iLeft r) (iRight r)).mpr
              ⟨r, rfl, rfl⟩
      · exact ⟨b, hb⟩
    obtain ⟨g, hg, _hfactor⟩ :=
      ehnHomomorphismEmbedding_factor_full_side
        hf jRight hImage
    exact (hRightAvoid g) hg

end AllThoseRamseyClasses.Lifts
