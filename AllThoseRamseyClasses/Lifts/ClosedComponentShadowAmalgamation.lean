import AllThoseRamseyClasses.Lifts.WholeComponentTaggedDescent
import AllThoseRamseyClasses.Lifts.EHNFullSideFactor
import Mathlib.Data.Set.Card

/-!
# Conditional strong free amalgamation of a full all-component tagged witness

The source-preserving STRICT A-only support descent theorem for all
closed-root component tags removes the entire printed Claim 2
multicomponent obstruction, PROVIDED a common FULL auxiliary
all-component tagged expansion X is already induced by both
witnesses A and B.

This module closes the Noetherian argument for ONE named finite
source, with no injectivity of forbidden weak HE maps:

  Assume A and B are fully embedded in a genuine target functional
  free amalgam D=A⊕_X B, and their all-component tagged canonical
  lifts share one actual full induced expansion of X. If the
  named forbidden source admits NO weak EHN map into B, it admits
  NO weak EHN map into D.

Proof: minimize the number of SOURCE vertices sent A-only among
all weak EHN maps of the SAME named finite source into D.
If the minimum is positive, use the verified whole-component
tagged flip to produce a strictly smaller weak map of the SAME
source. If the minimum is zero, all source vertices map into B,
and a full-side factorization gives a forbidden weak map into B.

This proves a real conditional SHADOW amalgamation statement for
one named source, with NO minimal separator/piece quotient and NO
right-component connectivity hypothesis. It does NOT prove the
class of MAXIMAL tagged lifts has amalgamation, since the common
full tagged expansion remains an input; neither does it validate
the printed 2019 regular infinite-family theorem.
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
theorem wholeComponentTaggedLift_freeAmalgam_avoids_source
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
    (hCommon : CommonAllClosedComponentLift
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
      wholeComponentTaggedLift_strict_leftSupport
        Source Target f hf Left Right
        jLeft jRight X iLeft iRight
        hFree hCommon x hx
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
