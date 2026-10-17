import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import AllThoseRamseyClasses.Lifts.FoldedSingleRightSupportDecrease

/-!
# The complete support-minimality contradiction in the one-right-component case

The verified folded-root special-case flip already constructs an
ACTUAL replacement forbidden source and weak EHN map with strictly
fewer left-exclusive SOURCE vertices whenever the source's opposite
exclusive region is connected.

The independent minimization lemma chooses a FINITE forbidden-source
weak witness minimizing that exact support count, WITHOUT invoking
the invalid blanket homomorphism-embedding injectivization.

This module composes these two mechanisms: a support-minimal actual
forbidden witness CANNOT satisfy the connected-right-region and
common-full-folded-lift hypotheses. The replacement is explicitly
packaged back into the same finite forbidden-witness type.

This is a closed, conditional FIRST minimality contradiction, not
the unrestricted Claim 1 / Claim 2 or strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A support-minimal finite forbidden witness into an actual
functional free amalgam cannot have the one-sided configuration
covered by the folded-root flip.

Unlike the printed WLOG reduction, neither the minimal old map
nor its replacement is assumed injective, and full functional
root/side data are not weakened. -/
theorem minimalFoldedWitness_contradiction_of_connectedRightRegion
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonFoldedGlobalCanonicalLift
      F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (x y : w.Carrier)
    (hx : x ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (hy : y ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hConnected : ReachOutside w.source.graph
      (∅ : Set w.Carrier)
      (⟨x, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨y, by simp⟩ : {z : w.Carrier // z ∉ ∅}))
    (hAllRight : ∀ z : w.Carrier,
      (hz : z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight)
        w.toTarget) →
      ReachOutside w.source.graph
        (weakFreeRootPart (sL := iLeft) (iL := jLeft)
          w.toTarget)
        ⟨y, hy.2⟩ ⟨z, hz.2⟩) :
    False := by
  obtain ⟨V', New, hNewForbidden, f', hf', hStrict⟩ :=
    foldedFirstMinimality_of_connectedRightRegion
      F hFiniteF w.source w.finiteCarrier w.forbidden
      Target w.toTarget w.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon x y hx hy hConnected hAllRight
  let replacement : ForbiddenEHNWitness F Target := {
    Carrier := V'
    finiteCarrier := hFiniteF New hNewForbidden
    source := New
    forbidden := hNewForbidden
    toTarget := f'
    homEmbedding := hf'
  }
  have hDrop :
      replacement.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) <
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) := hStrict
  exact (minimalForbiddenEHNWitness_no_strict_drop
    (fullFreeLeftExclusiveTarget iLeft jLeft)
    w hMin replacement) hDrop

end AllThoseRamseyClasses.Lifts
