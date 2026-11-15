import AllThoseRamseyClasses.Lifts.FullRangeSaturationNormalForm
import AllThoseRamseyClasses.Lifts.GlobalOriginalClaim1OneSided

/-!
# Claim 1 for the explicitly repaired relational presentation

Start from any ORIGINAL forbidden witness. Saturate the forbidden
family, and minimize original-source support over the SATURATED family.
The full-image normalization produces an actual full embedding at that
minimum, so ALL its selected ordered roots are injective automatically.
The existing genuine source-replacement proof of Claim 1 then applies.

Crucially, the common canonical lift is indexed by the SATURATED family.
Agreement of the old F-lifts is not substituted for this new hypothesis.
No regularity of an infinite saturation, Claim 2 iteration, or strong AP
is asserted here. There is no pairwise root-test-cover assumption.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} [IsEmpty L.FuncSymbol]

/-- A genuine full source-support minimizer for the repaired relational
family satisfies Claim 1 for EVERY selected positive-width geometric
piece with its roots in the complete common seam. Root-image injection
is derived, not assumed. The required common lift is the repaired one. -/
theorem exists_saturatedRelational_fullMinimizer_with_claim1
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift
      (FullRangeEHNSaturation F) X Left Right iLeft iRight)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ w : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
      (∃ e : Structure.Embedding w.source Target,
        ∀ x : w.Carrier, e x = w.toTarget x) ∧
      (∀ v : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      (∀ {n : ℕ} (d : GeometricFunctionalPieceData w.source n),
        0 < n →
        Set.range d.roots ⊆
          weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget →
        d.left.1 ∈ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) w.toTarget →
        ∃ z : w.Carrier,
          z ∈ functionalComponentFrom w.source (Set.range d.roots) d.left ∧
          z ∈ weakFreeRightPart
            (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget) := by
  obtain ⟨w, ⟨e, he⟩, hMin⟩ :=
    exists_saturatedRelational_fullEmbeddingMinimizer
      F Target (fullFreeLeftExclusiveTarget iLeft jLeft) hExists
  have hInj : Function.Injective w.toTarget := by
    intro a b hab
    apply e.injective
    rw [he a, he b]
    exact hab
  refine ⟨w, ⟨e, he⟩, hMin, ?_⟩
  intro n d hn hRoots hLeft
  exact minimalGlobalWitness_pieceMeetsRight_of_rootInjective
    (FullRangeEHNSaturation F)
    (fun A hA => finite_of_fullRangeEHNSaturation F A hA)
    Target Left Right jLeft jRight X iLeft iRight hTargetFree hCommon
    w hMin d hn hRoots hLeft (hInj.comp d.roots_injective)

end AllThoseRamseyClasses.Lifts
