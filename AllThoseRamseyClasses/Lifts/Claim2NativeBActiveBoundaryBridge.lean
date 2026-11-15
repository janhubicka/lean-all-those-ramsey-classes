import AllThoseRamseyClasses.Lifts.Claim2WeakRightExclusiveTargetIff
import AllThoseRamseyClasses.Lifts.Claim2ActualGeometricPieceBoundaryTransfer

/-!
# Track B: translate same-Q target B-boundary transfer to native next-state hypothesis

The actual selected-Q source step returns injectivity on the generated
functional boundary for B-exclusive SOURCE vertices of the new outer
piece. Its premise in the positive-rank dichotomy is expressed using
`weakFreeRightPart` and `weakFreeRootPart`. For a TRUE target free
amalgam, these are the exact same right-exclusive region and seam
preimage; no weak SOURCE-map injectivity on the entire seam is needed.

This lemma discharges the interface mismatch without assuming any
unproved global seam or root-collision repair.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The image-level full B-exclusive boundary-injection certificate
for one genuine outer source implies precisely the native weak-right
local hypothesis required on the NEXT state. This is a logical
change of predicate, NOT a second selected-Q source replacement. -/
theorem claim2_fullRightActiveBoundary_to_weakRightActiveBoundary
    {W UX UA UB UT : Type}
    (Source : Structure L W)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT)
    (f : W → UT)
    (X : Structure L UX)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hBTargetInjection :
      ∀ (y : W)
        (hyPart : y ∈ geometricPieceVertices Source P)
        (hyB : f y ∈ fullFreeRightExclusiveTarget iRight jRight)
        (hyOutside : f y ∉ Set.range (jLeft.comp iLeft)),
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (f ⁻¹' Set.range (jLeft.comp iLeft))
                (⟨y, hyOutside⟩ :
                  {w : W // w ∉ f ⁻¹' Set.range (jLeft.comp iLeft)}))))) :
    ∀ (y : {w : W //
        w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
      y.1 ∈ geometricPieceVertices Source P →
      y.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f →
      Set.InjOn f
        (Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) y))) := by
  intro y hyPart hyRight
  have hyB : f y.1 ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeRightPart_iff_fullFreeRightExclusiveTarget
      iLeft iRight jLeft jRight hFree f y.1).mp hyRight
  exact hBTargetInjection y.1 hyPart hyB y.2

end AllThoseRamseyClasses.Lifts
