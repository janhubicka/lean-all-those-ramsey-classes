import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece
import AllThoseRamseyClasses.Lifts.GlobalOriginalClaim1OneSided

/-!
# Exact two-case obstruction at a support-minimal global forbidden witness

The original 2019 regular root-injective global lift's strong AP
is reduced to the old functional free-amalgam forbidden-avoidance
problem. The previously kernel-verified source partition and actual
positive-width minimal-separator selection apply to an arbitrary
connected forbidden weak EHN source map, even if it is noninjective.

Now choose an actual forbidden witness minimizing the number of
SOURCE vertices mapped into the exclusive left side. For the genuine
positive-width minimal-cut piece selected between opposite exclusive
source regions, the newly verified Claim 1 says that an INJECTIVE
root image forces an exclusive-right vertex inside its chosen
left-root component. Therefore EVERY alleged support-minimal
obstruction falls into the following two cases:

(1) the image of the ordered separator root COLLAPSES distinct
    source coordinates; or
(2) the chosen genuine minimal piece is MIXED: its selected
    component has a right-exclusive vertex as well.

This is a source-matched, constructive proof-theoretic REDUCTION:
a real geometric forbidden piece and the disjunction are produced.
It does NOT pretend that (1) can be converted to an injective
weak image in the target, or that the multicomponent (2) admits
the printed Claim 2 flip. Those are the still-open hard cases
needed for the unrestricted regular-family strong AP theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For every support-minimal forbidden EHN map into an actual
full functional free amalgam of F-free witnesses carrying a
common FULL original global canonical lift, there exists a
genuine POSITIVE-width forbidden geometric piece with ordered
roots in the shared seam and opposite-side distinguished vertices.

Moreover either the ROOT IMAGE is noninjective, or the selected
component is genuinely MIXED and meets the right-exclusive
source region. There are no other cases for the chosen piece.

No finite-family restriction, global map injectivity, closure-
under-images, or arbitrary source-root injection is assumed. -/
theorem minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData w.source n),
      0 < n ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget ∧
      d.left.1 ∈
        weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget ∧
      d.right.1 ∈
        weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget ∧
      geometricFunctionalRootedPattern w.source d ∈
        forbiddenGeometricFunctionalPieces F n ∧
      (¬ Function.Injective
          (fun i : Fin n => w.toTarget (d.roots i)) ∨
        ∃ z : w.Carrier,
          z ∈ functionalComponentFrom w.source
            (Set.range d.roots) d.left ∧
          z ∈ weakFreeRightPart
            (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget) := by
  obtain ⟨n, d, hn, hRoots,
      ⟨x, hx, hdLeft⟩, ⟨y, hy, hdRight⟩, hPiece⟩ :=
    globalConnectedForbiddenWitness_hasPositivePiece
      F hConnected hTargetFree hAvoidLeft hAvoidRight
      w.source w.finiteCarrier w.forbidden
      w.toTarget w.homEmbedding
  have hChosenLeft :
      d.left.1 ∈
        weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget := by
    rw [hdLeft]
    exact hx
  have hChosenRight :
      d.right.1 ∈
        weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget := by
    rw [hdRight]
    exact hy
  refine ⟨n, d, hn, hRoots, hChosenLeft, hChosenRight, hPiece, ?_⟩
  by_cases hInjective :
      Function.Injective (fun i : Fin n => w.toTarget (d.roots i))
  · right
    exact minimalGlobalWitness_pieceMeetsRight_of_rootInjective
      F hFiniteF Target Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon w hMin
      d hn hRoots hChosenLeft hInjective
  · exact Or.inl hInjective

end AllThoseRamseyClasses.Lifts
