import AllThoseRamseyClasses.Lifts.GlobalOriginalClaim1Minimality
import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates

/-!
# The geometric one-sided alternative at a support-minimal global witness

The original Section 3 Claim 1 is usually formulated by stating that
a piece of a support-minimal forbidden source, with its root in the
common full amalgamation seam and with a left-exclusive vertex, must
also have a right-exclusive vertex.

The existing verified common-global-lift flip and minimality theorem
required an auxiliary LEFT weak piece map and its full shared-root
coordinate tuple. Those are NOT independent mathematical hypotheses:
when the chosen entire component has no right-exclusive source
vertex, the already verified side dichotomy constructs the weak
piece factorization through Left, and the common-root coordinates
lemma reconstructs its exact root tuple.

This module discharges both auxiliary premises and gives the
genuine one-sided exclusion, requiring only root-image INJECTIVITY
and the presence of the selected left-exclusive component root.
The original forbidden map itself may be noninjective elsewhere.

The root-image-injectivity premise cannot be inferred merely from
the EHN weak-map condition. The mixed-piece Claim 2 and the
unrestricted original regular-family strong-amalgamation theorem
remain unproved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- At an actual minimum of forbidden weak-map A-only SOURCE
support, a positive-width minimal geometric piece rooted in the
shared full seam cannot be wholly on the LEFT if its ordered
root images are injective.

The piece-side EHN map and the complete common-root tuple are
constructed, not postulated. This makes the remaining two
assumptions -- one-sidedness and injective ROOT images -- transparent.
-/
theorem minimalGlobalWitness_noOneSidedPiece_of_rootInjective
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
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (d : GeometricFunctionalPieceData w.source n)
    (hn : 0 < n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hNoRight : ∀ z : w.Carrier,
      z ∈ functionalComponentFrom w.source (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hRootImageInjective : Function.Injective
      (fun i : Fin n => w.toTarget (d.roots i))) :
    False := by
  obtain ⟨pLeft, hpLeft, hPieceMap⟩ :=
    weakGeometricPiece_factor_left_if_no_right
      hTargetFree w.toTarget w.homEmbedding d hRoots hNoRight
  obtain ⟨xsX, hRootLeft⟩ :=
    geometricPiece_commonRootCoordinates
      w.source d Target w.toTarget X Left
      iLeft jLeft pLeft hPieceMap hRoots
  have hInComponent :
      d.left.1 ∈
        functionalComponentFrom w.source (Set.range d.roots) d.left :=
    functionalComponentFrom_root w.source (Set.range d.roots) d.left
  exact minimalGlobalForbiddenWitness_noOneSidedInjectiveRootPiece
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon w hMin
    d hn pLeft hpLeft hPieceMap xsX hRootLeft
    hRootImageInjective d.left.1 hInComponent hLeft

/-- Precise Claim 1 in the original global root-INJECTIVE
canonical lift: if a chosen positive-width geometric piece has
its whole root in the common seam and the selected component root
is left-exclusive, then a support-minimal forbidden weak EHN
witness must have a right-exclusive vertex IN THAT COMPONENT,
provided the piece's root images are injective.

Nothing here promotes an arbitrary EHN source map to an injection.
-/
theorem minimalGlobalWitness_pieceMeetsRight_of_rootInjective
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
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (d : GeometricFunctionalPieceData w.source n)
    (hn : 0 < n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hRootImageInjective : Function.Injective
      (fun i : Fin n => w.toTarget (d.roots i))) :
    ∃ z : w.Carrier,
      z ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left ∧
      z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget := by
  classical
  by_contra hNoRightExists
  have hNoRight (z : w.Carrier)
      (hz : z ∈ functionalComponentFrom
        w.source (Set.range d.roots) d.left) :
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget := by
    intro hr
    exact hNoRightExists ⟨z, hz, hr⟩
  exact minimalGlobalWitness_noOneSidedPiece_of_rootInjective
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon w hMin
    d hn hRoots hNoRight hLeft hRootImageInjective

end AllThoseRamseyClasses.Lifts
