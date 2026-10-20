import AllThoseRamseyClasses.Lifts.GlobalMinimalForbiddenObstructionDichotomy
import AllThoseRamseyClasses.Lifts.MinimalMixedGeometricPiece

/-!
# Select a smallest genuine mixed piece from a minimal weak obstruction

The printed Section 3 proof minimizes the left-exclusive SOURCE
support of a forbidden EHN witness and subsequently chooses a
genuine mixed geometric piece with the fewest nonroot vertices.

The verified obstruction dichotomy now supplies an actual
positive-width geometric forbidden piece. When the original weak
map is injective JUST ON THE PREIMAGE OF THE COMMON AMALGAMATION
ROOT, every candidate root tuple contained in that preimage has
an injective image. The collision alternative disappears; hence
the produced piece is genuinely mixed (its selected component
contains both exclusive colours).

The previously kernel-verified finite minimization theorem then
chooses a mixed piece minimizing the actual number of NONROOT
source vertices, with its full closed-root functional geometry.

This is a sound weakened replacement for the overstrong printed
initial "assume the whole forbidden witness map injective" in
the specific Claim 2 selection step. It does NOT prove that the
map can always be made injective even on the common-root preimage,
nor that the smallest mixed piece admits the desired proper-subpiece
descent. Those are the remaining hard obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For a support-minimal forbidden weak EHN witness in a genuine
full native free amalgam of two F-free witnesses with matching
FULL original global lifts, it suffices to assume injectivity
on the SHARED-ROOT PREIMAGE (not on all source vertices) to
construct a smallest true positive-width MIXED geometric piece.

The class of pieces and the nonroot size use actual native
function-closed minimal separators. No weak image quotient,
global injectivization or arbitrary tagged source is substituted.
-/
theorem minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
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
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hRootInjOn : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)) :
    ∃ P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      ∀ Q : MixedGeometricPiece w.source
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
        (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
        (weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
        P.nonrootCount ≤ Q.nonrootCount := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  obtain ⟨n, d, hn, hRoots, hLeft, _hRight, _hSelected, hCases⟩ :=
    minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
  have hRootInjective :
      Function.Injective (fun i : Fin n => w.toTarget (d.roots i)) := by
    intro i j hij
    apply d.roots_injective
    exact hRootInjOn
      (hRoots ⟨i, rfl⟩) (hRoots ⟨j, rfl⟩) hij
  have hMixedRight :
      ∃ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range d.roots) d.left ∧
        z ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget := by
    rcases hCases with hCollision | hRight
    · exact False.elim (hCollision hRootInjective)
    · exact hRight
  let P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget) := {
    width := n
    data := d
    positive := hn
    roots_in_common := hRoots
    left_mixed := ⟨d.left.1,
      functionalComponentFrom_root w.source (Set.range d.roots) d.left,
      hLeft⟩
    right_mixed := hMixedRight
  }
  exact exists_minimalMixedGeometricPiece w.source
    (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    ⟨P⟩

end AllThoseRamseyClasses.Lifts
