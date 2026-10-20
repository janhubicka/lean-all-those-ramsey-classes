import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization

/-!
# The original global-lift conditional Claim 1 closes at a support minimizer

A genuine geometric forbidden piece of the original Section 3
root-INJECTIVE global lift which lies entirely on one target side,
has its roots in the common FULL old seam, and has INJECTIVE
root images may be replaced by an equivalent piece realized on
the other side. The source-vertex exclusive-left count decreases.

All of these conditional ingredients were previously kernel checked:
the literal global quotient-indexed common-lift flip, exact source
support-count strict decrease, and existence of support-minimal
actual forbidden weak EHN witnesses. Here we combine them into
the full minimality contradiction for the printed Claim 1 under
those EXPLICIT additional hypotheses.

The contradiction does NOT require global source-map injectivity.
However a selected root image need not be injective under an
arbitrary weak EHN map, and the geometric piece may involve both
exclusive sides. Discharging those conditions (Claim 2 /
the original noninjective-root problem) remains OPEN. The
unrestricted strong-amalgamation theorem is not claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A support-minimal actual forbidden weak EHN map cannot possess
a genuine positive-width, one-sided geometric piece with
injective TARGET root image and compatible FULL common global lift.

This is the exact conditional Claim 1 minimality contradiction,
including construction of the forbidden replacement witness,
not merely a standalone strict support inequality. -/
theorem minimalGlobalForbiddenWitness_noOneSidedInjectiveRootPiece
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
    (pLeft : (geometricGlobalFunctionalChart w.source d).ext.Carrier → UA)
    (hpLeft : Structure.IsEHNHomomorphismEmbedding
      (geometricGlobalFunctionalChart w.source d).ext.str
      Left pLeft)
    (hPieceMap : ∀ z :
      (geometricGlobalFunctionalChart w.source d).ext.Carrier,
      jLeft (pLeft z) = w.toTarget z.1)
    (xsX : Fin n → UX)
    (hRootLeft : ∀ i : Fin n,
      pLeft ((geometricGlobalFunctionalChart w.source d).ext.rootEmbedding i)
        = iLeft (xsX i))
    (hRootImageInjective : Function.Injective
      (fun i : Fin n => w.toTarget (d.roots i)))
    (oldVertex : w.Carrier)
    (hvComponent : oldVertex ∈
      functionalComponentFrom w.source (Set.range d.roots) d.left)
    (hvLeft : oldVertex ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget) :
    False := by
  obtain ⟨V', New, hNewForbidden, flip, hFlip, hStrict⟩ :=
    geometricGlobalCommonFullLiftFlip_strict_leftSupport
      F hFiniteF w.source w.finiteCarrier w.forbidden d hn
      Target w.toTarget w.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon
      pLeft hpLeft hPieceMap xsX hRootLeft hRootImageInjective
      oldVertex hvComponent hvLeft
  let replacement : ForbiddenEHNWitness F Target := {
    Carrier := V'
    finiteCarrier := hFiniteF New hNewForbidden
    source := New
    forbidden := hNewForbidden
    toTarget := flip
    homEmbedding := hFlip
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
