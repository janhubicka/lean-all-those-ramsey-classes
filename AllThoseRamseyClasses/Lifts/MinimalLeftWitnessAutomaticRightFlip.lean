import AllThoseRamseyClasses.Lifts.MinimalMixedRootInjOneStepFlip
import AllThoseRamseyClasses.Lifts.GlobalMinimalForbiddenObstructionDichotomy

/-!
# Every left-support-minimal forbidden witness admits a strict right-support flip

Combine the actual original-global minimal forbidden witness
dichotomy (genuine positive-width source piece or root-image collision)
with the arbitrary-width proper B-only flip built in
MinimalMixedRootInjOneStepFlip.

The only EXTRA condition beyond the finite connected forbidden
family, free native target amalgam of forbidden-free full witnesses,
common full original lift, and LEFT-support minimization is:

  the ORIGINAL weak forbidden-source map is injective on its
  exact common-root preimage S.

Under that condition the collision alternative is impossible.
Thus a genuine mixed source piece exists. Minimize its number of
nonroot vertices, select an interior positive-width auxiliary
piece automatically, use Claim 1 to force capture of the old
root, then flip a proper B-only sub-piece. This constructs an
ACTUAL NEW member of the forbidden family and a genuine weak
EHN map into the SAME amalgam target, strictly lowering the
original RIGHT-exclusive SOURCE count.

No extra premise requiring a mixed piece, an auxiliary cut,
a separator capture, one-sidedness of a chosen piece, root width
or an available flip remains. All those are proved from
the given conditions, except injectivity on S.

IMPORTANT: This is not a contradiction to minimal LEFT support
because a B→A flip may increase the LEFT count. To complete
the published Claim 2 one must iterate flips INSIDE an outer
piece while preserving its geometric/minimal separator and full
forbidden incompatibility profile, then carry out the outer flip.
The original HE-image collision issue is also still open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- From any LEFT-support-minimal actual forbidden weak EHN witness
into a real full free amalgam of forbidden-free original-global
common-lift witnesses, construct a SECOND actual forbidden witness
with STRICTLY fewer RIGHT-exclusive SOURCE vertices, assuming
only injectivity on the original shared-root preimage.

The new witness is packaged in the SAME reusable structure as the
original, despite having a potentially different finite source
carrier and source native function structure. This is a genuine
one-step certificate, not an iterated Claim 2 contradiction. -/
theorem minimalLeftForbiddenWitness_strictRightReplacement_of_rootInjOn
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
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMinLeft : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hInjOnRoot : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)) :
    ∃ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) <
      w.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) := by
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  letI : Finite w.Carrier := w.finiteCarrier
  obtain ⟨n, d, hn, hRoots, hLeft, _hRight, _hPattern, hCases⟩ :=
    minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hAvoidLeft hAvoidRight w hMinLeft
  have hInjD :
      Function.Injective (fun i : Fin n => w.toTarget (d.roots i)) := by
    intro i j hij
    apply d.roots_injective
    exact hInjOnRoot
      (hRoots ⟨i, rfl⟩) (hRoots ⟨j, rfl⟩) hij
  have hMixedB :
      ∃ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range d.roots) d.left ∧ z ∈ BOnly := by
    rcases hCases with hCollision | hRight
    · exact False.elim (hCollision hInjD)
    · exact hRight
  let P0 : MixedGeometricPiece w.source S AOnly BOnly := {
    width := n
    data := d
    positive := hn
    roots_in_common := hRoots
    left_mixed := ⟨d.left.1,
      functionalComponentFrom_root w.source
        (Set.range d.roots) d.left, hLeft⟩
    right_mixed := hMixedB
  }
  obtain ⟨P, hMinP⟩ :=
    exists_minimalMixedGeometricPiece
      w.source S AOnly BOnly ⟨P0⟩
  obtain ⟨m, Qright, _hProper, _hNoLeft,
      V', New, hNew, flip, hFlip, hStrict⟩ :=
    minimalLeftMixedPiece_hasProperRightFlip_of_rootInjOn
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      w hMinLeft hInjOnRoot P hMinP
  let newWitness : ForbiddenEHNWitness F Target := {
    Carrier := V'
    finiteCarrier := hFiniteF New hNew
    source := New
    forbidden := hNew
    toTarget := flip
    homEmbedding := hFlip
  }
  refine ⟨newWitness, ?_⟩
  exact hStrict

end AllThoseRamseyClasses.Lifts
