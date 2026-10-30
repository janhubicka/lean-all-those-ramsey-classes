import AllThoseRamseyClasses.Lifts.EHNInjectiveSupportMinimizer
import AllThoseRamseyClasses.Lifts.MinimalLeftWitnessCollisionOrRightFlip

/-!
# Original Claim 2 one-step flip after legitimate image injectivization

The original 2019 lift argument needs TWO nontrivial corrections:
* a possibly noninjective forbidden EHN map cannot generally be
  replaced by its raw weak image in the functional setting;
* a successful B-to-A flip lowers B-source support but does not
  automatically contradict global LEFT-source-support minimality.

The first issue is eliminated for forbidden families whose actual
native function input tuples are covered by full irreducible source
tests. The now verified EHN image results then make the complete
target range function-closed, allow factorization through its FULL
induced target substructure, and permit an injective forbidden
minimum-LEFT-support witness under surjective EHN-image closure.

The separately verified arbitrary-width Claim 2 source geometry
then yields a genuine one-step B-to-A flip from that witness:
the alternative of a colliding actual auxiliary separator root
is impossible for an injective witness, so another actual finite
forbidden EHN witness maps into the same target with strictly
lower original RIGHT-exclusive SOURCE support.

This removes all preliminary root collision hypotheses from the
ONE-STEP statement under the explicit tuple-cover condition.
It is NOT YET a contradiction to the left minimum, because the
B-to-A flip may increase left support. The contextual outer-piece
minimal separator and its all-test profile must still survive
a sequence of B flips before a final A-to-B flip can be used.
The unrestricted arbitrary-arity 2019 theorem is NOT claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In the ORIGINAL full maximal canonical-lift setting,
surjective EHN-image closure plus irreducible source INPUT-TUPLE
coverage permit choosing an actual INJECTIVE left-support
minimizer, and the proven arbitrary-width Claim 2 geometry
performs a genuine strict B-support replacement.

No global EHN injection hypothesis is supplied externally,
and no fictitious full weak-image quotient is used.
This remains the one-step version of the printed argument:
the new witness need not be left-support-minimal. -/
theorem exists_injectiveLeftMinimizer_and_strictRightReplacement
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hImageClosed :
      ∀ {X Y : Type}
        (Src : Structure L X) (Dst : Structure L Y)
        (q : X → Y),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    (hInputCover :
      ∀ {V : Type} (A : Structure L V),
        F A → FunctionInputTuplesCoveredByIrreducibleTests A)
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
    (hBad : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ w : ForbiddenEHNWitness F Target,
      Function.Injective w.toTarget ∧
      (∀ v : ForbiddenEHNWitness F Target,
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      ∃ v : ForbiddenEHNWitness F Target,
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) <
        w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) := by
  obtain ⟨w, hwInjective, hwMin⟩ :=
    exists_injectiveMinimalForbiddenEHNWitness_of_inputTests
      F hImageClosed hInputCover Target
      (fullFreeLeftExclusiveTarget iLeft jLeft) hBad
  rcases minimalLeftWitness_rootCollision_or_strictRightReplacement
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight w hwMin with
    hCollision | hDrop
  · obtain ⟨n, d, _hn, _hRoot, hNoninj⟩ := hCollision
    have hRootInjective :
        Function.Injective
          (fun i : Fin n => w.toTarget (d.roots i)) := by
      intro i j hij
      exact d.roots_injective (hwInjective hij)
    exact False.elim (hNoninj hRootInjective)
  · exact ⟨w, hwInjective, hwMin, hDrop⟩

end AllThoseRamseyClasses.Lifts
