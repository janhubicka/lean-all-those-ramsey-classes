import AllThoseRamseyClasses.Lifts.FiniteNamedCommonComponentLift
import AllThoseRamseyClasses.Lifts.RootedTransferShadowAvoidance

/-!
# Conditional free amalgamation of forbidden shadows for a FINITE named family

For a finite family of finite named forbidden native functional
sources, our auxiliary all-closed-component canonical lift has a
finite global signature and allows weak rooted realizations with
colliding coordinates.

If two structures A and B induce the SAME FULL such finite-family
tagged expansion on a shared full old functional substructure X,
then their ACTUAL full functional free amalgam D=A⊕_X B avoids
every named forbidden source, provided B already avoids them.

This is a complete SHADOW-LEVEL conditional free-amalgamation
statement. No minimal separator, multicomponent Claim 2,
forbidden image quotient, homomorphism-embedding injectivity,
or change of forbidden source is required.

The common full tagged expansion is a real hypothesis, NOT a
consequence merely of sharing an old-language shadow.
The separate class of maximal finite-family tagged lifts,
existence of witnesses, lifting the free shadow amalgam
while preserving both expanded sides, hereditary/JEP and
Ramsey consequences are NOT proved here.

The original 2019 theorem for arbitrary regular INFINITE
forbidden families is not inferred from this alternative.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Exact avoidance of a FINITE NAMED forbidden family by
original 2019/EHN weak homomorphism-embeddings.
Naming source representatives makes the avoidance predicate
independent of any image normalization. -/
def AvoidsFiniteNamedEHN
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {W : Type} (A : Structure L W) : Prop :=
  ∀ (i : Family.Index) (f : Family.Carrier i → W),
    ¬ (Family.source i).IsEHNHomomorphismEmbedding A f

/-- All true source-component rooted realizations of ONE member
of the finite named family transfer from Left to Right whenever
their entire family tagged lifts share the SAME FULL expansion of X.

Repeated images of distinct source-root coordinates are allowed. -/
theorem commonFiniteNamedLifts_rootedTransfer
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA UB : Type}
    (X : Structure L UX)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hCommon : CommonFiniteNamedComponentLift
      Family X Left Right iLeft iRight)
    (i : Family.Index)
    [Finite (Family.Carrier i)] :
    AllClosedComponentRootedTransfer
      (Family.source i) X Left Right iLeft iRight := by
  letI : Finite (Family.Carrier i) := Family.finiteCarrier i
  intro tag xs hLeft
  exact commonFiniteNamedComponentLift_rightWitness
    Family X Left Right iLeft iRight hCommon
    i tag xs hLeft

/-- The MAIN finite-family SHADOW amalgamation lemma for the
NEW all-closed-root-component folded lift.

If the full functional witnesses share a FULL canonical
finite-family tagged expansion on X, their free functional
shadow amalgam excludes EVERY named forbidden source.
No root-image/source-map injectivity; no assumption on number
of exclusive-side components; no minimal separator or Claim 2.

The theorem does not claim that canonical tagged LIFTS of
the free amalgam embed both original expanded witnesses:
that extra maximality/preservation step is independent. -/
theorem finiteNamedAllComponentLift_freeAmalgam_avoids
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonFiniteNamedComponentLift
      Family X Left Right iLeft iRight)
    (hRightAvoid : AvoidsFiniteNamedEHN Family Right) :
    AvoidsFiniteNamedEHN Family Target := by
  intro i f hf
  letI : Finite (Family.Carrier i) := Family.finiteCarrier i
  have hTransfer : AllClosedComponentRootedTransfer
      (Family.source i) X Left Right iLeft iRight :=
    commonFiniteNamedLifts_rootedTransfer
      Family X Left Right iLeft iRight hCommon i
  exact (wholeComponentRootedTransfer_freeAmalgam_avoids_source
    (Family.source i)
    Target Left Right jLeft jRight X iLeft iRight
    hFree hTransfer (hRightAvoid i) f) hf

end AllThoseRamseyClasses.Lifts
