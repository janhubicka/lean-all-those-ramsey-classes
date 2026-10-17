import AllThoseRamseyClasses.Lifts.FiniteFamilyCanonicalMaximality
import AllThoseRamseyClasses.Lifts.FiniteFamilyShadowFreeAmalgamation

/-!
# Actual full induced finite-family lifted traces and shadow amalgamation

A finite-family canonical lift of A is not hereditary along an
arbitrary old full embedding X ↪ A: a tagged component can be
realized in A but not in X. Instead we keep the *induced FULL*
expansion of X with component relations evaluated in A.

This file constructs that expanded trace, proves that its old shadow
is literally X, and constructs a FULL embedding back into the
canonical finite-family lift of A. If A is maximal along X and
A ↪ C is an allowed full extension, the same trace embeds FULLY into
the canonical finite-family lift of C. No false reflection of
canonical predicates along arbitrary old embeddings is used.

Equality of the complete canonical tag profiles from A and B on X
then produces the exact CommonFiniteNamedComponentLift required by
the conditional finite-family shadow free-amalgamation theorem.
This removes the need to supply an abstract common expanded witness
as an independent assumption.

The existence of a free amalgam in the expanded age and the original
2019 arbitrary regular-family theorem are NOT claimed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The full induced canonical tagged expansion of X *as seen in A*.
The OLD relation and complete partial-function fibres are exactly
X; a new tag is present iff its native piece is weakly realized in
A over the corresponding embedded root tuple. -/
noncomputable def finiteNamedCanonicalTrace
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) UX :=
  functionalWithExtraBig L Family.ComponentTag
    (fun tag => tag.width Family) X
    (fun tag xs =>
      (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr tag) (iA ∘ xs))

/-- Nothing in the old functional shadow changes when taking
the full tagged trace of a witness on its root X. -/
@[simp] theorem finiteNamedCanonicalTrace_shadow
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    functionalShadowBig L Family.ComponentTag
      (fun tag => tag.width Family)
      (finiteNamedCanonicalTrace Family iA) = X :=
  functionalShadowBig_withExtra L Family.ComponentTag
    (fun tag => tag.width Family) X _

/-- The FULL induced trace embeds into the canonical lift
of the ambient witness, including reflection of ALL new relations.
This is not an embedding of the canonical lift of X itself. -/
noncomputable def finiteNamedCanonicalTrace_into_witness
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    Structure.Embedding
      (finiteNamedCanonicalTrace Family iA)
      (finiteNamedClosedComponentFoldedLift Family A) := by
  apply functionalWithExtraBigEmbedding L Family.ComponentTag
    (fun tag => tag.width Family)
    (fun tag xs =>
      (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr tag) (iA ∘ xs))
    (fun tag xs => FunctionalRootRealization
      (tag.pattern Family) A xs)
    iA
  intro tag xs
  exact Iff.rfl

/-- The underlying vertex map of the full tagged trace inclusion
is EXACTLY the originally prescribed old full embedding. -/
@[simp] theorem finiteNamedCanonicalTrace_into_witness_apply
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (x : UX) :
    finiteNamedCanonicalTrace_into_witness Family iA x = iA x := rfl

/-- If A is maximal on X, its true full tagged trace on X embeds
as a FULL substructure of the canonical lift of every allowed full
extension C of A. Here maximality supplies the missing REFLECTION
direction for new relations, while the old functions remain exact. -/
noncomputable def finiteNamedCanonicalTrace_into_allowed_extension
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UC : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (hMax : FiniteNamedCanonicalMaximalAlong Family K iA)
    (C : Structure L UC) (hC : K C)
    (e : Structure.Embedding A C) :
    Structure.Embedding
      (finiteNamedCanonicalTrace Family iA)
      (finiteNamedClosedComponentFoldedLift Family C) := by
  apply functionalWithExtraBigEmbedding L Family.ComponentTag
    (fun tag => tag.width Family)
    (fun tag xs =>
      (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr tag) (iA ∘ xs))
    (fun tag xs => FunctionalRootRealization
      (tag.pattern Family) C xs)
    (e.comp iA)
  intro tag xs
  exact hMax C hC e tag xs

/-- Canonical tag agreement on a common OLD root is sufficient to
build a SINGLE actual FULL shared expanded structure, with full
embeddings into both finite-family canonical lifted witnesses. -/
noncomputable def commonFiniteNamedComponentLift_of_agreement
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA UB : Type}
    (X : Structure L UX)
    (A : Structure L UA) (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hAgree : FiniteNamedComponentLiftsAgreeOn Family iA iB) :
    CommonFiniteNamedComponentLift Family X A B iA iB where
  lifted := finiteNamedCanonicalTrace Family iA
  shadow_eq := finiteNamedCanonicalTrace_shadow Family iA
  intoA := finiteNamedCanonicalTrace_into_witness Family iA
  intoB := by
    apply functionalWithExtraBigEmbedding L Family.ComponentTag
      (fun tag => tag.width Family)
      (fun tag xs =>
        (finiteNamedClosedComponentFoldedLift Family A).rel
          (.inr tag) (iA ∘ xs))
      (fun tag xs => FunctionalRootRealization
        (tag.pattern Family) B xs)
      iB
    intro tag xs
    exact (hAgree tag xs).symm
  intoA_verts := by intro x; rfl
  intoB_verts := by intro x; rfl

/-- Direct conditional SHADOW-level finite-family amalgamation:
agreement of ALL actual canonical tag predicates on the common full
root X, rather than an separately hypothesized expanded witness,
prevents the appearance of any forbidden weak EHN source map in
the old functional free amalgam.

The trace construction above supplies the entire expanded witness
needed by the previously proved theorem. -/
theorem finiteNamedAllComponentLift_freeAmalgam_avoids_of_agreement
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
    (hAgree : FiniteNamedComponentLiftsAgreeOn
      Family iLeft iRight)
    (hRightAvoid : AvoidsFiniteNamedEHN Family Right) :
    AvoidsFiniteNamedEHN Family Target :=
  finiteNamedAllComponentLift_freeAmalgam_avoids
    Family Target Left Right jLeft jRight X iLeft iRight
    hFree (commonFiniteNamedComponentLift_of_agreement
      Family X Left Right iLeft iRight hAgree)
    hRightAvoid

end AllThoseRamseyClasses.Lifts
