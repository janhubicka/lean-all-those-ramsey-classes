import AllThoseRamseyClasses.Lifts.RelativeContinuationGlobalTransfer

/-!
# Raw closed-component observations agree on a common old root

This is a source-faithful semantic interface for the proposed
unconditional (possibly nonprecompact) functional lift.

For EVERY finite ORIGINAL forbidden source, EVERY closed-root
component pattern, and EVERY root tuple (including COLLAPSED
target-root coordinates), its EHN realization has the same truth
value on both allowed sides of a proposed native free amalgam.

Such agreement ensures the old-language free amalgam stays in
Forb_HE(F). This proves a core clause of the raw-trace lift
construction; it does not yet prove that canonical raw traces on
the ENTIRE sides remain unchanged after amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Genuine source-component observations on the same finite
old root have equal truth values. Root images may be noninjective,
and the old language includes arbitrary native partial functions. -/
def AllForbiddenClosedComponentTracesAgree
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VX VA VB : Type}
    (X : Structure L VX)
    (A : Structure L VA) (B : Structure L VB)
    (sA : Structure.Embedding X A)
    (sB : Structure.Embedding X B) : Prop :=
  ∀ {V : Type} [Finite V]
    (Source : Structure L V), F Source →
    ∀ (tag : ClosedComponentTag Source)
      (xs : Fin tag.width → VX),
      (FunctionalRootRealization tag.rootedPattern A (sA ∘ xs) ↔
       FunctionalRootRealization tag.rootedPattern B (sB ∘ xs))

theorem allForbiddenClosedComponentTracesAgree_symm
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VX VA VB : Type}
    {X : Structure L VX}
    {A : Structure L VA} {B : Structure L VB}
    {sA : Structure.Embedding X A}
    {sB : Structure.Embedding X B}
    (h : AllForbiddenClosedComponentTracesAgree F X A B sA sB) :
    AllForbiddenClosedComponentTracesAgree F X B A sB sA := by
  intro V _ Source hF tag xs
  exact (h Source hF tag xs).symm

/-- Full native free amalgams of two allowed witness sides
remain original-family EHN forbidden-free if the raw
component realization tables match on their shared full root.
No image closure and no finite number of forbidden source
types is assumed. -/
theorem rawClosedComponentAgreement_freeAmalgam_avoids
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VX VA VB VW : Type}
    (X : Structure L VX)
    (A : Structure L VA)
    (B : Structure L VB)
    (Whole : Structure L VW)
    (sA : Structure.Embedding X A)
    (sB : Structure.Embedding X B)
    (iA : Structure.Embedding A Whole)
    (iB : Structure.Embedding B Whole)
    (hFree : Structure.IsFreeAmalgam sA sB iA iB)
    (hAgrees : AllForbiddenClosedComponentTracesAgree F X A B sA sB)
    (hB : AvoidsGlobalFunctionalEHN F B) :
    AvoidsGlobalFunctionalEHN F Whole := by
  intro V Source hFin hF f hf
  letI : Finite V := hFin
  have hTransfer : AllClosedComponentRootedTransfer Source X A B sA sB := by
    intro tag xs hA
    exact (hAgrees Source hF tag xs).mp hA
  have hNo : ∀ g : V → VB,
      ¬ Source.IsEHNHomomorphismEmbedding B g :=
    hB Source hFin hF
  have hAvoid : ∀ g : V → VW,
      ¬ Source.IsEHNHomomorphismEmbedding Whole g :=
    wholeComponentRootedTransfer_freeAmalgam_avoids_source
      Source Whole A B iA iB X sA sB hFree hTransfer hNo
  exact hAvoid f hf

end AllThoseRamseyClasses.Lifts
