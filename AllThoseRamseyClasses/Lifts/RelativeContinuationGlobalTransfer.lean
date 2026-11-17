import AllThoseRamseyClasses.Lifts.RootedTransferShadowAvoidance
import AllThoseRamseyClasses.Lifts.GlobalForbiddenEHNAvoidance

/-!
# Source-faithful global avoidance from native closed-component transfer

This is the family-wide assembly of the already established
finite-source whole-component flip. For EACH original forbidden
finite source, equality of all folded closed-component observations
on a shared full root provides the transfer premise. No quotient
source, minimal cut, target root injectivity, image closure, or
uniform bound on forbidden source size is required.

This theorem proves only the CONDITIONAL structural transfer
implication. It does not show a finite or precompact coding of
all source queries, finite continuation index, or maximal lift
existence.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For arbitrary original finite forbidden sources, the FULL
native free amalgam is allowed if every genuine source closed
component on the left transfers to the right on the same possibly
collapsed root values, and the right side is forbidden-free. -/
theorem avoidsGlobalFunctionalEHN_of_allClosedComponentTransfer
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
    (hTransfer : ∀ {V : Type} [Finite V]
       (Source : Structure L V), F Source →
       AllClosedComponentRootedTransfer Source X A B sA sB)
    (hRight : AvoidsGlobalFunctionalEHN F B) :
    AvoidsGlobalFunctionalEHN F Whole := by
  intro V Source hFin hF f hf
  letI : Finite V := hFin
  have hT : AllClosedComponentRootedTransfer Source X A B sA sB :=
    hTransfer Source hF
  have hNo : ∀ g : V → VB,
      ¬ Source.IsEHNHomomorphismEmbedding B g :=
    hRight Source hFin hF
  have hAvoid :
      ∀ g : V → VW,
        ¬ Source.IsEHNHomomorphismEmbedding Whole g :=
    wholeComponentRootedTransfer_freeAmalgam_avoids_source
      Source Whole A B iA iB X sA sB hFree hT hNo
  exact hAvoid f hf

end AllThoseRamseyClasses.Lifts
