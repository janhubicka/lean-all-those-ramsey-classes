import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceConditionalStrongAmalgamation
import AllThoseRamseyClasses.Lifts.GlobalForbiddenEHNAvoidance
import PartiteConstruction.Structure.FreeAmalgamationClass

/-!
# Unconditional global maximal-trace strong amalgamation for irreducible forbidden sources

The printed Section 3 strong-amalgamation proof is unresolved for general
regular forbidden families: in particular a weak forbidden-source map need
not be injective on a reducible root. There is, however, a substantial
unconditional subclass. If EVERY finite forbidden source is irreducible
in the native functional free-amalgamation sense, a weak EHN map of the
entire source contains a FULL embedding of that source. Irreducibility
then forces its image to lie entirely on one side of any actual full
native functional free amalgam.

Consequently the native EHN-forbidden-free class is closed under genuine
free amalgamation, WITHOUT a canonical tag-agreement hypothesis. Combining
this with the already verified regular global maximal-trace construction
gives true class-level strong amalgamation for the ORIGINAL root-INJECTIVE
global lift when all forbidden sources are irreducible.

No claim is made for nonirreducible forbidden families, the printed
multicomponent Claim 2, or the final Ramsey property. All native partial
and set-valued function fibres remain exact.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A useful restricted case of the original forbidden family: every
finite forbidden source is genuinely irreducible in the full native
relational/functional sense. This hypothesis is stronger than regularity. -/
def GlobalForbiddenSourcesIrreducible
    (F : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {U : Type} (Source : Structure L U),
    Finite U → F Source → Source.Irreducible

/-- An arbitrary free amalgam of TWO globally forbidden-free functional
structures is forbidden-free when every forbidden source is irreducible.

The key step is NOT injectivizing a general weak map: the source itself
is irreducible, so the EHN condition already supplies a FULL embedding
of the entire source into the amalgam. Native irreducibility places that
embedding into one side. Factor the original EHN map through the same
FULL side, contradicting its forbidden-source avoidance. -/
theorem avoidsGlobalFunctionalEHN_freeAmalgam_irreducible
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hIrred : GlobalForbiddenSourcesIrreducible F)
    {UX UA UB UT : Type}
    {X : Structure L UX}
    {A : Structure L UA}
    {B : Structure L UB}
    {D : Structure L UT}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    {jA : Structure.Embedding A D}
    {jB : Structure.Embedding B D}
    (hFree : Structure.IsFreeAmalgam iA iB jA jB)
    (hA : AvoidsGlobalFunctionalEHN F A)
    (hB : AvoidsGlobalFunctionalEHN F B) :
    AvoidsGlobalFunctionalEHN F D := by
  intro U Source hFin hF f hf
  have hS : Source.Irreducible := hIrred Source hFin hF
  obtain ⟨e, he⟩ := hf.2 Source hS (Structure.Embedding.id Source)
  have heq (x : U) : e x = f x := he x
  rcases hS hFree e with hLeft | hRight
  · have hRange : ∀ x : U, ∃ a : UA, f x = jA a := by
      intro x
      obtain ⟨a, ha⟩ := hLeft x
      exact ⟨a, (heq x).symm.trans ha⟩
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jA hRange
    exact (hA Source hFin hF g) hg
  · have hRange : ∀ x : U, ∃ b : UB, f x = jB b := by
      intro x
      obtain ⟨b, hb⟩ := hRight x
      exact ⟨b, (heq x).symm.trans hb⟩
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jB hRange
    exact (hB Source hFin hF g) hg

/-- The difficult global-piece shadow-free amalgamation property is
UNCONDITIONALLY valid for irreducible forbidden families. Indeed
compatibility of added canonical global relations is unused here:
native avoidance and irreducibility suffice. -/
theorem globalCanonicalShadowFree_irreducible
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hIrred : GlobalForbiddenSourcesIrreducible F) :
    GlobalCanonicalShadowFreeAmalgamation F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) := by
  intro UX UA UB UT X A B D iA iB jA jB hFree _ hA hB
  exact avoidsGlobalFunctionalEHN_freeAmalgam_irreducible
    F hIrred hFree hA hB

/-- An ACTUAL finite, full, strong amalgam in the ORIGINAL regular
global maximal-trace age when all forbidden sources are irreducible.
This is an unconditional instance of the Section 3 class-level
strong-amalgamation construction, rather than a proof that assumes
its missing global shadow-avoidance principle. -/
theorem globalFiniteMaximalTraceAge_strongAmalgamation_irreducible
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hIrred : GlobalForbiddenSourcesIrreducible F)
    {VX VY VZ : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (Y : Structure (globalFunctionalPieceLanguage F) VY)
    (Z : Structure (globalFunctionalPieceLanguage F) VZ)
    (hY : IsGlobalFiniteMaximalTrace F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) Y)
    (hZ : IsGlobalFiniteMaximalTrace F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) Z)
    (fY : Structure.Embedding X Y)
    (fZ : Structure.Embedding X Z) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {V : Type} (A : Structure L V) =>
          AvoidsGlobalFunctionalEHN F A) T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T),
        ∀ y : VY, ∀ z : VZ,
          jY y = jZ z ↔
            ∃ x : VX, y = fY x ∧ z = fZ x := by
  exact globalFiniteMaximalTraceAge_strongAmalgamation_of_shadowFree
    F (fun {V : Type} (A : Structure L V) =>
      AvoidsGlobalFunctionalEHN F A)
    hRegular (globalCanonicalShadowFree_irreducible F hIrred)
    X Y Z hY hZ fY fZ

end AllThoseRamseyClasses.Lifts
