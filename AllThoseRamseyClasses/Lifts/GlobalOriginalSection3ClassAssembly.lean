import AllThoseRamseyClasses.Lifts.GlobalConnectedPositiveArityJEP
import AllThoseRamseyClasses.Lifts.GlobalShadowAvoidanceFromGeometricConditions
import AllThoseRamseyClasses.Lifts.GlobalIrreducibleForbiddenStrongAmalgamation
import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceIsoPrecompactness

/-!
# Section 3, Track F: class-level assembly of the ORIGINAL global lift

The original root-INJECTIVE global maximal-trace age already has
kernel-checked hereditary, exact-reduct, and isomorphism-type
precompactness theorems. Its genuine finite strong amalgamation is
available ONLY with the named shadow-forbidden-avoidance hypothesis,
or with stronger source assumptions such as irreducibility.

This module assembles the FINITE-age HP/JEP/strong-AP interface, with
no hidden Claim 2, root-injectivity, or nullary-language shortcut.
It also records a typewise Ramsey-arrow colour transfer. A colour
argument for ONE expanded A-type is not a Ramsey theorem for the
original native shadow: all expansion types must be handled, and the
missing regular-family Ramsey step remains separate.

A Fraisse limit is NOT constructed here. Existence additionally
requires the relevant countability/nonempty age hypotheses; the
omega-categoricity, existential completeness, and Section 3 Ramsey
claims are not consequences of the declarations below alone.
The numbered 2019 manuscript is left unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The three genuine finite-class amalgamation axioms used for the
Fraisse-age part of Section 3. Membership itself implies finite
carriers; hereditary embeddings and all maps here are FULL native
functional/lifted embeddings, not weak HE maps.

This record deliberately does NOT contain countability of
isomorphism types, existence of a Fraisse limit, the Ramsey
property, or a theorem saying the shadows are FREE amalgams. -/
structure GlobalFiniteMaximalTraceAmalgamationCore
    (F K : ∀ {W : Type}, Structure L W → Prop) : Prop where
  hereditary :
    ∀ {VA VB : Type}
      {A : Structure (globalFunctionalPieceLanguage F) VA}
      {B : Structure (globalFunctionalPieceLanguage F) VB},
      Structure.Embedding A B →
      IsGlobalFiniteMaximalTrace F K B →
      IsGlobalFiniteMaximalTrace F K A
  jointEmbedding :
    ∀ {VY VZ : Type}
      (Y : Structure (globalFunctionalPieceLanguage F) VY)
      (Z : Structure (globalFunctionalPieceLanguage F) VZ),
      IsGlobalFiniteMaximalTrace F K Y →
      IsGlobalFiniteMaximalTrace F K Z →
      ∃ (VT : Type)
        (T : Structure (globalFunctionalPieceLanguage F) VT),
        IsGlobalFiniteMaximalTrace F K T ∧
        ∃ (_jY : Structure.Embedding Y T)
          (_jZ : Structure.Embedding Z T), True
  strongAmalgamation :
    ∀ {VX VY VZ : Type}
      (X : Structure (globalFunctionalPieceLanguage F) VX)
      (Y : Structure (globalFunctionalPieceLanguage F) VY)
      (Z : Structure (globalFunctionalPieceLanguage F) VZ),
      IsGlobalFiniteMaximalTrace F K Y →
      IsGlobalFiniteMaximalTrace F K Z →
      (fY : Structure.Embedding X Y) →
      (fZ : Structure.Embedding X Z) →
      ∃ (VT : Type)
        (T : Structure (globalFunctionalPieceLanguage F) VT),
        IsGlobalFiniteMaximalTrace F K T ∧
        ∃ (jY : Structure.Embedding Y T)
          (jZ : Structure.Embedding Z T),
          ∀ y : VY, ∀ z : VZ,
            jY y = jZ z ↔
              ∃ x : VX, y = fY x ∧ z = fZ x

/-- The genuine global maximal-trace HP/JEP/strong-AP construction:
regularity plus FULL finite native JEP and the EXACT native-shadow
avoidance condition produce all three class-level properties.
The last assumption is precisely the outstanding Claim 2 obligation
for an arbitrary connected image-closed forbidden family. -/
theorem globalFiniteMaximalTrace_fraisseCore_of_shadowFree
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hNativeJEP : GlobalNativeFiniteJEP K)
    (hShadowFree : GlobalCanonicalShadowFreeAmalgamation F K) :
    GlobalFiniteMaximalTraceAmalgamationCore F K := by
  refine ⟨?_, ?_, ?_⟩
  · intro VA VB A B e hB
    exact IsGlobalFiniteMaximalTrace.of_embedding F K hB e
  · intro VY VZ Y Z hY hZ
    exact globalFiniteMaximalTraceAge_JEP_of_nativeJEP
      F K hRegular hNativeJEP Y Z hY hZ
  · intro VX VY VZ X Y Z hY hZ fY fZ
    exact globalFiniteMaximalTraceAge_strongAmalgamation_of_shadowFree
      F K hRegular hShadowFree X Y Z hY hZ fY fZ

/-- Assembly for Forb_EHN(F), with JEP derived from connected
nonempty forbidden sources and positive arity, but strong AP still
conditional on the ORIGINAL distinct-root shadow-avoidance lemma.
No regularity/image-closure shortcut discharges hShadowFree. -/
theorem globalOriginalMaximalTrace_fraisseCore_of_shadowFree
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hArity : NativeLanguagePositiveArity L)
    (hShadowFree : GlobalCanonicalShadowFreeAmalgamation F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A)) :
    GlobalFiniteMaximalTraceAmalgamationCore F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) :=
  globalFiniteMaximalTrace_fraisseCore_of_shadowFree
    F (fun {V : Type} (A : Structure L V) =>
      AvoidsGlobalFunctionalEHN F A)
    hRegular
    (globalNativeFiniteJEP_connected_positiveArity F hArity hConnected)
    hShadowFree

/-- Stronger source-geometric package: if both full irreducible
function-input-root coverage and the two complete generated
boundaries of every minimal mixed source piece are supplied,
the already proved Claim 2 conditional theorem discharges
shadow avoidance and produces the genuine finite-age core.

Those source-geometric premises remain ADDITIONAL hypotheses,
not verified consequences of the printed Section 3 assumptions. -/
theorem globalOriginalMaximalTrace_fraisseCore_of_geometricConditions
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hArity : NativeLanguagePositiveArity L)
    (hGeometry : GlobalMinimalWitnessGeometricConditions F) :
    GlobalFiniteMaximalTraceAmalgamationCore F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) :=
  globalOriginalMaximalTrace_fraisseCore_of_shadowFree
    F hRegular hConnected hArity
    (globalCanonicalShadowFree_of_minimalGeometricConditions
      F hFiniteF hConnected hGeometry)

/-- A genuinely UNCONDITIONAL strong-amalgamation case for the
original root-injective global maximal-trace age: forbidden sources
irreducible in the native functional sense. Connectivity/nonemptiness
and positive arity provide a separate, genuine JEP proof. -/
theorem globalOriginalMaximalTrace_fraisseCore_irreducible
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hArity : NativeLanguagePositiveArity L)
    (hIrred : GlobalForbiddenSourcesIrreducible F) :
    GlobalFiniteMaximalTraceAmalgamationCore F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) :=
  globalOriginalMaximalTrace_fraisseCore_of_shadowFree
    F hRegular hConnected hArity
    (globalCanonicalShadowFree_irreducible F hIrred)

/-- Exact original native reduct, with every old function-value fibre
unchanged. This needs regularity and the already checked full-
embedding heredity of Forb_EHN(F), NOT the hard shadow-avoidance lemma. -/
theorem globalOriginalMaximalTrace_exactReduct
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {VA : Type} [Finite VA] (A : Structure L VA) :
    (∃ (Y : Structure (globalFunctionalPieceLanguage F) VA),
      functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y = A ∧
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (B : Structure L W) =>
          AvoidsGlobalFunctionalEHN F B) Y) ↔
    AvoidsGlobalFunctionalEHN F A := by
  exact globalFiniteMaximalTraceAge_exact_reduct
    F (fun {W : Type} (B : Structure L W) =>
      AvoidsGlobalFunctionalEHN F B)
    hRegular
    (fun e hB => avoidsGlobalFunctionalEHN_of_embedding F e hB)
    A

/-- A fixed expanded copy type can pull back an arbitrary colouring
of OLD full embeddings. The resulting monochromatic statement holds
only for old copies induced by that ONE expanded type.

It does not claim a Ramsey arrow for the native shadow or for all
expanded A-types. Iteration over the finite exact fibre and the
class-level Ramsey existence theorem remain separate obligations. -/
def GlobalMaximalTraceExpandedArrow
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VA VB VC : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (C : Structure (globalFunctionalPieceLanguage F) VC)
    (Color : Type) : Prop :=
  ∀ χ : Structure.Embedding A C → Color,
    ∃ (j : Structure.Embedding B C) (monochrome : Color),
      ∀ e : Structure.Embedding A B,
        χ (j.comp e) = monochrome

theorem globalMaximalTrace_expandedArrow_controls_shadowColor_oneType
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VA VB VC : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (C : Structure (globalFunctionalPieceLanguage F) VC)
    (Color : Type)
    (hArrow : GlobalMaximalTraceExpandedArrow F A B C Color)
    (χold : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) A)
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) C) → Color) :
    ∃ (j : Structure.Embedding B C) (monochrome : Color),
      ∀ e : Structure.Embedding A B,
        χold (functionalShadowBigEmbedding L
          (GlobalFunctionalPieceSymbol F)
          (globalFunctionalPieceArity F) (j.comp e)) =
          monochrome := by
  exact hArrow (fun e =>
    χold (functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) e))

end AllThoseRamseyClasses.Lifts
