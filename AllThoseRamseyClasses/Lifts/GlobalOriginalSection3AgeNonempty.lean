import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3ClassAssembly

/-!
# Track F: the original regular global maximal-trace age is nonempty

The printed Section 3 homogenization theorem uses a Fraisse age.
The verified finite maximal-trace HP/JEP/AP core intentionally does
not assert its age is nonempty.

For the actual original native Forb_EHN(F), with each finite
forbidden source NONEMPTY, the entirely empty native functional
structure is forbidden-free: no weak EHN map from any nonempty
source can land in Empty. The proof does not need source
irreducibility, root-injectivity, image closure, JEP or Claim 2.

For regular F, the already certified finite maximal-along-root
extension theorem supplies a genuine maximal induced trace on
the SAME empty carrier. This is a nonempty-age witness regardless
of nullary data; the native empty structure has all nullary
relation tables false and nullary partial-function fibres empty.

This discharges the NONEMPTY age condition, not the distinct
missing countability / Fraisse limit / strong amalgamation /
Ramsey class claims. The numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- The native empty functional structure forbids every nonempty
finite EHN source. Connectedness is used only for its asserted
nonemptiness, and no actual forbidden root geometry is required. -/
theorem nativeEmpty_avoids_connectedForbiddenSources
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F) :
    AvoidsGlobalFunctionalEHN F (nativeEmptyStructure L) := by
  intro U Source hFinite hF f _hf
  obtain ⟨x⟩ := (hConnected Source hFinite hF).1
  exact isEmptyElim (f x)

/-- The ORIGINAL regular global maximal-trace age has an ACTUAL member
on the empty carrier. This proves nonemptiness without assuming any
strong-amalgamation, native JEP or positivity of the signature's
arities. It is not the Fraisse limit. -/
theorem globalOriginalMaximalTraceAge_nonempty
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F) :
    ∃ (Y : Structure (globalFunctionalPieceLanguage F) Empty),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN F A) Y := by
  obtain ⟨Y, _hShadow, hAge⟩ :=
    globalFiniteMaximalTraceAge_exists_above
      F (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)
      hRegular (nativeEmptyStructure L)
      (nativeEmpty_avoids_connectedForbiddenSources L F hConnected)
  exact ⟨Y, hAge⟩

end AllThoseRamseyClasses.Lifts
