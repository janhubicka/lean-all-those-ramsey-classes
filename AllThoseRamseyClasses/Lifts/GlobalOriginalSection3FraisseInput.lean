import AllThoseRamseyClasses.Lifts.GlobalCountableTraceRepresentatives
import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3AgeNonempty

/-!
# Track F: exact original Section 3 finite Fraisse-age INPUT

Assemble four independently certified obligations for the ORIGINAL
root-injective regular maximal-trace age of Forb_EHN(F):
  * a genuine age member (on the empty carrier);
  * hereditary membership, FULL finite joint embedding and strong
    amalgamation with exactly prescribed overlap;
  * a countable type of actual age representatives on Fin n;
  * FULL surjective expanded embeddings from representatives onto
    every finite age member.

For finite native signatures with positive arities and connected
nonempty forbidden sources, the only additional mathematical
hypothesis is exactly the outstanding
GlobalCanonicalShadowFreeAmalgamation for the ORIGINAL canonical lift.
The irreducible-source special case discharges it.

This is deliberately a certificate for the finite Fraisse-age
conditions, NOT a construction of a Fraisse limit or an assertion
of omega-categoricity, existential completeness, free shadows of
arbitrary expanded amalgams, or the full Ramsey property. Mathlib's
FirstOrder.Language formalism has a different signature/embedding API
than the native set-valued functional Structures used here. A limit
construction and any interface transport remain separate.

The original printed ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Concrete, genuinely finite original maximal-trace age
representatives on Fin n for the actual native EHN-forbidden-free
class. No quotient by isomorphism or abstract selection oracle. -/
abbrev GlobalOriginalFiniteTraceRepresentatives
    (F : ∀ {W : Type}, Structure L W → Prop) :=
  Σ n : ℕ,
    {Z : Structure (globalFunctionalPieceLanguage F) (Fin n) //
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN F A) Z}

/-- The complete FINITE-AGE prerequisites of a Fraisse construction
for the ORIGINAL global maximal lift: nonempty, HP/JEP/strong AP,
and a countable cover by FULL isomorphism types.

This record is intentionally stronger than ordinary AP yet makes
no existence claim about a limit. It does not silently assume
that the original forbidden family satisfies Claim 2. -/
structure GlobalOriginalFiniteFraisseInput
    (F : ∀ {W : Type}, Structure L W → Prop) : Prop where
  nonempty :
    ∃ (Y : Structure (globalFunctionalPieceLanguage F) Empty),
      IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN F A) Y
  finiteAgeCore :
    GlobalFiniteMaximalTraceAmalgamationCore F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)
  countableRepresentatives :
    Countable (GlobalOriginalFiniteTraceRepresentatives F)
  coversEveryAgeMember :
    ∀ {V : Type}
      (Y : Structure (globalFunctionalPieceLanguage F) V)
      (hY : IsGlobalFiniteMaximalTrace F
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN F A) Y),
      ∃ p : GlobalOriginalFiniteTraceRepresentatives F,
        ∃ e : Structure.Embedding p.2.1 Y,
          Function.Surjective e

/-- All finite-age Fraisse-input axioms follow from REGULARITY,
connected nonempty forbidden sources, a FINITE native signature,
positive symbol arities (so native JEP holds), and the precise
additional ORIGINAL shadow-avoidance hypothesis.

In particular this theorem does NOT discharge shadow avoidance
from mere HE-image-closure or the printed Claim 2 proof. -/
theorem globalOriginalFiniteFraisseInput_of_shadowFree
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hArity : NativeLanguagePositiveArity L)
    (hShadowFree : GlobalCanonicalShadowFreeAmalgamation F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)) :
    GlobalOriginalFiniteFraisseInput F := by
  obtain ⟨hCount, hCover⟩ :=
    globalMaximalTraceAge_countableIsoCover L F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) hRegular
  exact {
    nonempty :=
      globalOriginalMaximalTraceAge_nonempty
        L F hRegular hConnected
    finiteAgeCore :=
      globalOriginalMaximalTrace_fraisseCore_of_shadowFree
        F hRegular hConnected hArity hShadowFree
    countableRepresentatives := hCount
    coversEveryAgeMember := hCover
  }

/-- Fully assembled finite Fraisse-age prerequisites in the
IRREDUCIBLE forbidden-source special case, for a finite original
positive-arity signature. This case does not assume ANY shadow
avoidance as an external axiom.

The general reducible connected-source case remains conditional. -/
theorem globalOriginalFiniteFraisseInput_irreducible
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hArity : NativeLanguagePositiveArity L)
    (hIrred : GlobalForbiddenSourcesIrreducible F) :
    GlobalOriginalFiniteFraisseInput F :=
  globalOriginalFiniteFraisseInput_of_shadowFree
    L F hRegular hConnected hArity
    (globalCanonicalShadowFree_irreducible F hIrred)

end AllThoseRamseyClasses.Lifts
