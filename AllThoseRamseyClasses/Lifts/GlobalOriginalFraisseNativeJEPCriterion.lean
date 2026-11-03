import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3FraisseInput
import AllThoseRamseyClasses.Lifts.GlobalCountableLiftSignature
import AllThoseRamseyClasses.Lifts.GlobalNullaryMaximalTraceJEPObstruction

/-!
# Track F — native JEP criterion for the original global Fraïssé-age input

The earlier finite-age assembly required every old relation/function
symbol to have positive arity solely to derive native JEP from
connected nonempty forbidden sources. This is a SUFFICIENT condition,
not the correct general assumption when the native language admits
nullary data.

The exact condition is full native finite JEP of Forb_EHN(F).
Under regularity, global maximal-trace JEP is equivalent to this
condition. Therefore, assuming the STILL OPEN original root-injective
GlobalCanonicalShadowFreeAmalgamation, finite original signature
and nonempty connected forbidden sources, the COMPLETE FINITE-AGE
Fraïssé input is equivalent to native JEP.

Countability of both original lift symbol types is bundled as a
separate proved consequence of regularity. The old functions are
preserved as entire set-valued fibres; no positive-only EHN map
is silently substituted for a FULL embedding.

The irreducible-source case discharges shadow avoidance but retains
native JEP, permitting compatible nullary signatures. For the empty
forbidden family with an incompatible nullary relation, the age input
itself fails, now a direct corollary of the Lean-verified JEP
counterexample.

None of these declarations constructs a Fraïssé limit or proves
the unrestricted Section 3 shadow-avoidance / Ramsey theorem.
The numbered 2019 manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every original global finite Fraïssé-age input forces genuine
FULL native JEP of the forbidden-free old structures.
It is independent of the missing shadow-avoidance theorem;
regularity is needed to expand arbitrary finite old members
to actual finite maximal traces. -/
theorem globalOriginalFiniteFraisseInput_implies_nativeJEP
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    GlobalNativeFiniteJEP
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) := by
  exact globalFiniteMaximalTrace_jep_implies_nativeJEP
    F (fun {W : Type} (A : Structure L W) =>
      AvoidsGlobalFunctionalEHN F A)
    hRegular
    (fun e hB => avoidsGlobalFunctionalEHN_of_embedding F e hB)
    hInput.finiteAgeCore.jointEmbedding

/-- The original global finite-age Fraïssé input can be built
WITHOUT a blanket positive-arity assumption. A native FULL JEP
hypothesis supplies precisely the missing joint embedding, while
regularity supplies finite maximal traces and a countable
representative cover, and shadow avoidance supplies strong AP.

This theorem is conditional on the ORIGINAL root-injective
GlobalCanonicalShadowFreeAmalgamation and does not derive it. -/
theorem globalOriginalFiniteFraisseInput_of_nativeJEP
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hNativeJEP : GlobalNativeFiniteJEP
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A))
    (hShadowFree : GlobalCanonicalShadowFreeAmalgamation F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)) :
    GlobalOriginalFiniteFraisseInput F := by
  obtain ⟨hCount, hCover⟩ :=
    globalMaximalTraceAge_countableIsoCover L F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) hRegular
  exact {
    nonempty := globalOriginalMaximalTraceAge_nonempty
      L F hRegular hConnected
    finiteAgeCore := globalFiniteMaximalTrace_fraisseCore_of_shadowFree
      F (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)
      hRegular hNativeJEP hShadowFree
    countableRepresentatives := hCount
    coversEveryAgeMember := hCover
  }

/-- An exact criterion, WITH shadow avoidance supplied:
the complete finite Fraïssé-age package for the actual ORIGINAL
regular root-injective global lift holds if and only if the old
forbidden-free finite class has FULL native JEP.

No extra positive-arity condition, no finite forbidden family,
and no image-injectivization premise. For an arbitrary reducible
family the original shadow-avoidance hypothesis remains OPEN. -/
theorem globalOriginalFiniteFraisseInput_iff_nativeJEP_of_shadowFree
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hShadowFree : GlobalCanonicalShadowFreeAmalgamation F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)) :
    GlobalOriginalFiniteFraisseInput F ↔
      GlobalNativeFiniteJEP
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN F A) := by
  constructor
  · exact globalOriginalFiniteFraisseInput_implies_nativeJEP
      F hRegular
  · intro hNativeJEP
    exact globalOriginalFiniteFraisseInput_of_nativeJEP
      L F hRegular hConnected hNativeJEP hShadowFree

/-- Finite Fraïssé-age conditions PLUS the countability of the
ACTUAL entire lifted signature, including all global positive-width
piece-class relations and the old native function symbols.

The signature can be infinite. No uniform piece width bound is used. -/
theorem globalOriginalFiniteFraisseInput_and_countableLanguage
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hNativeJEP : GlobalNativeFiniteJEP
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A))
    (hShadowFree : GlobalCanonicalShadowFreeAmalgamation F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)) :
    GlobalOriginalFiniteFraisseInput F ∧
      Countable (globalFunctionalPieceLanguage F).RelSymbol ∧
      Countable (globalFunctionalPieceLanguage F).FuncSymbol := by
  obtain ⟨hR, hFun⟩ :=
    globalFunctionalPieceLanguage_countable_of_finiteOld F hRegular
  exact ⟨globalOriginalFiniteFraisseInput_of_nativeJEP
    L F hRegular hConnected hNativeJEP hShadowFree,
    hR, hFun⟩

/-- In the irreducible forbidden-source special case, exact
finite Fraïssé prerequisites and countable language follow from
regularity, nonempty connected sources, a finite old signature,
and FULL native JEP. Shadow avoidance is discharged by the
previously checked irreducible-source theorem, not assumed. -/
theorem globalOriginalFiniteFraisseInput_irreducible_nativeJEP
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hIrred : GlobalForbiddenSourcesIrreducible F)
    (hNativeJEP : GlobalNativeFiniteJEP
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A)) :
    GlobalOriginalFiniteFraisseInput F ∧
      Countable (globalFunctionalPieceLanguage F).RelSymbol ∧
      Countable (globalFunctionalPieceLanguage F).FuncSymbol :=
  globalOriginalFiniteFraisseInput_and_countableLanguage
    L F hRegular hConnected hNativeJEP
    (globalCanonicalShadowFree_irreducible F hIrred)

/-- The nullary obstruction also rules out the FULL original
finite Fraïssé-age input, not merely native JEP or a larger
axiom package. The forbidden family is empty (thus regular),
and one old nullary relation has opposite truth values on two
otherwise finite allowed native singleton structures. -/
theorem emptyForbidden_globalOriginalFiniteFraisseInput_fails_nullary
    (L : Language.{u}) (R : L.RelSymbol)
    (hZero : L.relArity R = 0) :
    ¬ GlobalOriginalFiniteFraisseInput (emptyGlobalForbiddenFamily L) := by
  intro hInput
  have hJEP :
      GlobalNativeFiniteJEP
        (fun {W : Type} (A : Structure L W) =>
          AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A) :=
    globalOriginalFiniteFraisseInput_implies_nativeJEP
      (emptyGlobalForbiddenFamily L)
      (emptyGlobalForbiddenFamily_regular L) hInput
  exact (emptyForbidden_nativeJEP_fails_of_nullaryRelation
    L R hZero) hJEP

end AllThoseRamseyClasses.Lifts
