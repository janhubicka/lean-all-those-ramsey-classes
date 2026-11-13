import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFullHomogeneity
import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3FraisseInput

/-!
# Track F: FULL native homogeneity with explicit finite-age hypotheses

The actual fair native limit has finite FULL ultrahomogeneity whenever
the original finite Fraïssé input has been established. In particular:

* For irreducible forbidden sources the input is proved by the existing
  `globalOriginalFiniteFraisseInput_irreducible` theorem, with NO separate
  canonical shadow-avoidance assumption.
* For arbitrary connected forbidden sources the more general result
  still requires the precise `GlobalCanonicalShadowFreeAmalgamation`
  hypothesis; this is NOT known from the published unrestricted Claim 2.

Both theorems below produce genuine mutually inverse FULL native
embeddings, not merely bijections or first-order relational isomorphisms.
The original numbered manuscript is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- For irreducible forbidden sources, the actual fair native limit
is finitely FULL ultrahomogeneous without an additional shadow-free
amalgamation premise. Inverse maps preserve all complete partial
and multivalued function fibres, including nullary ones. -/
theorem globalOriginalActualFairNativeLimit_irreducible_fullHomogeneous_withInverse
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hArity : NativeLanguagePositiveArity L)
    (hIrred : GlobalForbiddenSourcesIrreducible F)
    {V : Type} [Finite V]
    (A : Structure (globalFunctionalPieceLanguage F) V)
    (j₀ j₁ : Structure.Embedding A
      (globalOriginalActualFairNativeLimit F
        (globalOriginalFiniteFraisseInput_irreducible
          L F hRegular hConnected hArity hIrred))) :
    ∃ (aut inv : Structure.Embedding
      (globalOriginalActualFairNativeLimit F
        (globalOriginalFiniteFraisseInput_irreducible
          L F hRegular hConnected hArity hIrred))
      (globalOriginalActualFairNativeLimit F
        (globalOriginalFiniteFraisseInput_irreducible
          L F hRegular hConnected hArity hIrred))),
      (∀ x, aut (inv x) = x) ∧
      (∀ x, inv (aut x) = x) ∧
      (∀ v : V, aut (j₀ v) = j₁ v) := by
  exact globalOriginalActualFairNativeLimit_finiteFullHomogeneous_withInverse
    F (globalOriginalFiniteFraisseInput_irreducible
      L F hRegular hConnected hArity hIrred) A j₀ j₁

/-- Explicitly isolate the precise extra geometric hypothesis
needed for the general connected, potentially reducible, case.
This is a conditional result and does not prove 2019 Claim 2. -/
theorem globalOriginalActualFairNativeLimit_shadowFree_fullHomogeneous_withInverse
    (L : Language.{u})
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hArity : NativeLanguagePositiveArity L)
    (hShadowFree : GlobalCanonicalShadowFreeAmalgamation F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A))
    {V : Type} [Finite V]
    (A : Structure (globalFunctionalPieceLanguage F) V)
    (j₀ j₁ : Structure.Embedding A
      (globalOriginalActualFairNativeLimit F
        (globalOriginalFiniteFraisseInput_of_shadowFree
          L F hRegular hConnected hArity hShadowFree))) :
    ∃ (aut inv : Structure.Embedding
      (globalOriginalActualFairNativeLimit F
        (globalOriginalFiniteFraisseInput_of_shadowFree
          L F hRegular hConnected hArity hShadowFree))
      (globalOriginalActualFairNativeLimit F
        (globalOriginalFiniteFraisseInput_of_shadowFree
          L F hRegular hConnected hArity hShadowFree))),
      (∀ x, aut (inv x) = x) ∧
      (∀ x, inv (aut x) = x) ∧
      (∀ v : V, aut (j₀ v) = j₁ v) := by
  exact globalOriginalActualFairNativeLimit_finiteFullHomogeneous_withInverse
    F (globalOriginalFiniteFraisseInput_of_shadowFree
      L F hRegular hConnected hArity hShadowFree) A j₀ j₁

end AllThoseRamseyClasses.Lifts
