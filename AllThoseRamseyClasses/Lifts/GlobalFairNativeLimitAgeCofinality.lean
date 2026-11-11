import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFullLimitInclusions
import AllThoseRamseyClasses.Lifts.GlobalFairFraisseWholeAgeCofinality

/-!
# Track F — every finite original maximal-trace age member embeds in the fair native limit

The finite original maximal-trace age has a genuine FAIR chain of
finite stages (merged Track F #928) with the whole-age cofinality
theorem (merged #932). The later proposed full stage-to-limit theorem
(Track F #930) reconstructs genuinely FULL native functional
embeddings of each stage into the decoded direct limit.

Combining these two facts gives the *forward* age-inclusion:
every finite structure in the actual original maximal-trace age
FULLY embeds into the decoded native fair direct limit.

The theorem is conditional on `GlobalOriginalFiniteFraisseInput`
and on the kernel verification of #930 and its prerequisites.
The OTHER direction of age equality requires factoring every
finite FULL limit copy into a full finite stage and applying
heredity. It is NOT claimed here. Finite extension property
and ultrahomogeneity are also separate.

No reduct or weak EHN map substitutes for a FULL functional
embedding: the complete output fibres, nullaries and added
root-injective piece relations are preserved by composition.

The frozen numbered ramsey.tex is not edited.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual native functional structure obtained from the
first-order direct limit of the original FULL fair chain. -/
noncomputable def globalOriginalActualFairNativeLimit
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    Structure (globalFunctionalPieceLanguage F)
      (GlobalOriginalTraceFirstOrderDirectLimit F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)) :=
  globalOriginalTraceNativeDirectLimitModel F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput)

/-- Every actual finite original maximal-trace member fully
embeds in the actual decoded native FAIR limit. This proves
ONE implication of finite-age equality, without assuming
the converse finite-factorization lemma or homogeneity. -/
theorem globalOriginalActualFairNativeLimit_contains_fullAge
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {V : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) V)
    (hY : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) Y) :
    ∃ (_jY : Structure.Embedding Y
      (globalOriginalActualFairNativeLimit F hInput)), True := by
  obtain ⟨N, hN⟩ :=
    globalOriginalActualFairTraceChain_eventually_contains_age_member
      F hInput Y hY
  obtain ⟨jY, _⟩ := hN N (le_refl N)
  let jLimit : Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput (N + 1)).model
      (globalOriginalActualFairNativeLimit F hInput) :=
    globalOriginalTraceFullLimitIncl F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput) (N + 1)
  exact ⟨jLimit.comp jY, True.intro⟩

end AllThoseRamseyClasses.Lifts
