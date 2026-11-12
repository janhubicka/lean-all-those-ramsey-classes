import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitActualFirstOrderLift
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitAllStageTargetCover

/-!
# Track F: actual first-order direct-limit embedding is SURJECTIVE

The real Mathlib first-order directed-limit lift of all original
finite fair-chain function-graph models is an embedding, not a
surjection by construction. This module proves onto-ness from
the exhaustive diagonal source/target request schedule and the
FULL strict selected-stage coherence.

The canonical initial state is stage 0 with the actual FULL
inclusion X_0 ↪ M. The exhaustive optional decoding schedule
hits every native-limit vertex, including the empty-carrier
edge case without requiring an arbitrary default vertex.

The existing ALL-ORIGINAL-STAGE image coverage theorem gives,
for every y∈M, an original finite stage X_i and vertex x∈X_i
such that h_i(x)=y. Applying Mathlib's exact lift_of law to
the real canonical stage inclusion u_i(x) produces a preimage
of y for the infinite first-order map.

Nothing is postulated about ultrahomogeneity. Conversion of
this onto first-order function-graph embedding to a genuine
FULL native automorphism is a separate step using the proven
surjective graph-to-FULL bridge.

All statements remain conditional on GlobalOriginalFiniteFraisseInput F,
which retains unresolved unrestricted reducible-source
shadow-avoidance/2019 Claim 2. Numbered manuscript frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Actual first-order self-embedding of the complete
function-graph directed-limit model from the canonical
strict FULL stage sequence and exhaustive diagonal schedule.

The target and source are the same genuine quotient model. -/
noncomputable def globalOriginalFairNativeCanonicalFirstOrderLimitMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    @FirstOrder.Language.Embedding
      (GlobalOriginalTraceFirstOrderLanguage F)
      (GlobalOriginalFairNativeVertex F hInput)
      (GlobalOriginalFairNativeVertex F hInput)
      (globalOriginalTraceFirstOrderLimitModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput))
      (globalOriginalTraceFirstOrderLimitModel F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)) :=
  globalOriginalFairNativeStrictSequence_firstOrderLimitMap F hInput
    (globalOriginalFairNativeCanonicalInitialState F hInput)
    (globalOriginalFairNativeDiagonalSchedule F hInput)

/-- Surjectivity follows from exact all-original-stage
target coverage together with Mathlib's checked
direct-limit lift equation, not from an infinite map
being declared onto by fiat. -/
theorem globalOriginalFairNativeCanonicalFirstOrderLimitMap_surjective
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    Function.Surjective
      (globalOriginalFairNativeCanonicalFirstOrderLimitMap F hInput) := by
  intro y
  obtain ⟨i, x, hix⟩ :=
    globalOriginalFairNativeCanonicalStrictSequence_allStage_targetCover
      F hInput y
  refine ⟨globalOriginalTraceFirstOrderLimitIncl F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput) i x, ?_⟩
  change
    (globalOriginalFairNativeStrictSequence_firstOrderLimitMap F hInput
      (globalOriginalFairNativeCanonicalInitialState F hInput)
      (globalOriginalFairNativeDiagonalSchedule F hInput))
      (globalOriginalTraceFirstOrderLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput) i x) = y
  rw [globalOriginalFairNativeStrictSequence_firstOrderLimitMap_of]
  exact hix

/-- The genuinely constructed first-order limit map is a
BIJECTION preserving and reflecting every complete
function-graph relation. Full native functional structure
conversion is a separate theorem. -/
theorem globalOriginalFairNativeCanonicalFirstOrderLimitMap_bijective
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    Function.Bijective
      (globalOriginalFairNativeCanonicalFirstOrderLimitMap F hInput) :=
  ⟨(globalOriginalFairNativeCanonicalFirstOrderLimitMap
      F hInput).injective,
    globalOriginalFairNativeCanonicalFirstOrderLimitMap_surjective
      F hInput⟩

end AllThoseRamseyClasses.Lifts
