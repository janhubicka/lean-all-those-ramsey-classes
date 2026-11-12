import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStageChainGeneric
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStrictStageSequence

/-!
# Track F: cofinal-in-index and coherent FULL stage recursion

Combine the certified-one-step generic stage-chain algebra
(#1035 proposed) with the strictly increasing proof-carrying
native stage recursion (#1032 proposed).

The result is a genuinely chosen countable sequence
g_n:X_(m_n) ↪ M of FULL native functional embeddings that:
* satisfies m_n ≥ n and therefore is cofinal in the ORIGINAL
  directed-system indices;
* is exactly coherent across EVERY pair of iteration indices;
* permanently preserves every source-cover/target-hit request,
  not just those of the latest finite batch.

This supplies precisely the finite-stage input family needed
to construct compatible FULL maps h_i:X_i↪M for ALL original
finite stages and then invoke Mathlib's actual
FirstOrder.Language.DirectLimit.lift. It does not assert that
the resulting infinite map or automorphism is already built.

Conditional on GlobalOriginalFiniteFraisseInput F; the
general reducible-source shadow-avoidance / 2019 Claim 2
condition is still unresolved. No numbered-manuscript edits.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The strictly growing chosen FULL native stage maps are
compatible along the genuine FULL original fair-chain
transition between ANY two selected stages i≤j. -/
theorem globalOriginalFairNativeStrictStageSequence_coherent
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i j : ℕ) (hij : i ≤ j) :
    ∃ hlevels :
        (globalOriginalFairNativeStrictStageSequence F hInput initial schedule i).1 ≤
        (globalOriginalFairNativeStrictStageSequence F hInput initial schedule j).1,
      ∀ a : (globalOriginalActualFairTraceChain F hInput
        (globalOriginalFairNativeStrictStageSequence F hInput initial schedule i).1).Carrier,
        (globalOriginalFairNativeStrictStageSequence
          F hInput initial schedule j).2
          ((globalOriginalFiniteTraceChainLE F hInput
            (globalOriginalRepresentativePrefix F hInput)
            (globalOriginalExtensionDiagramPrefix F hInput)
            (globalOriginalFairNativeStrictStageSequence
              F hInput initial schedule i).1
            (globalOriginalFairNativeStrictStageSequence
              F hInput initial schedule j).1 hlevels) a) =
        (globalOriginalFairNativeStrictStageSequence
          F hInput initial schedule i).2 a := by
  exact globalOriginalFairNativeStageChain_coherent_of_stepSpec
    F hInput
    (globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule)
    schedule
    (fun n => (globalOriginalFairNativeStrictStageSequence_stepSpec
      F hInput initial schedule n).1)
    i j hij

/-- A source/target request met at stage i permanently
persists in the canonical source image and FULL-map target
image of every later strict stage j≥i+1. -/
theorem globalOriginalFairNativeStrictStageSequence_request_persists
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i j : ℕ) (hij : i + 1 ≤ j)
    (p : GlobalOriginalFairNativeVertex F hInput ×
      GlobalOriginalFairNativeVertex F hInput)
    (hp : p ∈ schedule i) :
    ∃ (a b : (globalOriginalActualFairTraceChain F hInput
      (globalOriginalFairNativeStrictStageSequence F hInput initial schedule j).1).Carrier),
      (globalOriginalTraceFullLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        (globalOriginalFairNativeStrictStageSequence
          F hInput initial schedule j).1) a = p.1 ∧
      (globalOriginalFairNativeStrictStageSequence
        F hInput initial schedule j).2 b = p.2 := by
  exact globalOriginalFairNativeStageChain_request_persists_of_stepSpec
    F hInput
    (globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule)
    schedule
    (fun n => (globalOriginalFairNativeStrictStageSequence_stepSpec
      F hInput initial schedule n).1)
    i j hij p hp

end AllThoseRamseyClasses.Lifts
