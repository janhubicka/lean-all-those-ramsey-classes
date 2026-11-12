import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitAllStageCoherentMaps
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitRequestEnumeration

/-!
# Track F: surjective union of the coherent all-original-stage FULL images

The strict sequence of genuine FULL native stage embeddings
has two kinds of maps: chosen maps g_n:X_(m_n) ↪ M and the
ALL-ORIGINAL-STAGE maps h_i:X_i ↪ M used for Mathlib's
first-order direct-limit universal property.

Target requests are hit by g_n, not automatically h_n.
We prove the necessary missing transport using the strict
stage-index bound n≤m_n and all-selected-stage coherence:
h_(m_n)(a) = g_n(a) for every a in X_(m_n).

Consequently, if the schedule eventually requests every
limit vertex in its target coordinate, the union of the
FULL all-stage images h_i(X_i) is exactly the limit carrier.
This proves the intended surjectivity *at the stage level*,
without assuming an infinite map or its properties.

The canonical initial stage and the exhaustive diagonal
schedule are also defined from the already verified native
limit constructors and countability theorem. Empty carriers
are handled without assuming any inhabitant.

The original finite Fraïssé input remains an explicit
hypothesis, including unresolved unrestricted reducible
shadow-avoidance/2019 Claim 2. No original manuscript edits.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine starting finite fair stage and its FULL canonical
embedding into the decoded native limit, even if the stage is
empty. No nonemptiness is postulated. -/
noncomputable def globalOriginalFairNativeCanonicalInitialState
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    GlobalOriginalFairNativeStageState F hInput :=
  ⟨0, globalOriginalTraceFullLimitIncl F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput) 0⟩

/-- An explicit chosen exhaustive diagonal schedule of
finite source/target requests, obtained from native
countability and the optional Encodable decoding. -/
noncomputable def globalOriginalFairNativeDiagonalSchedule
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    ℕ → GlobalOriginalFairNativeRequests F hInput :=
  Classical.choose
    (globalOriginalActualFairNativeLimit_diagonalSchedule_exists F hInput)

/-- Every limit vertex occurs diagonally in the chosen schedule,
without any Inhabited assumption on the carrier. -/
theorem globalOriginalFairNativeDiagonalSchedule_covers
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (y : GlobalOriginalFairNativeVertex F hInput) :
    ∃ n : ℕ,
      (y, y) ∈ globalOriginalFairNativeDiagonalSchedule F hInput n := by
  exact (Classical.choose_spec
    (globalOriginalActualFairNativeLimit_diagonalSchedule_exists
      F hInput)) y

/-- For arbitrary initial FULL stage map and any exhaustive
diagonal schedule, the all-original-stage FULL maps hit every
target vertex. The witness i is a genuine ORIGINAL fair-chain
index and the witness a lies in the actual finite stage X_i.

Proof uses coherence between selected iteration indices
n+1 and m_(n+1), not any assumption about the limit quotient. -/
theorem globalOriginalFairNativeStrictSequence_allStage_targetCover
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (hReq : ∀ y : GlobalOriginalFairNativeVertex F hInput,
      ∃ n : ℕ, (y, y) ∈ schedule n)
    (y : GlobalOriginalFairNativeVertex F hInput) :
    ∃ (i : ℕ)
      (a : (globalOriginalActualFairTraceChain F hInput i).Carrier),
      globalOriginalFairNativeStrictSequence_allStageMap
        F hInput initial schedule i a = y := by
  classical
  let seq := globalOriginalFairNativeStrictStageSequence
    F hInput initial schedule
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨n, hn⟩ := hReq y
  obtain ⟨a, b, ha, hb⟩ :=
    globalOriginalFairNativeStrictStageSequence_request_persists
      F hInput initial schedule n (n + 1) (le_refl _) (y, y) hn
  let k := (seq (n + 1)).1
  have hnk : n + 1 ≤ k :=
    globalOriginalFairNativeStrictStageSequence_index_ge
      F hInput initial schedule (n + 1)
  obtain ⟨hlater, hcompat⟩ :=
    globalOriginalFairNativeStrictStageSequence_coherent
      F hInput initial schedule (n + 1) k hnk
  refine ⟨k, b, ?_⟩
  calc
    globalOriginalFairNativeStrictSequence_allStageMap
        F hInput initial schedule k b =
      (seq k).2
        ((globalOriginalFiniteTraceChainLE F hInput
          representatives diagrams k (seq k).1
          (globalOriginalFairNativeStrictStageSequence_index_ge
            F hInput initial schedule k)) b) :=
        globalOriginalFairNativeStrictSequence_allStageMap_apply
          F hInput initial schedule k b
    _ = (seq (n + 1)).2 b := hcompat b
    _ = y := hb

/-- The canonical strict sequence using the actual first
fair stage and the chosen diagonal schedule has ALL-stage
FULL images covering the whole native limit. This is the
surjectivity input for the pending actual first-order lift. -/
theorem globalOriginalFairNativeCanonicalStrictSequence_allStage_targetCover
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (y : GlobalOriginalFairNativeVertex F hInput) :
    ∃ (i : ℕ)
      (a : (globalOriginalActualFairTraceChain F hInput i).Carrier),
      globalOriginalFairNativeStrictSequence_allStageMap F hInput
        (globalOriginalFairNativeCanonicalInitialState F hInput)
        (globalOriginalFairNativeDiagonalSchedule F hInput)
        i a = y := by
  exact globalOriginalFairNativeStrictSequence_allStage_targetCover
    F hInput
    (globalOriginalFairNativeCanonicalInitialState F hInput)
    (globalOriginalFairNativeDiagonalSchedule F hInput)
    (globalOriginalFairNativeDiagonalSchedule_covers F hInput) y

end AllThoseRamseyClasses.Lifts
