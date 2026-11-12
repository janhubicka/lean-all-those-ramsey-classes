import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStageSequence
import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainCoherence

/-!
# Track F: global coherence and durable coverage for a chosen FULL stage sequence

The previous module builds the actual Nat-indexed sequence of
genuine FULL embeddings X_(m_n) ↪ M and certifies coherence
only across consecutive stages.  Here we prove the transitive
coherence theorem between EVERY two selected stages i≤j.
This is the exact replacement for a hypothesized "compatible
family of finite maps" in the final directed-limit construction.

We also show that a vertex covered/hit during a scheduled
finite batch remains covered/hit at every later stage. These
are explicit source and target coverage invariants; no
unverified direct-limit map is claimed yet.

The entire proof remains conditional on the genuine finite
Fraïssé input and its unresolved general reducible-source
shadow-avoidance/Claim 2 hypothesis. No numbered-manuscript edits.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any two stages of the actual proof-carrying sequence have
a genuine FULL transition between their underlying fair-chain
levels, and the selected FULL maps into the native limit agree
exactly on that transition. -/
theorem globalOriginalFairNativeStageSequence_coherent
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i j : ℕ) (hij : i ≤ j) :
    ∃ hlevels :
        (globalOriginalFairNativeStageSequence F hInput initial schedule i).1 ≤
        (globalOriginalFairNativeStageSequence F hInput initial schedule j).1,
      ∀ a : (globalOriginalActualFairTraceChain F hInput
          (globalOriginalFairNativeStageSequence F hInput initial schedule i).1).Carrier,
        (globalOriginalFairNativeStageSequence F hInput initial schedule j).2
          ((globalOriginalFiniteTraceChainLE F hInput
            (globalOriginalRepresentativePrefix F hInput)
            (globalOriginalExtensionDiagramPrefix F hInput)
            (globalOriginalFairNativeStageSequence F hInput initial schedule i).1
            (globalOriginalFairNativeStageSequence F hInput initial schedule j).1
            hlevels) a) =
        (globalOriginalFairNativeStageSequence F hInput initial schedule i).2 a := by
  classical
  induction j, hij using Nat.le_induction with
  | base =>
      refine ⟨le_refl _, ?_⟩
      intro a
      rw [globalOriginalFiniteTraceChainLE_self]
      rfl
  | succ j hj ih =>
      obtain ⟨hij', hcompat⟩ := ih
      obtain ⟨hstep, _, hstepCompat⟩ :=
        globalOriginalFairNativeStageSequence_stepSpec
          F hInput initial schedule j
      let seq := globalOriginalFairNativeStageSequence F hInput initial schedule
      let representatives := globalOriginalRepresentativePrefix F hInput
      let diagrams := globalOriginalExtensionDiagramPrefix F hInput
      refine ⟨le_trans hij' hstep, ?_⟩
      intro a
      have hcomp :=
        congrArg
          (fun e : Structure.Embedding
            (globalOriginalActualFairTraceChain F hInput (seq i).1).model
            (globalOriginalActualFairTraceChain F hInput (seq (j + 1)).1).model =>
              e a)
          (globalOriginalFiniteTraceChainLE_comp
            F hInput representatives diagrams
            (seq i).1 (seq j).1 (seq (j + 1)).1 hij' hstep)
      calc
        (seq (j + 1)).2
            ((globalOriginalFiniteTraceChainLE F hInput
              representatives diagrams (seq i).1
              (seq (j + 1)).1 (le_trans hij' hstep)) a) =
          (seq (j + 1)).2
            ((globalOriginalFiniteTraceChainLE F hInput
              representatives diagrams (seq j).1
              (seq (j + 1)).1 hstep)
              ((globalOriginalFiniteTraceChainLE F hInput
                representatives diagrams (seq i).1
                (seq j).1 hij') a)) :=
            congrArg (seq (j + 1)).2 hcomp.symm
        _ = (seq j).2
              ((globalOriginalFiniteTraceChainLE F hInput
                representatives diagrams (seq i).1
                (seq j).1 hij') a) :=
            hstepCompat _
        _ = (seq i).2 a := hcompat a

/-- Once a scheduled pair has been covered in the source and
hit in the range, its two witnesses transport through EVERY
subsequent FULL stage transition. -/
theorem globalOriginalFairNativeStageSequence_request_persists
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i j : ℕ) (hij : i + 1 ≤ j)
    (p : GlobalOriginalFairNativeVertex F hInput ×
      GlobalOriginalFairNativeVertex F hInput)
    (hp : p ∈ schedule i) :
    ∃ (a b : (globalOriginalActualFairTraceChain F hInput
      (globalOriginalFairNativeStageSequence F hInput initial schedule j).1).Carrier),
      (globalOriginalTraceFullLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        (globalOriginalFairNativeStageSequence F hInput initial schedule j).1) a =
          p.1 ∧
      (globalOriginalFairNativeStageSequence F hInput initial schedule j).2 b =
          p.2 := by
  classical
  let seq := globalOriginalFairNativeStageSequence F hInput initial schedule
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨hstep, hCoverStep, _⟩ :=
    globalOriginalFairNativeStageSequence_stepSpec
      F hInput initial schedule i
  obtain ⟨ai, bi, hai, hbi⟩ := hCoverStep p hp
  obtain ⟨hlater, hlaterCompat⟩ :=
    globalOriginalFairNativeStageSequence_coherent
      F hInput initial schedule (i + 1) j hij
  let e := globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams
    (seq (i + 1)).1 (seq j).1 hlater
  refine ⟨e ai, e bi, ?_, ?_⟩
  · have hcocone :=
      globalOriginalTraceFullLimitIncl_comp
        F hInput representatives diagrams
        (seq (i + 1)).1 (seq j).1 hlater
    have hpt :=
      congrArg
        (fun v : Structure.Embedding
          (globalOriginalActualFairTraceChain F hInput (seq (i + 1)).1).model
          (globalOriginalActualFairNativeLimit F hInput) =>
            v ai) hcocone
    exact hpt.trans hai
  · exact (hlaterCompat bi).trans hbi

/-- If every limit vertex occurs as the left coordinate of
some request, the chosen canonical selected-stage images
jointly cover the ENTIRE native-limit carrier. -/
theorem globalOriginalFairNativeStageSequence_source_cofinal
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (hCoverage : ∀ x : GlobalOriginalFairNativeVertex F hInput,
      ∃ (i : ℕ) (p : GlobalOriginalFairNativeVertex F hInput ×
        GlobalOriginalFairNativeVertex F hInput),
        p ∈ schedule i ∧ p.1 = x)
    (x : GlobalOriginalFairNativeVertex F hInput) :
    ∃ (i : ℕ)
      (a : (globalOriginalActualFairTraceChain F hInput
        (globalOriginalFairNativeStageSequence F hInput initial schedule i).1).Carrier),
      (globalOriginalTraceFullLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        (globalOriginalFairNativeStageSequence F hInput initial schedule i).1) a =
        x := by
  obtain ⟨i, p, hp, hpx⟩ := hCoverage x
  obtain ⟨a, b, ha, hb⟩ :=
    globalOriginalFairNativeStageSequence_request_persists
      F hInput initial schedule i (i + 1) (le_refl _) p hp
  exact ⟨i + 1, a, ha.trans hpx⟩

/-- If every limit vertex occurs as the right coordinate of
some request, the selected FULL stage maps collectively have
SURJECTIVE union of images. This is the range counterpart to
source cofinality; it does not yet build the limit map. -/
theorem globalOriginalFairNativeStageSequence_target_cofinal
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (hCoverage : ∀ y : GlobalOriginalFairNativeVertex F hInput,
      ∃ (i : ℕ) (p : GlobalOriginalFairNativeVertex F hInput ×
        GlobalOriginalFairNativeVertex F hInput),
        p ∈ schedule i ∧ p.2 = y)
    (y : GlobalOriginalFairNativeVertex F hInput) :
    ∃ (i : ℕ)
      (b : (globalOriginalActualFairTraceChain F hInput
        (globalOriginalFairNativeStageSequence F hInput initial schedule i).1).Carrier),
      (globalOriginalFairNativeStageSequence F hInput initial schedule i).2 b =
        y := by
  obtain ⟨i, p, hp, hpy⟩ := hCoverage y
  obtain ⟨a, b, ha, hb⟩ :=
    globalOriginalFairNativeStageSequence_request_persists
      F hInput initial schedule i (i + 1) (le_refl _) p hp
  exact ⟨i + 1, b, hb.trans hpy⟩

end AllThoseRamseyClasses.Lifts
