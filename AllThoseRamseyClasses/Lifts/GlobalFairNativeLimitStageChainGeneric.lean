import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStageSequenceCoherence

/-!
# Track F: generic coherence of any certified FULL native stage chain

The chosen finite-stage sequence has a special construction
using Classical.choose, but coherence depends on NONE of those
choice details. It follows only from the one-step FULL extension
certificate and the exact all-stage composition law.

Extract that argument as an API for an ARBITRARY sequence
s : ℕ → Σ n, X_n ↪ M carrying, for each step, the native FULL
StageStepSpec. This is needed for the stricter cofinal-index
recursion: it has a different choice procedure but satisfies
the SAME certificate. The generic API avoids re-proving the
directed transition/coherence algebra for every constructor.

A scheduled source/target vertex pair persists to every later
stage, using the canonical FULL cocone for the source image
and the FULL stage-map compatibility for the target image.

No direct-limit lift or automorphism is introduced here. The
original finite Fraïssé input is still explicit, with unresolved
unrestricted reducible-source shadow-avoidance/Claim 2.
The numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any sequence of FULL finite-stage embeddings that
satisfies the verified one-step stage-extension certificate
is coherent across ALL indices i≤j. No assumptions about
how the individual successor witnesses were chosen. -/
theorem globalOriginalFairNativeStageChain_coherent_of_stepSpec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (seq : ℕ → GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (hStep : ∀ n : ℕ,
      GlobalOriginalFairNativeStageStepSpec
        F hInput (seq n) (seq (n + 1)) (schedule n))
    (i j : ℕ) (hij : i ≤ j) :
    ∃ hlevels : (seq i).1 ≤ (seq j).1,
      ∀ a : (globalOriginalActualFairTraceChain F hInput (seq i).1).Carrier,
        (seq j).2
          ((globalOriginalFiniteTraceChainLE F hInput
            (globalOriginalRepresentativePrefix F hInput)
            (globalOriginalExtensionDiagramPrefix F hInput)
            (seq i).1 (seq j).1 hlevels) a) =
        (seq i).2 a := by
  classical
  induction j, hij using Nat.le_induction with
  | base =>
      refine ⟨le_refl _, ?_⟩
      intro a
      rw [globalOriginalFiniteTraceChainLE_self]
      rfl
  | succ j hj ih =>
      obtain ⟨hij', hcompat⟩ := ih
      obtain ⟨hstep, _, hstepCompat⟩ := hStep j
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

/-- The two coverage witnesses for a requested pair
persist along ANY later selected stage of an arbitrary
certified FULL sequence. The proof is independent of the
witness choice algorithm. -/
theorem globalOriginalFairNativeStageChain_request_persists_of_stepSpec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (seq : ℕ → GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (hStep : ∀ n : ℕ,
      GlobalOriginalFairNativeStageStepSpec
        F hInput (seq n) (seq (n + 1)) (schedule n))
    (i j : ℕ) (hij : i + 1 ≤ j)
    (p : GlobalOriginalFairNativeVertex F hInput ×
      GlobalOriginalFairNativeVertex F hInput)
    (hp : p ∈ schedule i) :
    ∃ (a b : (globalOriginalActualFairTraceChain F hInput (seq j).1).Carrier),
      (globalOriginalTraceFullLimitIncl F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        (seq j).1) a = p.1 ∧
      (seq j).2 b = p.2 := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  obtain ⟨hstep, hCoverStep, _⟩ := hStep i
  obtain ⟨ai, bi, hai, hbi⟩ := hCoverStep p hp
  obtain ⟨hlater, hlaterCompat⟩ :=
    globalOriginalFairNativeStageChain_coherent_of_stepSpec
      F hInput seq schedule hStep (i + 1) j hij
  let e := globalOriginalFiniteTraceChainLE F hInput
    representatives diagrams (seq (i + 1)).1 (seq j).1 hlater
  refine ⟨e ai, e bi, ?_, ?_⟩
  · have hcocone :=
      globalOriginalTraceFullLimitIncl_comp F hInput
        representatives diagrams (seq (i + 1)).1 (seq j).1 hlater
    have hpt :=
      congrArg
        (fun v : Structure.Embedding
          (globalOriginalActualFairTraceChain F hInput (seq (i + 1)).1).model
          (globalOriginalActualFairNativeLimit F hInput) => v ai)
        hcocone
    exact hpt.trans hai
  · exact (hlaterCompat bi).trans hbi

end AllThoseRamseyClasses.Lifts
