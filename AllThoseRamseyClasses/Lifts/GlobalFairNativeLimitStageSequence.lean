import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteListStage

/-!
# Track F: proof-carrying countable sequence of FULL fair stages

The verified local two-sided FULL stage extension can be iterated
over an arbitrary prescribed sequence of FINITE lists of
source/target vertex requests in the *actual* decoded native fair
limit. Rather than postulating an infinite automorphism, we build
an explicit dependent sequence of genuine finite-stage FULL
embeddings with a certificate at EVERY successor stage.

A state consists of its original fair chain stage index n and
a genuine FULL embedding of that stage into the decoded limit.
A certified step records the actual monotone stage transition,
full map coherence, and simultaneous source/target coverage of
its finite list of requests.

The recursion uses Classical.choose on the already verified
finite-list existence theorem; it adds no axioms about global
amalgamation, homogeneity, or maps of the quotient. This is a
formalization of the *sequence*, not yet its directed-limit lift
or the final FULL native automorphism.

All statements remain conditional on GlobalOriginalFiniteFraisseInput,
including the unresolved general reducible-source Claim 2/shadow-
avoidance obligation. Frozen numbered ramsey.tex untouched.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Carrier type of the already constructed actual native fair limit. -/
abbrev GlobalOriginalFairNativeVertex
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :=
  GlobalOriginalTraceFirstOrderDirectLimit F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput)

/-- A list of source/target pairs to be met at one stage of
the alternating back-and-forth construction. -/
abbrev GlobalOriginalFairNativeRequests
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :=
  List (GlobalOriginalFairNativeVertex F hInput ×
    GlobalOriginalFairNativeVertex F hInput)

/-- A finite stage and an actual FULL structural embedding of
that entire stage into the decoded native fair limit. -/
abbrev GlobalOriginalFairNativeStageState
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :=
  Σ n : ℕ, Structure.Embedding
    (globalOriginalActualFairTraceChain F hInput n).model
    (globalOriginalActualFairNativeLimit F hInput)

/-- A later state genuinely extends an earlier FULL stage state,
and meets ALL prescribed finite source/target requests. -/
def GlobalOriginalFairNativeStageStepSpec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (s t : GlobalOriginalFairNativeStageState F hInput)
    (requests : GlobalOriginalFairNativeRequests F hInput) : Prop :=
  ∃ hst : s.1 ≤ t.1,
    (∀ p ∈ requests,
      ∃ (a b : (globalOriginalActualFairTraceChain F hInput t.1).Carrier),
        (globalOriginalTraceFullLimitIncl F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput) t.1) a = p.1 ∧
        t.2 b = p.2) ∧
    ∀ a : (globalOriginalActualFairTraceChain F hInput s.1).Carrier,
      t.2 ((globalOriginalFiniteTraceChainLE F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)
        s.1 t.1 hst) a) = s.2 a

/-- Every stage state admits a later stage satisfying any
finite batch of source and target requests. The witness is
fully certified and uses only genuine FULL stage maps. -/
theorem globalOriginalFairNativeStageStep_exists
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (s : GlobalOriginalFairNativeStageState F hInput)
    (requests : GlobalOriginalFairNativeRequests F hInput) :
    ∃ t : GlobalOriginalFairNativeStageState F hInput,
      GlobalOriginalFairNativeStageStepSpec F hInput s t requests := by
  obtain ⟨n, hsn, g, hcover, hcompat⟩ :=
    globalOriginalActualFairNativeLimit_finiteList_twoSided_stage
      F hInput requests s.1 s.2
  exact ⟨⟨n, g⟩, hsn, hcover, hcompat⟩

/-- A noncomputably chosen, CERTIFIED next stage, with
the full monotonicity/coverage/coherence proof attached.
The only choice is of a witness to a proved finite-list
existence theorem. -/
noncomputable def globalOriginalFairNativeStageStep
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (s : GlobalOriginalFairNativeStageState F hInput)
    (requests : GlobalOriginalFairNativeRequests F hInput) :
    {t : GlobalOriginalFairNativeStageState F hInput //
      GlobalOriginalFairNativeStageStepSpec F hInput s t requests} :=
  ⟨Classical.choose
      (globalOriginalFairNativeStageStep_exists F hInput s requests),
    Classical.choose_spec
      (globalOriginalFairNativeStageStep_exists F hInput s requests)⟩

/-- A real recursively defined chain of FULL finite-stage
embeddings, parameterized by a schedule of finite batches
of limit-vertex source/target requests. No unsupported
infinite Fraïssé map has been introduced. -/
noncomputable def globalOriginalFairNativeStageSequence
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput) :
    ℕ → GlobalOriginalFairNativeStageState F hInput :=
  Nat.rec initial (fun n s =>
    (globalOriginalFairNativeStageStep F hInput s (schedule n)).val)

/-- The recursively chosen sequence begins with the given
genuine FULL initial stage embedding. -/
theorem globalOriginalFairNativeStageSequence_zero
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput) :
    globalOriginalFairNativeStageSequence F hInput initial schedule 0 =
      initial := by
  rfl

/-- Successor stages are exactly the certified chosen finite-list
extensions of the previous FULL stage, with no arbitrary
reindexing or changed vertex maps. -/
theorem globalOriginalFairNativeStageSequence_succ
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (n : ℕ) :
    globalOriginalFairNativeStageSequence F hInput initial schedule
      (n + 1) =
      (globalOriginalFairNativeStageStep F hInput
        (globalOriginalFairNativeStageSequence F hInput initial schedule n)
        (schedule n)).val := by
  rfl

/-- Every successor stage in the actual recursive sequence
satisfies the full finite-list source/target coverage and
preserves the previous FULL map along the genuine transition. -/
theorem globalOriginalFairNativeStageSequence_stepSpec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (n : ℕ) :
    GlobalOriginalFairNativeStageStepSpec F hInput
      (globalOriginalFairNativeStageSequence F hInput initial schedule n)
      (globalOriginalFairNativeStageSequence F hInput initial schedule (n + 1))
      (schedule n) := by
  rw [globalOriginalFairNativeStageSequence_succ]
  exact (globalOriginalFairNativeStageStep F hInput
    (globalOriginalFairNativeStageSequence F hInput initial schedule n)
    (schedule n)).property

end AllThoseRamseyClasses.Lifts
