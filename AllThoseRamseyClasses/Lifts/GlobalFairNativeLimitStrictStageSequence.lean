import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStageSequence
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStrictFiniteListStage

/-!
# Track F: countable FULL stage recursion with guaranteed cofinal indices

The general proof-carrying stage sequence records successive
FULL extensions, but its chosen stage indices need not increase:
one could keep satisfying all finite requests at a single stage.

Here we make the crucial refinement for the actual directed-limit
construction. At every round, apply the verified STRICT finite-
batch extension (#1025) instead of the weaker finite-batch
existence theorem. Each chosen stage has a strictly greater
index than the previous one. Thus the selected level m_n is
at least n for every n and is cofinal in the original ℕ-indexed
fair chain. The maps remain genuine FULL structural embeddings,
with a complete step-level coherence/coverage certificate.

This works even for an empty native limit or empty request
batch: no arbitrary default vertex, total operation, or
unjustified surjectivity assumption is introduced.

Still conditional on GlobalOriginalFiniteFraisseInput F, which
retains the unresolved general reducible-source Claim 2 /
global shadow-avoidance premise. No full limit automorphism
is claimed at this stage. Frozen 2019 manuscript unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A strict stage step satisfies the general FULL
source/target/coherence specification, AND increases the
actual original fair-chain index. -/
def GlobalOriginalFairNativeStrictStageStepSpec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (s t : GlobalOriginalFairNativeStageState F hInput)
    (requests : GlobalOriginalFairNativeRequests F hInput) : Prop :=
  GlobalOriginalFairNativeStageStepSpec F hInput s t requests ∧
    s.1 < t.1

/-- A strict next stage exists for EVERY state and finite batch,
including the empty batch, by the strict finite-list theorem. -/
theorem globalOriginalFairNativeStrictStageStep_exists
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (s : GlobalOriginalFairNativeStageState F hInput)
    (requests : GlobalOriginalFairNativeRequests F hInput) :
    ∃ t : GlobalOriginalFairNativeStageState F hInput,
      GlobalOriginalFairNativeStrictStageStepSpec
        F hInput s t requests := by
  obtain ⟨n, hsn, hstrict, g, hcover, hcompat⟩ :=
    globalOriginalActualFairNativeLimit_finiteList_strictStage
      F hInput requests s.1 s.2
  exact ⟨⟨n, g⟩, ⟨hsn, hcover, hcompat⟩, hstrict⟩

/-- The strict witness is selected noncomputably from a PROVED
existence theorem and carries its complete proof certificate. -/
noncomputable def globalOriginalFairNativeStrictStageStep
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (s : GlobalOriginalFairNativeStageState F hInput)
    (requests : GlobalOriginalFairNativeRequests F hInput) :
    {t : GlobalOriginalFairNativeStageState F hInput //
      GlobalOriginalFairNativeStrictStageStepSpec
        F hInput s t requests} :=
  ⟨Classical.choose
      (globalOriginalFairNativeStrictStageStep_exists
        F hInput s requests),
    Classical.choose_spec
      (globalOriginalFairNativeStrictStageStep_exists
        F hInput s requests)⟩

/-- An actual Nat-indexed chain of genuine FULL stage maps
whose selected finite stage indices strictly increase. -/
noncomputable def globalOriginalFairNativeStrictStageSequence
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput) :
    ℕ → GlobalOriginalFairNativeStageState F hInput :=
  Nat.rec initial (fun n s =>
    (globalOriginalFairNativeStrictStageStep F hInput s (schedule n)).val)

/-- The strict sequence really starts at its chosen FULL
initial finite-stage map. -/
theorem globalOriginalFairNativeStrictStageSequence_zero
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput) :
    globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule 0 = initial := by
  rfl

/-- Each successor is exactly the strictly later certified
FULL stage selected by the finite-batch existence theorem. -/
theorem globalOriginalFairNativeStrictStageSequence_succ
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (n : ℕ) :
    globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule (n + 1) =
      (globalOriginalFairNativeStrictStageStep F hInput
        (globalOriginalFairNativeStrictStageSequence
          F hInput initial schedule n)
        (schedule n)).val := by
  rfl

/-- At every round, source and target coverage are established
by FULL embeddings, the previous full map is preserved, and
the original fair-chain stage index grows strictly. -/
theorem globalOriginalFairNativeStrictStageSequence_stepSpec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (n : ℕ) :
    GlobalOriginalFairNativeStrictStageStepSpec F hInput
      (globalOriginalFairNativeStrictStageSequence
        F hInput initial schedule n)
      (globalOriginalFairNativeStrictStageSequence
        F hInput initial schedule (n + 1))
      (schedule n) := by
  rw [globalOriginalFairNativeStrictStageSequence_succ]
  exact (globalOriginalFairNativeStrictStageStep F hInput
    (globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule n) (schedule n)).property

/-- The chosen fair-stage index at iteration n is AT LEAST n.
In particular the selected indices are cofinal in ℕ, a property
not implied by finite vertex coverage alone. -/
theorem globalOriginalFairNativeStrictStageSequence_index_ge
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (n : ℕ) :
    n ≤ (globalOriginalFairNativeStrictStageSequence
      F hInput initial schedule n).1 := by
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      have hstrict :=
        (globalOriginalFairNativeStrictStageSequence_stepSpec
          F hInput initial schedule n).2
      exact le_trans (Nat.succ_le_succ ih) hstrict

/-- Every original finite fair-chain stage index i lies below
the selected stage index at iteration i, giving a canonical
FULL transition X_i ↪ X_(m_i) for the eventual universal lift. -/
theorem globalOriginalFairNativeStrictStageSequence_cofinal
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (initial : GlobalOriginalFairNativeStageState F hInput)
    (schedule : ℕ → GlobalOriginalFairNativeRequests F hInput)
    (i : ℕ) :
    ∃ n : ℕ,
      i ≤ (globalOriginalFairNativeStrictStageSequence
        F hInput initial schedule n).1 := by
  exact ⟨i, globalOriginalFairNativeStrictStageSequence_index_ge
    F hInput initial schedule i⟩

end AllThoseRamseyClasses.Lifts
