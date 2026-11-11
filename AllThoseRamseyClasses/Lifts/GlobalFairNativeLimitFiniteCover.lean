import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteExtension
import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceLimitFiniteTupleStage

/-!
# Track F: finite FULL stage covers and countability of the native fair limit

Every finite family of arbitrary vertices of the ACTUAL decoded
native fair limit lies in one finite, function-closed stage image.
The carrier-cover statement uses the genuine common-stage quotient
lemma, while the fact that the stage inclusion is a FULL embedding
comes from the exact closed-image theorem, not from relational
embeddings alone.

This is needed for a subsequent countable back-and-forth argument:
adding any new vertex can be done inside a finite FULL age member,
and that member is an original maximal-trace stage.

These results assume the original finite Fraisse-age input, which
retains the global shadow-avoidance hypothesis for unrestricted
reducible forbidden sources. No ultrahomogeneity or unrestricted
Ramsey theorem is asserted here. The numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Every finite vertex family in the actual decoded native fair
limit lies in the image of one genuine FULL embedding of a finite
maximal-trace age stage. This is stronger than a first-order
relational cover because the stage embedding preserves complete
set-valued function fibres, including nullaries and empty fibres. -/
theorem globalOriginalActualFairNativeLimit_finiteFamily_fullStageCover
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {α : Type v} [Finite α]
    (xs : α → (GlobalOriginalTraceFirstOrderDirectLimit F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput))) :
    ∃ (n : ℕ)
      (ys : α → (globalOriginalActualFairTraceChain F hInput n).Carrier),
      ∀ a : α,
        (globalOriginalTraceFullLimitIncl
          F hInput
          (globalOriginalRepresentativePrefix F hInput)
          (globalOriginalExtensionDiagramPrefix F hInput)
          n) (ys a) = xs a := by
  classical
  obtain ⟨n, ys, hys⟩ :=
    globalOriginalTraceFirstOrderLimit_finiteTuple_commonStage
      F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput)
      xs
  refine ⟨n, ys, ?_⟩
  intro a
  rw [globalOriginalTraceFullLimitIncl_apply]
  exact hys a

/-- The actual FULL native fair limit is countable because its
first-order quotient carrier is a quotient of the countable
dependent union of genuinely finite chain-stage carriers. -/
theorem globalOriginalActualFairNativeLimit_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    Countable (GlobalOriginalTraceFirstOrderDirectLimit F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput)) := by
  classical
  let representatives := globalOriginalRepresentativePrefix F hInput
  let diagrams := globalOriginalExtensionDiagramPrefix F hInput
  letI (n : ℕ) :
      Finite (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n) :=
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).member.1
  -- The underlying Mathlib directed-limit quotient is countable
  -- because the dependent union of the finite stage carriers is.
  -- Explicitly register the sigma countability instance rather than
  -- relying on synthesis through the dependent first-order alias.
  haveI hSigma :
      Countable (Σ n : ℕ, GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n) := by
    infer_instance
  change Countable
    (GlobalOriginalTraceFirstOrderDirectLimit
      F hInput representatives diagrams)
  exact Quotient.countable

end AllThoseRamseyClasses.Lifts
