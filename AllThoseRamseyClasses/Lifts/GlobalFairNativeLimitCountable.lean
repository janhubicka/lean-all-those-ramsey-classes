import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitStageSequence

/-!
# Track F: countability of the actual first-order and native fair limits

The actual Mathlib directed-limit carrier is a quotient of the
dependent sum of its genuine finite stages. This is a proof of
countability for the SAME first-order quotient used by the
certified full stage embeddings and the native decoded model.
It is not an independent or hypothetical Fraïssé limit.

No assumption about original shadow avoidance is hidden:
the existing `GlobalOriginalFiniteFraisseInput F` parameter
remains explicit. The 2019 numbered manuscript is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual Mathlib FIRST-ORDER graph directed limit has a
countable carrier, because all genuine original chain stages
are finite. Its first-order structure is not replaced by the
unrelated vertex-only direct limit. -/
theorem globalOriginalTraceFirstOrderDirectLimit_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :
    Countable
      (GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams) := by
  classical
  letI (n : ℕ) :
      Finite (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n) :=
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).member.1
  infer_instance

/-- The ACTUAL native fair limit has a countable underlying
vertex type; its carrier is definitionally the quotient of
the actual original first-order complete-graph system. -/
theorem globalOriginalFairNativeVertex_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    Countable (GlobalOriginalFairNativeVertex F hInput) :=
  globalOriginalTraceFirstOrderDirectLimit_countable
    F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput)

end AllThoseRamseyClasses.Lifts
