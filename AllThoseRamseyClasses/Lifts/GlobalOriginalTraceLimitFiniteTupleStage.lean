import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFirstOrderDirectLimit
import Mathlib.ModelTheory.DirectLimit

/-!
# Track F: every finite collection of vertices of the genuine first-order limit has a common stage

Mathlib's ACTUAL first-order directed limit is the quotient of
stage-tagged vertices of the finite original maximal-trace chain.
Its `exists_quotient_mk'_sigma_mk'_eq` theorem ensures that every
FINITE family of limit vertices can be represented simultaneously
at ONE finite stage, not merely separately at unrelated stages.

This lemma is indispensable for the reverse age inclusion:
a finite FULL substructure of the decoded limit must factor
through some genuine finite maximal-trace age stage.
The factorization must later be shown FULL for all complete
partial-function fibres; that is a separate proof, using
the full stage-limit embeddings proposed in #930.

No first-order Fraïssé existence axiom is inserted.
The original finite-age input is still conditional on the
unrestricted reducible-source shadow-avoidance obligation.
The frozen numbered ramsey.tex is untouched.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Every finite family of vertices of the genuine first-order
direct limit arises at a SINGLE finite original maximal-trace
age stage, with exact equality under the canonical inclusion.

This is purely a quotient-carrier assertion: a finite set
of arbitrary vertices is not thereby asserted to be
function-closed, nor is the original age already recovered. -/
theorem globalOriginalTraceFirstOrderLimit_finiteTuple_commonStage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    {α : Type v} [Finite α]
    (xs : α → GlobalOriginalTraceFirstOrderDirectLimit
      F hInput representatives diagrams) :
    ∃ (n : ℕ)
      (ys : α → GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n),
      ∀ a : α,
        globalOriginalTraceFirstOrderLimitIncl
          F hInput representatives diagrams n (ys a) = xs a := by
  classical
  obtain ⟨n, ys, hEq⟩ :=
    FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq
      (L := GlobalOriginalTraceFirstOrderLanguage F)
      (G := fun n : ℕ => GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n)
      (f := fun i j h => globalOriginalTraceStageFirstOrderMap
        F hInput representatives diagrams i j h)
      xs
  refine ⟨n, ys, ?_⟩
  intro a
  have ha := congrFun hEq a
  have hb :
      xs a = globalOriginalTraceFirstOrderLimitIncl
        F hInput representatives diagrams n (ys a) := by
    simpa only [globalOriginalTraceFirstOrderLimitIncl,
      FirstOrder.Language.DirectLimit.of_apply] using ha
  exact hb.symm

end AllThoseRamseyClasses.Lifts
