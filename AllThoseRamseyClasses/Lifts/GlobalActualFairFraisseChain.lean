import AllThoseRamseyClasses.Lifts.GlobalScheduledFiniteFraisseChain
import AllThoseRamseyClasses.Lifts.GlobalFairFiniteFraisseSchedules

/-!
# Track F: instantiate the real finite Fraïssé chain with FAIR schedules

The existing finite original maximal-trace chain accepts any
finite list of age representatives and finite full extension
diagrams at each stage. The separately verified prefix schedules
visit each actual representative and each genuine extension
diagram at ALL sufficiently late stages.

This module chooses those fair prefix lists in the REAL
constructed finite chain and proves the two eventual invariants:

1. Every actual labelled finite age representative has a FULL
   embedding into every sufficiently late successor stage.
2. Every prescribed finite FULL extension diagram A ↪ B is
   realized at every sufficiently late successor stage over
   EVERY full embedding of A into the CURRENT finite stage.

The latter quantification is essential: diagrams introduced
earlier are rescheduled after new root copies arise.

No first-order direct limit, image-closedness, age equality,
or ultrahomogeneity is inferred from this finite scheduling
alone. The finite-age input still retains the original
shadow-avoidance hypothesis for unrestricted reducible
forbidden source families.

The 2019 numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A concrete finite maximal-trace Fraïssé chain using the
already verified fair countable prefixes at EVERY stage. -/
noncomputable def globalOriginalActualFairTraceChain
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    ℕ → GlobalOriginalFiniteTraceStage F :=
  globalOriginalFiniteTraceChain F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput)

/-- The actual full functional embedding of each finite stage
of the fair chain into the following stage. -/
noncomputable def globalOriginalActualFairTraceChainStep
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (n : ℕ) :
    Structure.Embedding
      (globalOriginalActualFairTraceChain F hInput n).model
      (globalOriginalActualFairTraceChain F hInput (n + 1)).model :=
  globalOriginalFiniteTraceChainStep F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput) n

/-- Every actual finite age representative has a FULL copy
in every sufficiently late successor stage. This is
cofinality of the real fair finite chain, not a mere
abstract countability assertion. -/
theorem globalOriginalActualFairTraceChain_eventually_contains
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (P : GlobalOriginalFiniteTraceRepresentatives F) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (_e : Structure.Embedding P.2.1
        (globalOriginalActualFairTraceChain F hInput (n + 1)).model),
        True := by
  obtain ⟨N, hN⟩ :=
    globalOriginalRepresentativePrefix_eventually_mem F hInput P
  refine ⟨N, ?_⟩
  intro n hn
  exact (globalOriginalFiniteTraceChainStep_spec
    F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput) n).1
    P (hN n hn)

/-- Each actual full extension diagram A ↪ B is satisfied
at every sufficiently late successor stage over ALL copies
A ↪ X_n of its source in the current stage X_n.

The finite-stage maps and extension maps preserve all old
set-valued function fibres and reflect all added relations.
This is precisely the recurrent scheduling invariant
required before a limit extension-property proof. -/
theorem globalOriginalActualFairTraceChain_eventually_extends
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (d : GlobalOriginalFiniteTraceDiagram F) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ f : Structure.Embedding d.1.2.1
          (globalOriginalActualFairTraceChain F hInput n).model,
        ∃ jB : Structure.Embedding d.2.1.2.1
          (globalOriginalActualFairTraceChain F hInput (n + 1)).model,
          ∀ a,
            jB (d.2.2 a) =
              globalOriginalActualFairTraceChainStep
                F hInput n (f a) := by
  obtain ⟨N, hN⟩ :=
    globalOriginalExtensionDiagramPrefix_eventually_mem F hInput d
  refine ⟨N, ?_⟩
  intro n hn f
  exact (globalOriginalFiniteTraceChainStep_spec
    F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput) n).2
    d (hN n hn) f

end AllThoseRamseyClasses.Lifts
