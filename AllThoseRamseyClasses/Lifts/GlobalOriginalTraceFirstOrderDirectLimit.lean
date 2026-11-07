import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceDirectLimitCarrier
import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderEmbeddingBridge
import Mathlib.ModelTheory.DirectLimit

/-!
# Track F: a genuine first-order direct limit of complete function graphs

The original maximal-trace finite chain has fully faithful
set-valued functional embeddings at each stage. Its all-stage
maps are coherent (Track F #857). The closed functional
graph/first-order bridge is already certified (#848).

This module uses the ACTUAL Mathlib first-order directed-limit
construction to build an infinite relational graph model,
not an assumed existence witness. Native relation symbols and
each complete set-valued function fibre are encoded by the
already proved pure first-order graph language (#837).

The canonical first-order stage embeddings are genuine
structure embeddings for ALL graph relation symbols.
The quotient first-order structure is supplied by Mathlib's
verified DirectLimit construction, not by an unverified new
model-theoretic postulate.

**Boundary:** A canonical first-order graph embedding is not
automatically a FULL native functional embedding. It must
also have function-closed image (no new function outputs
over an old image tuple). This step remains to be proved
for the infinite limit, using finite-stage complete-fibre
stability (#901). This module does NOT claim that its
first-order age equals the original maximal-trace age, nor
ultrahomogeneity, unrestricted shadow avoidance or Ramsey.

The original numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual functionless FIRST-ORDER language encoding every
old and new global maximal-trace relation, plus the graph
of each original set-valued partial function. -/
abbrev GlobalOriginalTraceFirstOrderLanguage
    (F : ∀ {W : Type}, Structure L W → Prop) :=
  firstOrderRelGraphLanguage (globalFunctionalPieceLanguage F).graph

/-- The complete function-graph first-order structure on the
ACTUAL finite age member at stage n. -/
noncomputable instance globalOriginalTraceStageFirstOrderModel
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    (GlobalOriginalTraceFirstOrderLanguage F).Structure
      (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n) :=
  firstOrderNativeGraphStructure
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).model

/-- Every full functional transition also gives a genuine
FIRST-ORDER embedding of the exact relationalized function
graphs, including the old and newly added relation symbols. -/
noncomputable def globalOriginalTraceStageFirstOrderMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n) :
    @FirstOrder.Language.Embedding
      (GlobalOriginalTraceFirstOrderLanguage F)
      (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams m)
      (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n)
      (globalOriginalTraceStageFirstOrderModel
        F hInput representatives diagrams m)
      (globalOriginalTraceStageFirstOrderModel
        F hInput representatives diagrams n) :=
  firstOrderNativeGraphEmbedding
    (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams m n h)

/-- The original chain's first-order graphs form a GENUINE
coherent directed system. The equations follow from the
full functional transition identity and composition laws,
not from a one-directional weak graph map. -/
instance globalOriginalTraceStageFirstOrder_directedSystem
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :
    DirectedSystem
      (fun n : ℕ => GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n)
      (fun m n h => globalOriginalTraceStageFirstOrderMap
        F hInput representatives diagrams m n h) where
  map_self := by
    intro i x
    change (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams i i (le_refl i)) x = x
    rw [globalOriginalFiniteTraceChainLE_self]
    rfl
  map_map := by
    intro k j i hij hjk x
    change
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams j k hjk)
        ((globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams i j hij) x) =
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams i k
        (le_trans hij hjk)) x
    exact congrArg
      (fun e : Structure.Embedding
        (globalOriginalFiniteTraceChain
          F hInput representatives diagrams i).model
        (globalOriginalFiniteTraceChain
          F hInput representatives diagrams k).model => e x)
      (globalOriginalFiniteTraceChainLE_comp
        F hInput representatives diagrams i j k hij hjk)

/-- The ACTUAL Mathlib first-order directed-limit quotient
of the complete function graphs of all finite age stages.
The standard Mathlib structure is installed below. -/
abbrev GlobalOriginalTraceFirstOrderDirectLimit
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :=
  FirstOrder.Language.DirectLimit
    (fun n : ℕ => GlobalOriginalTraceStageVertex
      F hInput representatives diagrams n)
    (fun m n h => globalOriginalTraceStageFirstOrderMap
      F hInput representatives diagrams m n h)

/-- The limit is a genuine first-order relational structure,
constructed by Mathlib's quotiented directed limit of the
verified stage embeddings. No total function symbol is added. -/
noncomputable instance globalOriginalTraceFirstOrderLimitModel
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :
    (GlobalOriginalTraceFirstOrderLanguage F).Structure
      (GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams) :=
  inferInstance

/-- Actual canonical FIRST-ORDER structure embedding of each
finite stage's complete function graph into the directed limit.
This map reflects every first-order graph relation; a separate
closed-image proof is necessary for full native function fibres. -/
noncomputable def globalOriginalTraceFirstOrderLimitIncl
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    @FirstOrder.Language.Embedding
      (GlobalOriginalTraceFirstOrderLanguage F)
      (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n)
      (GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams)
      (globalOriginalTraceStageFirstOrderModel
        F hInput representatives diagrams n)
      (globalOriginalTraceFirstOrderLimitModel
        F hInput representatives diagrams) :=
  FirstOrder.Language.DirectLimit.of
    (GlobalOriginalTraceFirstOrderLanguage F) ℕ
    (fun i : ℕ => GlobalOriginalTraceStageVertex
      F hInput representatives diagrams i)
    (fun i j h => globalOriginalTraceStageFirstOrderMap
      F hInput representatives diagrams i j h) n

end AllThoseRamseyClasses.Lifts
