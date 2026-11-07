import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainAllStages
import PartiteConstruction.Structure.Relationalize

/-!
# Track F: no new function outputs over old finite Fraïssé stages

Each stage of the original regular maximal-trace chain carries
complete set-valued interpretations of the old partial functions.
The transition maps are FULL functional embeddings, not merely
weak homomorphism embeddings or induced relational graph maps.

This module isolates the crucial direct-limit stability invariant:
for every old tuple x at stage m, the COMPLETE output fibre at
a later stage n, over the image of x, is EXACTLY the image of
the entire old fibre at stage m. Consequently, no genuinely
new function value over an old input tuple may arise at a
later stage. It works even for nullary symbols, repeated
input coordinates, undefined fibres, and set-valued outputs.

The corresponding closure property also holds for every
early-to-late transition. This is the exact extra invariant
needed to promote first-order graph-colimit embeddings
to FULL native-functional embeddings in the eventual limit.

All results apply to the actual root-injective global piece
lift's OLD and added symbols, conditional only on the
finite-age input that retains the unrestricted
shadow-avoidance gap. A limit model is not claimed here.
The numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every early-to-late full transition has function-closed
image: no target-stage output over an image tuple can fall
outside the image of an earlier-stage output. -/
theorem globalOriginalFiniteTraceChainLE_closedMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n) :
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams m).model.ClosedMap
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).model
    (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams m n h) := by
  exact
    (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams m n h).isHomomorphism.closedMap

/-- Exact equality of COMPLETE function-value fibres, written
as a pointwise iff: a later-stage output is present if and
only if it is the image of an earlier-stage output.

There is no restriction to positive fibres or to a single
output: the theorem handles genuine partial/set-valued
native functions and all arities, including zero. -/
theorem globalOriginalFiniteTraceChainLE_fibre_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n)
    (S : (globalFunctionalPieceLanguage F).FuncSymbol)
    (xs : Fin ((globalFunctionalPieceLanguage F).funcArity S) →
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams m).Carrier)
    (y : (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).Carrier) :
    y ∈ (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).model.func S
      ((globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n h) ∘ xs) ↔
    ∃ z, z ∈ (globalOriginalFiniteTraceChain
      F hInput representatives diagrams m).model.func S xs ∧
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n h) z = y := by
  let e := globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams m n h
  have hFibre := e.map_func S xs
  rw [← hFibre]
  rfl

/-- Relations are both preserved AND reflected at every finite
stage, including the added positive-width forbidden-piece
symbols. This is a separate requirement from closure of
the complete partial-function fibres. -/
theorem globalOriginalFiniteTraceChainLE_rel_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n)
    (S : (globalFunctionalPieceLanguage F).RelSymbol)
    (xs : Fin ((globalFunctionalPieceLanguage F).relArity S) →
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams m).Carrier) :
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).model.rel S
      ((globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n h) ∘ xs) ↔
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams m).model.rel S xs :=
  (globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams m n h).map_rel_iff S xs

end AllThoseRamseyClasses.Lifts
