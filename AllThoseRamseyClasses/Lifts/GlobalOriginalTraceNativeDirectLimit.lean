import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFirstOrderDirectLimit
import AllThoseRamseyClasses.Lifts.GlobalFraisseFirstOrderGraphDecode

/-!
# Track F: a genuine native functional structure on the first-order limit

The finite original maximal-trace age supplies an actual chain of
FULL structural embeddings. The first-order graph bridge interprets
old relations and each complete set-valued function fibre as
first-order relations (functions of arity n use relations of arity n+1).
The first-order direct-limit module constructs the corresponding
relational quotient model using Mathlib's verified construction.

Here we DECODE that actual first-order limit as a genuine
StructuralRamsey.Structure with complete sets of outputs for
every native (partial, possibly multivalued) function symbol.

This is a real native functional STRUCTURE on the limit carrier,
not an assumed Fraisse-limit existence theorem. Its old relation
tables and whole function-value fibres are characterized exactly
by the first-order graph relations, including nullaries.

The CRUCIAL next theorem is still missing: each canonical finite-stage
embedding into this decoded native limit must have function-CLOSED
image. Only then can the first-order stage embedding be promoted to
a FULL native embedding using the verified #848 bridge. No age equality,
finite extension property, homogeneity or unrestricted shadow-free
amalgamation is claimed by this module.

The numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u
variable {L : Language.{u}}

/-- The ACTUAL decoded native set-valued functional structure
on Mathlib's first-order directed-limit quotient of the
complete graph models of the finite original maximal traces.
This definition does NOT assume stage embeddings are closed
in the limit; that property remains to be proven. -/
noncomputable def globalOriginalTraceNativeDirectLimitModel
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :
    Structure (globalFunctionalPieceLanguage F)
      (GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams) :=
  firstOrderNativeGraphDecode
    (globalOriginalTraceFirstOrderLimitModel
      F hInput representatives diagrams)

/-- Each relation of the decoded limit, including all added
piece predicates, holds EXACTLY when its corresponding
first-order graph relation holds on that same tuple.
No finite-stage semantics is guessed or weakened. -/
theorem globalOriginalTraceNativeDirectLimit_rel_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (S : (globalFunctionalPieceLanguage F).RelSymbol)
    (xs : Fin ((globalFunctionalPieceLanguage F).relArity S) →
      GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams) :
    (globalOriginalTraceNativeDirectLimitModel
      F hInput representatives diagrams).rel S xs ↔
    (globalOriginalTraceFirstOrderLimitModel
      F hInput representatives diagrams).RelMap
        (⟨Sum.inl S, rfl⟩ :
          (GlobalOriginalTraceFirstOrderLanguage F).Relations
            ((globalFunctionalPieceLanguage F).relArity S)) xs := by
  rfl

/-- Every output of a decoded native function over an arbitrary
tuple of limit vertices is EXACTLY one first-order graph
relation incidence with an additional output coordinate.

There is no assumed totality or uniqueness of the outputs;
nullary functions have one input tuple and a potentially
empty or multi-element output fibre. -/
theorem globalOriginalTraceNativeDirectLimit_func_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (S : (globalFunctionalPieceLanguage F).FuncSymbol)
    (xs : Fin ((globalFunctionalPieceLanguage F).funcArity S) →
      GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams)
    (y : GlobalOriginalTraceFirstOrderDirectLimit
      F hInput representatives diagrams) :
    y ∈ (globalOriginalTraceNativeDirectLimitModel
      F hInput representatives diagrams).func S xs ↔
    (globalOriginalTraceFirstOrderLimitModel
      F hInput representatives diagrams).RelMap
        (⟨Sum.inr S, rfl⟩ :
          (GlobalOriginalTraceFirstOrderLanguage F).Relations
            ((globalFunctionalPieceLanguage F).funcArity S + 1))
        (Structure.funcTuple xs y) := by
  rfl

/-- The ENTIRE output fibre of each decoded function is
exactly the set of vertices satisfying its graph relation,
including all negative and undefined incidences. -/
theorem globalOriginalTraceNativeDirectLimit_wholeFibre
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (S : (globalFunctionalPieceLanguage F).FuncSymbol)
    (xs : Fin ((globalFunctionalPieceLanguage F).funcArity S) →
      GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams) :
    (globalOriginalTraceNativeDirectLimitModel
      F hInput representatives diagrams).func S xs =
      {y | (globalOriginalTraceFirstOrderLimitModel
        F hInput representatives diagrams).RelMap
          (⟨Sum.inr S, rfl⟩ :
            (GlobalOriginalTraceFirstOrderLanguage F).Relations
              ((globalFunctionalPieceLanguage F).funcArity S + 1))
          (Structure.funcTuple xs y)} := by
  ext y
  exact globalOriginalTraceNativeDirectLimit_func_iff
    F hInput representatives diagrams S xs y

end AllThoseRamseyClasses.Lifts
