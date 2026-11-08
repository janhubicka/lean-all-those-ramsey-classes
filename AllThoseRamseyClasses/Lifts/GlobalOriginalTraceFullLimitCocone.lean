import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceFullLimitInclusions

/-!
# Track F: the FULL native stage inclusions form a genuine cocone

The canonical first-order direct-limit embeddings satisfy
`u_n ∘ e_{m,n} = u_m` for every full finite transition
`e_{m,n}:X_m↪X_n`. The closed-image argument (proposed
in #919) and the full-embedding reconstruction (#930)
give genuine FULL native set-valued-functional embeddings
with exactly these underlying vertex maps.

This module records their cocone equation as EQUALITY OF
FULL NATIVE STRUCTURAL EMBEDDINGS, not just an equation
of relational graph maps. It is the exact compatibility
needed when transporting finite-stage extension witnesses
into the decoded native direct limit.

There is no assertion that first-order graph embeddings
are full without function-output closure. No arbitrary
weak image quotient, one-point completion, or hidden
shadow-avoidance theorem is introduced.

The numbered 2019 manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The canonical FULL functional embedding of stage m into
the actual native limit is exactly the composite of its
FULL transition to stage n and the canonical FULL inclusion
of stage n, for all m≤n. This is an equality of genuine
`Structure.Embedding` values, hence includes all the old
partial/multivalued function-fibre preservation, not merely
agreement on positive relation tuples. -/
theorem globalOriginalTraceFullLimitIncl_comp
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (hmn : m ≤ n) :
    (globalOriginalTraceFullLimitIncl
      F hInput representatives diagrams n).comp
        (globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams m n hmn) =
    globalOriginalTraceFullLimitIncl
      F hInput representatives diagrams m := by
  apply Structure.Embedding.ext
  intro x
  change
    (globalOriginalTraceFullLimitIncl
      F hInput representatives diagrams n)
      ((globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n hmn) x) =
    (globalOriginalTraceFullLimitIncl
      F hInput representatives diagrams m) x
  rw [globalOriginalTraceFullLimitIncl_apply,
      globalOriginalTraceFullLimitIncl_apply]
  exact globalOriginalTraceFirstOrderLimitIncl_comp
    F hInput representatives diagrams m n hmn x

end AllThoseRamseyClasses.Lifts
