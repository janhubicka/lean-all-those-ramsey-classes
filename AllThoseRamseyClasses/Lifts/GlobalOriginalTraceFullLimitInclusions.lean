import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceDirectLimitClosed
import PartiteConstruction.Functional.Closed

/-!
# Track F: genuine FULL native embeddings of finite stages into the limit

Mathlib's verified first-order directed limit of the complete
function graph has canonical first-order relational embeddings.
The original finite chain already has genuine full set-valued
functional embeddings between all finite stages.

The preceding closed-image theorem (Track F #919) proves that
no new function value over an old stage input tuple appears in
the infinite graph limit. This is exactly the missing condition
for converting a relational first-order stage embedding into
a FULL native-functional structural embedding.

Here we use the already verified
`Structure.Embedding.ofClosedGraphTarget` interface of
PartiteConstruction.Functional.Closed, obtaining, for every
finite original root-injective maximal-trace stage X_n, an
ACTUAL FULL embedding X_n ↪ M into the decoded direct-limit
native structure. It reflects every old and added relation
and preserves the ENTIRE set-valued function output fibre.

Neither an independent existence axiom for a Fraïssé limit
nor a weak EHN image quotient is introduced. This result is
still conditional on the finite Fraïssé-age input, which for
general reducible sources retains the open original
shadow-avoidance hypothesis. Finite age equality, extension
property, back-and-forth and Ramsey remain separate.

The 2019 numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A canonical full native functional embedding of an
actual finite original maximal-trace stage into the
directed-limit decoded native structure. Its vertex
function is exactly Mathlib's original first-order
direct-limit inclusion, with no additional completion
or generated hull. -/
noncomputable def globalOriginalTraceFullLimitIncl
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    Structure.Embedding
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams n).model
      (globalOriginalTraceNativeDirectLimitModel
        F hInput representatives diagrams) := by
  let e := globalOriginalTraceFirstOrderLimitIncl
    F hInput representatives diagrams n
  let R :
      RelStructure (globalFunctionalPieceLanguage F).graph
        (GlobalOriginalTraceFirstOrderDirectLimit
          F hInput representatives diagrams) :=
    firstOrderRelGraphDecode
      (globalOriginalTraceFirstOrderLimitModel
        F hInput representatives diagrams)
  let c : RelStructure.ClosedEmbedding
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams n).model.graph R := {
    -- The limit's first-order model is only propositionally the graph
    -- encoding of its relational decoder, not definitionally identical.
    -- Build the relational embedding against that decoder directly.
    toEmbedding := {
      toFun := e
      injective := e.injective
      map_rel_iff := by
        intro S xs
        change
          (globalOriginalTraceFirstOrderLimitModel
            F hInput representatives diagrams).RelMap
              (⟨S, rfl⟩ :
                (GlobalOriginalTraceFirstOrderLanguage F).Relations
                  ((globalFunctionalPieceLanguage F).graph.arity S))
              (e ∘ xs) ↔
          (globalOriginalTraceStageFirstOrderModel
            F hInput representatives diagrams n).RelMap
              (⟨S, rfl⟩ :
                (GlobalOriginalTraceFirstOrderLanguage F).Relations
                  ((globalFunctionalPieceLanguage F).graph.arity S))
              xs
        exact e.map_rel _ xs
    }
    closed := by
      intro S xs y hy
      have hyNative :
          y ∈ (globalOriginalTraceNativeDirectLimitModel
            F hInput representatives diagrams).func S
            (e ∘ xs) := hy
      obtain ⟨z, hz, hzy⟩ :=
        (globalOriginalTraceFirstOrderLimitIncl_closedMap
          F hInput representatives diagrams n) S xs y hyNative
      exact ⟨z, (Structure.graph_func_snoc
        (globalOriginalFiniteTraceChain
          F hInput representatives diagrams n).model
        S xs z).mpr hz, hzy⟩
  }
  exact Structure.Embedding.ofClosedGraphTarget c

/-- The full native limit inclusion retains the exact
underlying vertex map of Mathlib's canonical first-order
graph inclusion. This rules out hidden vertex quotients
or further closure operations in the conversion. -/
theorem globalOriginalTraceFullLimitIncl_apply
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ)
    (x : (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).Carrier) :
    globalOriginalTraceFullLimitIncl
      F hInput representatives diagrams n x =
    globalOriginalTraceFirstOrderLimitIncl
      F hInput representatives diagrams n x := by
  rfl

end AllThoseRamseyClasses.Lifts
