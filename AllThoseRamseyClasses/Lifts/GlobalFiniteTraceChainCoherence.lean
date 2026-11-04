import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainAllStages

/-!
# Track F: coherence of all-stage FULL functional embeddings

The actual nat-indexed chain is built from finite maximal-trace
age members and full successor embeddings. The previous module
defines each early-to-late transition by dependent natural
recursion and proves its identity case.

Here we verify that every pair of consecutive transitions
COMPOSES to the single direct transition. In particular the
transition maps form a genuine directed diagram of FULL
native/lifted functional embeddings: complete old set-valued
function fibres are reflected and all new piece predicates are
preserved in both directions.

This is the key input for defining a direct limit of these
structures by quotienting stage-tagged vertices. There is
still no claim of a completed infinite limit, Fraisse
ultrahomogeneity, or unrestricted shadow avoidance.

The numbered 2019 manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The chosen full embedding from stage m to stage k is
the composition of the maps m → n and n → k whenever
m ≤ n ≤ k. This uses genuine full embedding composition
and the transitivity law for the dependent Nat.leRecOn
iteration, not a weak image quotient. -/
theorem globalOriginalFiniteTraceChainLE_comp
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) :
    (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams n k hnk).comp
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n hmn) =
    globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams m k
      (le_trans hmn hnk) := by
  induction k, hnk using Nat.le_induction with
  | base =>
      apply Structure.Embedding.ext
      intro x
      simp [globalOriginalFiniteTraceChainLE, Nat.leRecOn_self]
  | succ k hnk ih =>
      calc
        (globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams n (k + 1)
          (Nat.le_succ_of_le hnk)).comp
          (globalOriginalFiniteTraceChainLE
            F hInput representatives diagrams m n hmn) =
        (globalOriginalFiniteTraceChainStep
          F hInput representatives diagrams k).comp
          ((globalOriginalFiniteTraceChainLE
            F hInput representatives diagrams n k hnk).comp
            (globalOriginalFiniteTraceChainLE
              F hInput representatives diagrams m n hmn)) := by
                apply Structure.Embedding.ext
                intro x
                simp [globalOriginalFiniteTraceChainLE, Nat.leRecOn_succ,
                  Structure.Embedding.comp_apply]
        _ = (globalOriginalFiniteTraceChainStep
          F hInput representatives diagrams k).comp
          (globalOriginalFiniteTraceChainLE
            F hInput representatives diagrams m k
            (le_trans hmn hnk)) := by rw [ih]
        _ = globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams m (k + 1)
          (le_trans hmn (Nat.le_succ_of_le hnk)) := by
                apply Structure.Embedding.ext
                intro x
                simp [globalOriginalFiniteTraceChainLE, Nat.leRecOn_succ,
                  Structure.Embedding.comp_apply]

end AllThoseRamseyClasses.Lifts
