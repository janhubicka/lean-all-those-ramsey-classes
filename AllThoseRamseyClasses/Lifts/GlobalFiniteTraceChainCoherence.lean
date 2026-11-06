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

/-- A direct transition to stage n+1 is exactly the
full successor map after the transition to stage n. -/
theorem globalOriginalFiniteTraceChainLE_succ
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n) :
    globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams m (n + 1)
      (Nat.le_succ_of_le h) =
    (globalOriginalFiniteTraceChainStep
      F hInput representatives diagrams n).comp
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n h) := by
  unfold globalOriginalFiniteTraceChainLE
  exact Nat.leRecOn_succ h _

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
      rw [globalOriginalFiniteTraceChainLE_self]
      apply Structure.Embedding.ext
      intro x
      rfl
  | succ k hnk ih =>
      rw [globalOriginalFiniteTraceChainLE_succ
        F hInput representatives diagrams n k hnk]
      rw [globalOriginalFiniteTraceChainLE_succ
        F hInput representatives diagrams m k (le_trans hmn hnk)]
      apply Structure.Embedding.ext
      intro x
      have hpoint :=
        congrArg
          (fun e : Structure.Embedding
            (globalOriginalFiniteTraceChain
              F hInput representatives diagrams m).model
            (globalOriginalFiniteTraceChain
              F hInput representatives diagrams k).model => e x) ih
      exact congrArg
        (globalOriginalFiniteTraceChainStep
          F hInput representatives diagrams k) hpoint

end AllThoseRamseyClasses.Lifts
