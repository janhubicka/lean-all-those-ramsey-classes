import AllThoseRamseyClasses.Lifts.GlobalScheduledFiniteFraisseChain

/-!
# Track F: full functional embeddings between ANY two chain stages

The original regular global maximal-trace finite-age input
constructs, for any finite schedules, an ACTUAL nat-indexed
chain of genuine finite age members with FULL successor embeddings.

A directed-limit construction also needs canonical full
embeddings of earlier stages into arbitrary later stages.
We construct them by dependent recursion on a proof m ≤ n,
using exactly the existing full successor embeddings and
their genuine full native/lifted functional composition.

The maps preserve COMPLETE old set-valued function fibres,
not merely positive graph incidences. No finite stage is
replaced by an image quotient or a weak substructure.

The future direct-limit step still needs coherent transition
laws and the complete fibre-reflection argument. This module
does not assert a quotient colimit or a Fraïssé limit.

The numbered ramsey.tex is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine FULL functional embedding from any earlier
finite stage m to any later stage n, obtained by composing
the actual successive full stage maps, with no extra
amalgamation or uniform boundedness assumption. -/
noncomputable def globalOriginalFiniteTraceChainLE
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n) :
    Structure.Embedding
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams m).model
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams n).model :=
  Nat.leRecOn h
    (@fun k g =>
      (globalOriginalFiniteTraceChainStep F hInput
        representatives diagrams k).comp g)
    (Structure.Embedding.id
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams m).model)

/-- Each component of the finite original global chain fully
embeds into itself via the canonical identity transition. -/
theorem globalOriginalFiniteTraceChainLE_self
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    globalOriginalFiniteTraceChainLE F hInput
      representatives diagrams n n (le_refl n) =
      Structure.Embedding.id
        (globalOriginalFiniteTraceChain
          F hInput representatives diagrams n).model := by
  apply Structure.Embedding.ext
  intro x
  simp [globalOriginalFiniteTraceChainLE, Nat.leRecOn_self]

end AllThoseRamseyClasses.Lifts
