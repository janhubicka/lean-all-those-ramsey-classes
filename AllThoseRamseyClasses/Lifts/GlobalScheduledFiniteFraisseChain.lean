import AllThoseRamseyClasses.Lifts.GlobalFiniteFraisseCombinedStage

/-!
# Track F: an actual countable chain of finite original maximal-trace stages

The verified finite class input already yields nonempty members,
full JEP and genuine finite strong amalgamation. The separate
finite-stage theorem schedules any finite list of cofinal age
representatives and extension diagrams over all copies in the
CURRENT finite stage.

We now construct a real NAT-INDEXED chain of genuine finite
root-injective maximal-trace age members, equipped with FULL
functional embeddings between consecutive stages. An arbitrary
schedule of finite representative lists and finite extension
diagram lists is accepted as input; at stage n, both lists
are realized in the next finite stage.

This is a meaningful first step toward a Fraisse limit:
there is no postulated chain, and no missing step existence axiom.
The chain is built by dependent classical selection from the
already proved finite strong-AP/JEP stage theorem.

The theorem does NOT claim that the chosen schedule enumerates
all objects/diagrams, nor construct a direct-limit structure,
all-stage transition maps, the extension property or
ultrahomogeneity. Those remain separate steps.

The output maps preserve every old set-valued function fibre
exactly and reflect every added global piece-class relation,
because each is a genuine full Structure.Embedding.

The numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One actual finite structure in the ORIGINAL global
root-injective maximal-trace age. Its carrier is allowed to
vary between stages; its finite age membership is stored. -/
structure GlobalOriginalFiniteTraceStage
    (F : ∀ {W : Type}, Structure L W → Prop) where
  Carrier : Type
  model : Structure (globalFunctionalPieceLanguage F) Carrier
  member : IsGlobalFiniteMaximalTrace F
    (fun {W : Type} (C : Structure L W) =>
      AvoidsGlobalFunctionalEHN F C) model

/-- The genuine empty-carrier age member from the verified
nonemptiness theorem is the first stage of the chain. -/
noncomputable def globalOriginalFiniteTraceInitialStage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    GlobalOriginalFiniteTraceStage F where
  Carrier := Empty
  model := Classical.choose hInput.nonempty
  member := Classical.choose_spec hInput.nonempty

/-- A finite stage can always be enlarged FULLY to realize a
list of cofinal representatives and extension diagrams, with
every root copy of each prescribed diagram in that initial
stage extended in the new target. -/
theorem globalOriginalFiniteTraceStage_existsNext
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (X : GlobalOriginalFiniteTraceStage F)
    (representatives : List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : List (GlobalOriginalFiniteTraceDiagram F)) :
    ∃ (T : GlobalOriginalFiniteTraceStage F)
      (jX : Structure.Embedding X.model T.model),
      (∀ P : GlobalOriginalFiniteTraceRepresentatives F,
        P ∈ representatives →
          ∃ (_jP : Structure.Embedding P.2.1 T.model), True) ∧
      (∀ d : GlobalOriginalFiniteTraceDiagram F,
        d ∈ diagrams →
        ∀ f : Structure.Embedding d.1.2.1 X.model,
          ∃ (jB : Structure.Embedding d.2.1.2.1 T.model),
            ∀ a, jB (d.2.2 a) = jX (f a)) := by
  obtain ⟨VT, T, hT, jX, hReps, hDiagrams⟩ :=
    globalOriginalFiniteFraisseInput_realizeCofinalAndDiagrams
      F hInput X.model X.member representatives diagrams
  exact ⟨⟨VT, T, hT⟩, jX, hReps, hDiagrams⟩

/-- Choose an actual one-step age extension; no theorem conclusion
is assumed. This is classical choice from a verified existence
statement, retaining its full embedding in the next definition. -/
noncomputable def globalOriginalFiniteTraceNextStage
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (X : GlobalOriginalFiniteTraceStage F)
    (representatives : List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : List (GlobalOriginalFiniteTraceDiagram F)) :
    GlobalOriginalFiniteTraceStage F :=
  Classical.choose
    (globalOriginalFiniteTraceStage_existsNext
      F hInput X representatives diagrams)

/-- The chosen next stage has a FULL embedding of its predecessor,
satisfying the prescribed finite cofinality and extension demands.
This is a theorem obtained from the explicit one-step existence
construction rather than an external step axiom. -/
theorem globalOriginalFiniteTraceNextStage_spec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (X : GlobalOriginalFiniteTraceStage F)
    (representatives : List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : List (GlobalOriginalFiniteTraceDiagram F)) :
    ∃ (jX : Structure.Embedding X.model
        (globalOriginalFiniteTraceNextStage
          F hInput X representatives diagrams).model),
      (∀ P : GlobalOriginalFiniteTraceRepresentatives F,
        P ∈ representatives →
          ∃ (_jP : Structure.Embedding P.2.1
            (globalOriginalFiniteTraceNextStage
              F hInput X representatives diagrams).model), True) ∧
      (∀ d : GlobalOriginalFiniteTraceDiagram F,
        d ∈ diagrams →
        ∀ f : Structure.Embedding d.1.2.1 X.model,
          ∃ (jB : Structure.Embedding d.2.1.2.1
            (globalOriginalFiniteTraceNextStage
              F hInput X representatives diagrams).model),
            ∀ a, jB (d.2.2 a) = jX (f a)) :=
  Classical.choose_spec
    (globalOriginalFiniteTraceStage_existsNext
      F hInput X representatives diagrams)

/-- The successor embedding for the chosen finite step is a
genuine full native-functional-and-lifted Structure.Embedding. -/
noncomputable def globalOriginalFiniteTraceNextEmbedding
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (X : GlobalOriginalFiniteTraceStage F)
    (representatives : List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : List (GlobalOriginalFiniteTraceDiagram F)) :
    Structure.Embedding X.model
      (globalOriginalFiniteTraceNextStage
        F hInput X representatives diagrams).model :=
  Classical.choose
    (globalOriginalFiniteTraceNextStage_spec
      F hInput X representatives diagrams)

/-- Every one-step cofinal and extension request is satisfied
by the specifically selected successor embedding, not just
by an unrelated existential embedding. -/
theorem globalOriginalFiniteTraceNextEmbedding_spec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (X : GlobalOriginalFiniteTraceStage F)
    (representatives : List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : List (GlobalOriginalFiniteTraceDiagram F)) :
    (∀ P : GlobalOriginalFiniteTraceRepresentatives F,
      P ∈ representatives →
        ∃ (_jP : Structure.Embedding P.2.1
          (globalOriginalFiniteTraceNextStage
            F hInput X representatives diagrams).model), True) ∧
    (∀ d : GlobalOriginalFiniteTraceDiagram F,
      d ∈ diagrams →
      ∀ f : Structure.Embedding d.1.2.1 X.model,
        ∃ (jB : Structure.Embedding d.2.1.2.1
          (globalOriginalFiniteTraceNextStage
            F hInput X representatives diagrams).model),
          ∀ a, jB (d.2.2 a) =
            globalOriginalFiniteTraceNextEmbedding
              F hInput X representatives diagrams (f a)) :=
  Classical.choose_spec
    (globalOriginalFiniteTraceNextStage_spec
      F hInput X representatives diagrams)

/-- For ANY chosen finite list of age representatives and
finite extension diagrams at each natural-number stage,
construct an ACTUAL sequence of finite maximal-trace members.
The step itself enforces both demands. -/
noncomputable def globalOriginalFiniteTraceChain
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :
    ℕ → GlobalOriginalFiniteTraceStage F :=
  fun n =>
    Nat.rec
      (globalOriginalFiniteTraceInitialStage F hInput)
      (fun i S =>
        globalOriginalFiniteTraceNextStage
          F hInput S (representatives i) (diagrams i)) n

/-- Consecutive stages of the concrete scheduled chain admit
ACTUAL FULL functional/lifted embeddings. No future-stage
inclusion is assumed in the definition of the chain. -/
noncomputable def globalOriginalFiniteTraceChainStep
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    Structure.Embedding
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams n).model
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams (n + 1)).model := by
  change Structure.Embedding
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).model
    (globalOriginalFiniteTraceNextStage F hInput
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams n)
      (representatives n) (diagrams n)).model
  exact globalOriginalFiniteTraceNextEmbedding F hInput
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n)
    (representatives n) (diagrams n)

/-- The concrete chain satisfies the ENTIRE finite demand contract
at every successor stage: all listed representative objects embed
fully in its next member, and every listed extension diagram is
realized over EVERY full copy of its root in the current member.

This is the exact invariant needed for a later fair diagonal
schedule. It does not claim saturation of root copies that first
appear inside the new target, nor the infinite extension property
before construction of a direct limit. -/
theorem globalOriginalFiniteTraceChainStep_spec
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    (∀ P : GlobalOriginalFiniteTraceRepresentatives F,
      P ∈ representatives n →
        ∃ (_jP : Structure.Embedding P.2.1
          (globalOriginalFiniteTraceChain F hInput
            representatives diagrams (n + 1)).model), True) ∧
    (∀ d : GlobalOriginalFiniteTraceDiagram F,
      d ∈ diagrams n →
      ∀ f : Structure.Embedding d.1.2.1
          (globalOriginalFiniteTraceChain F hInput
            representatives diagrams n).model,
        ∃ (jB : Structure.Embedding d.2.1.2.1
          (globalOriginalFiniteTraceChain F hInput
            representatives diagrams (n + 1)).model),
          ∀ a, jB (d.2.2 a) =
            globalOriginalFiniteTraceChainStep F hInput
              representatives diagrams n (f a)) := by
  exact globalOriginalFiniteTraceNextEmbedding_spec
    F hInput
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n)
    (representatives n) (diagrams n)

end AllThoseRamseyClasses.Lifts
