import AllThoseRamseyClasses.Published.CoordinatedCycleClosedCliques
import AllThoseRamseyClasses.Published.CoordinatedCycleControlHom
import AllThoseRamseyClasses.Published.CoordinatedCycleFixtures
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness

/-!
# Reduce coordinated (4a) and (4b) to two finite gadget facts

The uniform long-cycle C_k is U-closed, and its fixed label projection
is already a positive homomorphism. The previous module establishes
that the matching-block support of every CLOSED U-irreducible test
is pairwise gadget-related.

This module gives an explicit factorization theorem: if all such
finite block cliques lie in a single gadget and every gadget carries
an induced B0 copy whose control image is itself an induced B0 copy,
then every protected test factors through B0. Consequently BOTH
coordinated (4a) and (4b) follow.

These two combinatorial assumptions are EXPOSITORY proof obligations,
not claims of finished Lean proofs. The separate weak-test (4c)
completion condition and global no-copywise-completion theorem
remain outside this module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Pure block-hypergraph obligation: every clique, including the
empty clique, is contained in at least one installed gadget. -/
def CycleBlockCliqueCoverage (k : ℕ) : Prop :=
  ∀ (S : Set (CycleBlock k)),
    (∀ a ∈ S, ∀ b ∈ S, cycleRelatedBlocks k a b) →
    ∃ g : CycleGadget k,
      ∀ b ∈ S, cycleGadgetContains k g b

/-- Explicit *induced* gadget witnesses, not merely positive maps.
Their compositions with the fixed C0 projection are full embeddings. -/
def CycleInducedGadgetTemplates (k : ℕ) : Prop :=
  ∀ g : CycleGadget k,
    ∃ (u : Embedding CycleBaseB0 (cycleGadgetWitness k))
      (v : Embedding CycleBaseB0 CycleControlC0),
      (∀ x : CycleVertex k,
        cycleGadgetContains k g x.1 →
          ∃ b : Fin 6, u b = x) ∧
      (∀ b : Fin 6, cycleControlVertex k (u b) = v b)

/-- Every closed irreducible test genuinely factors through a SINGLE
induced B0-gadget, with the control projection commuting. -/
theorem cycle_closedTest_factors_through_B0
    (k : ℕ)
    (hClique : CycleBlockCliqueCoverage k)
    (hGadgets : CycleInducedGadgetTemplates k)
    {X : Type} (Test : RelStructure Lang X)
    (hClosed : IsUClosed mateRules Test)
    (hIrred : IsUIrreducible mateRules Test)
    (e : Embedding Test (cycleGadgetWitness k)) :
    ∃ (u : Embedding CycleBaseB0 (cycleGadgetWitness k))
      (v : Embedding CycleBaseB0 CycleControlC0)
      (d : Embedding Test CycleBaseB0),
      (∀ x : X, e x = u (d x)) ∧
      (∀ b : Fin 6, cycleControlVertex k (u b) = v b) := by
  classical
  let S : Set (CycleBlock k) := {b | ∃ x : X, (e x).1 = b}
  have hRelated : ∀ a ∈ S, ∀ b ∈ S,
      cycleRelatedBlocks k a b := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact cycle_closedUIrreducible_blocks_pairwise_related
      k Test hClosed hIrred e x y
  obtain ⟨g, hg⟩ := hClique S hRelated
  obtain ⟨u, v, hInside, hComm⟩ := hGadgets g
  have hRange (x : X) : ∃ b : Fin 6, e x = u b := by
    obtain ⟨b, hb⟩ := hInside (e x)
      (hg (e x).1 ⟨x, rfl⟩)
    exact ⟨b, hb.symm⟩
  let d : Embedding Test CycleBaseB0 :=
    e.factorThroughRange u hRange
  refine ⟨u, v, d, ?_, hComm⟩
  intro x
  change e x = u (Classical.choose (hRange x))
  exact Classical.choose_spec (hRange x)

/-- The exact coordinated Definition 2.17(4b) follows from the two
explicit finite gadget hypotheses, using ONLY closed hereditariness. -/
theorem cycle_closedUIrreduciblesIn_of_gadgets
    (k : ℕ)
    (hClique : CycleBlockCliqueCoverage k)
    (hGadgets : CycleInducedGadgetTemplates k) :
    ClosedUIrreduciblesIn finitePairedClass mateRules
      (cycleGadgetWitness k) := by
  intro X Test hClosed hIrred e
  obtain ⟨u, v, d, hFact, hComm⟩ :=
    cycle_closedTest_factors_through_B0
      k hClique hGadgets Test hClosed hIrred e
  exact finitePairedClass_closedUHereditary
    Test CycleBaseB0 CycleBaseB0_mem hClosed d

/-- The exact COORDINATED Definition 2.15 map property (4a), not the
unrepaired literal 2019 U-homomorphism-embedding, follows from the
same finite gadget hypotheses. -/
theorem cycle_control_closedUHomomorphismEmbedding_of_gadgets
    (k : ℕ)
    (hClique : CycleBlockCliqueCoverage k)
    (hGadgets : CycleInducedGadgetTemplates k) :
    IsClosedUHomomorphismEmbedding mateRules
      (cycleGadgetWitness k) CycleControlC0
      (cycleControlVertex k) := by
  refine ⟨cycleGadgetWitness_control_homomorphism k, ?_⟩
  intro X Test hClosed hIrred e
  obtain ⟨u, v, d, hFact, hComm⟩ :=
    cycle_closedTest_factors_through_B0
      k hClique hGadgets Test hClosed hIrred e
  refine ⟨v.comp d, ?_⟩
  intro x
  change v (d x) = cycleControlVertex k (e x)
  rw [hFact x]
  exact (hComm (d x)).symm

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
