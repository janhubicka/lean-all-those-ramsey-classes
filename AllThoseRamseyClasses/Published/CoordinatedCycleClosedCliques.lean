import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import PartiteConstruction.Ramsey.ClosureClosedCover
import Mathlib.Tactic

/-!
# Closed U-irreducible tests use pairwise gadget-related matching blocks

This is the main relative-support lemma for the coordinated 2019 repair.
The long-cycle source need NOT have transitive E or total <.
The protected test is intrinsically U-closed and U-irreducible and
embeds into the source via a full relational embedding.

If two test vertices lie in distinct nonadjacent matching blocks,
delete each of those complete blocks in turn. Both remaining subsets
are U-substructures of the test, because every M-tuple stays in its
matching block; together they cover the test, and every relation tuple
lies wholly on one side because it cannot cross the nonadjacent pair.
The pinned upstream IsUIrreducible.closed_cover theorem then contradicts
U-irreducibility.

This establishes pairwise adjacency of the support, NOT YET the finite
maximal-clique lemma identifying a common B0 gadget.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Every positive relation tuple of C_k is supported by one
matching block or by two blocks from a common installed gadget. -/
theorem cycleGadgetWitness_edge_supported (k : ℕ)
    (R : Symbol) (x y : CycleVertex k)
    (h : edge (cycleGadgetWitness k) R x y) :
    cycleRelatedBlocks k x.1 y.1 := by
  cases R with
  | lt => exact h.1
  | equiv => exact h.1
  | mate => exact Or.inl h.1

theorem cycleGadgetWitness_tuple_supported (k : ℕ)
    (R : Symbol) (z : Fin 2 → CycleVertex k)
    (h : (cycleGadgetWitness k).rel R z)
    (i j : Fin 2) :
    cycleRelatedBlocks k (z i).1 (z j).1 := by
  have ht : z = ![z 0, z 1] := by
    funext q
    fin_cases q <;> rfl
  have h01 : cycleRelatedBlocks k (z 0).1 (z 1).1 := by
    apply cycleGadgetWitness_edge_supported k R
    change (cycleGadgetWitness k).rel R ![z 0, z 1]
    rw [← ht]
    exact h
  fin_cases i <;> fin_cases j
  · exact Or.inl rfl
  · exact h01
  · exact cycleRelatedBlocks_symm k _ _ h01
  · exact Or.inl rfl

/-- Removing an entire matching block from an induced protected test
leaves a U-substructure, regardless of E/order on the test. -/
private theorem test_avoidBlock_isUSubstructure
    (k : ℕ) {X : Type}
    (Test : RelStructure Lang X)
    (e : Embedding Test (cycleGadgetWitness k))
    (b : CycleBlock k) :
    IsUSubstructure mateRules Test
      {x : X | (e x).1 ≠ b} := by
  intro rule hrule t ht hRoot j
  have hRule : rule = mateRule := by
    simpa only [mateRules, Set.mem_singleton_iff] using hrule
  subst rule
  have hTarget : (cycleGadgetWitness k).rel .mate (e ∘ t) :=
    (e.map_rel_iff .mate t).mpr ht
  have hTuple : (e ∘ t) = ![e (t 0), e (t 1)] := by
    funext i
    fin_cases i <;> rfl
  have hM : cycleMatching k (e (t 0)) (e (t 1)) := by
    rw [hTuple] at hTarget
    exact hTarget
  have hSame : (e (t 0)).1 = (e (t 1)).1 := hM.1
  have h0 := hRoot (0 : Fin 1)
  change (e (t 0)).1 ≠ b at h0
  fin_cases j
  · exact h0
  · change (e (t 1)).1 ≠ b
    rw [← hSame]
    exact h0

/-- The blocks occupied by an arbitrary *closed U-irreducible test*
form a clique in the block-interaction graph of the long-cycle C_k.
In particular, this lemma uses all U-closed tests, not weak singleton
tests and not only copies of B0. -/
theorem cycle_closedUIrreducible_blocks_pairwise_related
    (k : ℕ) {X : Type}
    (Test : RelStructure Lang X)
    (hClosed : IsUClosed mateRules Test)
    (hIrred : IsUIrreducible mateRules Test)
    (e : Embedding Test (cycleGadgetWitness k))
    (a b : X) :
    cycleRelatedBlocks k (e a).1 (e b).1 := by
  classical
  by_contra hNo
  have hab : (e a).1 ≠ (e b).1 := by
    intro h
    exact hNo (Or.inl h)
  let S : Set X := {x | (e x).1 ≠ (e a).1}
  let T : Set X := {x | (e x).1 ≠ (e b).1}
  have hS : IsUSubstructure mateRules Test S :=
    test_avoidBlock_isUSubstructure k Test e (e a).1
  have hT : IsUSubstructure mateRules Test T :=
    test_avoidBlock_isUSubstructure k Test e (e b).1
  have hCover : ∀ x : X, x ∈ S ∨ x ∈ T := by
    intro x
    by_cases hx : (e x).1 = (e a).1
    · right
      change (e x).1 ≠ (e b).1
      rw [hx]
      exact hab
    · exact Or.inl hx
  have hTuples :
      ∀ R (z : Fin (Lang.arity R) → X), Test.rel R z →
        (∀ j, z j ∈ S) ∨ (∀ j, z j ∈ T) := by
    intro R z hz
    by_cases hs : ∀ j, z j ∈ S
    · exact Or.inl hs
    by_cases ht : ∀ j, z j ∈ T
    · exact Or.inr ht
    push_neg at hs ht
    obtain ⟨i, hi⟩ := hs
    obtain ⟨j, hj⟩ := ht
    have hai : (e (z i)).1 = (e a).1 := by
      change ¬ ((e (z i)).1 ≠ (e a).1) at hi
      exact not_ne.mp hi
    have hbj : (e (z j)).1 = (e b).1 := by
      change ¬ ((e (z j)).1 ≠ (e b).1) at hj
      exact not_ne.mp hj
    have hTarget : (cycleGadgetWitness k).rel R (e ∘ z) :=
      (e.map_rel_iff R z).mpr hz
    have hRelated : cycleRelatedBlocks k
        (e (z i)).1 (e (z j)).1 := by
      exact cycleGadgetWitness_tuple_supported k R (e ∘ z)
        hTarget i j
    rw [hai, hbj] at hRelated
    exact False.elim (hNo hRelated)
  rcases hIrred.closed_cover hClosed S T
      hS hT hCover hTuples with hAllS | hAllT
  · have ha : a ∈ S := hAllS a
    change (e a).1 ≠ (e a).1 at ha
    exact ha rfl
  · have hb : b ∈ T := hAllT b
    change (e b).1 ≠ (e b).1 at hb
    exact hb rfl

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
