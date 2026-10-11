import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import Mathlib.Tactic

/-!
# Each private matching block belongs to exactly one cycle gadget

Path-private block t_i is adjacent only to b_i,b_(i+1) and itself.
The special closing-private block t_* is adjacent only to b_0,
b_(m-1), and itself. This works for arbitrary k, and uses no
complex combinatorial classification theorem.

Consequently any clique containing a known private block lies
in the corresponding installed three-block gadget. This is
one of the two cases of CycleBlockCliqueCoverage (the other
case is a clique entirely in the long backbone cycle).
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- All blocks related to the i-th private D block occur in the
SAME i-th path gadget; none can occur in any other gadget. -/
theorem cycle_related_to_path_private_in_gadget
    (k : ℕ) (i : Fin (cycleBackboneCount k - 1))
    (b : CycleBlock k)
    (h : cycleRelatedBlocks k (cycleEdgePrivateBlock k i) b) :
    cycleGadgetContains k (.inl i) b := by
  rcases h with hEqual | ⟨g, hp, hb⟩
  · rw [← hEqual]
    change (cycleEdgePrivateBlock k i).val = i.val ∨
      (cycleEdgePrivateBlock k i).val = i.val + 1 ∨
      cycleEdgePrivateBlock k i = cycleEdgePrivateBlock k i
    exact Or.inr (Or.inr rfl)
  · cases g with
    | inl j =>
      change (cycleBackboneCount k + i.val = j.val ∨
        cycleBackboneCount k + i.val = j.val + 1 ∨
        cycleEdgePrivateBlock k i = cycleEdgePrivateBlock k j) at hp
      have hj : j.val < cycleBackboneCount k - 1 := j.isLt
      have heq : i = j := by
        rcases hp with h0 | h1 | hEq
        · exfalso
          omega
        · exfalso
          omega
        · apply Fin.ext
          have hv := congrArg (fun z : CycleBlock k => z.val) hEq
          change cycleBackboneCount k + i.val =
            cycleBackboneCount k + j.val at hv
          omega
      subst j
      exact hb
    | inr _ =>
      change (cycleBackboneCount k + i.val = 0 ∨
        cycleBackboneCount k + i.val = cycleBackboneCount k - 1 ∨
        cycleEdgePrivateBlock k i = cycleClosingPrivateBlock k) at hp
      have hi : i.val < cycleBackboneCount k - 1 := i.isLt
      exfalso
      rcases hp with h0 | h1 | hEq
      · simp only [cycleBackboneCount] at *
        omega
      · simp only [cycleBackboneCount] at *
        omega
      · have hv := congrArg (fun z : CycleBlock k => z.val) hEq
        change cycleBackboneCount k + i.val =
          cycleBlockCount k - 1 at hv
        simp only [cycleBackboneCount, cycleBlockCount] at *
        omega

/-- The closing T block participates only in its designated closing
gadget; no path-edge-private gadget can contain it. -/
theorem cycle_related_to_closing_private_in_gadget
    (k : ℕ) (b : CycleBlock k)
    (h : cycleRelatedBlocks k (cycleClosingPrivateBlock k) b) :
    cycleGadgetContains k (.inr ()) b := by
  rcases h with hEqual | ⟨g, hp, hb⟩
  · rw [← hEqual]
    change (cycleClosingPrivateBlock k).val = 0 ∨
      (cycleClosingPrivateBlock k).val = cycleBackboneCount k - 1 ∨
      cycleClosingPrivateBlock k = cycleClosingPrivateBlock k
    exact Or.inr (Or.inr rfl)
  · cases g with
    | inr _ => exact hb
    | inl j =>
      change (cycleBlockCount k - 1 = j.val ∨
        cycleBlockCount k - 1 = j.val + 1 ∨
        cycleClosingPrivateBlock k = cycleEdgePrivateBlock k j) at hp
      have hj : j.val < cycleBackboneCount k - 1 := j.isLt
      exfalso
      rcases hp with h0 | h1 | hEq
      · simp only [cycleBackboneCount, cycleBlockCount] at *
        omega
      · simp only [cycleBackboneCount, cycleBlockCount] at *
        omega
      · have hv := congrArg (fun z : CycleBlock k => z.val) hEq
        change cycleBlockCount k - 1 =
          cycleBackboneCount k + j.val at hv
        simp only [cycleBackboneCount, cycleBlockCount] at *
        omega

/-- Any block clique containing the path-private block t_i
must be contained in the complete i-th gadget triple. -/
theorem cycle_path_private_clique_in_gadget
    (k : ℕ) (S : Set (CycleBlock k))
    (hClique : ∀ a ∈ S, ∀ b ∈ S, cycleRelatedBlocks k a b)
    (i : Fin (cycleBackboneCount k - 1))
    (hi : cycleEdgePrivateBlock k i ∈ S) :
    ∀ b ∈ S, cycleGadgetContains k (.inl i) b := by
  intro b hb
  exact cycle_related_to_path_private_in_gadget k i b
    (hClique _ hi b hb)

/-- Analogously the whole clique is inside the closing triangle
if it includes the designated closing private T block. -/
theorem cycle_closing_private_clique_in_gadget
    (k : ℕ) (S : Set (CycleBlock k))
    (hClique : ∀ a ∈ S, ∀ b ∈ S, cycleRelatedBlocks k a b)
    (hi : cycleClosingPrivateBlock k ∈ S) :
    ∀ b ∈ S, cycleGadgetContains k (.inr ()) b := by
  intro b hb
  exact cycle_related_to_closing_private_in_gadget k b
    (hClique _ hi b hb)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
