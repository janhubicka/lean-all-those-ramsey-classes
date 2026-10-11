import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetLabels
import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetPositions
import Mathlib.Tactic

/-!
# Uniform gadgetwise injectivity of the fixed C0 block labels

Every installed three-block gadget uses DISTINCT control block labels:
path gadgets have AB(D) or BC(D) (with alternating A/B orientation
along the backbone), and the closing gadget uses A/T/C.

This is exactly the hypothesis needed to reflect the matching relation
inside the gadget from control C0 back to the original C_k.
All arguments are uniform in k, including the final B-C-D path edge.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- Every block of a path gadget is one of its three named blocks. -/
theorem cyclePath_gadget_block_cases (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1))
    (b : CycleBlock k)
    (h : cycleGadgetContains k (.inl i) b) :
    b = cyclePathStart k i ∨
    b = cyclePathFinish k i ∨
    b = cycleEdgePrivateBlock k i := by
  change b.val = i.val ∨ b.val = i.val + 1 ∨
    b = cycleEdgePrivateBlock k i at h
  rcases h with h | h | h
  · left
    apply Fin.ext
    exact h
  · right
    left
    apply Fin.ext
    exact h
  · right
    right
    exact h

/-- Likewise the closing gadget contains exactly its three blocks. -/
theorem cycleClosing_gadget_block_cases (k : ℕ)
    (b : CycleBlock k)
    (h : cycleGadgetContains k (.inr ()) b) :
    b = cycleClosingFirst k ∨
    b = cycleClosingLast k ∨
    b = cycleClosingPrivateBlock k := by
  change b.val = 0 ∨
    b.val = cycleBackboneCount k - 1 ∨
    b = cycleClosingPrivateBlock k at h
  rcases h with h | h | h
  · left
    apply Fin.ext
    exact h
  · right
    left
    apply Fin.ext
    exact h
  · right
    right
    exact h

/-- Consecutive backbone blocks carry distinct control labels,
even in the last path gadget ending at the special C-labelled block. -/
theorem cyclePath_start_finish_label_ne (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBlockLabel k (cyclePathStart k i) ≠
      cycleBlockLabel k (cyclePathFinish k i) := by
  rw [cyclePathStart_label, cyclePathFinish_label]
  split_ifs <;> omega

theorem cyclePath_start_private_label_ne (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBlockLabel k (cyclePathStart k i) ≠
      cycleBlockLabel k (cycleEdgePrivateBlock k i) := by
  rw [cyclePathStart_label, cyclePathPrivate_label]
  split_ifs <;> omega

theorem cyclePath_finish_private_label_ne (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBlockLabel k (cyclePathFinish k i) ≠
      cycleBlockLabel k (cycleEdgePrivateBlock k i) := by
  rw [cyclePathFinish_label, cyclePathPrivate_label]
  split_ifs <;> omega

/-- The three different labels in the closing gadget are A/T/C. -/
theorem cycleClosing_label_distinct (k : ℕ) :
    (cycleBlockLabel k (cycleClosingFirst k) ≠
        cycleBlockLabel k (cycleClosingLast k)) ∧
    (cycleBlockLabel k (cycleClosingFirst k) ≠
        cycleBlockLabel k (cycleClosingPrivateBlock k)) ∧
    (cycleBlockLabel k (cycleClosingLast k) ≠
        cycleBlockLabel k (cycleClosingPrivateBlock k)) := by
  simp [cycleClosingFirst_label, cycleClosingLast_label,
    cycleClosingPrivate_label]

/-- A fixed gadget never identifies two different blocks under the
five-label projection to C0. This is the essential matching-reflection
condition for lifting B0 control templates. -/
theorem cycleGadget_blockLabel_injective (k : ℕ)
    (g : CycleGadget k) (a b : CycleBlock k)
    (ha : cycleGadgetContains k g a)
    (hb : cycleGadgetContains k g b)
    (hLabel : cycleBlockLabel k a = cycleBlockLabel k b) :
    a = b := by
  cases g with
  | inl i =>
      rcases cyclePath_gadget_block_cases k i a ha with h | h | h <;>
        rcases cyclePath_gadget_block_cases k i b hb with j | j | j
      all_goals
        rw [h, j] at hLabel ⊢
        first
        | rfl
        | 
          have h01 := cyclePath_start_finish_label_ne k i
          have h04 := cyclePath_start_private_label_ne k i
          have h14 := cyclePath_finish_private_label_ne k i
          simp_all
  | inr _ =>
      rcases cycleClosing_gadget_block_cases k a ha with h | h | h <;>
        rcases cycleClosing_gadget_block_cases k b hb with j | j | j
      all_goals
        rw [h, j] at hLabel ⊢
        first
        | rfl
        |
          have hThree := cycleClosing_label_distinct k
          simp_all

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
