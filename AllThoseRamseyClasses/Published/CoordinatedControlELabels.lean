import AllThoseRamseyClasses.Published.CoordinatedCycleBlocks
import Mathlib.Tactic

/-!
# Exact block-label semantics of the fixed C0 equivalence relation

The fixed control C0 has positive cross-block E edges exactly AB,
BC and AT, plus reflexivity within each matching block. Its
equivalence tuple depends only on the natural-number control block
labels, not on the individual matching-pair bits.

This module turns the ten-vertex numerical definition of C0 into
one small, reusable predicate. This avoids ad hoc rewriting in
the proof that every exact weak cycle test has a K completion.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The precise positive E relation between control block labels
A=0, B=1, T=2, C=3, D=4. It is intentionally not transitive. -/
def cycleControlELabels (a b : ℕ) : Prop :=
  a = b ∨
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
    (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

/-- Every C0 E tuple between projected Ck vertices is exactly an
E tuple of their underlying FIVE control matching-block labels. -/
theorem cycleControlVertex_E_iff_labels
    (k : ℕ) (x y : CycleVertex k) :
    edge CycleControlC0 .equiv
        (cycleControlVertex k x) (cycleControlVertex k y) ↔
      cycleControlELabels
        (cycleBlockLabel k x.1) (cycleBlockLabel k y.1) := by
  rcases x with ⟨a,i⟩
  rcases y with ⟨b,j⟩
  have hi : (2 * cycleBlockLabel k a + i.val) / 2 =
      cycleBlockLabel k a := by
    have hb := i.isLt
    omega
  have hj : (2 * cycleBlockLabel k b + j.val) / 2 =
      cycleBlockLabel k b := by
    have hb := j.isLt
    omega
  change cycleControlELabels
      ((2 * cycleBlockLabel k a + i.val) / 2)
      ((2 * cycleBlockLabel k b + j.val) / 2) ↔
        cycleControlELabels (cycleBlockLabel k a) (cycleBlockLabel k b)
  rw [hi,hj]

/-- The control E relation is symmetric at the block-label level. -/
theorem cycleControlELabels_symm
    (a b : ℕ) (h : cycleControlELabels a b) :
    cycleControlELabels b a := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl ⟨h.2,h.1⟩))
  · exact Or.inr (Or.inl ⟨h.2,h.1⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2,h.1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2,h.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2,h.1⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2,h.1⟩))))

/-- D control label never has positive E edges to the four other
control labels A/B/T/C, in either order. -/
theorem cycleControlELabels_private_iff
    (a : ℕ) :
    cycleControlELabels a 4 ↔ a = 4 := by
  unfold cycleControlELabels
  omega

theorem cycleControlELabels_private_left_iff
    (b : ℕ) :
    cycleControlELabels 4 b ↔ b = 4 := by
  unfold cycleControlELabels
  omega

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
