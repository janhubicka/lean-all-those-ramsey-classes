import AllThoseRamseyClasses.Published.CoordinatedCycleSmallTests
import Mathlib.Tactic

/-!
# Explicit component labels for short weak tests of the long E-cycle

Rather than taking an abstract transitive closure of the positive E
edges, label a backbone block i by the number of missing backbone
blocks BEFORE i. Consecutive present blocks have the same label;
a missing block between two present blocks separates their labels.

This is an elementary, explicit and computable replacement for the
equivalence-closure oracle in clause (4c). It will be combined with
private D/T labels and a linear order to construct finite paired
equivalence completions of exact weak n-vertex tests.

The present file formalizes the numerical segment lemmas only.
No completion theorem is asserted.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- Number of holes before index i, relative to a set of present
backbone indices. -/
def cycleGapCount (present : Finset ℕ) (i : ℕ) : ℕ :=
  ((Finset.range i).filter (fun j => j ∉ present)).card

theorem cycleGapCount_zero (present : Finset ℕ) :
    cycleGapCount present 0 = 0 := by
  simp [cycleGapCount]

/-- If the current block i is PRESENT then moving to i+1 does
not cross a gap, so the connected-component label is unchanged. -/
theorem cycleGapCount_succ_of_mem
    (present : Finset ℕ) (i : ℕ) (hi : i ∈ present) :
    cycleGapCount present (i + 1) = cycleGapCount present i := by
  classical
  simp [cycleGapCount, Finset.range_add_one, Finset.filter_insert,
    Finset.notMem_range_self, hi]

/-- If block i is MISSING, crossing its position increases the
component label by precisely one. -/
theorem cycleGapCount_succ_of_not_mem
    (present : Finset ℕ) (i : ℕ) (hi : i ∉ present) :
    cycleGapCount present (i + 1) = cycleGapCount present i + 1 := by
  classical
  simp [cycleGapCount, Finset.range_add_one, Finset.filter_insert,
    Finset.notMem_range_self, hi]

/-- Labels cannot decrease as one travels along the backbone. -/
theorem cycleGapCount_mono (present : Finset ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    cycleGapCount present a ≤ cycleGapCount present b := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 hab, hi.2⟩

/-- If there is a missing block between a and b, these endpoint
labels differ strictly. This statement uses a <= i < b rather
than assuming both endpoints belong to the test. -/
theorem cycleGapCount_lt_of_missing
    (present : Finset ℕ) {a i b : ℕ}
    (hai : a ≤ i) (hib : i < b) (hMiss : i ∉ present) :
    cycleGapCount present a < cycleGapCount present b := by
  have hBefore := cycleGapCount_mono present hai
  have hStep := cycleGapCount_succ_of_not_mem present i hMiss
  have hAfter : cycleGapCount present (i + 1) ≤
      cycleGapCount present b :=
    cycleGapCount_mono present (by omega : i + 1 ≤ b)
  omega

/-- A missing INTERNAL backbone block separates the first and last
backbone blocks (the closing E-negative pair). -/
theorem cycleGapCount_endpoints_separate
    (present : Finset ℕ) (m i : ℕ)
    (_hm : 2 ≤ m) (hi : 0 < i ∧ i < m - 1)
    (hMiss : i ∉ present) :
    cycleGapCount present 0 <
      cycleGapCount present (m - 1) := by
  exact cycleGapCount_lt_of_missing present
    (Nat.zero_le _) hi.2 hMiss

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
