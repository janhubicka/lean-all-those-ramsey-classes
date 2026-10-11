import AllThoseRamseyClasses.Published.CoordinatedCycleSmallTests
import Mathlib.Tactic

/-!
# Every sufficiently small exact weak test misses an INTERNAL backbone block

The existing theorem cycle_exists_unhit_backbone gives some
missing backbone block. For the explicit segment-label K-completion
we need a stronger result: a missing INTERNAL block, even if the
tested weak source includes both endpoint blocks.

For |S| <= k and m=2k+5, add one first-root vertex and one
last-root vertex to S. This enlarged test still has size < m.
An entirely missing backbone block in it must therefore be
neither endpoint. No U-closedness assumption is ever put on S.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- One distinguished root vertex of the first backbone block. -/
def cycleFirstRootVertex (k : ℕ) : CycleVertex k :=
  (cycleBackboneBlock k
    ⟨0, by simp only [cycleBackboneCount]; omega⟩, (0 : Fin 2))

/-- One distinguished root vertex of the final backbone block. -/
def cycleLastRootVertex (k : ℕ) : CycleVertex k :=
  (cycleBackboneBlock k
    ⟨cycleBackboneCount k - 1, by
       simp only [cycleBackboneCount]
       omega⟩, (0 : Fin 2))

/-- Exact weak n-vertex subsets miss some internal backbone block.
The threshold is uniform in k, and unlike the older lemma this
witness cannot be the first or last backbone block. -/
theorem cycle_cutoff_tests_miss_internal_backbone
    (k : ℕ) (S : Finset (CycleVertex k))
    (hCard : S.card ≤ k) :
    ∃ i : Fin (cycleBackboneCount k),
      0 < i.val ∧ i.val < cycleBackboneCount k - 1 ∧
      (∀ v ∈ S, v.1 ≠ cycleBackboneBlock k i) := by
  classical
  let Splus : Finset (CycleVertex k) :=
    insert (cycleFirstRootVertex k)
      (insert (cycleLastRootVertex k) S)
  have hOne :
      (insert (cycleLastRootVertex k) S).card ≤ S.card + 1 :=
    Finset.card_insert_le _ _
  have hTwo :
      Splus.card ≤ (insert (cycleLastRootVertex k) S).card + 1 := by
    exact Finset.card_insert_le _ _
  have hSmall : Splus.card < cycleBackboneCount k := by
    have hm := cycleBackboneCount_ge_five k
    simp only [cycleBackboneCount] at *
    omega
  obtain ⟨i, hiMissing⟩ := cycle_exists_unhit_backbone k Splus hSmall
  have hFirst :
      (cycleFirstRootVertex k).1 ≠ cycleBackboneBlock k i := by
    exact hiMissing _ (Finset.mem_insert_self _ _)
  have hLast :
      (cycleLastRootVertex k).1 ≠ cycleBackboneBlock k i := by
    apply hiMissing
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hi0 : i.val ≠ 0 := by
    intro hzero
    apply hFirst
    apply Fin.ext
    change 0 = i.val
    omega
  have hiLast : i.val ≠ cycleBackboneCount k - 1 := by
    intro hlast
    apply hLast
    apply Fin.ext
    change cycleBackboneCount k - 1 = i.val
    omega
  have hiLt := i.isLt
  refine ⟨i, by omega, by omega, ?_⟩
  intro v hv
  apply hiMissing v
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
