import AllThoseRamseyClasses.Published.CoordinatedWeakPairedCompletionTarget
import AllThoseRamseyClasses.Published.CoordinatedCycleInternalGap
import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetPositions
import Mathlib.Tactic

/-!
# Component classes on the exact weak test: missing internal gap

The explicit K-target D(k,S) assigns a backbone E-class according to
the number of ABSENT backbone blocks before its index. A weak test S
of at most k vertices misses an INTERNAL backbone block, so the
FIRST and LAST backbone blocks have different E-classes in D(k,S).
This is the negative E requirement of the closing B0 gadget.

The weak S need not be U-closed, and the completion target uses
exactly the set of blocks touched by S (including incomplete pairs).
The remaining path/closing cross-block relations are separate.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- Every matching block touched by an exact weak test is present
in its explicit block-index image. -/
theorem cycleWeakPresentBlocks_of_mem (k : ℕ)
    (S : Finset (CycleVertex k)) (v : CycleVertex k)
    (hv : v ∈ S) :
    v.1.val ∈ cycleWeakPresentBlocks k S :=
  Finset.mem_image.mpr ⟨v,hv,rfl⟩

/-- Every backbone block has the tag (0, number of earlier gaps),
regardless of which bit of its matched pair is selected. -/
theorem cycleWeakEClass_backbone (k : ℕ)
    (S : Finset (CycleVertex k))
    (i : Fin (cycleBackboneCount k)) (bit : Fin 2) :
    cycleWeakEClass k S (cycleBackboneBlock k i,bit) =
      (0,cycleGapCount (cycleWeakPresentBlocks k S) i.val) := by
  have hi := i.isLt
  change (if i.val < cycleBackboneCount k then
      (0,cycleGapCount (cycleWeakPresentBlocks k S) i.val)
    else if i.val = cycleBlockCount k - 1 then (0,0)
    else (1,i.val)) = _
  simp [hi]

/-- The internal missing backbone block remains absent from
the exact weak source's image of matching-block indices. -/
theorem cycleWeak_missing_internal_gap (k : ℕ)
    (S : Finset (CycleVertex k)) (hCard : S.card ≤ k) :
    ∃ i : Fin (cycleBackboneCount k),
      0 < i.val ∧ i.val < cycleBackboneCount k - 1 ∧
      i.val ∉ cycleWeakPresentBlocks k S := by
  obtain ⟨i,hi0,hiLast,hi⟩ :=
    cycle_cutoff_tests_miss_internal_backbone k S hCard
  refine ⟨i,hi0,hiLast,?_⟩
  intro hMem
  obtain ⟨v,hv,hval⟩ := Finset.mem_image.mp hMem
  apply hi v hv
  apply Fin.ext
  change v.1.val = i.val
  exact hval

/-- Uniform separation of completed E-class tags on the two
closing backbone blocks. This is a statement for EVERY exact weak
S with |S|≤k, not a bounded computational regression. -/
theorem cycleWeak_gap_endpoints_separate (k : ℕ)
    (S : Finset (CycleVertex k)) (hCard : S.card ≤ k) :
    cycleGapCount (cycleWeakPresentBlocks k S) 0 <
      cycleGapCount (cycleWeakPresentBlocks k S)
        (cycleBackboneCount k - 1) := by
  obtain ⟨i,hi0,hiLast,hMiss⟩ :=
    cycleWeak_missing_internal_gap k S hCard
  exact cycleGapCount_endpoints_separate
    (cycleWeakPresentBlocks k S)
    (cycleBackboneCount k) i.val
    (by have hm := cycleBackboneCount_ge_five k; omega)
    ⟨hi0,hiLast⟩ hMiss

/-- First and last backbone vertices remain E-INEQUIVALENT in
the completed target D(k,S), for any choices of their two bits. -/
theorem cycleWeakCandidate_closing_backbone_E_negative
    (k : ℕ) (S : Finset (CycleVertex k))
    (hCard : S.card ≤ k) (a b : Fin 2) :
    ¬ edge (cycleWeakCandidate k S) .equiv
      (cycleClosingFirst k,a) (cycleClosingLast k,b) := by
  intro hE
  change cycleWeakEClass k S (cycleClosingFirst k,a) =
      cycleWeakEClass k S (cycleClosingLast k,b) at hE
  let firstI : Fin (cycleBackboneCount k) :=
    ⟨0,by have hm := cycleBackboneCount_ge_five k; omega⟩
  let lastI : Fin (cycleBackboneCount k) :=
    ⟨cycleBackboneCount k - 1,
      by have hm := cycleBackboneCount_ge_five k; omega⟩
  have hFirst : cycleClosingFirst k = cycleBackboneBlock k firstI := by
    apply Fin.ext
    rfl
  have hLast : cycleClosingLast k = cycleBackboneBlock k lastI := by
    apply Fin.ext
    rfl
  rw [hFirst,hLast,cycleWeakEClass_backbone,
    cycleWeakEClass_backbone] at hE
  have hv := congrArg (fun t : ℕ × ℕ => t.2) hE
  have hsep := cycleWeak_gap_endpoints_separate k S hCard
  exact (Nat.ne_of_lt hsep) hv

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
