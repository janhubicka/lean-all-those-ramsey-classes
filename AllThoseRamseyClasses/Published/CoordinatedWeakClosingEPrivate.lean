import AllThoseRamseyClasses.Published.CoordinatedWeakEEndpointSeparation
import AllThoseRamseyClasses.Published.CoordinatedWeakEGadgetTags

/-!
# The closing T block has exactly the intended completed E class

The weak completion K target D(k,S) groups matching blocks by
explicit tags. The first backbone b0 has tag (0,0), just like the
closing private T block. The final backbone b_(m-1) is separated
from both of these by any internal missing backbone block.

These statements hold for all exact weak vertex S of size <= k,
without any closedness assumption, and complete the three E-value
comparisons for the closing gadget.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- First backbone and closing T are E-equivalent, including any
choice of their individual matching-pair bits. -/
theorem cycleWeakCandidate_closing_first_private_E_positive
    (k : ℕ) (S : Finset (CycleVertex k))
    (a b : Fin 2) :
    edge (cycleWeakCandidate k S) .equiv
      (cycleClosingFirst k, a) (cycleClosingPrivateBlock k, b) := by
  change cycleWeakEClass k S (cycleClosingFirst k, a) =
    cycleWeakEClass k S (cycleClosingPrivateBlock k, b)
  let firstI : Fin (cycleBackboneCount k) :=
    ⟨0, by have hm := cycleBackboneCount_ge_five k; omega⟩
  have hFirst : cycleClosingFirst k = cycleBackboneBlock k firstI := by
    apply Fin.ext
    rfl
  rw [hFirst, cycleWeakEClass_backbone,
    cycleWeakEClass_closingPrivate]
  change cycleGapCount (cycleWeakPresentBlocks k S) 0 = 0
  exact cycleGapCount_zero _

/-- Closing T remains E-inequivalent to the last backbone block
when S meets at most k vertices. -/
theorem cycleWeakCandidate_closing_last_private_E_negative
    (k : ℕ) (S : Finset (CycleVertex k))
    (hCard : S.card ≤ k) (a b : Fin 2) :
    ¬ edge (cycleWeakCandidate k S) .equiv
      (cycleClosingLast k, a) (cycleClosingPrivateBlock k, b) := by
  intro hE
  change cycleWeakEClass k S (cycleClosingLast k, a) =
    cycleWeakEClass k S (cycleClosingPrivateBlock k, b) at hE
  let lastI : Fin (cycleBackboneCount k) :=
    ⟨cycleBackboneCount k - 1, by
      have hm := cycleBackboneCount_ge_five k
      omega⟩
  have hLast : cycleClosingLast k = cycleBackboneBlock k lastI := by
    apply Fin.ext
    rfl
  rw [hLast, cycleWeakEClass_backbone,
    cycleWeakEClass_closingPrivate] at hE
  have hGap := cycleWeak_gap_endpoints_separate k S hCard
  have hEq : cycleGapCount (cycleWeakPresentBlocks k S)
      (cycleBackboneCount k - 1) = 0 :=
    congrArg (fun t : ℕ × ℕ => t.2) hE
  have hZero : cycleGapCount (cycleWeakPresentBlocks k S) 0 = 0 :=
    cycleGapCount_zero _
  omega

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
