import AllThoseRamseyClasses.Published.CoordinatedControlELabels
import AllThoseRamseyClasses.Published.CoordinatedGadgetLabelInjectivity
import Mathlib.Tactic

/-!
# All C0 E profiles of installed Ck gadgets

On each path gadget the first two backbone blocks are E-related;
its D private matching block is unrelated to both. On the closing
gadget the first backbone block is related to T, but the final
backbone block is related to neither first nor T.

These are all cross-block E patterns in the actual partial Ck.
The equivalence relation in C0 is deliberately not transitive.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

theorem cycleControlELabels_pathStartFinish (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleControlELabels
      (cycleBlockLabel k (cyclePathStart k i))
      (cycleBlockLabel k (cyclePathFinish k i)) := by
  rw [cyclePathStart_label, cyclePathFinish_label]
  by_cases hLast : i.val + 1 = cycleBackboneCount k - 1
  · have hOdd : i.val % 2 = 1 := by
      simp only [cycleBackboneCount] at hLast
      omega
    simp [cycleControlELabels, hLast, hOdd]
  · by_cases hEven : i.val % 2 = 0
    · have hNext : (i.val + 1) % 2 = 1 := by omega
      simp [cycleControlELabels, hLast, hEven, hNext]
    · have hOdd : i.val % 2 = 1 := by omega
      have hNext : (i.val + 1) % 2 = 0 := by omega
      simp [cycleControlELabels, hLast, hOdd, hNext]

theorem cycleControlELabels_pathStartPrivate_neg (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    ¬ cycleControlELabels
      (cycleBlockLabel k (cyclePathStart k i))
      (cycleBlockLabel k (cycleEdgePrivateBlock k i)) := by
  rw [cyclePathPrivate_label, cycleControlELabels_private_iff]
  exact cyclePath_start_private_label_ne k i

theorem cycleControlELabels_pathFinishPrivate_neg (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    ¬ cycleControlELabels
      (cycleBlockLabel k (cyclePathFinish k i))
      (cycleBlockLabel k (cycleEdgePrivateBlock k i)) := by
  rw [cyclePathPrivate_label, cycleControlELabels_private_iff]
  exact cyclePath_finish_private_label_ne k i

theorem cycleControlELabels_closingFirstPrivate (k : ℕ) :
    cycleControlELabels
      (cycleBlockLabel k (cycleClosingFirst k))
      (cycleBlockLabel k (cycleClosingPrivateBlock k)) := by
  simp [cycleClosingFirst_label, cycleClosingPrivate_label,
    cycleControlELabels]

theorem cycleControlELabels_closingFirstLast_neg (k : ℕ) :
    ¬ cycleControlELabels
      (cycleBlockLabel k (cycleClosingFirst k))
      (cycleBlockLabel k (cycleClosingLast k)) := by
  simp [cycleClosingFirst_label, cycleClosingLast_label,
    cycleControlELabels]

theorem cycleControlELabels_closingLastPrivate_neg (k : ℕ) :
    ¬ cycleControlELabels
      (cycleBlockLabel k (cycleClosingLast k))
      (cycleBlockLabel k (cycleClosingPrivateBlock k)) := by
  simp [cycleClosingLast_label, cycleClosingPrivate_label,
    cycleControlELabels]

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
