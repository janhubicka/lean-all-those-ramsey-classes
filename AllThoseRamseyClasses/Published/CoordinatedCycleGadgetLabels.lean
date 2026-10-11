import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetPositions
import Mathlib.Tactic

/-!
# The exact fixed-control label profile of each installed B0 gadget

An edge gadget always consists of two consecutive backbone blocks and
one private D block. The start label alternates A/B, the endpoint
label is B/A except at the final edge where it is C, and the private
label is D. The closing labels are exactly A,T,C in that order.

These formulae are the numerical input needed to order each gadget
canonically as an induced copy of the fixed B0, whose E-classes
have profile X,X,Y. No B0 embedding claim is asserted here.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

theorem cyclePathStart_label (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBlockLabel k (cyclePathStart k i) =
      (if i.val % 2 = 0 then 0 else 1) := by
  have hi := i.isLt
  have hfirst : i.val < cycleBackboneCount k := by omega
  have hlast : i.val ≠ cycleBackboneCount k - 1 := by omega
  simp [cycleBlockLabel, cyclePathStart, hfirst, hlast]

theorem cyclePathFinish_label (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBlockLabel k (cyclePathFinish k i) =
      if i.val + 1 = cycleBackboneCount k - 1 then 3
      else if (i.val + 1) % 2 = 0 then 0 else 1 := by
  have hi := i.isLt
  have hfirst : i.val + 1 < cycleBackboneCount k := by
    simp only [cycleBackboneCount] at *
    omega
  simp [cycleBlockLabel, cyclePathFinish, hfirst]

theorem cyclePathPrivate_label (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBlockLabel k (cycleEdgePrivateBlock k i) = 4 := by
  have hfirst :
      ¬ (cycleEdgePrivateBlock k i).val < cycleBackboneCount k := by
    change ¬ cycleBackboneCount k + i.val < cycleBackboneCount k
    omega
  have hlast :
      (cycleEdgePrivateBlock k i).val ≠ cycleBlockCount k - 1 := by
    change cycleBackboneCount k + i.val ≠ cycleBlockCount k - 1
    have hi := i.isLt
    simp only [cycleBackboneCount, cycleBlockCount] at *
    omega
  simp [cycleBlockLabel, hfirst, hlast]

theorem cycleClosingFirst_label (k : ℕ) :
    cycleBlockLabel k (cycleClosingFirst k) = 0 := by
  simp [cycleBlockLabel, cycleClosingFirst, cycleBackboneCount, cycleBlockCount]

theorem cycleClosingLast_label (k : ℕ) :
    cycleBlockLabel k (cycleClosingLast k) = 3 := by
  have hlt : cycleBackboneCount k - 1 < cycleBackboneCount k := by
    simp only [cycleBackboneCount]
    omega
  simp [cycleBlockLabel, cycleClosingLast, hlt]

theorem cycleClosingPrivate_label (k : ℕ) :
    cycleBlockLabel k (cycleClosingPrivateBlock k) = 2 := by
  have hfirst :
      ¬ (cycleClosingPrivateBlock k).val < cycleBackboneCount k := by
    change ¬ cycleBlockCount k - 1 < cycleBackboneCount k
    simp only [cycleBackboneCount, cycleBlockCount]
    omega
  simp [cycleBlockLabel, cycleClosingPrivateBlock, hfirst]

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
