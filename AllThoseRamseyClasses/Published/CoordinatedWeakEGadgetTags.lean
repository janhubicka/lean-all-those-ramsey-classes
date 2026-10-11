import AllThoseRamseyClasses.Published.CoordinatedWeakPairedCompletionTarget
import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetPositions
import AllThoseRamseyClasses.Published.CoordinatedCycleInternalGap
import Mathlib.Tactic

/-!
# Concrete E-component tags on the long-cycle gadgets

The finite K-target D(k,S) is defined for every exact weak S.
This file computes its class tags on the three blocks of each
path gadget and on the special closing T block.

The start/finish matching blocks of a path gadget share the same
completed E-class whenever S touches the START block: this is the
only positive cross-block E tuple in an ordinary path gadget.
Every edge-private D block has its own E-class distinct from
every backbone E-class, exactly preserving the negative E pairs.
The closing T block shares the first backbone component.

The remaining proof packages these equalities into full E relation
reflection for EVERY protected pair inside a common gadget.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The first backbone block of an edge gadget has the
gap-count E-class tag of its natural index i. -/
theorem cycleWeakEClass_pathStart (k : ℕ)
    (S : Finset (CycleVertex k))
    (i : Fin (cycleBackboneCount k - 1))
    (bit : Fin 2) :
    cycleWeakEClass k S (cyclePathStart k i,bit) =
      (0,cycleGapCount (cycleWeakPresentBlocks k S) i.val) := by
  have hi := i.isLt
  have hlt : i.val < cycleBackboneCount k := by omega
  change (if i.val < cycleBackboneCount k then
      (0,cycleGapCount (cycleWeakPresentBlocks k S) i.val)
    else if i.val = cycleBlockCount k - 1 then (0,0)
    else (1,i.val)) = _
  simp [hlt]

/-- The second backbone block of an edge gadget has the next
gap-count component label. -/
theorem cycleWeakEClass_pathFinish (k : ℕ)
    (S : Finset (CycleVertex k))
    (i : Fin (cycleBackboneCount k - 1))
    (bit : Fin 2) :
    cycleWeakEClass k S (cyclePathFinish k i,bit) =
      (0,cycleGapCount (cycleWeakPresentBlocks k S) (i.val+1)) := by
  have hi := i.isLt
  have hlt : i.val + 1 < cycleBackboneCount k := by
    simp only [cycleBackboneCount] at *
    omega
  change (if i.val + 1 < cycleBackboneCount k then
      (0,cycleGapCount (cycleWeakPresentBlocks k S) (i.val+1))
    else if i.val + 1 = cycleBlockCount k - 1 then (0,0)
    else (1,i.val+1)) = _
  simp [hlt]

/-- An edge-private D block receives a fresh E-class,
even when its gadget's two backbone blocks are present. -/
theorem cycleWeakEClass_pathPrivate (k : ℕ)
    (S : Finset (CycleVertex k))
    (i : Fin (cycleBackboneCount k - 1))
    (bit : Fin 2) :
    cycleWeakEClass k S (cycleEdgePrivateBlock k i,bit) =
      (1,cycleBackboneCount k + i.val) := by
  have hi := i.isLt
  have hlt : ¬ cycleBackboneCount k + i.val <
      cycleBackboneCount k := by omega
  have hlast : cycleBackboneCount k + i.val ≠
      cycleBlockCount k - 1 := by
    simp only [cycleBackboneCount, cycleBlockCount] at *
    omega
  change (if cycleBackboneCount k + i.val < cycleBackboneCount k then
      (0,cycleGapCount (cycleWeakPresentBlocks k S)
        (cycleBackboneCount k + i.val))
    else if cycleBackboneCount k + i.val = cycleBlockCount k - 1 then
      (0,0) else (1,cycleBackboneCount k+i.val)) = _
  simp [hlt, hlast]

/-- The closing T block has precisely class (0,0), matching the
first backbone block even if the first backbone block is absent. -/
theorem cycleWeakEClass_closingPrivate (k : ℕ)
    (S : Finset (CycleVertex k)) (bit : Fin 2) :
    cycleWeakEClass k S (cycleClosingPrivateBlock k,bit) =
      (0,0) := by
  have hlt : ¬ (cycleBlockCount k - 1 < cycleBackboneCount k) := by
    simp only [cycleBlockCount,cycleBackboneCount]
    omega
  change (if cycleBlockCount k - 1 < cycleBackboneCount k then
      (0,cycleGapCount (cycleWeakPresentBlocks k S)
        (cycleBlockCount k - 1))
    else if cycleBlockCount k - 1 = cycleBlockCount k - 1 then
      (0,0) else (1,cycleBlockCount k - 1)) = _
  simp [hlt]

/-- A positive E-edge along a path is preserved in D(k,S)
whenever its first backbone block occurs in the weak test. -/
theorem cycleWeakCandidate_path_backbone_E_positive
    (k : ℕ) (S : Finset (CycleVertex k))
    (i : Fin (cycleBackboneCount k - 1))
    (a b : Fin 2)
    (hPresent : ∃ bit : Fin 2, (cyclePathStart k i,bit) ∈ S) :
    edge (cycleWeakCandidate k S) .equiv
      (cyclePathStart k i,a) (cyclePathFinish k i,b) := by
  obtain ⟨bit,hIn⟩ := hPresent
  have hMem : i.val ∈ cycleWeakPresentBlocks k S := by
    have h := Finset.mem_image.mpr
      (show ∃ v : CycleVertex k,
        v ∈ S ∧ v.1.val = i.val from
        ⟨(cyclePathStart k i,bit),hIn,rfl⟩)
    exact h
  change cycleWeakEClass k S (cyclePathStart k i,a) =
      cycleWeakEClass k S (cyclePathFinish k i,b)
  rw [cycleWeakEClass_pathStart,cycleWeakEClass_pathFinish]
  exact congrArg (fun v : ℕ => (0,v))
    (cycleGapCount_succ_of_mem (cycleWeakPresentBlocks k S) i.val hMem).symm

/-- A path gadget's private D block stays E-inequivalent to its
first backbone block in every weak target. -/
theorem cycleWeakCandidate_path_first_private_E_negative
    (k : ℕ) (S : Finset (CycleVertex k))
    (i : Fin (cycleBackboneCount k - 1))
    (a b : Fin 2) :
    ¬ edge (cycleWeakCandidate k S) .equiv
      (cyclePathStart k i,a) (cycleEdgePrivateBlock k i,b) := by
  intro h
  change cycleWeakEClass k S (cyclePathStart k i,a) =
      cycleWeakEClass k S (cycleEdgePrivateBlock k i,b) at h
  rw [cycleWeakEClass_pathStart,cycleWeakEClass_pathPrivate] at h
  cases h

/-- And to the second backbone block. -/
theorem cycleWeakCandidate_path_second_private_E_negative
    (k : ℕ) (S : Finset (CycleVertex k))
    (i : Fin (cycleBackboneCount k - 1))
    (a b : Fin 2) :
    ¬ edge (cycleWeakCandidate k S) .equiv
      (cyclePathFinish k i,a) (cycleEdgePrivateBlock k i,b) := by
  intro h
  change cycleWeakEClass k S (cyclePathFinish k i,a) =
      cycleWeakEClass k S (cycleEdgePrivateBlock k i,b) at h
  rw [cycleWeakEClass_pathFinish,cycleWeakEClass_pathPrivate] at h
  cases h

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
