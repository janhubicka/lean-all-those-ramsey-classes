import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import Mathlib.Tactic

/-!
# Concrete three-block positions of each installed B0 gadget

This is the first step toward proving that all installed copies are
induced B0 embeddings, rather than relying on an informal picture.

The i-th path gadget contains two consecutive distinct backbone blocks
and its unique private D block. The closing gadget contains first and
last backbone blocks and its unique private T block.

All the assertions are uniform in the cutoff parameter k.
The relative vertex order and full B0 relation reflections are the
next stage; neither is assumed here.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The first backbone block of a path gadget. -/
def cyclePathStart (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    CycleBlock k :=
  ⟨i.val, by
    have hi := i.isLt
    simp only [cycleBackboneCount, cycleBlockCount] at *
    omega⟩

/-- The next backbone block of a path gadget. -/
def cyclePathFinish (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    CycleBlock k :=
  ⟨i.val + 1, by
    have hi := i.isLt
    simp only [cycleBackboneCount, cycleBlockCount] at *
    omega⟩

theorem cyclePathStart_in_gadget
    (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    cycleGadgetContains k (.inl i) (cyclePathStart k i) := by
  left
  rfl

theorem cyclePathFinish_in_gadget
    (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    cycleGadgetContains k (.inl i) (cyclePathFinish k i) := by
  right
  left
  rfl

theorem cyclePathPrivate_in_gadget
    (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    cycleGadgetContains k (.inl i) (cycleEdgePrivateBlock k i) := by
  right
  right
  rfl

/-- The path-gadget endpoints are genuinely distinct blocks. -/
theorem cyclePathStart_ne_finish
    (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    cyclePathStart k i ≠ cyclePathFinish k i := by
  intro h
  have hval := congrArg (fun b : CycleBlock k => b.val) h
  change i.val = i.val + 1 at hval
  omega

/-- Private D-blocks have strictly larger indices than the two
adjacent backbone blocks. -/
theorem cyclePathFinish_lt_private
    (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    (cyclePathFinish k i).val < (cycleEdgePrivateBlock k i).val := by
  change i.val + 1 < cycleBackboneCount k + i.val
  simp only [cycleBackboneCount]
  omega

theorem cyclePathStart_lt_private
    (k : ℕ) (i : Fin (cycleBackboneCount k - 1)) :
    (cyclePathStart k i).val < (cycleEdgePrivateBlock k i).val := by
  change i.val < cycleBackboneCount k + i.val
  simp only [cycleBackboneCount]
  omega

/-- First/last backbone blocks in the special closing gadget. -/
def cycleClosingFirst (k : ℕ) : CycleBlock k :=
  ⟨0, by simp only [cycleBlockCount]; omega⟩

def cycleClosingLast (k : ℕ) : CycleBlock k :=
  ⟨cycleBackboneCount k - 1, by
    simp only [cycleBackboneCount, cycleBlockCount]
    omega⟩

theorem cycleClosingFirst_in_gadget (k : ℕ) :
    cycleGadgetContains k (.inr ()) (cycleClosingFirst k) := by
  left
  rfl

theorem cycleClosingLast_in_gadget (k : ℕ) :
    cycleGadgetContains k (.inr ()) (cycleClosingLast k) := by
  right
  left
  rfl

theorem cycleClosingPrivate_in_gadget (k : ℕ) :
    cycleGadgetContains k (.inr ()) (cycleClosingPrivateBlock k) := by
  right
  right
  rfl

theorem cycleClosingFirst_lt_last (k : ℕ) :
    (cycleClosingFirst k).val < (cycleClosingLast k).val := by
  change 0 < cycleBackboneCount k - 1
  simp only [cycleBackboneCount]
  omega

theorem cycleClosingLast_lt_private (k : ℕ) :
    (cycleClosingLast k).val <
      (cycleClosingPrivateBlock k).val := by
  change cycleBackboneCount k - 1 < cycleBlockCount k - 1
  simp only [cycleBackboneCount, cycleBlockCount]
  omega

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
