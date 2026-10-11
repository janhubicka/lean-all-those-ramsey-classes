import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import AllThoseRamseyClasses.Published.FinitePairedClass
import Mathlib.Tactic

/-!
# Exact smallest E-cycle regression for the partial gadget structure

For k=0 the backbone has five matching blocks. Its induced partial
relations carry four positive consecutive E-links but do not relate
the first and third, nor the first and final backbone block.
In particular, the witness is genuinely NOT in the transitive
paired-equivalence class K. The complete small-test and B0-copywise
arguments remain uniform higher-k obligations, not inferred from
these finite computations.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

private abbrev witnessBlockVertex (i : Fin 5) : CycleVertex 0 :=
  (⟨i.val, by
    have hi := i.isLt
    simp only [cycleBlockCount]
    omega⟩, 0)

/-- The k=0 finite source has the intended positive backbone E-path,
while the endpoints are E-negative. -/
theorem cycleGadgetWitness_zero_path :
    edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 0) (witnessBlockVertex 1) ∧
    edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 1) (witnessBlockVertex 2) ∧
    edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 2) (witnessBlockVertex 3) ∧
    edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 3) (witnessBlockVertex 4) ∧
    ¬ edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 0) (witnessBlockVertex 4) := by
  decide

/-- E in the witness already violates transitivity on the first
three backbone blocks. This demonstrates that the U-closed witness
should NOT be treated as a genuine K-member. -/
theorem cycleGadgetWitness_zero_not_pairedClass :
    ¬ pairedClass (cycleGadgetWitness 0) := by
  intro hK
  have h01 : edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 0) (witnessBlockVertex 1) :=
    cycleGadgetWitness_zero_path.1
  have h12 : edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 1) (witnessBlockVertex 2) :=
    cycleGadgetWitness_zero_path.2.1
  have h02 : ¬ edge (cycleGadgetWitness 0) .equiv
      (witnessBlockVertex 0) (witnessBlockVertex 2) := by
    decide
  exact h02 (hK.equiv.trans h01 h12)

theorem cycleGadgetWitness_zero_not_K :
    ¬ finitePairedClass (cycleGadgetWitness 0) := by
  intro h
  exact cycleGadgetWitness_zero_not_pairedClass h.2

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
