import AllThoseRamseyClasses.Published.CoordinatedGadgetLabelInjectivity
import AllThoseRamseyClasses.Published.CoordinatedCycleControlTemplates
import Mathlib.Tactic

/-!
# Exact control fibres of each installed long-cycle B0 gadget

To lift a fixed induced B0 control template, it is enough to prove
that the C0-control image of the three matching blocks coincides
with the range of one of the three fixed Fin6->Fin10 embeddings.

Each matched pair gives exactly the two C0 vertices belonging to
its label. This finite-fibre principle reduces all later surjectivity
proofs to THREE NATURAL-NUMBER BLOCK LABELS.

This file proves the basic fibre lemma, the control-range reduction,
and decidable ranges of A/B/D, B/C/D and A/T/C templates. The
uniform matching of these ranges with each gadget's three labels
is the next module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The two vertices of an actual matching block map exactly to the
two vertices of the identically labelled matching block of C0. -/
theorem cycle_pair_fibre_iff (k : ℕ)
    (b : CycleBlock k) (z : Fin 10) :
    (∃ j : Fin 2, cycleControlVertex k (b,j) = z) ↔
      z.val / 2 = cycleBlockLabel k b := by
  constructor
  · rintro ⟨j, hj⟩
    have hval := congrArg (fun a : Fin 10 => a.val) hj
    change 2 * cycleBlockLabel k b + j.val = z.val at hval
    have hjLt := j.isLt
    omega
  · intro hz
    let j : Fin 2 := ⟨z.val % 2, Nat.mod_lt _ (by omega)⟩
    refine ⟨j, Fin.ext ?_⟩
    change 2 * cycleBlockLabel k b + z.val % 2 = z.val
    omega

/-- General gadget control range is determined exactly by the
three natural-number labels of its matching blocks. -/
theorem cycle_gadget_controlRange_iff (k : ℕ)
    (g : CycleGadget k) (z : Fin 10) :
    (∃ x : CycleVertex k,
      cycleGadgetContains k g x.1 ∧ cycleControlVertex k x = z) ↔
    (∃ b : CycleBlock k,
      cycleGadgetContains k g b ∧
      cycleBlockLabel k b = z.val / 2) := by
  constructor
  · rintro ⟨⟨b,j⟩, hb, hz⟩
    exact ⟨b,hb,((cycle_pair_fibre_iff k b z).mp ⟨j,hz⟩).symm⟩
  · rintro ⟨b,hb,hlabel⟩
    obtain ⟨j,hj⟩ := (cycle_pair_fibre_iff k b z).mpr hlabel.symm
    exact ⟨(b,j),hb,hj⟩

/-- Exactly the A, B and D control vertices form the range
of the ABD embedded B0 template. -/
theorem controlABD_range_iff (z : Fin 10) :
    (∃ b : Fin 6, controlABDFun b = z) ↔
      (z.val / 2 = 0 ∨ z.val / 2 = 1 ∨ z.val / 2 = 4) := by
  fin_cases z <;> decide

/-- Exactly the B, C and D control vertices form the
range of the BCD embedded B0 template. -/
theorem controlBCD_range_iff (z : Fin 10) :
    (∃ b : Fin 6, controlBCDFun b = z) ↔
      (z.val / 2 = 1 ∨ z.val / 2 = 3 ∨ z.val / 2 = 4) := by
  fin_cases z <;> decide

/-- Exactly the A, T and C control vertices form the
range of the closing ATC embedded B0 template. -/
theorem controlATC_range_iff (z : Fin 10) :
    (∃ b : Fin 6, controlATCFun b = z) ↔
      (z.val / 2 = 0 ∨ z.val / 2 = 2 ∨ z.val / 2 = 3) := by
  fin_cases z <;> decide

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
