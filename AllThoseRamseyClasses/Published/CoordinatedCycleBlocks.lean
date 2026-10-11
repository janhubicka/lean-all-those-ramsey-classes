import AllThoseRamseyClasses.Published.CoordinatedCycleFixtures
import Mathlib.Tactic

/-!
# Finite carriers and fixed-control labels for the long E-cycle family

The coordinated 2019 correction requires a failure of local
finiteness at EVERY cutoff. For k>=0 put m=2k+5, an odd backbone
length > 4. The witness has:
* m backbone matching blocks b_0,...,b_(m-1);
* m-1 private edge-gadget matching blocks t_i;
* 1 closing matching block t_*.

There are 2m=4k+10 blocks, hence 4m=8k+20 vertices.
Labels in the fixed control C0 are A=0, B=1, T=2, C=3, D=4.

This module establishes the UNBOUNDED finite carriers, block labels,
and projection of each vertex into the fixed ten-vertex control.
It does not assert that the full relational C_k witness satisfies
the repaired local axioms: its gadget relations and local completion
proofs remain separate tasks.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Odd backbone length, large when k is large. -/
def cycleBackboneCount (k : ℕ) : ℕ := 2 * k + 5

/-- Backbone blocks, edge-private gadget blocks, and the closing
private block constitute exactly twice the backbone count. -/
def cycleBlockCount (k : ℕ) : ℕ := 4 * k + 10

abbrev CycleBlock (k : ℕ) := Fin (cycleBlockCount k)
abbrev CycleVertex (k : ℕ) := CycleBlock k × Fin 2

/-- The i-th backbone block at its natural block index. -/
def cycleBackboneBlock (k : ℕ)
    (i : Fin (cycleBackboneCount k)) : CycleBlock k :=
  ⟨i.val, by
    have hi := i.isLt
    simp only [cycleBackboneCount, cycleBlockCount] at *
    omega⟩

/-- A separate private D block for each backbone edge. -/
def cycleEdgePrivateBlock (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) : CycleBlock k :=
  ⟨cycleBackboneCount k + i.val, by
    have hi := i.isLt
    simp only [cycleBackboneCount, cycleBlockCount] at *
    omega⟩

/-- The private T block appears only in the closing gadget. -/
def cycleClosingPrivateBlock (k : ℕ) : CycleBlock k :=
  ⟨cycleBlockCount k - 1, by
    simp only [cycleBlockCount]
    omega⟩

/-- Block types in the fixed control C0. The final backbone
vertex gets label C; earlier backbone labels alternate A,B;
all edge-private blocks are D and the closing private one is T. -/
def cycleBlockLabel (k : ℕ) (b : CycleBlock k) : ℕ :=
  if b.val < cycleBackboneCount k then
    if b.val = cycleBackboneCount k - 1 then 3
    else if b.val % 2 = 0 then 0 else 1
  else if b.val = cycleBlockCount k - 1 then 2
  else 4

theorem cycleBlockLabel_lt_five
    (k : ℕ) (b : CycleBlock k) :
    cycleBlockLabel k b < 5 := by
  unfold cycleBlockLabel
  split_ifs <;> omega

/-- Each matched vertex projects to the corresponding root/output
of its labelled block in the concrete fixed control C0. -/
def cycleControlVertex (k : ℕ)
    (v : CycleVertex k) : Fin 10 :=
  ⟨2 * cycleBlockLabel k v.1 + v.2.val, by
    have hb := cycleBlockLabel_lt_five k v.1
    have hv := v.2.isLt
    omega⟩

/-- The fixed-label projection respects the two distinct vertices
in each matched pair. -/
theorem cycleControlVertex_pair_distinct
    (k : ℕ) (b : CycleBlock k) :
    cycleControlVertex k (b, 0) ≠
      cycleControlVertex k (b, 1) := by
  intro he
  have h := congrArg Fin.val he
  change 2 * cycleBlockLabel k b + 0 =
    2 * cycleBlockLabel k b + 1 at h
  omega

/-- Every backbone length is odd and at least five. -/
theorem cycleBackboneCount_odd (k : ℕ) :
    cycleBackboneCount k % 2 = 1 := by
  simp only [cycleBackboneCount]
  omega

theorem cycleBackboneCount_ge_five (k : ℕ) :
    5 ≤ cycleBackboneCount k := by
  simp only [cycleBackboneCount]
  omega

/-- Every finite cycle has exactly twice as many matching blocks as
backbone vertices: one private gadget block for each backbone block. -/
theorem cycleBlockCount_twice (k : ℕ) :
    cycleBlockCount k = 2 * cycleBackboneCount k := by
  simp only [cycleBlockCount, cycleBackboneCount]
  omega

/-- Distinct backbone indices have distinct matching blocks. -/
theorem cycleBackboneBlock_injective (k : ℕ) :
    Function.Injective (cycleBackboneBlock k) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (fun b : CycleBlock k => b.val) hij
  simpa only [cycleBackboneBlock] using h

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
