import AllThoseRamseyClasses.Published.CoordinatedCycleControlRanges
import AllThoseRamseyClasses.Published.CoordinatedCycleControlFibreLifts
import AllThoseRamseyClasses.Published.CoordinatedClosedGadgetCoverage
import Mathlib.Tactic

/-!
# Uniform actual B0 copies for every Ck gadget

The fixed control offers exactly three six-vertex induced B0 templates:
  A,B,D for all ordinary path gadgets,
  B,C,D for the final path gadget,
  A,T,C for the closing gadget.
Their ranges are exactly the three control block labels supported by
the corresponding gadget, including the last edge B-C-D.

This file identifies the exact control range of EVERY gadget, chooses
one representative of each of its six control values, and uses the
already-checked fibre-lifting theorem to obtain actual induced
B0 copies inside each Ck. Consequently the coordinated closed-test
premises (4a) and (4b) become UNCONDITIONAL for each Ck.

The weak n-vertex completion premise (4c) and the global path/closing
copywise obstruction are separate remaining obligations.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Every block label in the i-th path gadget is one of precisely
its start, finish, and private block labels. -/
private theorem cyclePath_supported_label_iff (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) (q : ℕ) :
    (∃ b : CycleBlock k,
      cycleGadgetContains k (.inl i) b ∧ cycleBlockLabel k b = q) ↔
    (cycleBlockLabel k (cyclePathStart k i) = q ∨
     cycleBlockLabel k (cyclePathFinish k i) = q ∨
     cycleBlockLabel k (cycleEdgePrivateBlock k i) = q) := by
  constructor
  · rintro ⟨b,hb,hl⟩
    rcases cyclePath_gadget_block_cases k i b hb with h | h | h
    · left
      simpa only [h] using hl
    · right
      left
      simpa only [h] using hl
    · right
      right
      simpa only [h] using hl
  · rintro (h | h | h)
    · exact ⟨cyclePathStart k i, cyclePathStart_in_gadget k i, h⟩
    · exact ⟨cyclePathFinish k i, cyclePathFinish_in_gadget k i, h⟩
    · exact ⟨cycleEdgePrivateBlock k i,
        cyclePathPrivate_in_gadget k i, h⟩

/-- Every path gadget is either AB(D) or the final BC(D).
The parity of the path starting block only swaps the first two
blocks; it does not change its set of control labels. -/
theorem cyclePath_gadget_label_profile (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) (q : ℕ) :
    (∃ b : CycleBlock k,
      cycleGadgetContains k (.inl i) b ∧ cycleBlockLabel k b = q) ↔
    (if i.val + 1 = cycleBackboneCount k - 1 then
      q = 1 ∨ q = 3 ∨ q = 4
     else q = 0 ∨ q = 1 ∨ q = 4) := by
  rw [cyclePath_supported_label_iff,
    cyclePathStart_label, cyclePathFinish_label,
    cyclePathPrivate_label]
  by_cases hLast : i.val + 1 = cycleBackboneCount k - 1
  · have hiOdd : i.val % 2 = 1 := by
      simp only [cycleBackboneCount] at hLast
      omega
    simp [hLast, hiOdd, eq_comm]
  · have hParity : i.val % 2 = 0 ∨ i.val % 2 = 1 := by
      omega
    rcases hParity with heven | hodd
    · have hNext : (i.val + 1) % 2 = 1 := by omega
      simp [hLast, heven, hNext, eq_comm, or_comm]
    · have hNext : (i.val + 1) % 2 = 0 := by omega
      simp [hLast, hodd, hNext, eq_comm, or_comm]

private theorem cycleClosing_supported_label_iff (k : ℕ) (q : ℕ) :
    (∃ b : CycleBlock k,
      cycleGadgetContains k (.inr ()) b ∧ cycleBlockLabel k b = q) ↔
    (cycleBlockLabel k (cycleClosingFirst k) = q ∨
     cycleBlockLabel k (cycleClosingLast k) = q ∨
     cycleBlockLabel k (cycleClosingPrivateBlock k) = q) := by
  constructor
  · rintro ⟨b,hb,hl⟩
    rcases cycleClosing_gadget_block_cases k b hb with h | h | h
    · left
      simpa only [h] using hl
    · right
      left
      simpa only [h] using hl
    · right
      right
      simpa only [h] using hl
  · rintro (h | h | h)
    · exact ⟨cycleClosingFirst k, cycleClosingFirst_in_gadget k, h⟩
    · exact ⟨cycleClosingLast k, cycleClosingLast_in_gadget k, h⟩
    · exact ⟨cycleClosingPrivateBlock k,
        cycleClosingPrivate_in_gadget k, h⟩

/-- The special closing triangle has exactly the labels A,T,C. -/
theorem cycleClosing_gadget_label_profile (k : ℕ) (q : ℕ) :
    (∃ b : CycleBlock k,
      cycleGadgetContains k (.inr ()) b ∧ cycleBlockLabel k b = q) ↔
      (q = 0 ∨ q = 2 ∨ q = 3) := by
  rw [cycleClosing_supported_label_iff,
    cycleClosingFirst_label, cycleClosingLast_label,
    cycleClosingPrivate_label]
  constructor
  · rintro (h | h | h) <;> omega
  · rintro (h | h | h) <;> omega

/-- EVERY installed Ck gadget has exactly the image of one of
the verified induced B0→C0 control embeddings. -/
theorem cycle_gadgetControlRange_matches_B0 (k : ℕ) :
    ∀ g : CycleGadget k,
      ∃ v : Embedding CycleBaseB0 CycleControlC0,
        ∀ z : Fin 10,
          (∃ x : CycleVertex k,
            cycleGadgetContains k g x.1 ∧
            cycleControlVertex k x = z) ↔
          (∃ b : Fin 6, v b = z) := by
  intro g
  cases g with
  | inl i =>
      by_cases hLast : i.val + 1 = cycleBackboneCount k - 1
      · refine ⟨controlBCDEmbedding, ?_⟩
        intro z
        rw [cycle_gadget_controlRange_iff,
          cyclePath_gadget_label_profile k i (z.val / 2)]
        simpa [hLast, eq_comm] using (controlBCD_range_iff z).symm
      · refine ⟨controlABDEmbedding, ?_⟩
        intro z
        rw [cycle_gadget_controlRange_iff,
          cyclePath_gadget_label_profile k i (z.val / 2)]
        simpa [hLast, eq_comm] using (controlABD_range_iff z).symm
  | inr _ =>
      refine ⟨controlATCEmbedding, ?_⟩
      intro z
      rw [cycle_gadget_controlRange_iff,
        cycleClosing_gadget_label_profile k (z.val / 2)]
      simpa [eq_comm] using (controlATC_range_iff z).symm

/-- Construct the actual six-vertex control fibres by choosing
a preimage in a gadget for every template vertex. Exact control
range equality supplies both directions of the required coverage. -/
theorem cycle_gadgetControlFibreLifts (k : ℕ) :
    CycleGadgetControlFibreLifts k := by
  classical
  intro g
  obtain ⟨v,hRange⟩ := cycle_gadgetControlRange_matches_B0 k g
  have hPre (b : Fin 6) :
      ∃ x : CycleVertex k,
        cycleGadgetContains k g x.1 ∧
        cycleControlVertex k x = v b :=
    (hRange (v b)).mpr ⟨b,rfl⟩
  let f : Fin 6 → CycleVertex k := fun b => Classical.choose (hPre b)
  have hIn : ∀ b, cycleGadgetContains k g (f b).1 :=
    fun b => (Classical.choose_spec (hPre b)).1
  have hProj : ∀ b, cycleControlVertex k (f b) = v b :=
    fun b => (Classical.choose_spec (hPre b)).2
  refine ⟨v,f,hIn,hProj,?_⟩
  intro x hx
  obtain ⟨b,hb⟩ := (hRange (cycleControlVertex k x)).mp
    ⟨x,hx,rfl⟩
  exact ⟨b,hb.symm⟩

/-- Genuine induced B0-copy inside each long-cycle gadget,
including all six support vertices and exact relation reflection. -/
theorem cycle_inducedGadgetTemplates (k : ℕ) :
    CycleInducedGadgetTemplates k :=
  cycle_inducedTemplates_of_controlFibreLifts k
    (fun g a b ha hb hl =>
      cycleGadget_blockLabel_injective k g a b ha hb hl)
    (cycle_gadgetControlFibreLifts k)

/-- Coordinated Definition 2.17(4b) holds for every Ck:
EVERY closed intrinsic U-irreducible test is a valid K member. -/
theorem cycleGadgetWitness_closedUIrreduciblesIn (k : ℕ) :
    ClosedUIrreduciblesIn finitePairedClass mateRules
      (cycleGadgetWitness k) :=
  cycle_closedUIrreduciblesIn_of_induced_gadgets
    k (cycle_inducedGadgetTemplates k)

/-- Coordinated Definition 2.17(4a) also holds for every Ck:
its full positive control homomorphism restricts to an embedding
of every closed intrinsic U-irreducible test. -/
theorem cycleGadgetWitness_control_closedEmbedding (k : ℕ) :
    IsClosedUHomomorphismEmbedding mateRules
      (cycleGadgetWitness k) CycleControlC0
      (cycleControlVertex k) :=
  cycle_control_closedUHomomorphismEmbedding_of_induced_gadgets
    k (cycle_inducedGadgetTemplates k)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
