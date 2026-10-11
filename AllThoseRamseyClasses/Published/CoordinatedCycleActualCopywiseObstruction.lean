import AllThoseRamseyClasses.Published.CoordinatedCycleConcreteB0Gadgets
import AllThoseRamseyClasses.Published.PairedEquivalenceCycleObstruction
import Mathlib.Tactic

/-!
# Actual long-cycle B0-copywise non-completion

The long E-path source is now a concrete finite RelStructure C_k,
with actual induced B0 gadgets established in the preceding module.

All consecutive backbone matching blocks are positively E-related
inside their installed B0 edge gadget (labels AB, BA, or BC).
The special closing B0 gadget has NEGATIVE E between its
first and last backbone blocks (control labels A and C).

Since every genuine K target has transitive E, its copywise
completion would require these endpoints both E-related and
E-unrelated. This file supplies the final UNCONDITIONAL copywise
noncompletion for every k. It is independent of small-test
premise (4c), the only remaining antecedent for local nonfiniteness.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

private theorem cycleControlVertex_label_div_two (k : ℕ)
    (b : CycleBlock k) (i : Fin 2) :
    (cycleControlVertex k (b,i)).val / 2 =
      cycleBlockLabel k b := by
  change (2 * cycleBlockLabel k b + i.val) / 2 = _
  have hi := i.isLt
  omega

/-- The labels on consecutive path backbone blocks are AB, BA, or BC.
The last path edge has the BC pattern. -/
theorem cyclePath_backbone_control_E_positive (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) (a b : Fin 2) :
    edge CycleControlC0 .equiv
      (cycleControlVertex k (cyclePathStart k i,a))
      (cycleControlVertex k (cyclePathFinish k i,b)) := by
  have ha := cyclePathStart_label k i
  have hb := cyclePathFinish_label k i
  have hPairs :
      (cycleBlockLabel k (cyclePathStart k i) = 0 ∧
       cycleBlockLabel k (cyclePathFinish k i) = 1) ∨
      (cycleBlockLabel k (cyclePathStart k i) = 1 ∧
       cycleBlockLabel k (cyclePathFinish k i) = 0) ∨
      (cycleBlockLabel k (cyclePathStart k i) = 1 ∧
       cycleBlockLabel k (cyclePathFinish k i) = 3) := by
    rw [ha,hb]
    have hi := i.isLt
    have hm := cycleBackboneCount_ge_five k
    simp only [cycleBackboneCount] at *
    split_ifs <;> omega
  have hd0 := cycleControlVertex_label_div_two k (cyclePathStart k i) a
  have hd1 := cycleControlVertex_label_div_two k (cyclePathFinish k i) b
  change
    let q0 := (cycleControlVertex k (cyclePathStart k i,a)).val / 2
    let q1 := (cycleControlVertex k (cyclePathFinish k i,b)).val / 2
    q0 = q1 ∨
    (q0 = 0 ∧ q1 = 1) ∨ (q0 = 1 ∧ q1 = 0) ∨
    (q0 = 1 ∧ q1 = 3) ∨ (q0 = 3 ∧ q1 = 1) ∨
    (q0 = 0 ∧ q1 = 2) ∨ (q0 = 2 ∧ q1 = 0)
  dsimp
  rw [hd0,hd1]
  rcases hPairs with h01 | h10 | h13
  · exact Or.inr (Or.inl h01)
  · exact Or.inr (Or.inr (Or.inl h10))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h13)))

/-- Consecutive backbone blocks really have positive E in Ck,
for every choice of their matching-pair vertices. -/
theorem cycleGadgetWitness_path_backbone_E_positive (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) (a b : Fin 2) :
    edge (cycleGadgetWitness k) .equiv
      (cyclePathStart k i,a) (cyclePathFinish k i,b) := by
  constructor
  · exact Or.inr ⟨.inl i,
      cyclePathStart_in_gadget k i, cyclePathFinish_in_gadget k i⟩
  · exact cyclePath_backbone_control_E_positive k i a b

/-- The two backbone endpoints are NOT E-equivalent in the
closing gadget: their C0 labels are A=0 and C=3. -/
theorem cycleGadgetWitness_closing_backbone_E_negative (k : ℕ)
    (a b : Fin 2) :
    ¬ edge (cycleGadgetWitness k) .equiv
      (cycleClosingFirst k,a) (cycleClosingLast k,b) := by
  intro h
  have h0 := cycleControlVertex_label_div_two k (cycleClosingFirst k) a
  have h1 := cycleControlVertex_label_div_two k (cycleClosingLast k) b
  rw [cycleClosingFirst_label] at h0
  rw [cycleClosingLast_label] at h1
  have he := h.2
  change
    let q0 := (cycleControlVertex k (cycleClosingFirst k,a)).val / 2
    let q1 := (cycleControlVertex k (cycleClosingLast k,b)).val / 2
    q0 = q1 ∨
    (q0 = 0 ∧ q1 = 1) ∨ (q0 = 1 ∧ q1 = 0) ∨
    (q0 = 1 ∧ q1 = 3) ∨ (q0 = 3 ∧ q1 = 1) ∨
    (q0 = 0 ∧ q1 = 2) ∨ (q0 = 2 ∧ q1 = 0) at he
  dsimp at he
  rw [h0,h1] at he
  omega

/-- The representative of every backbone matching block, clamped
at the last valid backbone index for irrelevant arguments. -/
def cycleBackboneRepresentative (k : ℕ) (i : ℕ) :
    CycleVertex k :=
  (⟨min i (cycleBackboneCount k - 1), by
      have hm := cycleBackboneCount_ge_five k
      have hbc := cycleBlockCount_twice k
      omega⟩, (0 : Fin 2))

theorem cycleBackboneRepresentative_pathStart (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBackboneRepresentative k i.val =
      (cyclePathStart k i, (0 : Fin 2)) := by
  apply Prod.ext
  · apply Fin.ext
    have hi := i.isLt
    change min i.val (cycleBackboneCount k - 1) = i.val
    omega
  · rfl

theorem cycleBackboneRepresentative_pathFinish (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    cycleBackboneRepresentative k (i.val + 1) =
      (cyclePathFinish k i, (0 : Fin 2)) := by
  apply Prod.ext
  · apply Fin.ext
    have hi := i.isLt
    change min (i.val + 1) (cycleBackboneCount k - 1) = i.val + 1
    omega
  · rfl

theorem cycleBackboneRepresentative_first (k : ℕ) :
    cycleBackboneRepresentative k 0 =
      (cycleClosingFirst k, (0 : Fin 2)) := by
  apply Prod.ext
  · apply Fin.ext
    change min 0 (cycleBackboneCount k - 1) = 0
    omega
  · rfl

theorem cycleBackboneRepresentative_last (k : ℕ) :
    cycleBackboneRepresentative k (cycleBackboneCount k - 1) =
      (cycleClosingLast k, (0 : Fin 2)) := by
  apply Prod.ext
  · apply Fin.ext
    change min (cycleBackboneCount k - 1)
      (cycleBackboneCount k - 1) = cycleBackboneCount k - 1
    omega
  · rfl

/-- The real installed B0 copy on each path gadget witnesses
the required positive E edge, not merely a syntactic triple. -/
theorem cycleGadgetWitness_path_positiveCopyEdge (k : ℕ)
    (i : Fin (cycleBackboneCount k - 1)) :
    PositiveCopyEdge CycleBaseB0 (cycleGadgetWitness k)
      (cyclePathStart k i, (0 : Fin 2))
      (cyclePathFinish k i, (0 : Fin 2)) := by
  obtain ⟨u,v,hRange,hProj⟩ :=
    cycle_inducedGadgetTemplates k (.inl i)
  obtain ⟨a,ha⟩ := hRange
    (cyclePathStart k i, (0 : Fin 2))
    (cyclePathStart_in_gadget k i)
  obtain ⟨b,hb⟩ := hRange
    (cyclePathFinish k i, (0 : Fin 2))
    (cyclePathFinish_in_gadget k i)
  have hE : edge (cycleGadgetWitness k) .equiv (u a) (u b) := by
    rw [ha,hb]
    exact cycleGadgetWitness_path_backbone_E_positive k i 0 0
  have hEtup : (u ∘ ![a,b]) = ![u a,u b] := by
    funext j
    fin_cases j <;> rfl
  have hBE : edge CycleBaseB0 .equiv a b := by
    apply (u.map_rel_iff .equiv ![a,b]).mp
    rw [hEtup]
    exact hE
  exact ⟨u,a,b,hBE,ha,hb⟩

/-- The installed closing B0 copy forces NEGATIVE E on
the endpoints of the long positive backbone path. -/
theorem cycleGadgetWitness_closing_negativeCopyEdge (k : ℕ) :
    NegativeCopyEdge CycleBaseB0 (cycleGadgetWitness k)
      (cycleClosingFirst k, (0 : Fin 2))
      (cycleClosingLast k, (0 : Fin 2)) := by
  obtain ⟨u,v,hRange,hProj⟩ :=
    cycle_inducedGadgetTemplates k (.inr ())
  obtain ⟨a,ha⟩ := hRange
    (cycleClosingFirst k, (0 : Fin 2))
    (cycleClosingFirst_in_gadget k)
  obtain ⟨b,hb⟩ := hRange
    (cycleClosingLast k, (0 : Fin 2))
    (cycleClosingLast_in_gadget k)
  have hNotE : ¬ edge (cycleGadgetWitness k) .equiv (u a) (u b) := by
    rw [ha,hb]
    exact cycleGadgetWitness_closing_backbone_E_negative k 0 0
  have hEtup : (u ∘ ![a,b]) = ![u a,u b] := by
    funext j
    fin_cases j <;> rfl
  have hBN : ¬ edge CycleBaseB0 .equiv a b := by
    intro hBase
    apply hNotE
    have hh : (cycleGadgetWitness k).rel .equiv (u ∘ ![a,b]) :=
      (u.map_rel_iff .equiv ![a,b]).mpr hBase
    rw [hEtup] at hh
    exact hh
  exact ⟨u,a,b,hBN,ha,hb⟩

/-- The entire uniform positive B0 backbone chain. -/
theorem cycleGadgetWitness_positive_backbone_chain (k : ℕ) :
    ∀ i : ℕ, i < cycleBackboneCount k - 1 →
      PositiveCopyEdge CycleBaseB0 (cycleGadgetWitness k)
        (cycleBackboneRepresentative k i)
        (cycleBackboneRepresentative k (i + 1)) := by
  intro i hi
  let j : Fin (cycleBackboneCount k - 1) := ⟨i,hi⟩
  rw [cycleBackboneRepresentative_pathStart k j,
    cycleBackboneRepresentative_pathFinish k j]
  exact cycleGadgetWitness_path_positiveCopyEdge k j

/-- Full, unconditional nonexistence of a finite K-completion
respecting all genuine B0-copies of the actual relational Ck. -/
theorem cycleGadgetWitness_no_K_copywise_completion (k : ℕ) :
    ¬ HasCopywiseCompletion finitePairedClass CycleBaseB0
      (cycleGadgetWitness k) := by
  apply no_K_copywise_completion_of_E_cycle
    CycleBaseB0 (cycleGadgetWitness k)
    (cycleBackboneCount k - 1)
    (cycleBackboneRepresentative k)
  · exact cycleGadgetWitness_positive_backbone_chain k
  · rw [cycleBackboneRepresentative_first k,
      cycleBackboneRepresentative_last k]
    exact cycleGadgetWitness_closing_negativeCopyEdge k

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
