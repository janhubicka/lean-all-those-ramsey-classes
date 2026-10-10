import AllThoseRamseyClasses.Published.OrderedAmbient
import AllThoseRamseyClasses.Published.FinitePairedClass
import Mathlib.Tactic

/-!
# Concrete fixed B0 and C0 for the coordinated repaired local axiom

The proposed *closed-test* map plus closed (4b) modification should
exclude the paired-equivalence class by an all-cutoff E-cycle.

Its fixed B0 is THREE matched blocks of class pattern X,X,Y.
Its fixed finite control C0 uses five matched labels A,B,T,C,D
in that order. Positive cross-block E instances are AB, BC, AT;
E in C0 is deliberately NONTRANSITIVE. Every matching block
has its own internal M and E.

These finite objects and their elementary properties are fully
explicit, to avoid using an arbitrary control or an abstract oracle
when building the long-cycle witnesses C_n later.

This module makes no claim about existence of the C_n witnesses.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The fixed six-vertex B0: first two matching pairs E-equivalent;
the third matching pair lies in a second E-class. -/
abbrev CycleBaseB0 : RelStructure Lang (Fin 6) where
  rel
    | .lt, t => (t 0).val < (t 1).val
    | .equiv, t =>
        ((t 0).val / 2 = 2) ↔ ((t 1).val / 2 = 2)
    | .mate, t =>
        (t 0).val / 2 = (t 1).val / 2 ∧ t 0 ≠ t 1

private theorem cycleBase_mate_total :
    ∀ x : Fin 6, ∃! y : Fin 6,
      x.val / 2 = y.val / 2 ∧ x ≠ y := by
  intro x
  fin_cases x
  · refine ⟨1, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
  · refine ⟨0, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
  · refine ⟨3, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
  · refine ⟨2, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
  · refine ⟨5, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all
  · refine ⟨4, by decide, ?_⟩
    intro y hy
    fin_cases y <;> simp_all

/-- The fixed B0 is a FINITE member of K. -/
theorem CycleBaseB0_mem : finitePairedClass CycleBaseB0 := by
  constructor
  · infer_instance
  · constructor
    · decide
    · decide
    · decide
    · exact ⟨by decide, by decide, by decide⟩
    · decide
    · decide
    · exact cycleBase_mate_total
    · decide

/-- Internal pair-label numbers:
A=0, B=1, T=2, C=3, D=4.
Positive E cross-pair labels are precisely AB, BC and AT. -/
abbrev CycleControlC0 : RelStructure Lang (Fin 10) where
  rel
    | .lt, t => (t 0).val < (t 1).val
    | .equiv, t =>
        let a := (t 0).val / 2
        let b := (t 1).val / 2
        a = b ∨
        (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
        (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨
        (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)
    | .mate, t =>
        (t 0).val / 2 = (t 1).val / 2 ∧ t 0 ≠ t 1

/-- The original ambient Ramsey class allows this control:
E and M are unconstrained in R, while the named order is strict total. -/
theorem CycleControlC0_mem_ambient :
    orderedAmbientClass CycleControlC0 := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- The control deliberately violates E-transitivity:
A~B and B~C, but A is not equivalent to C.
The fixed control therefore is not itself a K-member. -/
theorem CycleControlC0_E_nontransitive :
    (edge CycleControlC0 .equiv (0 : Fin 10) 2) ∧
    (edge CycleControlC0 .equiv (2 : Fin 10) 6) ∧
    ¬ edge CycleControlC0 .equiv (0 : Fin 10) 6 := by
  decide

theorem CycleControlC0_not_K :
    ¬ finitePairedClass CycleControlC0 := by
  intro h
  obtain ⟨hAB,hBC,hNotAC⟩ :=
    CycleControlC0_E_nontransitive
  exact hNotAC (h.2.equiv.trans hAB hBC)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
