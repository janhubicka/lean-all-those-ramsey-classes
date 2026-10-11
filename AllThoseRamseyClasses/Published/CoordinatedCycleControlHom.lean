import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import Mathlib.Tactic

/-!
# The explicit cycle-to-control projection is a positive homomorphism

For the actual finite gadget sources, preserving E and < is
immediate from the support-restricted pullback definition.
Preserving matching requires checking that the two vertices
in each matched pair have the same C0 block label but do NOT
coincide in C0. This module proves all three relation cases,
and hence the FULL positive homomorphism condition of (4a).

This does NOT yet show the stronger closed-test induced-embedding
part of Definition 2.15's proposed coordinated repair.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Distinct vertices in one matching pair map to distinct members
of the same paired control block, giving a genuine M-tuple of C0. -/
theorem cycleGadgetWitness_M_projects
    (k : ℕ) (x y : CycleVertex k)
    (h : edge (cycleGadgetWitness k) .mate x y) :
    edge CycleControlC0 .mate
      (cycleControlVertex k x) (cycleControlVertex k y) := by
  rcases x with ⟨b, i⟩
  rcases y with ⟨c, j⟩
  change cycleMatching k (b, i) (c, j) at h
  obtain ⟨hb, hij⟩ := h
  subst c
  change ((2 * cycleBlockLabel k b + i.val) / 2 =
      (2 * cycleBlockLabel k b + j.val) / 2) ∧
      (cycleControlVertex k (b, i) ≠ cycleControlVertex k (b, j))
  constructor
  · have hi := i.isLt
    have hj := j.isLt
    omega
  · intro he
    have hvals := congrArg (fun z : Fin 10 => z.val) he
    change 2 * cycleBlockLabel k b + i.val =
      2 * cycleBlockLabel k b + j.val at hvals
    apply hij
    apply Fin.ext
    omega

/-- The control-label map is a genuine positive relational
homomorphism from C_k to C0, in the EXACT 2019 language.
Reflection on closed irreducible sources is a separate task. -/
theorem cycleGadgetWitness_control_homomorphism (k : ℕ) :
    (cycleGadgetWitness k).IsHomomorphism
      CycleControlC0 (cycleControlVertex k) := by
  intro R t ht
  have hSrc : edge (cycleGadgetWitness k) R (t 0) (t 1) := by
    change (cycleGadgetWitness k).rel R ![t 0, t 1]
    have htup : ![t 0, t 1] = t := by
      funext i
      fin_cases i <;> rfl
    rw [htup]
    exact ht
  have htup :
      (cycleControlVertex k ∘ t) =
      ![cycleControlVertex k (t 0), cycleControlVertex k (t 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [htup]
  cases R with
  | lt =>
      exact cycleGadgetWitness_order_projects k (t 0) (t 1) hSrc
  | equiv =>
      exact cycleGadgetWitness_E_projects k (t 0) (t 1) hSrc
  | mate =>
      exact cycleGadgetWitness_M_projects k (t 0) (t 1) hSrc

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
