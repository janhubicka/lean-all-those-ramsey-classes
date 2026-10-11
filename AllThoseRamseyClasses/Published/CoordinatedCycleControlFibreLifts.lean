import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetReflection
import AllThoseRamseyClasses.Published.CoordinatedCycleProtectedReduction
import Mathlib.Tactic

/-!
# Turn finite control fibres into genuine induced B0 gadgets

A gadget is a three-block support with six vertices. To prove it is
an induced B0 copy, it is enough to:
  1. select six vertices by a map f : Fin 6 -> CycleVertex k;
  2. show that they occur inside that single gadget;
  3. exhibit an existing induced control template B0 -> C0 and
     show its control image is exactly the image of f;
  4. show EVERY vertex of the three-block gadget has its control
     value inside that fixed template.

The last condition is only SURJECTIVITY OF CONTROL VALUES, not a
direct construction of the inverse of f. If the C0 block labels are
distinct on the gadget, the control projection is injective there,
and the required inverse follows automatically.

This file proves the complete logical bridge. The uniform finite
control-fibre lifts and block-label injectivity are separately
displayed obligations (not axioms or silent assumptions).
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Distinct labels of gadget blocks make the actual
ten-vertex control projection injective on that gadget. -/
theorem cycle_control_injective_on_gadget
    (k : ℕ) (g : CycleGadget k)
    (hLabels : CycleGadgetLabelInjective k g)
    (x y : CycleVertex k)
    (hx : cycleGadgetContains k g x.1)
    (hy : cycleGadgetContains k g y.1)
    (hxy : cycleControlVertex k x = cycleControlVertex k y) :
    x = y := by
  rcases x with ⟨a, i⟩
  rcases y with ⟨b, j⟩
  have hv := congrArg (fun z : Fin 10 => z.val) hxy
  change 2 * cycleBlockLabel k a + i.val =
      2 * cycleBlockLabel k b + j.val at hv
  have hLabel : cycleBlockLabel k a = cycleBlockLabel k b := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hab : a = b := hLabels a b hx hy hLabel
  subst b
  have hij : i = j := Fin.ext (by omega)
  subst j
  rfl

/-- The remaining concrete arithmetic obligation: every gadget
comes with one control B0 embedding and six supported vertices
covering precisely the control values in that gadget. -/
def CycleGadgetControlFibreLifts (k : ℕ) : Prop :=
  ∀ g : CycleGadget k,
    ∃ (v : Embedding CycleBaseB0 CycleControlC0)
      (f : Fin 6 → CycleVertex k),
      (∀ b : Fin 6, cycleGadgetContains k g (f b).1) ∧
      (∀ b : Fin 6, cycleControlVertex k (f b) = v b) ∧
      (∀ x : CycleVertex k,
        cycleGadgetContains k g x.1 →
          ∃ b : Fin 6, cycleControlVertex k x = v b)

/-- Finite control-value witnesses and injectivity on each gadget
construct the *actual* induced B0 templates covering every vertex
of each gadget. Full E, order, and M relation reflection follows
from the already verified gadget-reflection theorem. -/
theorem cycle_inducedTemplates_of_controlFibreLifts
    (k : ℕ)
    (hLabels : ∀ g : CycleGadget k,
      CycleGadgetLabelInjective k g)
    (hLifts : CycleGadgetControlFibreLifts k) :
    CycleInducedGadgetTemplates k := by
  classical
  intro g
  obtain ⟨v, f, hIn, hProj, hAll⟩ := hLifts g
  have hf : Function.Injective f := by
    intro x y h
    apply v.injective
    calc
      v x = cycleControlVertex k (f x) := (hProj x).symm
      _ = cycleControlVertex k (f y) := congrArg _ h
      _ = v y := hProj y
  let u : Embedding CycleBaseB0 (cycleGadgetWitness k) :=
    cycleGadgetEmbedding_of_controlTemplate
      k g (hLabels g) f hf hIn v hProj
  refine ⟨u, v, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb⟩ := hAll x hx
    refine ⟨b, ?_⟩
    change f b = x
    apply cycle_control_injective_on_gadget k g
      (hLabels g) (f b) x (hIn b) hx
    exact (hProj b).trans hb.symm
  · intro b
    exact hProj b

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
