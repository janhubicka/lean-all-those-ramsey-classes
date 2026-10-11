import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import AllThoseRamseyClasses.Published.CoordinatedCycleFixtures
import Mathlib.Tactic

/-!
# Induced reflection on each individual supported gadget

The source C_k is obtained by restricting the pullback of the
nontransitive fixed ten-vertex control C0 to pairs of blocks
sharing an installed gadget. Therefore positive E and < reflect
EXACTLY on any one gadget, without checking global E transitivity
or completeness of < in the source.

The M relation is independent of block-support, and its reflection
requires a separate elementary hypothesis: *distinct matching blocks
in the gadget have distinct C0 labels*. The proof below derives
mate reflection from label injectivity using the two-bit structure.

Finally, any injective six-vertex map into one gadget whose
composition with the C0 projection is an induced B0->C0 map
is itself an induced B0->C_k embedding.

No hypothesis below is silently asserted for arbitrary C_k:
gadgetwise label injectivity and the concrete six-vertex maps
will be discharged by subsequent parametric arithmetic lemmas.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Pairwise distinct C0 block labels on the actual three-block
support of a gadget, the only auxiliary condition for M reflection. -/
def CycleGadgetLabelInjective (k : ℕ) (g : CycleGadget k) : Prop :=
  ∀ a b : CycleBlock k,
    cycleGadgetContains k g a →
    cycleGadgetContains k g b →
    cycleBlockLabel k a = cycleBlockLabel k b → a = b

/-- Every two vertices of one installed gadget are related by the
underlying block-support relation. -/
theorem cycleRelatedBlocks_of_common_gadget (k : ℕ)
    (g : CycleGadget k) (x y : CycleVertex k)
    (hx : cycleGadgetContains k g x.1)
    (hy : cycleGadgetContains k g y.1) :
    cycleRelatedBlocks k x.1 y.1 :=
  Or.inr ⟨g, hx, hy⟩

/-- The real E relation of C_k is the induced pullback of C0
on any prescribed gadget. Both positive and NEGATIVE E reflect. -/
theorem cycleGadgetWitness_E_iff_control_of_common_gadget
    (k : ℕ) (g : CycleGadget k) (x y : CycleVertex k)
    (hx : cycleGadgetContains k g x.1)
    (hy : cycleGadgetContains k g y.1) :
    edge (cycleGadgetWitness k) .equiv x y ↔
      edge CycleControlC0 .equiv
        (cycleControlVertex k x) (cycleControlVertex k y) := by
  change (cycleRelatedBlocks k x.1 y.1 ∧
      edge CycleControlC0 .equiv
        (cycleControlVertex k x) (cycleControlVertex k y)) ↔ _
  exact and_iff_right (cycleRelatedBlocks_of_common_gadget k g x y hx hy)

/-- The same exact reflection holds for the named order on a
single gadget, even though the global C_k order is incomplete. -/
theorem cycleGadgetWitness_lt_iff_control_of_common_gadget
    (k : ℕ) (g : CycleGadget k) (x y : CycleVertex k)
    (hx : cycleGadgetContains k g x.1)
    (hy : cycleGadgetContains k g y.1) :
    edge (cycleGadgetWitness k) .lt x y ↔
      edge CycleControlC0 .lt
        (cycleControlVertex k x) (cycleControlVertex k y) := by
  change (cycleRelatedBlocks k x.1 y.1 ∧
      edge CycleControlC0 .lt
        (cycleControlVertex k x) (cycleControlVertex k y)) ↔ _
  exact and_iff_right (cycleRelatedBlocks_of_common_gadget k g x y hx hy)

/-- An induced mate tuple in the control C0 determines the SAME
matching block in C_k, provided gadget block labels are distinct. -/
theorem cycleGadgetWitness_M_iff_control_of_common_gadget
    (k : ℕ) (g : CycleGadget k)
    (hLabels : CycleGadgetLabelInjective k g)
    (x y : CycleVertex k)
    (hx : cycleGadgetContains k g x.1)
    (hy : cycleGadgetContains k g y.1) :
    edge (cycleGadgetWitness k) .mate x y ↔
      edge CycleControlC0 .mate
        (cycleControlVertex k x) (cycleControlVertex k y) := by
  constructor
  · rcases x with ⟨a, i⟩
    rcases y with ⟨b, j⟩
    intro h
    change cycleMatching k (a, i) (b, j) at h
    obtain ⟨hab, hij⟩ := h
    change a = b at hab
    change i ≠ j at hij
    subst b
    change ((2 * cycleBlockLabel k a + i.val) / 2 =
        (2 * cycleBlockLabel k a + j.val) / 2) ∧
        (cycleControlVertex k (a,i) ≠ cycleControlVertex k (a,j))
    constructor
    · have hi := i.isLt
      have hj := j.isLt
      omega
    · intro he
      apply hij
      apply Fin.ext
      have hval := congrArg (fun z : Fin 10 => z.val) he
      change 2 * cycleBlockLabel k a + i.val =
        2 * cycleBlockLabel k a + j.val at hval
      exact Nat.add_left_cancel hval
  · rcases x with ⟨a, i⟩
    rcases y with ⟨b, j⟩
    intro h
    change ((2 * cycleBlockLabel k a + i.val) / 2 =
        (2 * cycleBlockLabel k b + j.val) / 2) ∧
        (cycleControlVertex k (a,i) ≠ cycleControlVertex k (b,j)) at h
    have hLabelsEqual : cycleBlockLabel k a = cycleBlockLabel k b := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    have hab : a = b := hLabels a b hx hy hLabelsEqual
    subst b
    change cycleMatching k (a,i) (a,j)
    constructor
    · rfl
    · intro hij
      apply h.2
      exact congrArg (fun z : Fin 2 => cycleControlVertex k (a,z)) hij

/-- Uniform induced relation reflection on ALL THREE symbols
inside any gadget whose block labels are pairwise distinct. -/
theorem cycleGadgetWitness_rel_iff_control_of_common_gadget
    (k : ℕ) (g : CycleGadget k)
    (hLabels : CycleGadgetLabelInjective k g)
    (R : Symbol) (x y : CycleVertex k)
    (hx : cycleGadgetContains k g x.1)
    (hy : cycleGadgetContains k g y.1) :
    edge (cycleGadgetWitness k) R x y ↔
      edge CycleControlC0 R
        (cycleControlVertex k x) (cycleControlVertex k y) := by
  cases R with
  | lt =>
      exact cycleGadgetWitness_lt_iff_control_of_common_gadget k g x y hx hy
  | equiv =>
      exact cycleGadgetWitness_E_iff_control_of_common_gadget k g x y hx hy
  | mate =>
      exact cycleGadgetWitness_M_iff_control_of_common_gadget
        k g hLabels x y hx hy

/-- Lift any concrete fixed-control B0 template to a GENUINE
induced B0 copy of the actual C_k, provided its six images
lie in one gadget, their labels are distinct between blocks,
and the projection agrees with the template. -/
def cycleGadgetEmbedding_of_controlTemplate
    (k : ℕ) (g : CycleGadget k)
    (hLabels : CycleGadgetLabelInjective k g)
    (f : Fin 6 → CycleVertex k)
    (hf : Function.Injective f)
    (hIn : ∀ x : Fin 6, cycleGadgetContains k g (f x).1)
    (v : Embedding CycleBaseB0 CycleControlC0)
    (hProj : ∀ x : Fin 6, cycleControlVertex k (f x) = v x) :
    Embedding CycleBaseB0 (cycleGadgetWitness k) where
  toFun := f
  injective := hf
  map_rel_iff := by
    intro R t
    have hSupported :=
      cycleGadgetWitness_rel_iff_control_of_common_gadget
        k g hLabels R (f (t 0)) (f (t 1))
        (hIn (t 0)) (hIn (t 1))
    have hControl := v.map_rel_iff R t
    have htup : t = ![t 0, t 1] := by
      funext i
      fin_cases i <;> rfl
    rw [htup] at hControl ⊢
    change edge (cycleGadgetWitness k) R (f (t 0)) (f (t 1)) ↔
      edge CycleBaseB0 R (t 0) (t 1)
    rw [hSupported]
    change edge CycleControlC0 R
        (cycleControlVertex k (f (t 0)))
        (cycleControlVertex k (f (t 1))) ↔
      edge CycleBaseB0 R (t 0) (t 1)
    rw [hProj (t 0), hProj (t 1)]
    exact hControl

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
