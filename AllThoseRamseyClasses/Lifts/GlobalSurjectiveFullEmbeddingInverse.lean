import AllThoseRamseyClasses.Lifts.GlobalCountableTraceRepresentatives

/-!
# Track F: invert surjective FULL functional embeddings

The actual finite maximal-trace representative cover provides
surjective FULL embeddings from a labelled representative P
ONTO each finite age member Y. To transport finite cofinality
from P to Y in the fair Fraïssé chain we need the inverse
embedding, including COMPLETE value-set preservation for
partial and multivalued functions.

This theorem constructs the inverse of any surjective
`StructuralRamsey.Structure.Embedding` as another FULL
embedding. Unlike an arbitrary relational graph inverse,
it reflects all old and added relation tables AND maps
every entire function-value set onto the corresponding
target fibre. It includes nullary functions and relations,
repeated entries, empty/undefined fibres and multiple outputs.

No Fraïssé limit, arbitrary-source shadow avoidance,
or assumption of a weaker HE map is used here.
The numbered ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w

/-- A surjective FULL native functional embedding has a FULL
inverse embedding. Every relation and every complete function
fibre is preserved in both directions. -/
noncomputable def fullEmbeddingInverseOfSurjective
    {L : Language.{u}} {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : Structure.Embedding A B)
    (hOnto : Function.Surjective e) :
    Structure.Embedding B A := by
  classical
  let eqv : V ≃ W :=
    Equiv.ofBijective e ⟨e.injective, hOnto⟩
  refine {
    toFun := eqv.symm
    injective := eqv.symm.injective
    map_rel_iff := ?_
    map_func := ?_
  }
  · intro S xs
    have hTuple : e ∘ (eqv.symm ∘ xs) = xs := by
      funext i
      exact eqv.apply_symm_apply (xs i)
    have hRel := e.map_rel_iff S (eqv.symm ∘ xs)
    rw [hTuple] at hRel
    exact hRel.symm
  · intro S xs
    have hTuple : e ∘ (eqv.symm ∘ xs) = xs := by
      funext i
      exact eqv.apply_symm_apply (xs i)
    have hFibre := e.map_func S (eqv.symm ∘ xs)
    rw [hTuple] at hFibre
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hFibre] at hw
      obtain ⟨z, hz, hzw⟩ := hw
      have hInv : eqv.symm w = z := by
        rw [← hzw]
        exact eqv.symm_apply_apply z
      rwa [hInv]
    · intro hy
      refine ⟨e y, ?_, ?_⟩
      · have he :
            e y ∈ imageSet e (A.func S (eqv.symm ∘ xs)) :=
          ⟨y, hy, rfl⟩
        rwa [hFibre] at he
      · exact eqv.symm_apply_apply y

/-- The constructed inverse is a genuine two-sided inverse
on vertices; no weak map or non-full function transport is
used. This gives an actual FULL isomorphism between the two
functional structures rather than an image-quotient map. -/
theorem fullEmbeddingInverseOfSurjective_rightInverse
    {L : Language.{u}} {V : Type v} {W : Type w}
    {A : Structure L V} {B : Structure L W}
    (e : Structure.Embedding A B)
    (hOnto : Function.Surjective e)
    (y : W) :
    e (fullEmbeddingInverseOfSurjective e hOnto y) = y := by
  classical
  let eqv : V ≃ W :=
    Equiv.ofBijective e ⟨e.injective, hOnto⟩
  exact eqv.apply_symm_apply y

end AllThoseRamseyClasses.Lifts
