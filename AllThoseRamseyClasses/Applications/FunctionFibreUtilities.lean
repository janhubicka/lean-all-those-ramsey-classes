import PartiteConstruction.Ramsey.FreeAmalgamationFunctions
import Mathlib.Tactic

/-!
# Reusable full-functional embedding and finite amalgam utilities

The pointed-equivalence and m-unary-function applications both use exact
equality of the entire output fibre under a FULL functional embedding.

The generic facts are simply about images of sets:
* a singleton output in the target must have a unique source preimage;
* a singleton output in the source stays a singleton;
* a carrier covered by images of two finite amalgamation sides is finite.

The first two results apply equally to multi-arity set-valued functions,
including empty-input (nullary) functions, because no arity assumption
occurs in their statements. They do NOT hold for merely positive
function-graph homomorphisms without full image equality.
-/

namespace AllThoseRamseyClasses.Applications.FunctionFibreUtilities

universe u v w

/-- Exact image equality and injectivity reflect a singleton target fibre
to a uniquely determined singleton source fibre. -/
theorem singleton_pullback_of_image
    {U : Type u} {V : Type v}
    (f : U → V) (hf : Function.Injective f)
    {S : Set U} {T : Set V}
    (hImage : f '' S = T) (b : V) (hT : T = {b}) :
    ∃ a : U, S = {a} ∧ f a = b := by
  have hb : b ∈ f '' S := by
    rw [hImage, hT]
    exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨a, ha, hea⟩ := hb
  refine ⟨a, ?_, hea⟩
  ext z
  constructor
  · intro hz
    have hez : f z ∈ T := by
      rw [← hImage]
      exact ⟨z, hz, rfl⟩
    rw [hT] at hez
    exact Set.mem_singleton_iff.mpr
      (hf ((Set.mem_singleton_iff.mp hez).trans hea.symm))
  · intro hz
    have hza : z = a := Set.mem_singleton_iff.mp hz
    subst z
    exact ha

/-- Exact image equality transports a source singleton to the target.
Injectivity is not necessary in this direction. -/
theorem singleton_map_of_image
    {U : Type u} {V : Type v}
    (f : U → V) {S : Set U} {T : Set V}
    (hImage : f '' S = T) (a : U) (hS : S = {a}) :
    T = {f a} := by
  calc
    T = f '' S := hImage.symm
    _ = f '' {a} := by rw [hS]
    _ = {f a} := by simp

/-- Finite amalgamation sides cover a finite full target whenever every
target vertex comes from one side. Independent of relations and functions. -/
theorem finite_of_two_image_cover
    {A : Type u} {B : Type v} {C : Type w}
    [Finite A] [Finite B]
    (iA : A → C) (iB : B → C)
    (hCover : ∀ x : C,
      (∃ a : A, x = iA a) ∨ (∃ b : B, x = iB b)) :
    Finite C := by
  apply Finite.of_surjective
    (fun z : A ⊕ B => Sum.elim iA iB z)
  intro x
  rcases hCover x with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨Sum.inl a, ha.symm⟩
  · exact ⟨Sum.inr b, hb.symm⟩

end AllThoseRamseyClasses.Applications.FunctionFibreUtilities
