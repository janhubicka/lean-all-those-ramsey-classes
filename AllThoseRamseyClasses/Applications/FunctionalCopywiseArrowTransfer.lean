import PartiteConstruction.Ramsey.CopywiseRamseyTransfer
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-!
# A reusable copywise Ramsey-arrow transfer across different languages

In applications which encode relational structures in a functional auxiliary
language (notably the totally ordered incidence construction), the difficult
task is to construct the full source/target copy maps and show that canonical
lifting commutes with forgetting an auxiliary copy.

The finite Ramsey colouring step itself is independent of either language,
of closure rules, and of the particular encoding:

* all auxiliary A⁺-copies can be projected to real original A-copies;
* all auxiliary B⁺-copies can be projected to real original B-copies;
* each original A -> B embedding lifts to a full auxiliary A⁺ -> B⁺ embedding;
* projection commutes with these B/A embedding compositions.

This theorem proves the actual Ramsey arrow, not just a combinatorial
schematic assertion, from precisely these four interfaces. It avoids any
invalid demand that every original A-copy in the decoded target be liftable
to an auxiliary copy; only the images inside the selected B-copy matter.
-/

namespace AllThoseRamseyClasses.Applications

open StructuralRamsey

universe u₁ u₂ v

/-- Transfer an actual functional auxiliary Ramsey arrow to a relational
Ramsey arrow using full copywise projections and canonical source lifts.
The underlying vertex maps commute on all original source vertices.

No finite-carrier or nonempty-colour assumption is needed ONCE the
auxiliary arrow is already given; those belong to its existence theorem. -/
theorem arrow_of_functional_copy_projection
    {L : RelLanguage.{u₁}} {M : Language.{u₂}}
    {U V X P Q R : Type v}
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L X}
    {Aplus : Structure M P} {Bplus : Structure M Q}
    {C : Structure M R}
    {κ : Type*}
    (projectA : Structure.Embedding Aplus C → RelStructure.Embedding A D)
    (projectB : Structure.Embedding Bplus C → RelStructure.Embedding B D)
    (lift : RelStructure.Embedding A B → Structure.Embedding Aplus Bplus)
    (hCompose :
      ∀ (b : Structure.Embedding Bplus C)
        (a : RelStructure.Embedding A B)
        (x : U),
        projectA (b.comp (lift a)) x = projectB b (a x))
    (hAux : Structure.Arrow Aplus Bplus C κ) :
    StructuralRamsey.Arrow A B D κ := by
  classical
  intro χ
  let pullColour : Structure.Embedding Aplus C → κ :=
    fun e => χ (projectA e)
  obtain ⟨b, hb⟩ := hAux pullColour
  refine ⟨projectB b, ?_⟩
  intro a₁ a₂
  have hComp₁ : projectA (b.comp (lift a₁)) =
      (projectB b).comp a₁ := by
    apply RelStructure.Embedding.ext
    intro x
    exact hCompose b a₁ x
  have hComp₂ : projectA (b.comp (lift a₂)) =
      (projectB b).comp a₂ := by
    apply RelStructure.Embedding.ext
    intro x
    exact hCompose b a₂ x
  calc
    χ ((projectB b).comp a₁) =
        pullColour (b.comp (lift a₁)) := by
          simp only [pullColour, hComp₁]
    _ = pullColour (b.comp (lift a₂)) := hb (lift a₁) (lift a₂)
    _ = χ ((projectB b).comp a₂) := by
          simp only [pullColour, hComp₂]

end AllThoseRamseyClasses.Applications
