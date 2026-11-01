import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import PartiteConstruction.Functional.WholeMaskWeakRelativeCompletionObstruction2019
import PartiteConstruction.Functional.PartialSetFunctionsPartPredicates2019

/-!
# Track C: a class-relative obstruction at an exact weak local test

This is an existential, CLASS-relative version of the domain-mask toy
obstruction. The intrinsic one-vertex whole-fibre weak restriction has a
FULL part-preserving genuine functional embedding into an H-member, where
H is the class of all-undefined unary structures.

Its AMBIENT-induced tagged OLD test, on the SAME one-vertex carrier,
has NO induced-closed relative completion into ANY member of H.
The source ambient graph records the positive F-domain at vertex zero
even though the intrinsic weak function becomes undefined.

This is a counterexample to an automatic transfer of *individual*
intrinsic local H-completion certificates to ambient OLD certificates.
It is NOT a refutation of the complete 2019 locally finite CLASS axiom:
that axiom additionally restricts the full U-closed candidate C and
its U-closed irreducible substructures. In particular, this lemma
does not prove that a candidate satisfying the complete antecedent
contains this test. No proof of the global local-axiom implication is
claimed, and the manuscript prose is not changed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

private def unaryS : Set (Fin 2) := {(0 : Fin 2)}

/-- The class of original genuine partial unary structures with
    undefined F on every input. Relations and finite target carrier
    are not part of this predicate. -/
def allUndefinedUnaryH :
    GenuinePartite2019Class (L := exampleLanguage) (Parts := Fin 2) :=
  fun {X} (Target : PartialSetStructure exampleLanguage X)
      (_ : X → Fin 2) =>
    ∀ xs : Fin 1 → X, Target.func () xs = none

/-- The exact ambient-induced OLD weak test, with closure tags.
The underlying carrier is literally S={0}, not its generated hull. -/
private def unaryAmbientTaggedTest :
    RelStructure
      ((exampleLanguage.withParts (Fin 2)).wholeMaskTagLanguage (Fin 2))
      unaryS :=
  (wholeMaskTagExpansion
    (withPartsWholeMaskOld weakDomainUnaryToy (fun x : Fin 2 => x))).induce unaryS

/-- Intrinsically, the original whole-weak restriction to S={0}
has a genuine FULL part-preserving completion in the class H. -/
theorem allUndefinedUnaryH_has_intrinsicWeakCompletion :
    ∃ (X : Type) (_ : Finite X)
      (Target : PartialSetStructure exampleLanguage X)
      (partTarget : X → Fin 2),
      allUndefinedUnaryH Target partTarget ∧
      FibreTransversal Target partTarget ∧
      ∃ e : PartialSetStructure.Embedding
          (wholeWeakInduce weakDomainUnaryToy unaryS) Target,
        ∀ x : unaryS, partTarget (e.toFun x) = x.1 := by
  refine ⟨Unit, inferInstance, undefinedExample,
    (fun _ : Unit => (0 : Fin 2)), ?_, ?_, ?_⟩
  · intro xs
    rfl
  · intro F xs U hValue y hy z hz hp
    cases hValue
  · refine ⟨weakDomainUnaryToy_fullWeakToUndefined, ?_⟩
    intro x
    exact (Set.mem_singleton_iff.mp x.2).symm

/-- No member of H, not even on a larger carrier, can receive an OLD
ambient-relative completion map from the SAME tagged weak test. The
proof uses the retained positive domain mask and applies for every
finite target and every vertex map. -/
theorem allUndefinedUnaryH_no_ambientRelativeCompletion :
    ¬ HasGenuinePartiteTagged2019RelativeCompletion
        allUndefinedUnaryH unaryAmbientTaggedTest := by
  rintro ⟨X, hX, Target, partTarget, hH, hTr, _, f, hf⟩
  letI : Finite X := hX
  let partSource : Fin 2 → Fin 2 := id
  have hTrSource :
      FibreTransversal (weakDomainUnaryToy.withParts partSource)
        partSource :=
    (weakDomainUnaryToy.withParts_fibreTransversal_iff partSource).mpr
      weakDomainUnaryToy_transversal
  have hTrTarget :
      FibreTransversal (Target.withParts partTarget) partTarget :=
    (Target.withParts_fibreTransversal_iff partTarget).mpr hTr
  have hOld :
      ((withPartsWholeMaskOld weakDomainUnaryToy partSource).induce
        unaryS).IsHomomorphism
      (withPartsWholeMaskOld Target partTarget) f := by
    intro R ys hRel
    exact hf.1 (.inl R) ys hRel
  let xs : Fin 1 → unaryS :=
    fun _ => ⟨(0 : Fin 2), by simp [unaryS]⟩
  have hSourceDefined :
      (weakDomainUnaryToy.withParts partSource).Defined
        (ULift.up ()) (Subtype.val ∘ xs) := by
    change ∃ U : Set (Fin 2),
      weakDomainUnaryToy.func () (Subtype.val ∘ xs) = some U
    refine ⟨{(1 : Fin 2)}, ?_⟩
    exact weakDomainUnaryToy_value
  have hTargetDefined :
      (Target.withParts partTarget).Defined
        (ULift.up ()) (f ∘ xs) :=
    oldInducedHom_target_defined_of_ambient_defined
      (weakDomainUnaryToy.withParts partSource)
      partSource hTrSource unaryS
      (Target.withParts partTarget) partTarget hTrTarget
      f hOld (ULift.up ()) xs hSourceDefined
  obtain ⟨U, hU⟩ := hTargetDefined
  change Target.func () (f ∘ xs) = some U at hU
  rw [hH (f ∘ xs)] at hU
  cases hU

/-- Existential counterexample for a SINGLE exact weak local test.
No same-target hypothesis is hidden: the second component excludes
every H target. -/
theorem allUndefinedUnaryH_intrinsic_not_ambient :
    (∃ (X : Type) (_ : Finite X)
      (Target : PartialSetStructure exampleLanguage X)
      (partTarget : X → Fin 2),
      allUndefinedUnaryH Target partTarget ∧
      FibreTransversal Target partTarget ∧
      ∃ e : PartialSetStructure.Embedding
          (wholeWeakInduce weakDomainUnaryToy unaryS) Target,
        ∀ x : unaryS, partTarget (e.toFun x) = x.1) ∧
    ¬ HasGenuinePartiteTagged2019RelativeCompletion
        allUndefinedUnaryH unaryAmbientTaggedTest :=
  ⟨allUndefinedUnaryH_has_intrinsicWeakCompletion,
   allUndefinedUnaryH_no_ambientRelativeCompletion⟩

end AllThoseRamseyClasses.Published
