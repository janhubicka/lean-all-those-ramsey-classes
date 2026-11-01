import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedIntrinsicLocalTransfer
import PartiteConstruction.Functional.WholeMaskWeakDomainUnaryExample2019

/-!
# Track C: total unary H has no full completion of a nonclosed weak test

Even in an original genuine partial function class H with TOTAL
unary definedness, its canonical U-closed tagged candidates can have
a genuinely nonclosed one-vertex whole-weak restriction. After
dropping an external output the weak unary operation is undefined.

No full genuine partial-function embedding of that intrinsic weak
test can exist into ANY target of H, because full embeddings reflect
undefined operation states. This is independent of which target or
vertex map is chosen and does not rely on a malformed OLD graph.

This file also proves that the original totality property is
hereditary under genuine full function-closed restrictions, so the
result is consistent with the actual hereditary class convention.
The full corrected (4b) coverage and ambient positive completion
tests are handled separately.

This is a regression against silently replacing canonical closed
OLD protected tests by ALL intrinsic whole-weak irreducible tests.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

private def totalS : Set (Fin 2) := {(0 : Fin 2)}

/-- All genuinely partial unary structures where the operation is
actually defined at EVERY vertex. The function's finite output set
is unrestricted; a value of some empty is still defined. -/
def totalUnaryPartiteH :
    GenuinePartite2019Class (L := exampleLanguage) (Parts := Fin 2) :=
  fun {X} (A : PartialSetStructure exampleLanguage X) _ =>
    ∀ xs : Fin 1 → X, ∃ U : Set X, A.func () xs = some U

/-- A two-point member: 0 maps to the external point 1, and 1
has a genuinely defined-empty value. Each vertex is its own part. -/
def totalUnaryToy :
    PartialSetStructure exampleLanguage (Fin 2) where
  rel := fun R => Empty.elim R
  func := fun _ xs =>
    if xs (0 : Fin 1) = (0 : Fin 2)
    then some ({(1 : Fin 2)} : Set (Fin 2))
    else some ∅

theorem totalUnaryToy_mem :
    totalUnaryPartiteH totalUnaryToy (fun x : Fin 2 => x) := by
  intro xs
  by_cases h : xs 0 = (0 : Fin 2)
  · exact ⟨{(1 : Fin 2)}, by simp [totalUnaryToy, h]⟩
  · exact ⟨∅, by simp [totalUnaryToy, h]⟩

theorem totalUnaryToy_transversal :
    FibreTransversal totalUnaryToy (fun x : Fin 2 => x) := by
  intro F xs U hValue y hy z hz hPart
  exact hPart

/-- Every total unary H-member stays total on a GENUINELY closed
restriction. No ordinary weak restriction is assumed to be closed. -/
theorem totalUnaryPartiteH_closedHereditary :
    GenuinePartiteClosedHereditary2019 totalUnaryPartiteH := by
  intro X hX A part hTotal S hS xs
  obtain ⟨U, hU⟩ := hTotal (Subtype.val ∘ xs)
  refine ⟨{y : S | y.1 ∈ U}, ?_⟩
  change
    (A.func () (Subtype.val ∘ xs)).map
      (fun T => {y : S | y.1 ∈ T}) =
      some {y : S | y.1 ∈ U}
  rw [hU]
  rfl

private theorem totalUnaryToy_value :
    totalUnaryToy.func () (fun _ : Fin 1 => (0 : Fin 2)) =
      some ({(1 : Fin 2)} : Set (Fin 2)) := rfl

/-- The singleton intrinsic whole-fibre weak test loses definedness
of F(0), because the entire value {1} lies outside S={0}. -/
theorem totalUnaryToy_singleton_weak_undefined :
    (wholeWeakInduce totalUnaryToy totalS).func ()
      (fun _ : Fin 1 => (⟨0, by simp [totalS]⟩ : totalS)) = none := by
  change wholeWeakValue totalS
    (totalUnaryToy.func ()
      (fun _ : Fin 1 => (0 : Fin 2))) = none
  rw [totalUnaryToy_value]
  exact wholeWeakValue_of_not_subset totalS {(1 : Fin 2)}
    weakDomainUnaryToy_lost

/-- An intrinsic weak singleton of a canonical ORIGINAL H-member
has no full genuine function embedding into ANY H target, whether
or not the proposed target is finite or part-transversal. -/
theorem totalUnaryToy_singleton_no_full_H_completion
    {X : Type}
    (Target : PartialSetStructure exampleLanguage X)
    (partTarget : X → Fin 2)
    (hH : totalUnaryPartiteH Target partTarget) :
    ¬ Nonempty
      (PartialSetStructure.Embedding
        (wholeWeakInduce totalUnaryToy totalS) Target) := by
  rintro ⟨e⟩
  let xs : Fin 1 → totalS :=
    fun _ => ⟨(0 : Fin 2), by simp [totalS]⟩
  have hWeakNone :
      (wholeWeakInduce totalUnaryToy totalS).func () xs = none :=
    totalUnaryToy_singleton_weak_undefined
  have hNone : Target.func () (e.toFun ∘ xs) = none := by
    have he := e.map_func () xs
    rw [hWeakNone] at he
    simpa only [Option.map_none] using he.symm
  obtain ⟨U, hU⟩ := hH (e.toFun ∘ xs)
  rw [hNone] at hU
  cases hU

end AllThoseRamseyClasses.Published
