import AllThoseRamseyClasses.PublicAPI

/-!
# Worked application blueprint: discharge every class hypothesis explicitly

This file is intended for researchers instantiating the corrected 2019
multiamalgamation theorem in a new relational language. It is compiled
alongside all project modules by GitHub Actions.

No target class or class hypothesis is *assumed to be valid*: the inputs
below list the exact separate obligations a new application must prove.
The theorem then builds the actual paper-style class record and uses
the **proved**, unrestricted corrected relational Theorem 2.18.

In particular, the local implication ranges over every ORIGINAL
induced weak subset on at most the preselected n(B,C0) vertices.
The ambient Ramsey control C0 need not be intrinsically U-closed.
This is a reusable template, not a proof of any class's hypotheses.
-/

namespace AllThoseRamseyClasses.Examples

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

universe u v
variable {L : RelLanguage.{u}}

/-- Assemble an application from the separate fields and apply the
proved theorem. All fields are explicit, including the often
overlooked isomorphism-invariance and exact local-completion axiom. -/
theorem ramsey_of_checked_class_fields
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hAmbient : FiniteRamseyClass R)
    (hAmbientIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hSubset : ∀ {X : Type v} (C : RelStructure L X),
      K C → R C)
    (hFinite : ∀ {X : Type v} (C : RelStructure L X),
      K C → Finite X)
    (hClosed : ∀ {X : Type v} (C : RelStructure L X),
      K C → IsUClosed rules C)
    (hHereditary : InducedClosed2019Hereditary K rules)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hLocal : ∀ {X Y : Type v} [Finite X] [Finite Y]
      (B : RelStructure L X) (C0 : RelStructure L Y),
      K B → R C0 →
      ∃ n : ℕ, InducedClosedULocalCompletionAt K rules B C0 n)
    (hIso : IsomorphismClosed2019 K) :
    FiniteRamseyClass K := by
  have hInduced : InducedClosed2019MultiamalgamationClass R K rules := by
    refine {
      subset := hSubset
      finite := hFinite
      closed := hClosed
      hereditary := hHereditary
      strong := hStrong
      localCompletion := ?_
    }
    intro X Y hFiniteX hFiniteY B C0 hB hC0
    exact hLocal B C0 hB hC0
  have hClass : IsCoordinated2019MultiamalgamationClass R K rules :=
    ⟨hInduced, hIso⟩
  exact coordinated2019_ramsey_by_profile_sparsening (L := L)
    R K rules hAmbient hAmbientIrred hClass

/-- A second convenient form: the coordinated hypothesis is
exactly the complete paper-style record (plus explicit isomorphism
invariance), and the theorem does not demand any constructor lemma. -/
theorem ramsey_of_coordinated_hypothesis
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hAmbient : FiniteRamseyClass R)
    (hAmbientIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hClass : IsCoordinated2019MultiamalgamationClass R K rules) :
    FiniteRamseyClass K :=
  coordinated2019_ramsey_by_profile_sparsening (L := L)
    R K rules hAmbient hAmbientIrred hClass

end AllThoseRamseyClasses.Examples
