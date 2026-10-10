import AllThoseRamseyClasses.Published.NamedOrderLanguage
import PartiteConstruction.Ramsey.EmptyClosureMultiamalgamation

/-!
# Ramsey property for the original finite ordered (<,E,M) class

This imports the VERIFIED general Ramsey theorem for all finite
ordered relational structures in an auxiliary language with two
unconstrained binary predicates E and M. The named symbol < in
the 2019 paper is IDENTICAL to the distinguished external order
in that theorem; no extra order is added to the class.

This is the final ambient-R hypothesis for the independent
paired-equivalence counterexample to the literal 2019 Theorem 2.18.
The separate strong-amalgamation property of K remains open.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Remove only the distinguished order symbol and retain both
E and M relations, including all absent tuples. -/
def auxiliaryReduct {V : Type} (C : RelStructure Lang V) :
    RelStructure AuxiliaryLanguage V where
  rel
    | false, t => C.rel .equiv t
    | true, t => C.rel .mate t

/-- The arbitrary E/M reduct plus its ORIGINAL extracted order
renames back to EXACTLY C: no new predicates, and no change to
positive or negative relation information. -/
theorem name_ordered_auxiliaryReduct_eq
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C) :
    nameExternal
      (@RelStructure.ordered AuxiliaryLanguage V
        (auxiliaryReduct C) (ambientLinearOrder C hC).toLT) = C := by
  letI : LinearOrder V := ambientLinearOrder C hC
  have hRel :
      (nameExternal ((auxiliaryReduct C).ordered)).rel = C.rel := by
    funext R t
    cases R with
    | lt =>
      change (t 0 < t 1) = C.rel .lt t
      have ht : (![t 0, t 1] : Fin 2 → V) = t := by
        funext i
        fin_cases i <;> rfl
      have heq :
          (t 0 < t 1) ↔ edge C .lt (t 0) (t 1) :=
        ambientLinearOrder_lt_iff C hC (t 0) (t 1)
      exact (propext heq).trans
        (congrArg (C.rel .lt) ht)
    | equiv => rfl
    | mate => rfl
  exact congrArg (fun rel =>
    (RelStructure.mk rel : RelStructure Lang V)) hRel

/-- The ambient class R, with three NAMED binary relations,
is a Ramsey class, using the checked ordered-relational theorem
and the explicit arrow-preserving language relabelling. -/
theorem orderedAmbient_isRamsey :
    FiniteRamseyClass orderedAmbientClass := by
  intro U V hU hV A B hA hB κ hκ hκNonempty
  letI : LinearOrder U := ambientLinearOrder A hA
  letI : LinearOrder V := ambientLinearOrder B hB
  let a : RelStructure AuxiliaryLanguage U := auxiliaryReduct A
  let b : RelStructure AuxiliaryLanguage V := auxiliaryReduct B
  obtain ⟨W, hW, o, c, hArrow⟩ :=
    StructuralRamsey.Partite.orderedRamsey a b κ
  letI : LinearOrder W := o
  let C : RelStructure Lang W := nameExternal c.ordered
  have hC : orderedAmbientClass C := by
    refine ⟨hW, ?_, ?_, ?_⟩
    · intro x hxx
      exact lt_irrefl x hxx
    · intro x y z hxy hyz
      exact lt_trans hxy hyz
    · intro x y hne
      exact lt_or_gt_of_ne hne
  have hName :
      StructuralRamsey.Arrow
        (nameExternal a.ordered)
        (nameExternal b.ordered) C κ :=
    arrow_nameExternal hArrow
  have hEqA : nameExternal a.ordered = A :=
    name_ordered_auxiliaryReduct_eq A hA
  have hEqB : nameExternal b.ordered = B :=
    name_ordered_auxiliaryReduct_eq B hB
  rw [hEqA, hEqB] at hName
  exact ⟨W, hW, C, hC, hName⟩

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
