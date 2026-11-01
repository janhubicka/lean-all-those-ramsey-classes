import AllThoseRamseyClasses.Lifts.FunctionalNestedReassociationReverse
import AllThoseRamseyClasses.Lifts.ActualNestedFunctionalProfileCongruence

/-!
# All-test congruence for nested FULL functional source diagrams

The Section 3 contextual argument contains two logical levels:

* FULL native nested gluing semantics, where an outer-root test is
  first attached to a retained right context T over Root, and the
  original inner piece M is attached over Start.
* The intended geometric outer-piece incompatibility profile, which
  additionally requires the nested semantics to coincide with
  gluing the actual transported outer piece against each test.

This file proves the FIRST level for EVERY outer-root test, without
assuming a pre-chosen forbidden replacement diagram. The proof
reuses exactly the original all-test functional diagram equivalence.
The second level remains a separate, explicitly open source-geometric
and interchange-of-gluing theorem; it cannot be inferred from the
closedness of the new outer context.

No restriction to relational signatures or injective weak target maps.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A forbidden two-stage full functional source diagram, obtained by
first attaching the outer-root test P to the retained context T
over Root, then attaching the inner piece M along Start.

The outer test P can be ANY rooted functional extension, not merely
a piece drawn from the forbidden family.  This predicate does not
assert that the resulting context is a geometric minimal-cut piece. -/
def forbiddenNestedFunctionalTestDiagram
    {S R : Type}
    (Start : Structure L S)
    (Root : Structure L R)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (M T : FunctionalRootExtension Start)
    (rT : Structure.Embedding Root T.str)
    (P : FunctionalRootExtension Root) : Prop :=
  ∃ (E : Type) (Ext : Structure L E)
    (jT : Structure.Embedding T.str Ext)
    (jP : Structure.Embedding P.str Ext),
    Structure.IsFreeAmalgam rT P.rootEmbedding jT jP ∧
    forbiddenFunctionalDiagram Start F M
      ({ Carrier := E, str := Ext,
         rootEmbedding := jT.comp T.rootEmbedding } :
        FunctionalRootExtension Start)

/-- Inner all-test diagram equivalence is a congruence for ALL
two-stage native functional test diagrams, with no additional
assumption that the chosen outer test is a forbidden piece.

The result is existentially about FULL nested sources. It does NOT
identify this predicate with the true outer geometric piece profile;
that identification requires compatible actual source diagrams. -/
theorem forbiddenNestedFunctionalTestDiagram_iff_of_inner_equiv
    {S R : Type}
    (Start : Structure L S)
    (Root : Structure L R)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (M M' T : FunctionalRootExtension Start)
    (rT : Structure.Embedding Root T.str)
    (hEq : (functionalDiagramPieceSetoid Start F).r M M')
    (P : FunctionalRootExtension Root) :
    forbiddenNestedFunctionalTestDiagram Start Root F M T rT P ↔
      forbiddenNestedFunctionalTestDiagram Start Root F M' T rT P := by
  have hProfile :=
    (functionalDiagramPiece_equiv_iff Start F M M').mp hEq
  constructor
  · rintro ⟨E, Ext, jT, jP, hExt, hBad⟩
    refine ⟨E, Ext, jT, jP, hExt, ?_⟩
    exact (hProfile
      ({ Carrier := E, str := Ext,
         rootEmbedding := jT.comp T.rootEmbedding } :
        FunctionalRootExtension Start)).mp hBad
  · rintro ⟨E, Ext, jT, jP, hExt, hBad⟩
    refine ⟨E, Ext, jT, jP, hExt, ?_⟩
    exact (hProfile
      ({ Carrier := E, str := Ext,
         rootEmbedding := jT.comp T.rootEmbedding } :
        FunctionalRootExtension Start)).mpr hBad

/-- The same nested-test congruence packaged as equality of the
complete sets of outer-root tests; this exposes the exact profile
invariant that later needs to be identified with the canonical
geometric outer-piece incompatibility set. -/
theorem forbiddenNestedFunctionalTestProfile_eq_of_inner_equiv
    {S R : Type}
    (Start : Structure L S)
    (Root : Structure L R)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (M M' T : FunctionalRootExtension Start)
    (rT : Structure.Embedding Root T.str)
    (hEq : (functionalDiagramPieceSetoid Start F).r M M') :
    {P : FunctionalRootExtension Root |
      forbiddenNestedFunctionalTestDiagram Start Root F M T rT P} =
    {P : FunctionalRootExtension Root |
      forbiddenNestedFunctionalTestDiagram Start Root F M' T rT P} := by
  apply Set.ext
  intro P
  exact forbiddenNestedFunctionalTestDiagram_iff_of_inner_equiv
    Start Root F M M' T rT hEq P

end AllThoseRamseyClasses.Lifts
