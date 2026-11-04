import AllThoseRamseyClasses.Lifts.NestedGeometricOuterExteriorPrivate
import AllThoseRamseyClasses.Lifts.OriginalGeometricPieceToNewContextProfile

/-!
# Genuine nested source geometry implies full original-outer profile transport

The contextual profile theorem was previously conditional on THREE
independently supplied geometric facts: the inner full root lies in the
outer piece, its full component lies there, and all older ordered outer
root coordinates survive outside the inner selected component.

For ACTUAL nested geometric minimal closed separators, all three follow
from a single component nesting hypothesis. The root inclusion uses
the source-native generated-boundary attachment lemma, not a
hypothetical graph edge or an EHN weak target-image injection.
The older outer root survives because a component of the complement of
its own closed cut cannot contain any outer root coordinate.

This is a source-to-profile integration lemma. It identifies the
ORIGINAL outer piece's complete rooted forbidden-diagram profile with
the actual transported closed context after a literal full native Q
replacement. It does NOT identify that context with the newly
reconstructed geometric outer piece. That carrier/profile comparison
and the Claim 2 local B-support descent remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A single genuine nesting premise supplies all geometric
hypotheses of the original Section 3 full outer-context profile
transport theorem.

The conclusion covers ALL forbidden full native functional
free-amalgam tests, provided the selected replacement Q has the same
rooted forbidden-diagram profile as the original inner piece.
This is not an unrestricted 2019 lift theorem or a source-support
descent certificate. -/
theorem nestedGeometric_originalOuter_profile_equiv_transportContext
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range d.roots) d.left ⊆
        componentFrom Old.graph (Set.range P.roots) P.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old d).root F).r
        (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding
      iQ iE) :
    let E := geometricGlobalComplementChart Old d
    let S := oldOuterContextInInnerComplement Old P d
    let NewK : Set W :=
      iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' S
    ∃ (hNewK : New.IsClosed NewK)
      (newRoot : Structure.Embedding
        (geometricGlobalFunctionalChart Old P).root
        (New.induce NewK hNewK)),
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old P).root F).r
        (geometricGlobalFunctionalChart Old P).ext
        ({ Carrier := NewK, str := New.induce NewK hNewK,
           rootEmbedding := newRoot } :
          FunctionalRootExtension
            (geometricGlobalFunctionalChart Old P).root) ∧
      (∀ i : Fin n,
        (newRoot i).1 =
          iE (⟨P.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old d P hNested i⟩ : E.Carrier)) := by
  have hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P :=
    nestedGeometric_innerRoot_in_outerPiece Old d P hNested
  have hInnerComponent :
      functionalComponentFrom Old (Set.range d.roots) d.left ⊆
        geometricPieceVertices Old P := by
    intro x hx
    change x ∈ Set.range P.roots ∪
      componentFrom Old.graph (Set.range P.roots) P.left
    exact Or.inr (hNested hx)
  have hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left :=
    nestedGeometric_outerRoot_avoids_innerComponent Old d P hNested
  exact geometricOriginalPiece_profile_equiv_transportContext
    F Old P d hInnerRoot hInnerComponent hOuterRootOutside
    Q hEq New iQ iE hFree

end AllThoseRamseyClasses.Lifts
