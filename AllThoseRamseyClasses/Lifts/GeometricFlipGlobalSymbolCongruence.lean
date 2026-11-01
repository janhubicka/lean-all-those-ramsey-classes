import AllThoseRamseyClasses.Lifts.OriginalGeometricPieceToNewContextProfile
import AllThoseRamseyClasses.Lifts.FullRootStructureUniqueness
import AllThoseRamseyClasses.Lifts.GlobalProfileFromFullRootCongruence
import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol
import AllThoseRamseyClasses.Lifts.EqualClosedCarrierRootedProfiles

/-!
# Genuine geometric Claim 2 profile transfer gives the SAME GLOBAL lift symbol

The Section 3 canonical lift adds one new relation for each GLOBAL
incompatibility-equivalence class of genuine forbidden geometric pieces.
Replacing an inner piece inside an older outer piece should preserve
the ORIGINAL indexed relation symbol -- not merely the set of all
fixed-rooted tests in an arbitrary closed source context.

The verified actual-source congruence (#767) already proves that
the ORIGINAL genuine geometric piece and the ACTUAL transported
closed source context have identical ALL-test incompatibility profiles.

This module discharges the remaining algebraic conversion to the
published global quotient whenever the transported context really
IS a selected new geometric piece with the SAME ORDERED old root:
* the full root structures coincide, because both FULL source
  embeddings land at the same ordered vertices in the new source;
* the actual new closed context and the new geometric piece have
  identical native induced structures and rooted tests;
* equality of complete fixed-root diagram profiles descends to
  equality in the real global selected-piece quotient, and hence
  equality of the added relation symbol at this positive width.

This does NOT assume a free-standing symbolic equivalence conclusion.
It still explicitly requires that Track A recover a genuine new
geometric minimal-separator piece and prove its *entire* vertex set
equals the transported context. It does not establish those facts.
There is no weak target image quotient, bound on arities, or
forbidden-family isomorphism-closure hypothesis.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The *actual global* canonical-lift symbol of the old outer
geometric piece is preserved when the newly transported source
context has been certified to be exactly one NEW geometric
minimal-separator piece on the original ordered root.

The geometric-piece and carrier-equality premises are the precise
unproved Track A obligations. Everything else is native full
functional gluing and rooted incompatibility profile transport. -/
theorem geometricFlip_preserves_globalPieceSymbol_of_newGeometricContext
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type} [Finite V] [Finite W]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (hInnerComponent :
      functionalComponentFrom Old (Set.range d.roots) d.left ⊆
        geometricPieceVertices Old P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old d).root F).r
        (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE)
    (Pnew : GeometricFunctionalPieceData New n)
    (hRootCoords : ∀ i : Fin n,
      Pnew.roots i =
        iE (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))
    (hExactContext :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) =
          geometricPieceVertices New Pnew)
    (hn : 0 < n) :
    geometricGlobalPieceSymbol F Old
        (inferInstance : Finite V) hFOld P hn =
      geometricGlobalPieceSymbol F New
        (inferInstance : Finite W) hFNew Pnew hn := by
  classical
  let OldChart := geometricGlobalFunctionalChart Old P
  let NewChart := geometricGlobalFunctionalChart New Pnew
  let S := oldOuterContextInInnerComplement Old P d
  let K : Set W := iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' S
  obtain ⟨hK, newRoot, hOldNewProfile, hNewRootCoords⟩ :=
    geometricOriginalPiece_profile_equiv_transportContext
      F Old P d hInnerRoot hInnerComponent hOuterRootOutside
      Q hEq New iQ iE hFree
  have hGeomClosed : New.IsClosed (geometricPieceVertices New Pnew) :=
    functionalComponentUnion_isClosed New
      (Set.range Pnew.roots) Pnew.minimal.1 Pnew.left
  let incK : Structure.Embedding (New.induce K hK) New :=
    Structure.inclusion New K hK
  let eOldRoot : Structure.Embedding OldChart.root New :=
    incK.comp newRoot
  let eGeomRoot : Structure.Embedding NewChart.root New :=
    (geometricFunctionalPieceEmbedding New Pnew).comp
      NewChart.ext.rootEmbedding
  have hAgreeRoot (i : Fin n) : eOldRoot i = eGeomRoot i := by
    calc
      eOldRoot i = (newRoot i).1 := rfl
      _ = iE (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier) :=
            hNewRootCoords i
      _ = Pnew.roots i := (hRootCoords i).symm
      _ = eGeomRoot i := rfl
  have hRootStructure : OldChart.root = NewChart.root :=
    fullRootStructure_eq_of_same_full_image
      eOldRoot eGeomRoot hAgreeRoot
  have hRootedProfile :
      (functionalDiagramPieceSetoid OldChart.root F).r
        OldChart.ext (hRootStructure.symm ▸ NewChart.ext) := by
    cases hRootStructure
    have hNewSameRoot (i : Fin n) :
        (newRoot i).1 = (NewChart.ext.rootEmbedding i).1 := by
      calc
        (newRoot i).1 =
            iE (⟨P.roots i, hOuterRootOutside i⟩ :
              (geometricGlobalComplementChart Old d).Carrier) :=
                hNewRootCoords i
        _ = Pnew.roots i := (hRootCoords i).symm
        _ = (NewChart.ext.rootEmbedding i).1 := rfl
    have hActualNewGeom :
        (functionalDiagramPieceSetoid OldChart.root F).r
          ({ Carrier := K, str := New.induce K hK,
             rootEmbedding := newRoot } :
                FunctionalRootExtension OldChart.root)
          NewChart.ext := by
      exact equalClosedCarrier_rootedProfiles_equiv
        New K (geometricPieceVertices New Pnew)
        hK hGeomClosed hExactContext
        OldChart.root newRoot NewChart.ext.rootEmbedding
        hNewSameRoot F
    exact hOldNewProfile.trans hActualNewGeom
  let PoldSelected : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F Old
      (inferInstance : Finite V) hFOld P
  let PnewSelected : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F New
      (inferInstance : Finite W) hFNew Pnew
  have hClass :
      (Quotient.mk (globalFunctionalPieceSetoid F n) PoldSelected :
        GlobalFunctionalPieceClass F n) =
      Quotient.mk (globalFunctionalPieceSetoid F n) PnewSelected := by
    exact selectedFunctionalChart_global_class_eq_of_rootEq_and_diagram
      F PoldSelected PnewSelected
      hRootStructure hRootedProfile
  change
    (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
      PoldSelected⟩ : GlobalFunctionalPieceSymbol F) =
    (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
      PnewSelected⟩ : GlobalFunctionalPieceSymbol F)
  exact congrArg
    (fun cls : GlobalFunctionalPieceClass F n =>
      (⟨⟨n, hn⟩, cls⟩ : GlobalFunctionalPieceSymbol F))
    hClass

end AllThoseRamseyClasses.Lifts
