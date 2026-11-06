import AllThoseRamseyClasses.Lifts.SelectedReplacementInternalGeneratedRoot
import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoGaifmanPaths
import AllThoseRamseyClasses.Lifts.GeometricInnerSourceInterface
import AllThoseRamseyClasses.Lifts.PrivateRootComponentExact

/-!
# Every private vertex of a genuinely selected replacement Q is connected

Knowing one private component generates the entire root does NOT,
for a generic functional root extension, imply that other private
vertices belong to that component. The source of the original
2019 geometric selected piece has stronger geometry: it is
literally the full closed root together with ONE Gaifman
component. The full source free-amalgam diagram reflects this
component equality back into the induced selected extension.

A genuinely selected Q is FULLY root-isomorphic to that actual
source piece. Transporting complete functional Gaifman paths
through the rooted isomorphism shows every Q-private vertex
belongs to one single root-complement component.

This is the missing source-side connectivity property needed to
identify a transported older context with a reconstructed older
geometric piece. It does not assert outer context equality or
Claim 2's support descent.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual source-selected geometric root extension has a
single connected non-root component. It cannot have other
isolated private components: its full carrier is literally the
root U together with one original U-component, and paths
reflect through the original FULL functional source diagram. -/
theorem geometricSelectedPiece_allPrivate_connected
    {V : Type} (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    let P := geometricGlobalFunctionalChart A d
    ∃ x : {a : P.ext.Carrier //
        a ∉ Set.range P.ext.rootEmbedding},
      ∀ e : P.ext.Carrier,
        e ∉ Set.range P.ext.rootEmbedding →
          e ∈ componentFrom P.ext.str.graph
            (Set.range P.ext.rootEmbedding) x := by
  let P := geometricGlobalFunctionalChart A d
  let Comp := geometricGlobalComplementChart A d
  let iP : Structure.Embedding P.ext.str A :=
    functionalComponentEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let iComp : Structure.Embedding Comp.str A :=
    functionalComponentComplementEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let p : P.ext.Carrier :=
    ⟨d.left.1, Or.inr
      (componentFrom_root A.graph (Set.range d.roots) d.left)⟩
  have hpNot : p ∉ Set.range P.ext.rootEmbedding := by
    rintro ⟨i, hi⟩
    have hCoord : d.roots i = d.left.1 :=
      congrArg (fun z : P.ext.Carrier => z.1) hi
    exact d.left.2 ⟨i, hCoord⟩
  let x : {a : P.ext.Carrier //
      a ∉ Set.range P.ext.rootEmbedding} :=
    ⟨p, hpNot⟩
  have hRootImage :
      iP '' Set.range P.ext.rootEmbedding = Set.range d.roots := by
    ext z
    constructor
    · rintro ⟨e, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨P.ext.rootEmbedding i, ⟨i, rfl⟩, rfl⟩
  let xWhole :=
    fullFunctionalEmbedding_outsideCut iP
      (Set.range P.ext.rootEmbedding) x
  have hOldC :
      componentFrom A.graph (iP '' Set.range P.ext.rootEmbedding)
        xWhole =
      componentFrom A.graph (Set.range d.roots) d.left :=
    sourceGaifmanComponent_eq_of_cut_eq
      A hRootImage xWhole d.left rfl
  have hFree :
      Structure.IsFreeAmalgam
        P.ext.rootEmbedding Comp.rootEmbedding iP iComp :=
    geometricGlobalSource_freeDiagram A d
  have hExact :
      componentFrom A.graph
          (iP '' Set.range P.ext.rootEmbedding) xWhole =
        iP '' componentFrom P.ext.str.graph
          (Set.range P.ext.rootEmbedding) x :=
    fullFreeAmalgam_rightPrivateRoot_component_eq hFree.swap x
  refine ⟨x, ?_⟩
  intro e he
  have heOld :
      iP e ∈ componentFrom A.graph
        (Set.range d.roots) d.left :=
    geometricGlobalSource_innerPrivate_in_selectedComponent
      A d e he
  have hImage : iP e ∈ iP '' componentFrom P.ext.str.graph
      (Set.range P.ext.rootEmbedding) x := by
    rw [← hOldC, hExact] at heOld
    exact heOld
  obtain ⟨e', he'C, heEq⟩ := hImage
  have he' : e' = e := iP.injective heEq
  exact he' ▸ he'C

/-- ALL genuinely selected Q-private vertices lie in ONE
connected component after deleting its complete ordered root,
not merely in a component with a complete generated root.

This result requires actual geometric selection up to a FULL
root-preserving functional isomorphism. Mere equivalence of
rooted incompatibility profiles is not sufficient. -/
theorem selectedReplacementPiece_allPrivate_connected
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {n : ℕ}
    (R : Structure L (Fin n))
    (Q : FunctionalRootExtension R)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        R (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n) :
    ∃ x : {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding},
      ∀ q : Q.Carrier,
        q ∉ Set.range Q.rootEmbedding →
          q ∈ componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) x := by
  change IsForbiddenGeometricFunctionalPiece F
    (FunctionalRootExtension.toEnumeratedRootedPattern
      R (Equiv.refl (Fin n)) Q) at hSelected
  obtain ⟨W, A, _hFinite, _hFA, d, ⟨e⟩⟩ := hSelected
  obtain ⟨x, hAll⟩ :=
    geometricSelectedPiece_allPrivate_connected A d
  let qChosen := functionalRootedIso_outsideRoot e.symm x
  refine ⟨qChosen, ?_⟩
  intro q hq
  let qOut : {z : Q.Carrier //
      z ∉ Set.range Q.rootEmbedding} := ⟨q, hq⟩
  let pOut := functionalRootedIso_outsideRoot e qOut
  have hpC :
      pOut.1 ∈
        componentFrom
          (geometricFunctionalRootedPattern A d).str.graph
          (Set.range (geometricFunctionalRootedPattern A d).root)
          x :=
    hAll pOut.1 pOut.2
  have hQImage :
      e.symm.equiv pOut.1 ∈
        componentFrom Q.str.graph
          (Set.range Q.rootEmbedding) qChosen :=
    (functionalRootedIso_component_image_subset e.symm x)
      ⟨pOut.1, hpC, rfl⟩
  have hpVal : pOut.1 = e.equiv q := rfl
  have hQVal : e.symm.equiv pOut.1 = q := by
    rw [hpVal]
    exact e.equiv.symm_apply_apply q
  rw [hQVal] at hQImage
  exact hQImage

end AllThoseRamseyClasses.Lifts
