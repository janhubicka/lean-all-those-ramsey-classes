import AllThoseRamseyClasses.Lifts.OuterGeneratedBoundaryFromSelectedQ
import AllThoseRamseyClasses.Lifts.GeometricRetainedInteriorPath
import AllThoseRamseyClasses.Lifts.GeometricInnerRootOuterBoundary

/-!
# Recover an older outer boundary from the ACTUAL geometric old source

The generic new-boundary restoration theorem allows arbitrary
source free-amalgam charts and therefore carries several explicit
old-side geometric premises. In the real 2019 global canonical flip,
the old source is a finite forbidden structure A with a genuinely
selected minimal closed separator and its standard Fin n chart.

All required OLD inner-source premises now follow from that
geometric chart: the complete common root equals the selected
closed separator, all old private inner-side vertices belong to
ONE selected component D, and its entire generated boundary
is the complete root U. If that selected component is contained
in the older T-component C, every root vertex of U outside T
attaches to C even if the cuts are incomparable.

This theorem therefore leaves only:
* the genuine old OUTER boundary Cl_A(N_A(C)) = transported T;
* the actual OLD inner component D lying in C and the selected
  old outer component anchored inside D;
* the replacement Q's genuine internal generated boundary U;
* the literal complete new full functional source gluing.

It DERIVES the entire NEW opposite outer boundary, with no
assumed retained-path agreement or root-boundary contribution.
The required internal Q boundary is supplied by the selected
global canonical witness after separate Track A validation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type} {n : ℕ}

/-- For a genuine old geometric forbidden source, the only
old outer-context assumptions needed to restore the COMPLETE
new native generated boundary are that its selected inner
component lies in the chosen older outer component and that
the older boundary was already exact.

No arbitrary abstract old-source private component or older
root-attachment hypothesis survives in the theorem statement.
The new Q must have its full generated internal root equation;
the conclusion reconstructs the new older outer boundary
without assuming its equality or minimality. -/
theorem geometricGlobalSource_outerBoundary_from_selectedReplacement
    (A : Structure L V)
    (d : GeometricFunctionalPieceData A n)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart A d).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iCompNew : Structure.Embedding
      (geometricGlobalComplementChart A d).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart A d).rootEmbedding
      iQ iCompNew)
    (T : Set (geometricGlobalComplementChart A d).Carrier)
    (hTclosed : (geometricGlobalComplementChart A d).str.IsClosed T)
    (xOld : {v : V // v ∉
      (functionalComponentComplementEmbedding A
        (Set.range d.roots) d.minimal.1 d.left) '' T})
    (hxInInner :
      xOld.1 ∈ componentFrom A.graph (Set.range d.roots) d.left)
    (hInnerInOuter :
      componentFrom A.graph (Set.range d.roots) d.left ⊆
        componentFrom A.graph
          ((functionalComponentComplementEmbedding A
            (Set.range d.roots) d.minimal.1 d.left) '' T) xOld)
    (hOldBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph
            ((functionalComponentComplementEmbedding A
              (Set.range d.roots) d.minimal.1 d.left) '' T) xOld)) =
        (functionalComponentComplementEmbedding A
          (Set.range d.roots) d.minimal.1 d.left) '' T)
    (dQ : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding})
    (hQBoundary :
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) dQ)) =
        Set.range Q.rootEmbedding) :
    ∃ xNew : {w : W // w ∉ iCompNew '' T},
      xNew.1 = iQ dQ.1 ∧
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (iCompNew '' T) xNew)) =
        iCompNew '' T := by
  let P := geometricGlobalFunctionalChart A d
  let Comp := geometricGlobalComplementChart A d
  let iP : Structure.Embedding P.ext.str A :=
    functionalComponentEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let iCompOld : Structure.Embedding Comp.str A :=
    functionalComponentComplementEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  have hRootImage :
      iCompOld '' Set.range Comp.rootEmbedding =
        Set.range d.roots :=
    geometricGlobalSource_innerRoot_range_eq A d
  let dOld : {v : V // v ∉ iCompOld '' Set.range Comp.rootEmbedding} :=
    ⟨d.left.1, by
      rw [hRootImage]
      exact d.left.2⟩
  have hOldComponent :
      componentFrom A.graph
        (iCompOld '' Set.range Comp.rootEmbedding) dOld =
      componentFrom A.graph (Set.range d.roots) d.left :=
    sourceGaifmanComponent_eq_of_cut_eq
      A hRootImage dOld d.left rfl
  have hdOldInner : dOld.1 ∈ Set.range iP := by
    let e : P.ext.Carrier :=
      ⟨d.left.1, Or.inr
        (componentFrom_root A.graph (Set.range d.roots) d.left)⟩
    exact ⟨e, rfl⟩
  have hPrivateInD :
      ∀ e : P.ext.Carrier,
        e ∉ Set.range P.ext.rootEmbedding →
        iP e ∈ componentFrom A.graph
          (iCompOld '' Set.range Comp.rootEmbedding) dOld := by
    intro e he
    have hh :=
      geometricGlobalSource_innerPrivate_in_selectedComponent
        A d e he
    change e.1 ∈ componentFrom A.graph
      (iCompOld '' Set.range Comp.rootEmbedding) dOld
    rw [hOldComponent]
    exact hh
  have hxOld :
      xOld.1 ∈ componentFrom A.graph
        (iCompOld '' Set.range Comp.rootEmbedding) dOld := by
    rw [hOldComponent]
    exact hxInInner
  have hTclosedWhole : A.IsClosed (iCompOld '' T) :=
    functionalEmbedding_image_closed
      Comp.str A iCompOld T hTclosed
  have hRootAttached :
      Set.range d.roots \ (iCompOld '' T) ⊆
        componentFrom A.graph (iCompOld '' T) xOld :=
    generatedInnerRoot_outsideClosedOuterCut_attaches
      A (iCompOld '' T) hTclosedWhole xOld
      (componentFrom A.graph (Set.range d.roots) d.left)
      (Set.range d.roots) hInnerInOuter
      (geometricPiece_left_boundary_closure A d)
  have hRootOld :
      ∀ r : Fin n, Comp.rootEmbedding r ∉ T →
        iCompOld (Comp.rootEmbedding r) ∈
          componentFrom A.graph (iCompOld '' T) xOld := by
    intro r hrNotT
    have hRoot :
        iCompOld (Comp.rootEmbedding r) ∈ Set.range d.roots := by
      refine ⟨r, ?_⟩
      rfl
    have hNotT :
        iCompOld (Comp.rootEmbedding r) ∉ iCompOld '' T := by
      rintro ⟨b, hb, heq⟩
      have hEq : b = Comp.rootEmbedding r :=
        iCompOld.injective heq
      exact hrNotT (hEq ▸ hb)
    exact hRootAttached ⟨hRoot, hNotT⟩
  exact fullFreeAmalgam_outerBoundary_from_selectedInnerBoundary
    (geometricGlobalSource_freeDiagram A d) hNewFree
    T hTclosed dOld hdOldInner hPrivateInD
    xOld hxOld hRootOld hOldBoundary dQ hQBoundary

end AllThoseRamseyClasses.Lifts
