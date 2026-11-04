import AllThoseRamseyClasses.Lifts.SelectedGeometricFlipSourceFinite
import AllThoseRamseyClasses.Lifts.GeometricFlipOuterTargetRelation
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge

/-!
# Original outer global relation for an actual selected geometric source flip

The selected global canonical flip returns an actual full native source
with a geometrically selected replacement Q and the ORIGINAL fixed-root
canonical-gluing equivalence.  Its new source carrier is finite because
the selected Q and the old complement are finite full-amalgam sides.

The target-level outer relation theorem requires the existential
full-diagram profile formulation and a Finite instance for the new
source.  Both are now DERIVED from the real selected source data:

* equivalence of all canonical free-gluing tests is exactly equivalence
  of all genuine full native forbidden source diagrams;
* the genuine finite geometric witness for Q and full source coverage
  give finiteness of the new forbidden-source carrier;
* the geometric outer-root component premises, if established in
  the actual replacement, guarantee a NEW selected outer piece
  representing the ORIGINAL global indexed symbol;
* a weak EHN source-to-target map realizes that original relation
  whenever the image of the ordered outer root is injective.

There is NO added finite-source hypothesis, no assumption that Q is
an arbitrary geometric piece merely by profile equivalence, no
isomorphism-closure hypothesis on F, and no forced injectivity of a
weak target map.  The entire opposite generated boundary and exact
new outer component are STILL explicit geometric hypotheses.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A selected actual Q-flip with correct outside-root geometry
forces the ORIGINAL outer global relation in the weak-image target.

No new-source finiteness or existential-diagram-profile assumptions
are made: both are consequences of the selected witness and the
published canonical-gluing equivalence. Target-root injectivity
and the exact outer geometry are essential independent hypotheses. -/
theorem selectedGeometricFlip_preserves_originalOuterRelation
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W UT : Type} [Finite V]
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
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old d).root
        (Equiv.refl (Fin m)) Q) ∈
          forbiddenGeometricFunctionalPieces F m)
    (hEqGlue : (functionalRootPieceSetoid
      (geometricGlobalFunctionalChart Old d).root F).r
        (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE)
    (roots : Fin n → W)
    (hRootCoordinates : ∀ i : Fin n,
      roots i =
        iE (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))
    (x y : {w : W // w ∉ Set.range roots})
    (hSeparated : ¬ ReachOutside New.graph (Set.range roots) x y)
    (hLeftBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) x)) =
          Set.range roots)
    (hRightBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) y)) =
          Set.range roots)
    (hExactContext :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) =
        Set.range roots ∪
          componentFrom New.graph (Set.range roots) x)
    (hn : 0 < n)
    (Target : Structure L UT)
    (flip : W → UT)
    (hFlipWeak : New.IsEHNHomomorphismEmbedding Target flip)
    (hTargetRootInjective :
      Function.Injective (fun i : Fin n => flip (roots i))) :
    (globalFunctionalCanonicalLift F Target).rel
      (.inr (geometricGlobalPieceSymbol F Old
        (inferInstance : Finite V) hFOld P hn))
      (fun i : Fin n => flip (roots i)) := by
  classical
  letI : Finite W :=
    finiteSource_of_selectedGeometricFlip
      F Old d Q hSelected New iQ iE hFree
  have hEqDiagram :
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old d).root F).r
          (geometricGlobalFunctionalChart Old d).ext Q :=
    (functionalDiagramPiece_equiv_iff_glue
      (geometricGlobalFunctionalChart Old d).root F
      (geometricGlobalFunctionalChart Old d).ext Q).mpr hEqGlue
  exact geometricFlip_preserves_outerGlobalRelation_in_target
    F Old hFOld P d hInnerRoot hInnerComponent hOuterRootOutside
    Q hEqDiagram New hFNew iQ iE hFree
    roots hRootCoordinates x y hSeparated
    hLeftBoundary hRightBoundary hExactContext hn
    Target flip hFlipWeak hTargetRootInjective

end AllThoseRamseyClasses.Lifts
