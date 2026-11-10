import AllThoseRamseyClasses.Lifts.NestedSelectedGlobalOuterPieceSymbol
import AllThoseRamseyClasses.Lifts.GeometricFlipOuterTargetRelation

/-!
# The actual old GLOBAL outer canonical relation after a nested selected-Q flip

The completed source-side proof (Track A #899, conditional on its CI)
restores the genuine older geometric piece with its original complete
ordered Fin m root and proves equality of the *published* global
canonical piece symbols.

For an actual weak EHN map of the new forbidden source into Target,
the verified selected-piece realization lemma gives the new global
piece relation on the image of that ordered root. Rewriting the
verified source symbol equality gives precisely the old original
global relation on the same tuple.

The target image of a weak EHN map need not be injective. The
injectivity of the transported OLD ROOT tuple remains a genuine,
explicit hypothesis, as in the separately checked Track B target
relation theorem (#819). This module neither manufactures that
injectivity nor concludes source B-support descent, unrestricted
Claim 2, or strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W UT : Type}

/-- Under genuine original nested source geometry and an ACTUAL
selected equivalent canonical replacement Q, the same old
globally indexed outer piece relation holds in a weak target
at the transported old ordered root.

All actual source outer geometry, profile equality, root
orientation and new-source finiteness are derived from the
same selected Q; only root-image injectivity in the WEAK
target map is independent and is correctly kept explicit. -/
theorem nestedGeometric_selectedFlip_preserves_outerGlobalRelation_in_target
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (hm : 0 < m)
    (Target : Structure L UT) (flip : W → UT)
    (hFlipWeak : New.IsEHNHomomorphismEmbedding Target flip)
    (hRootTargetInjective :
      Function.Injective (fun i : Fin m =>
        flip (iE
          (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)))) :
    (globalFunctionalCanonicalLift F Target).rel
      (.inr (geometricGlobalPieceSymbol F Old
        (inferInstance : Finite V) hFOld outer hm))
      (fun i : Fin m =>
        flip (iE
          (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier))) := by
  obtain ⟨hFiniteNew, newOuter, hRootCoords, hSymbol⟩ :=
    nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol
      F Old hFOld inner outer hNested Q hSelected hEq
      New hFNew iQ iE hFree hm
  letI : Finite W := hFiniteNew
  have hNewRootInjective :
      Function.Injective (fun i : Fin m => flip (newOuter.roots i)) := by
    intro i j hEq
    apply hRootTargetInjective
    calc
      flip (iE (⟨outer.roots i,
        nestedGeometric_outerRoot_avoids_innerComponent
          Old inner outer hNested i⟩ :
          (geometricGlobalComplementChart Old inner).Carrier)) =
        flip (newOuter.roots i) :=
          congrArg flip (hRootCoords i).symm
      _ = flip (newOuter.roots j) := hEq
      _ = flip (iE (⟨outer.roots j,
        nestedGeometric_outerRoot_avoids_innerComponent
          Old inner outer hNested j⟩ :
          (geometricGlobalComplementChart Old inner).Carrier)) :=
          congrArg flip (hRootCoords j)
  have hNewRelation :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F New
          hFiniteNew hFNew newOuter hm))
        (fun i : Fin m => flip (newOuter.roots i)) :=
    geometricGlobalCanonicalRelation_of_weak
      F New hFiniteNew hFNew newOuter hm
      Target flip hFlipWeak hNewRootInjective
  let OldSelected : SelectedFunctionalChart F m :=
    geometricGlobalSelectedChart F Old
      (inferInstance : Finite V) hFOld outer
  let NewSelected : SelectedFunctionalChart F m :=
    geometricGlobalSelectedChart F New
      hFiniteNew hFNew newOuter
  have hClass :
      (Quotient.mk (globalFunctionalPieceSetoid F m) OldSelected :
        GlobalFunctionalPieceClass F m) =
      Quotient.mk (globalFunctionalPieceSetoid F m) NewSelected := by
    have hPair :
        (⟨⟨m, hm⟩, Quotient.mk (globalFunctionalPieceSetoid F m)
          OldSelected⟩ : GlobalFunctionalPieceSymbol F) =
        (⟨⟨m, hm⟩, Quotient.mk (globalFunctionalPieceSetoid F m)
          NewSelected⟩ : GlobalFunctionalPieceSymbol F) := by
      exact hSymbol
    exact eq_of_heq ((Sigma.mk.inj_iff.mp hPair).2)
  have hOldRelation :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm))
        (fun i : Fin m => flip (newOuter.roots i)) := by
    change (globalFunctionalCanonicalLift F Target).rel
      (.inr (⟨⟨m, hm⟩,
        Quotient.mk (globalFunctionalPieceSetoid F m) OldSelected⟩ :
          GlobalFunctionalPieceSymbol F))
      (fun i : Fin m => flip (newOuter.roots i))
    rw [hClass]
    exact hNewRelation
  have hTuple :
      (fun i : Fin m => flip (newOuter.roots i)) =
        (fun i : Fin m =>
          flip (iE (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier))) := by
    funext i
    exact congrArg flip (hRootCoords i)
  rw [← hTuple]
  exact hOldRelation

end AllThoseRamseyClasses.Lifts
