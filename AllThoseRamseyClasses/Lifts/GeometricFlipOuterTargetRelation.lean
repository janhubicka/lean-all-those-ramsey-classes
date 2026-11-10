import AllThoseRamseyClasses.Lifts.GeometricFlipGlobalSymbolFromBoundaries
import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol

/-!
# Preserve the ORIGINAL canonical outer-piece relation in the actual target

The full native source-level global-symbol theorem (#796) gives a genuine
new geometric piece with precisely the original outer class symbol
when the two complete generated-boundary equations, separated components
and exact new context carrier are supplied.

To apply the 2019 maximal-common-lift argument, the output must be the
actual GLOBAL CANONICAL LIFT RELATION in the TARGET of the weak source map.
The existing selected geometric-piece realization theorem provides this
for the new piece, and the proven symbol equality rewrites it to the OLD
outer symbol at exactly the original transported target root tuple.

IMPORTANT: Weak EHN source maps do NOT automatically send distinct roots
to distinct points. We demand target injectivity of the transported old
root tuple explicitly. It can later be supplied by an actual common-lift
relation witness; it is not inferred from the weak map or from source
closedness. There is no isomorphism-closure premise on the forbidden family.

The geometric boundary and exact-component premises are precisely
the still-open Track A obligations for an unrestricted nested flip.
This theorem does not assert that they hold, nor Claim 2/strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Once a genuine inner functional source flip has the EXACT new
outer-root component geometry and a weak map into Target whose old
outer root has injective image, the target's GLOBAL canonical lift
realizes the ORIGINAL old outer-piece relation at that root image.

Every old relation and complete set-valued functional fibre stays
native. The target map need not be injective away from the root.

This is a true target-LIFT relation, not merely source piece-setoid
congruence or a statement about the canonical relation in the NEW
forbidden source. -/
theorem geometricFlip_preserves_outerGlobalRelation_in_target
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W UT : Type} [Finite V] [Finite W]
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
  obtain ⟨Pnew, hPnewRoot, hGlobalSymbol⟩ :=
    geometricFlip_globalPieceSymbol_of_exactOppositeBoundaries
      F Old hFOld P d hInnerRoot hInnerComponent
      hOuterRootOutside Q hEq New hFNew iQ iE hFree
      roots hRootCoordinates x y hSeparated
      hLeftBoundary hRightBoundary hExactContext hn
  have hNewInj :
      Function.Injective (fun i : Fin n => flip (Pnew.roots i)) := by
    intro i j hij
    apply hTargetRootInjective
    calc
      flip (roots i) = flip (Pnew.roots i) := by
        exact congrArg flip
          ((hPnewRoot i).trans (hRootCoordinates i).symm).symm
      _ = flip (Pnew.roots j) := hij
      _ = flip (roots j) := by
        exact congrArg flip
          ((hPnewRoot j).trans (hRootCoordinates j).symm)
  have hNewRelation :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F New
          (inferInstance : Finite W) hFNew Pnew hn))
        (fun i : Fin n => flip (Pnew.roots i)) :=
    geometricGlobalCanonicalRelation_of_weak
      F New (inferInstance : Finite W) hFNew
      Pnew hn Target flip hFlipWeak hNewInj
  let OldSelected : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F Old
      (inferInstance : Finite V) hFOld P
  let NewSelected : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F New
      (inferInstance : Finite W) hFNew Pnew
  have hClass :
      (Quotient.mk (globalFunctionalPieceSetoid F n) OldSelected :
        GlobalFunctionalPieceClass F n) =
      Quotient.mk (globalFunctionalPieceSetoid F n) NewSelected := by
    have hPair :
        (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
          OldSelected⟩ : GlobalFunctionalPieceSymbol F) =
        (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
          NewSelected⟩ : GlobalFunctionalPieceSymbol F) := by
      exact hGlobalSymbol
    exact eq_of_heq ((Sigma.mk.inj_iff.mp hPair).2)
  have hOriginalRelation :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld P hn))
        (fun i : Fin n => flip (Pnew.roots i)) := by
    change (globalFunctionalCanonicalLift F Target).rel
      (.inr (⟨⟨n, hn⟩,
        Quotient.mk (globalFunctionalPieceSetoid F n) OldSelected⟩ :
          GlobalFunctionalPieceSymbol F))
      (fun i : Fin n => flip (Pnew.roots i))
    rw [hClass]
    exact hNewRelation
  have hTargetCoordinates :
      (fun i : Fin n => flip (Pnew.roots i)) =
        (fun i : Fin n => flip (roots i)) := by
    funext i
    exact congrArg flip
      ((hPnewRoot i).trans (hRootCoordinates i).symm)
  rw [hTargetCoordinates] at hOriginalRelation
  exact hOriginalRelation

end AllThoseRamseyClasses.Lifts
