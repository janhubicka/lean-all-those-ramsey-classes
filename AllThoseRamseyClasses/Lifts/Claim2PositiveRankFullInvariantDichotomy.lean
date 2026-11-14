import AllThoseRamseyClasses.Lifts.Claim2NoEscapePositiveRankBoundaryAlternative
import AllThoseRamseyClasses.Lifts.Claim2PartnerFullLocalInvariantStep
import AllThoseRamseyClasses.Lifts.ConnectedComponentBoundaryNonempty
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation

/-!
# Track B: positive B-rank supplies a full-invariant step or a smaller root

The existing no-escape dichotomy chooses a B-active generated
boundary inside a geometric outer piece. If its opposite A-anchor
boundary matches, the ACTUAL same-Q matched-partner construction
preserves both old target outer-root injectivity and all B-active
generated-boundary injections local to that outer piece, in
addition to the full global symbol, literal B-SOURCE-rank decrease,
every exterior SOURCE count, and an A-only anchor.

If the boundaries do not match, a genuine smaller positive separator
root is returned. No unjustified assumption says its component is
A-free or avoids capture of the old outer root.

The old root-target and active-boundary injections remain explicit
premises; this is not an unrestricted Claim 2 proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Refined positive-rank dichotomy with a *single real new source*
carrying the full local iterative invariants in the successful
matched-boundary branch.  Failure is a witnessed smaller root. -/
theorem claim2_positiveRank_fullInvariantActualSuccessor_or_smallerRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hn : 0 < n)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (a : V)
    (haK : a ∈ geometricPieceVertices Source P)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hPositiveB : 0 < Nat.card {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight})
    (hActiveBoundaryInjective :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))))
    (hOuterRootTargetInj :
      Function.Injective (fun i : Fin n => f (P.roots i))) :
    (∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      0 < m ∧
      geometricPieceVertices Source d ⊂
        geometricPieceVertices Source P ∧
      ∃ (V' : Type) (New : Structure L V')
        (hNew : F New) (hFiniteNew : Finite V')
        (flip : V' → UT)
        (newOuter : GeometricFunctionalPieceData New n),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ i : Fin n, flip (newOuter.roots i) = f (P.roots i)) ∧
        geometricGlobalPieceSymbol F Source
            hFinite hForbidden P hn =
          geometricGlobalPieceSymbol F New
            hFiniteNew hNew newOuter hn ∧
        Nat.card {w : V' //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Source P ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
        (∀ TargetSet : Set UT,
          Nat.card {w : V' //
            w ∉ geometricPieceVertices New newOuter ∧
            flip w ∈ TargetSet} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Source P ∧
            f v ∈ TargetSet}) ∧
        (∃ anew : V',
          anew ∈ geometricPieceVertices New newOuter ∧
          flip anew = f a ∧
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft ∧
          Function.Injective (fun i : Fin n => flip (newOuter.roots i)) ∧
          (∀ (z : V')
            (hzPart : z ∈ geometricPieceVertices New newOuter)
            (hzB : flip z ∈ fullFreeRightExclusiveTarget iRight jRight)
            (hzOutside : flip z ∉ Set.range (jLeft.comp iLeft)),
            Set.InjOn flip
              (New.functionClosure
                (gaifmanNeighborhood New.graph
                  (componentFrom New.graph
                    (flip ⁻¹' Set.range (jLeft.comp iLeft))
                    (⟨z, hzOutside⟩ :
                      {w : V' // w ∉ flip ⁻¹' Set.range (jLeft.comp iLeft)}))))))) ∨
    (∃ (x : {v : V // v ∉
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
        (T : Set V) (y : {v : V // v ∉ T})
        (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      x.1 ∈ geometricPieceVertices Source P ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      y.1 = a ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      0 < m ∧
      Set.range d.roots ⊂ T ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩
          geometricPieceVertices Source P ∧
      d.left.1 = x.1 ∧ d.right.1 = a ∧
      Set.range d.roots =
        Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph T y))) := by
  classical
  let K : Set V := geometricPieceVertices Source P
  let S : Set V := weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  have hKclosed : Source.IsClosed K :=
    functionalComponentUnion_isClosed Source
      (Set.range P.roots) P.minimal.1 P.left
  have hNoEscape : FunctionalContextNoEscapeOutsideSeam Source S K :=
    geometricPiece_noEscapeOutsideContainingSeam
      Source P S hOuterRootInSeam
  obtain ⟨x, T, hxK, hxRight, hT, hTInside,
      y, hYa, hAlternative⟩ :=
    positiveLocalRightRank_noEscape_partner_or_smallerRoot
      F hConnected Source hFinite hForbidden
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree
      K hKclosed hNoEscape a haK haLeft hPositiveB
  have hTS : T ⊆ S := fun z hz => (hTInside hz).1
  rcases hAlternative with hPartner |
      ⟨m, d, hm, hProper, hRootIn, hLeft, hRight, hExactRoot⟩
  · have hxOuter : x.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
      rcases hxK with hRoot | hComponent
      · obtain ⟨i, hi⟩ := hRoot
        have hxSeam : x.1 ∈ S := hi ▸
          hOuterRootInSeam ⟨i, rfl⟩
        exact False.elim (x.2 hxSeam)
      · exact hComponent
    have haOuter : a ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
      rcases haK with hRoot | hComponent
      · obtain ⟨i, hi⟩ := hRoot
        have haSeam : a ∈ S := hi ▸
          hOuterRootInSeam ⟨i, rfl⟩
        exact False.elim (haLeft.2 haSeam)
      · exact hComponent
    have haNotComponent :
        a ∉ componentFrom Source.graph S x := by
      intro haComponent
      have haRight : a ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
        weakFreePartition_component_right
          hFree f hf.1 x hxRight haComponent
      exact (Set.disjoint_left.mp
        (weakFreePartition_left_right_disjoint hFree f))
          haLeft haRight
    have hConnectedPath : ReachOutside Source.graph (∅ : Set V)
        (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
        (⟨a, by simp⟩ : {v : V // v ∉ ∅}) :=
      gaifmanPath_to_emptyCutReach Source
        ((hConnected Source hFinite hForbidden).2 x.1 a)
    have hTnonempty : T.Nonempty := by
      rw [hT]
      exact functionalComponent_generatedBoundary_nonempty_of_emptyCutReach
        Source S x a haNotComponent hConnectedPath
    obtain ⟨y', hy'Val, hSeparated'⟩ :=
      weakRightComponent_leftVertex_separatedByBoundary
        hFree f hf x hxRight T hT hTS a haLeft
    have hYeq : y' = y := Subtype.ext (hy'Val.trans hYa.symm)
    have hSeparated : ¬ ReachOutside Source.graph T
        (outsideCutMap hTS x) y := by
      simpa only [hYeq] using hSeparated'
    have hInjT : Set.InjOn f T := by
      rw [hT]
      exact hActiveBoundaryInjective x hxK hxRight
    obtain ⟨m, d, hm, hProper, V', New, hNew, Q, hSelected,
      iQ, iE, hNewFree, hFiniteNew, flip, newOuter,
      hFlip, hQNoRight, hEAgree, hCarrier, hTargetCoords,
      hSymbol, hRank, hExterior,
      anew, haNewOuter, haSame, haNewA, hRootInj, hNewBoundaryInj⟩ :=
      claim2_actualGeometricRightFlip_of_boundaryPartner_withFullLocalInvariants
        F hFiniteF Source hFinite hForbidden
        P hn Target f hf Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        hOuterRootInSeam x hxRight hxOuter
        a haLeft haOuter
        T hT hTS hTnonempty y hSeparated hPartner hInjT
        hOuterRootTargetInj hActiveBoundaryInjective
    exact Or.inl ⟨m, d, hm, hProper, V', New, hNew,
      hFiniteNew, flip, newOuter, hFlip,
      hTargetCoords, hSymbol, hRank, hExterior,
      anew, haNewOuter, haSame, haNewA, hRootInj, hNewBoundaryInj⟩
  · right
    exact ⟨x, T, y, m, d, hxK, hxRight, hYa, hT,
      hm, hProper, hRootIn, hLeft, hRight, hExactRoot⟩


end AllThoseRamseyClasses.Lifts
