import AllThoseRamseyClasses.Lifts.Claim2PositiveRankFullInvariantDichotomy
import AllThoseRamseyClasses.Lifts.Claim2SmallerRootFullInvariantFlip

/-!
# Track B: full-native positive rank trichotomy with exact two geometric obstructions

For every genuine admissible positive B-SOURCE-rank outer state
with injected B-active boundaries and an injective ordered root,
the original local no-escape argument gives a ONE-SOURCE actual
same-selected-Q successor preserving the ROOT injection and the
exact NATIVE next-state B-boundary injection, OR exhibits one of
two literal source-geometric smaller-root obstructions:
old outer-root capture or A-mixedness.

There is NO silent assumption that these two branches are impossible.
The old root and boundary injections are explicit; this does not
construct an initially normalized original minimizer or a terminal
Claim 2 contradiction. Exterior SOURCE counts and old global
canonical selected symbol are preserved on the actual successor.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- The positive-rank step-or-obstructions theorem with all native
iterative local-state invariants in the successful branch. -/
theorem claim2_positiveRank_fullStateStep_or_oldRootCapture_or_AMixed
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
    (hOldOuterRootTargetInj :
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
          (∀ (z : {w : V' //
              w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
            z.1 ∈ geometricPieceVertices New newOuter →
            z.1 ∈ weakFreeRightPart
              (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
            Set.InjOn flip
              (New.functionClosure
                (gaifmanNeighborhood New.graph
                  (componentFrom New.graph
                    (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) z)))))) ∨
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
            (componentFrom Source.graph T y)) ∧
      ((∃ i : Fin n,
          P.roots i ∈ functionalComponentFrom Source
            (Set.range d.roots) d.left) ∨
       (∃ z : V,
          z ∈ functionalComponentFrom Source
            (Set.range d.roots) d.left ∧
          z ∈ weakFreeLeftPart
            (sL := iLeft) (iL := jLeft) f))) := by
  classical
  rcases
      (claim2_positiveRank_fullInvariantActualSuccessor_or_smallerRoot
        F hFiniteF hConnected Source hFinite hForbidden
        P hn Target f hf Left Right jLeft jRight
        X iLeft iRight hFree hCommon hOuterRootInSeam
        a haK haLeft hPositiveB hActiveBoundaryInjective
        hOldOuterRootTargetInj) with
    hFlip | ⟨x, T, y, m, d, hxK, hxRight, hYa, hT,
      hm, hProper, hRootIn, hLeft, hRight, hExactRoot⟩
  · exact Or.inl hFlip
  · -- The new root is injected on the precise B-active boundary T,
    -- even when the weak map collapses other common-seam vertices.
    have hTInj : Set.InjOn f T := by
      rw [hT]
      exact hActiveBoundaryInjective x hxK hxRight
    have hDrootInj : Function.Injective
        (fun i : Fin m => f (d.roots i)) := by
      intro i j hij
      apply d.roots_injective
      exact hTInj
        (hProper.subset ⟨i, rfl⟩)
        (hProper.subset ⟨j, rfl⟩) hij
    have hxOuter :
        x.1 ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rcases hxK with hRoot | hComponent
      · obtain ⟨i, hi⟩ := hRoot
        have hxSeam : x.1 ∈
            weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
          hi ▸ hOuterRootInSeam ⟨i, rfl⟩
        exact False.elim (x.2 hxSeam)
      · exact hComponent
    have haOuter :
        a ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rcases haK with hRoot | hComponent
      · obtain ⟨i, hi⟩ := hRoot
        have haSeam : a ∈
            weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
          hi ▸ hOuterRootInSeam ⟨i, rfl⟩
        exact False.elim (haLeft.2 haSeam)
      · exact hComponent
    have hdLeftInOuter :
        d.left.1 ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rw [hLeft]
      exact hxOuter
    have hdRightInOuter :
        d.right.1 ∈ functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rw [hRight]
      exact haOuter
    have hdRootInOuter :
        Set.range d.roots ⊆ geometricPieceVertices Source P :=
      fun z hz => (hRootIn hz).2
    have hdRootInSeam :
        Set.range d.roots ⊆
          weakFreeRootPart (sL := iLeft) (iL := jLeft) f :=
      fun z hz => (hRootIn hz).1
    have hdLeftB : d.left.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
      rw [hLeft]
      exact hxRight
    have hdRightA : d.right.1 ∈ weakFreeLeftPart
        (sL := iLeft) (iL := jLeft) f := by
      rw [hRight]
      exact haLeft
    by_cases hOldRootCaptured :
        ∃ i : Fin n, P.roots i ∈
          functionalComponentFrom Source
            (Set.range d.roots) d.left
    · exact Or.inr ⟨x, T, y, m, d, hxK, hxRight,
        hYa, hT, hm, hProper, hRootIn, hLeft, hRight,
        hExactRoot, Or.inl hOldRootCaptured⟩
    · by_cases hAMixed :
          ∃ z : V, z ∈ functionalComponentFrom Source
              (Set.range d.roots) d.left ∧
            z ∈ weakFreeLeftPart
              (sL := iLeft) (iL := jLeft) f
      · exact Or.inr ⟨x, T, y, m, d, hxK, hxRight,
          hYa, hT, hm, hProper, hRootIn, hLeft, hRight,
          hExactRoot, Or.inr hAMixed⟩
      · have hNoOldRootCaptured :
            ∀ r : V, r ∈ Set.range P.roots →
              r ∉ functionalComponentFrom Source
                (Set.range d.roots) d.left := by
          intro r hr hrc
          obtain ⟨i, hi⟩ := hr
          exact hOldRootCaptured ⟨i, hi.symm ▸ hrc⟩
        have hNoAInsideD : ∀ z : V,
            z ∈ functionalComponentFrom Source
              (Set.range d.roots) d.left →
            z ∉ weakFreeLeftPart
              (sL := iLeft) (iL := jLeft) f := by
          intro z hz hA
          exact hAMixed ⟨z, hz, hA⟩
        -- Both precisely identified geometric obstructions are absent:
        -- the checked original same-Q actual-outer flip now applies.
        obtain ⟨hDproper, V', New, hNew, hFiniteNew, flip,
            newOuter, hFlip, hCoords, hSymbol, hRank, hExterior,
            anew, haInOuter, haSameTarget, haNewA,
            hNewRootInj, hNewNativeBoundaryInj⟩ :=
          claim2_smallerRoot_noOldCapture_noA_hasFullInvariantFlip
            F hFiniteF Source hFinite hForbidden
            P d hm hn
            hdRootInOuter hdLeftInOuter hdRightInOuter
            hNoOldRootCaptured
            Target f hf Left Right jLeft jRight
            X iLeft iRight hFree hCommon
            hdRootInSeam hNoAInsideD hDrootInj hdLeftB hdRightA
            hOldOuterRootTargetInj hActiveBoundaryInjective
        have haSameA : flip anew = f a := by
          simpa only [hRight] using haSameTarget
        exact Or.inl ⟨m, d, hm, hDproper, V', New, hNew,
          hFiniteNew, flip, newOuter, hFlip, hCoords, hSymbol,
          hRank, hExterior,
          ⟨anew, haInOuter, haSameA, haNewA,
            hNewRootInj, hNewNativeBoundaryInj⟩⟩

end AllThoseRamseyClasses.Lifts
