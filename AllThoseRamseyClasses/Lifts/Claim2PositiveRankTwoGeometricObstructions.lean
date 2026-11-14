import AllThoseRamseyClasses.Lifts.Claim2PositiveRankActiveBoundaryDichotomy
import AllThoseRamseyClasses.Lifts.Claim2SmallerRootNoCaptureGeometricFlip

/-!
# Positive B-source rank: an actual flip or two precise geometric obstructions

The verified active-boundary source dichotomy supplies a same-selected-Q
B-to-A flip, or a positive smaller rooted geometric source piece whose
selected component might be mixed or capture an older root vertex.

The independently checked conditional smaller-root theorem proves
a genuinely selected B-to-A flip if the smaller piece captures no OLD
outer-root vertex and its selected component contains NO A-exclusive
SOURCE vertex. The smaller root is also automatically TARGET-injective
because it lies in the chosen B-component's generated boundary.

Combining these WITHOUT any additional assumption yields:
* an actual full native selected-Q rank-decreasing source flip,
  preserving the original global symbol, every exterior SOURCE count,
  and a surviving A-exclusive source anchor;
* OR a literal original outer-root source vertex CAPTURED by the new
  smaller selected source component;
* OR an A-exclusive SOURCE vertex inside that smaller component.

The last alternatives are genuine remaining obligations. Neither
is claimed impossible or merely ruled out by root-width notation.
No assumption of injectivity on the entire weak target seam,
no quotient of target images, and no change to the frozen 2019 paper.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Positive B-exclusive SOURCE rank with a single outer A-anchor and
injectively mapped B-component generated boundaries. The failure
of an actual rank-decreasing B-to-A replacement must be witnessed
by a specific smaller native geometric separator component which
either captures one of the OLD complete outer-root vertices or
contains a literal A-exclusive source vertex.

In particular, there is no separate target seam-collision branch and
no hidden root-image injectivity hypothesis. -/
theorem claim2_positiveRank_actualStep_or_oldRootCapture_or_AMixed_of_activeBoundaryInj
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
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
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
          flip anew ∈ fullFreeLeftExclusiveTarget iLeft jLeft)) ∨
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
      (claim2_positiveRank_actualSuccessor_or_smallerRoot_of_activeBoundaryInjective
        F hFiniteF hConnected Source hFinite hForbidden
        P hn Target f hf Left Right jLeft jRight
        X iLeft iRight hFree hCommon hOuterRootInSeam
        a haK haLeft hPositiveB hActiveBoundaryInjective) with
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
            anew, haInOuter, haSameTarget, haNewA⟩ :=
          claim2_smallerRoot_noOldCapture_noA_hasActualGeometricFlip
            F hFiniteF Source hFinite hForbidden
            P d hm hn
            hdRootInOuter hdLeftInOuter hdRightInOuter
            hNoOldRootCaptured
            Target f hf Left Right jLeft jRight
            X iLeft iRight hFree hCommon
            hdRootInSeam hNoAInsideD hDrootInj hdLeftB hdRightA
        have haSameA : flip anew = f a := by
          simpa only [hRight] using haSameTarget
        exact Or.inl ⟨m, d, hm, hDproper, V', New, hNew,
          hFiniteNew, flip, newOuter, hFlip, hCoords, hSymbol,
          hRank, hExterior,
          ⟨anew, haInOuter, haSameA, haNewA⟩⟩

end AllThoseRamseyClasses.Lifts
