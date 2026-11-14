import AllThoseRamseyClasses.Lifts.Claim2SmallerMixedFiniteDescent

/-!
# A noncapturing A-mixed smaller piece is itself a positive-B-rank state

In the original 2019 Claim 2 source, the smaller-root branch can be
A-mixed. This is a genuine opportunity for a *nested geometric
state* provided its selected component does not capture the old
outer root: the entire smaller piece then has STRICTLY fewer
original SOURCE vertices and inherits the local generated B-active
boundary-injectivity hypothesis from the old outer piece.

The actual A-exclusive source vertex in the mixed component gives
an A-anchor IN the new smaller piece, and the selected B-exclusive
d.left gives POSITIVE B-SOURCE rank inside it. The entire d root
was already in the full target seam with injective ordered target
coordinates, so no new root-collision assumption is introduced.

The A/B source witnesses and no-capture hypothesis are all explicit.
This does not prove that every smaller-root alternative avoids
capture, nor that nesting preserves the old outer canonical symbol.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine noncapturing A-mixed smaller native root yields a
proper smaller actual source piece and a complete positive-B-rank,
A-anchored LOCAL generated-boundary-injective geometric state.

The strict measure is SOURCE piece cardinality (not root width m,
and never a cardinality of weak-map target images). -/
theorem claim2_smallerRoot_noCapture_mixed_has_smallerPositiveState
    {V UX UA UB UT : Type}
    (Source : Structure L V) (hFinite : Finite V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hNewRootInOldPiece :
      Set.range d.roots ⊆ geometricPieceVertices Source P)
    (hDleftInOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hDrightInOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hNoOldRootCapture :
      ∀ r : V, r ∈ Set.range P.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.left)
    (Target : Structure L UT) (f : V → UT)
    (X : Structure L UX) (Left : Structure L UA)
    (Right : Structure L UB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hOldLocalInjection :
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
    (hDRootInSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hDRootTargetInjective :
      Function.Injective (fun i : Fin m => f (d.roots i)))
    (hDleftRight : d.left.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hMixed :
      ∃ a : V,
        a ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left ∧
        a ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f) :
    geometricPieceVertices Source d ⊂
      geometricPieceVertices Source P ∧
    Nat.card {v : V // v ∈ geometricPieceVertices Source d} <
      Nat.card {v : V // v ∈ geometricPieceVertices Source P} ∧
    Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∧
    Function.Injective (fun i : Fin m => f (d.roots i)) ∧
    ∃ a : V,
      a ∈ geometricPieceVertices Source d ∧
      a ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f ∧
      0 < Nat.card {v : V //
        v ∈ geometricPieceVertices Source d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
      (∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source d →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) := by
  classical
  obtain ⟨hProper, hLocalInj, hSizeDrop⟩ :=
    claim2_smallerRoot_noCapture_finiteProperDescent
      Source hFinite P d hNewRootInOldPiece
      hDleftInOld hDrightInOld hNoOldRootCapture
      Target f X Left Right iLeft iRight jLeft jRight
      hOldLocalInjection
  have hTargetAgree : ∀ r : UX,
      jRight (iRight r) = jLeft (iLeft r) := by
    intro r
    exact ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  have hDleftSwapped :
      d.left.1 ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hDleftRight.1, ?_⟩
    intro hRootR
    obtain ⟨r, hr⟩ := hRootR
    apply hDleftRight.2
    exact ⟨r, (hTargetAgree r).symm.trans hr⟩
  have hDleftB :
      f d.left.1 ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeLeftPart_iff_targetExclusive
      iRight jRight f d.left.1).mp hDleftSwapped
  have hDleftComp :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left :=
    componentFrom_root Source.graph (Set.range d.roots) d.left
  letI : Finite V := hFinite
  letI : Fintype V := Fintype.ofFinite V
  have hBNonempty :
      Nonempty {v : V //
        v ∈ geometricPieceVertices Source d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
    ⟨⟨d.left.1, Or.inr hDleftComp, hDleftB⟩⟩
  have hPositiveB :
      0 < Nat.card {v : V //
        v ∈ geometricPieceVertices Source d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hBNonempty
  obtain ⟨a, haComp, haLeft⟩ := hMixed
  exact ⟨hProper, hSizeDrop, hDRootInSeam,
    hDRootTargetInjective, a, Or.inr haComp,
    haLeft, hPositiveB, hLocalInj⟩

end AllThoseRamseyClasses.Lifts
