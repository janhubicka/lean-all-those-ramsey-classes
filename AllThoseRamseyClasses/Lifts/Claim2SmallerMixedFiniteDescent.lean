import AllThoseRamseyClasses.Lifts.Claim2SmallerMixedNestedBoundary

/-!
# Strict finite SOURCE-vertex measure for a properly nested smaller root

The genuinely A-mixed smaller-root alternative may require descending
inside a proper old-source subpiece rather than a B-to-A source flip.
The no-old-root-capture hypothesis gives actual proper source-set
containment and hence a strict finite cardinal descent. At the same
time, the local B-active full generated-boundary injectivity invariant
restricts to the smaller piece without assuming it is A-free.

This is the precise finite measure for a possible nested-piece
well-founded induction; it does not solve the independent old-root
capture alternative or guarantee positivity/mixedness of a chosen
smaller piece without corresponding source witnesses.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Proper inclusion between subsets of a finite SOURCE carrier
strictly decreases the cardinality of their actual subtype
vertex sets. Unlike a weak EHN target-image count, this
counts each genuine source vertex exactly once. -/
theorem finiteSourceSubtype_card_lt_of_proper
    {V : Type} (hFinite : Finite V) (S T : Set V)
    (hProper : S ⊂ T) :
    Nat.card {v : V // v ∈ S} <
      Nat.card {v : V // v ∈ T} := by
  classical
  letI : Finite V := hFinite
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨hSubset, hNe⟩ :=
    Set.ssubset_iff_subset_ne.mp hProper
  let e : {v : V // v ∈ S} ↪ {v : V // v ∈ T} := {
    toFun := fun v => ⟨v.1, hSubset v.2⟩
    inj' := by
      intro a b hab
      have hab' : (a : V) = (b : V) :=
        congrArg (fun z : {v : V // v ∈ T} => (z : V)) hab
      exact Subtype.ext hab'
  }
  have hNotSurj : ¬ Function.Surjective e := by
    intro hSurj
    have hBack : T ⊆ S := by
      intro v hvT
      obtain ⟨a, ha⟩ := hSurj (⟨v, hvT⟩ : {v : V // v ∈ T})
      have hVal : a.1 = v := congrArg Subtype.val ha
      exact hVal ▸ a.2
    exact hNe (Set.Subset.antisymm hSubset hBack)
  have hCard :
      Fintype.card {v : V // v ∈ S} <
        Fintype.card {v : V // v ∈ T} :=
    Fintype.card_lt_of_injective_not_surjective
      e e.injective hNotSurj
  simpa only [Nat.card_eq_fintype_card] using hCard

/-- If a smaller genuine closed separator does not capture any
old outer-root source vertex, then both proper source nesting and
persistence of LOCAL B-active boundary injection hold, and the
finite number of source vertices in that piece STRICTLY decreases.
No A-free/one-sidedness assumption is used. -/
theorem claim2_smallerRoot_noCapture_finiteProperDescent
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
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) :
    geometricPieceVertices Source d ⊂
      geometricPieceVertices Source P ∧
      (∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source d →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) ∧
      Nat.card {v : V // v ∈ geometricPieceVertices Source d} <
      Nat.card {v : V // v ∈ geometricPieceVertices Source P} := by
  obtain ⟨hProper, hLocalInj⟩ :=
    claim2_smallerRoot_noCapture_proper_and_localBoundaryInj
      Source P d hNewRootInOldPiece hDleftInOld hDrightInOld
      hNoOldRootCapture Target f X Left Right
      iLeft iRight jLeft jRight hOldLocalInjection
  exact ⟨hProper, hLocalInj,
    finiteSourceSubtype_card_lt_of_proper hFinite
      (geometricPieceVertices Source d)
      (geometricPieceVertices Source P) hProper⟩

end AllThoseRamseyClasses.Lifts
