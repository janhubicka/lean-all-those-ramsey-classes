import AllThoseRamseyClasses.Lifts.Claim2BoundaryPartnerOrSmallerRoot
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# Claim 2: select the true opposite A-only vertex automatically

The partner-or-smaller-root theorem is purely source geometric,
but its input included an arbitrary opposite vertex y already
certified to be separated from the B-only component after
deleting its complete generated boundary T.

For an ACTUAL weak EHN source map into an actual native full
functional free amalgam, this is not an independent hypothesis:
any chosen A-exclusive SOURCE vertex a is separated from a
B-exclusive S-component by T=Cl(N(B)). The existing checked
monochromatic-component theorem supplies the whole separation
without global injectivity or any support-minimality of the source.

Under an actual full-source Gaifman path connecting the B vertex
and a, the untouched opposite a-component's generated boundary
either equals T (the genuine partner needed for the verified
contextual B→A flip) or is a STRICTLY smaller POSITIVE-width
minimal closed separator root U within S∩P. The distinguished
new right-side geometric endpoint is literally a.

In the uncovered case, the selected component of the new
smaller-root geometric piece may become mixed. We do not silently
declare it flippable: controlling that possibility is the open
general-width positive-B-rank successor obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A positive finite count of B-exclusive SOURCE vertices inside
a genuine geometric outer piece produces an actual right-exclusive
source vertex x in its selected nonroot component.

No assumption of minimality or injectivity of the EHN source map is
needed. The old ordered geometric root lies in the shared seam and
therefore cannot itself contribute to exclusive-right support. -/
theorem claim2_positiveLocalRightSupport_hasComponentVertex
    {V UX UA UB UT : Type}
    [Finite V]
    (Source : Structure L V)
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (f : V → UT)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hPositive : 0 < Nat.card {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f},
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      x.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
  classical
  letI : Fintype {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
    Fintype.ofFinite _
  have hCard : 0 < Fintype.card {v : V //
      v ∈ geometricPieceVertices Source P ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    simpa only [Nat.card_eq_fintype_card] using hPositive
  obtain ⟨⟨v, hvP, hvB⟩⟩ := (Fintype.card_pos_iff).mp hCard
  obtain ⟨⟨b, hb⟩, hNoCommonRight⟩ := hvB
  have hvRight : v ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
    refine ⟨⟨b, hb.symm⟩, ?_⟩
    intro hRoot
    obtain ⟨r, hr⟩ := hRoot
    have hrOverlap :
        jLeft (iLeft r) = jRight (iRight r) :=
      (hFree.overlap (iLeft r) (iRight r)).mpr
        ⟨r, rfl, rfl⟩
    exact hNoCommonRight
      ⟨r, hrOverlap.symm.trans hr⟩
  have hvComp :
      v ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
    rcases hvP with hvRoot | hvComponent
    · exact False.elim (hvRight.2 (hOuterRootInSeam hvRoot))
    · exact hvComponent
  exact ⟨⟨v, hvRight.2⟩, hvRight, hvComp⟩

/-- A real B-only source component and a connected A-only
source vertex inside a genuine outer geometric piece automatically
select the opposite witness and yield an exhaustive geometric
partner / strictly smaller positive-width-root alternative.

No intermediate left-support minimality, full weak-map
injectivity, partner existence or root width restriction
is postulated. The finite source and a true full target
free amalgam are the only structural hypotheses. -/
theorem claim2_actualOppositeColors_partner_or_positiveSmallerRoot
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hOuterRootInSeam :
      Set.range P.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (x : {v : V // v ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hxOuter : x.1 ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (haOuter : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (hConnected : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅}))
    (T : Set V)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))) :
    ∃ (y : {v : V // v ∉ T}),
      y.1 = a ∧
      (Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y)) = T ∨
       ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
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
  letI : Finite V := hFinite
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  have hSclosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft) f hf.1
  have hTS : T ⊆ S := by
    intro z hz
    exact functionalClosure_neighborhood_subset_cut
      Source S hSclosed x
      (by simpa only [hT] using hz)
  obtain ⟨y, hYa, hSep⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree f hf x hxRight T hT hTS a haLeft
  have hPathY : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨y.1, by simp⟩ : {v : V // v ∉ ∅}) := by
    simpa only [hYa] using hConnected
  rcases geometricInnerBoundary_partner_or_positiveSmallerRoot
      Source P S hSclosed hOuterRootInSeam
      x hxOuter T hT hTS y hSep hPathY with
    hPartner | ⟨m, d, hm, hRootProper, hRootInside, hLeft, hRight, hU⟩
  · exact ⟨y, hYa, Or.inl hPartner⟩
  · refine ⟨y, hYa, Or.inr ⟨m, d, hm,
      hRootProper, hRootInside, hLeft, ?_, hU⟩⟩
    exact hRight.trans hYa

end AllThoseRamseyClasses.Lifts
