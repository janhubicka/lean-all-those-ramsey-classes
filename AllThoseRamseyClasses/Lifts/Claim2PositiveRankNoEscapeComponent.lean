import AllThoseRamseyClasses.Lifts.Claim2ClosedContextNoEscape
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# Track C: positive B-source rank selects a monochromatic component inside ANY no-escape context

The successful literal B-to-A contextual flip need not preserve
an OUTER geometric minimal-closed-separator piece. We instead
consider any source subset K which is function-closed and has
the no-escape property relative to the full preimage S of the
shared target root.

A positive number of B-exclusive SOURCE vertices in K implies
that a concrete right-exclusive source vertex x lies in K
outside S. Its ENTIRE native Gaifman S-component is B-only
by the true full free-amalgam monochromatic-component theorem,
even for a globally noninjective weak EHN source map.

Because K has no outgoing Gaifman incidence at a vertex
outside S, this WHOLE component lies inside K. Since both
S and K are function-closed, the COMPLETE generated external
neighbourhood boundary T = Cl(N(component(Source-S,x)))
is contained in S∩K.

This obtains the exact source-geometric inputs for the
partner-based proper inner geometric-piece construction
without asserting K itself is a geometric minimal separator.
It needs no old left-support minimality or global image quotient.

The true remaining positive-B-rank successor obstacles are:
finding a matching opposite generated-boundary partner (or a
legitimate replacement in its absence), preserving injectivity
on T, and eventually constructing a selected geometric piece
for the final original-global canonical lift.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- From the positive finite B-exclusive SOURCE rank inside any
function-closed, no-escape context K, select a genuine B-only
component and localize its COMPLETE function-generated boundary
in the current source's seam S and the same contextual K.

This is independent of intermediate A-source support minimization
and does not require K to be a source-geometric minimal-cut piece. -/
theorem positiveLocalRightSupport_noEscape_hasInnerComponent
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
    (K : Set V)
    (hKclosed : Source.IsClosed K)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) K)
    (hPositive :
      0 < Nat.card {v : V //
        v ∈ K ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
      (T : Set V),
      x.1 ∈ K ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      componentFrom Source.graph
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x ⊆ K ∧
      (∀ z : V,
        z ∈ componentFrom Source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x →
        z ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f) ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      T ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩ K := by
  classical
  letI : Finite V := hFinite
  letI : Fintype {v : V //
      v ∈ K ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
    Fintype.ofFinite _
  have hCard : 0 < Fintype.card {v : V //
      v ∈ K ∧
      f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    simpa only [Nat.card_eq_fintype_card] using hPositive
  obtain ⟨⟨v, hvK, hvB⟩⟩ := (Fintype.card_pos_iff).mp hCard
  obtain ⟨⟨b, hb⟩, hNoCommonRight⟩ := hvB
  have hvRight : v ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
    refine ⟨⟨b, hb.symm⟩, ?_⟩
    intro hRoot
    obtain ⟨r, hr⟩ := hRoot
    have hOverlap : jLeft (iLeft r) = jRight (iRight r) :=
      (hFree.overlap (iLeft r) (iRight r)).mpr
        ⟨r, rfl, rfl⟩
    exact hNoCommonRight ⟨r, hOverlap.symm.trans hr⟩
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  let x : {v : V // v ∉ S} := ⟨v, hvRight.2⟩
  have hSclosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft) f hf.1
  have hCompInside :
      componentFrom Source.graph S x ⊆ K :=
    functionalNoEscape_wholeComponent_insideContext
      Source S K hNoEscape x hvK
  have hCompRight : ∀ z : V,
      z ∈ componentFrom Source.graph S x →
      z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
    intro z hz
    exact weakFreePartition_component_right
      hFree f hf.1 x hvRight hz
  let T : Set V := Source.functionClosure
    (gaifmanNeighborhood Source.graph
      (componentFrom Source.graph S x))
  have hTInside : T ⊆ S ∩ K :=
    functionalNoEscape_component_generatedBoundary_inside
      Source S K hSclosed hKclosed hNoEscape x hvK
  exact ⟨x, T, hvK, hvRight, hCompInside,
    hCompRight, rfl, hTInside⟩

end AllThoseRamseyClasses.Lifts
