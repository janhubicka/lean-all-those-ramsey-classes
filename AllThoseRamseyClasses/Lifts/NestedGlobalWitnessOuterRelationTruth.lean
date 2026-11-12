import AllThoseRamseyClasses.Lifts.NestedGlobalWitnessOuterSourceFlip
import AllThoseRamseyClasses.Lifts.GeometricGlobalTargetRelationCriterion

/-!
# Original global target relation truth under a genuine nested source flip

An actual selected-Q replacement preserves the ORIGINAL outer global
piece symbol and the exact ordered outer target tuple. Thus the truth
value of the ORIGINAL global target relation is unchanged, even if the
old weak image identifies distinct outer root coordinates.

This is not a collision repair. By the independently verified original
global relation criterion, a colliding ordered root tuple makes the
relation false on both sides. The source-level conservation theorem,
and its all-target exterior SOURCE support counts, remain meaningful
in that situation.

The first theorem below is a simple congruence interface; the second
uses the SAME selected replacement witness from the verified Track A
source construction. No new Q, replacement source, or target map is
chosen independently.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V UB UT : Type}

/-- Equality of the original globally indexed source symbol together
with equality of ordered target-root coordinates makes the two
ORIGINAL global target relation propositions equivalent.

Neither weak-map injectivity nor even a homomorphism property is needed
for this purely symbolic congruence statement. -/
theorem geometricGlobalCanonicalRelation_iff_of_symbol_and_coordinates
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    (Old : Structure L V) (hFiniteOld : Finite V) (hFOld : F Old)
    {W : Type} (New : Structure L W)
    (hFiniteNew : Finite W) (hFNew : F New)
    {m : ℕ}
    (outer : GeometricFunctionalPieceData Old m)
    (newOuter : GeometricFunctionalPieceData New m)
    (hm : 0 < m)
    (Target : Structure L UT)
    (f : V → UT) (flip : W → UT)
    (hSymbol :
      geometricGlobalPieceSymbol F Old hFiniteOld hFOld outer hm =
        geometricGlobalPieceSymbol F New hFiniteNew hFNew newOuter hm)
    (hCoordinates :
      ∀ i : Fin m, flip (newOuter.roots i) = f (outer.roots i)) :
    (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol
          F Old hFiniteOld hFOld outer hm))
        (fun i : Fin m => f (outer.roots i)) ↔
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol
          F New hFiniteNew hFNew newOuter hm))
        (fun i : Fin m => flip (newOuter.roots i)) := by
  have hTuples :
      (fun i : Fin m => flip (newOuter.roots i)) =
        (fun i : Fin m => f (outer.roots i)) := by
    funext i
    exact hCoordinates i
  rw [hSymbol, hTuples]

/-- The same actual selected-Q forbidden source replacement produced by
the original inner global witness preserves the truth of the ORIGINAL
outer target global relation. It simultaneously retains the exact
ordered coordinates and exterior SOURCE-count conservation.

This theorem has NO outer target-root injection assumption. In the
collision case the relation equivalence is between two FALSE
propositions, not evidence for an injectivization. -/
theorem nestedGeometric_actualGlobalWitness_outerTargetRelation_iff_withExterior
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (hn : 0 < n) (hm : 0 < m)
    (Target : Structure L UT)
    (f : V → UT) (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (B : Structure L UB)
    (jB : Structure.Embedding B Target)
    (xsB : Fin n → UB)
    (hInnerGlobal :
      (globalFunctionalCanonicalLift F B).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld inner hn)) xsB)
    (hInnerCoordinates : ∀ i : Fin n,
      jB (xsB i) = f (inner.roots i)) :
    ∃ (W : Type) (New : Structure L W) (hFNew : F New)
      (hFiniteNew : Finite W)
      (newOuter : GeometricFunctionalPieceData New m)
      (flip : W → UT),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ i : Fin m, flip (newOuter.roots i) = f (outer.roots i)) ∧
      ((globalFunctionalCanonicalLift F Target).rel
          (.inr (geometricGlobalPieceSymbol F Old
            (inferInstance : Finite V) hFOld outer hm))
          (fun i : Fin m => f (outer.roots i)) ↔
        (globalFunctionalCanonicalLift F Target).rel
          (.inr (geometricGlobalPieceSymbol F New
            hFiniteNew hFNew newOuter hm))
          (fun i : Fin m => flip (newOuter.roots i))) ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : W //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet}) := by
  obtain ⟨_Q, W, New, hFNew, _iQ, _iT, flip,
      hFiniteNew, newOuter, _hSelected, _hDiagram,
      _hFree, hFlip, _hTAgree, _hCarrier, _hRootCoords,
      hSymbol, hTargetCoords, hExterior⟩ :=
    nestedGeometric_actualGlobalWitness_restores_outerSourceSymbol_withExterior
      F Old hFOld inner outer hNested hn hm
      Target f hf B jB xsB hInnerGlobal hInnerCoordinates
  refine ⟨W, New, hFNew, hFiniteNew, newOuter,
    flip, hFlip, hTargetCoords, ?_, hExterior⟩
  exact geometricGlobalCanonicalRelation_iff_of_symbol_and_coordinates
    F Old (inferInstance : Finite V) hFOld
    New hFiniteNew hFNew outer newOuter hm
    Target f flip hSymbol hTargetCoords

end AllThoseRamseyClasses.Lifts
