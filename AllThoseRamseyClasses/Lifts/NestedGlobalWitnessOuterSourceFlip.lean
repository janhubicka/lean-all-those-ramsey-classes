import AllThoseRamseyClasses.Lifts.NestedActualGlobalWitnessOuterRelation
import AllThoseRamseyClasses.Lifts.NestedSelectedGlobalOuterPieceSymbol

/-!
# Genuine inner global witness restores an actual nested outer source symbol

Combine the exact selected-Q source witness with the already verified
nested-geometric source reconstruction. Given the original inner global
canonical relation in a second witness B, this exports an ACTUAL new
forbidden full-functional source, a weak EHN target map, and a genuine
outer minimal-separator piece with the ORIGINAL indexed global symbol
and the ORIGINAL outer target-root coordinates.

The old outer target-root image is NOT assumed injective, because the
conclusion is SOURCE-symbol equality and coordinate agreement, not
realization of the original global relation at a colliding target tuple.
The positive inner global relation, its exact coordinates, true nesting,
and the positive widths remain explicit inputs. No unrestricted Claim 2
successor or strong amalgamation result is claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V UB UT : Type}

/-- A realized genuine inner global symbol produces one literal forbidden
source replacement whose ACTUAL nested outer geometric piece retains the
original global piece symbol and every outer target-root coordinate.

This does not assume injectivity on the outer weak target-root tuple.
It does assume the inner global canonical relation is already present,
hence the inner source roots have distinct images. -/
theorem nestedGeometric_actualGlobalWitness_restores_outerSourceSymbol
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
      geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm =
        geometricGlobalPieceSymbol F New hFiniteNew hFNew newOuter hm ∧
      (∀ i : Fin m, flip (newOuter.roots i) = f (outer.roots i)) := by
  obtain ⟨Q, _hRootPieceEq, hDiagram, hSelected,
      _g, _hg, _hgRoots, W, New,
      iQ, iT, flip, hFNew, hFree, hFlip,
      _hQAgree, hTAgree⟩ :=
    geometric_actualGlobalWitness_selectedFlip_withSelection
      F Old hFOld inner hn
      Target f hf B jB xsB hInnerGlobal hInnerCoordinates
  obtain ⟨hFiniteNew, newOuter, hRootCoords, hSymbol, _hCarrier⟩ :=
    nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier
      F Old hFOld inner outer hNested
      Q hSelected hDiagram New hFNew iQ iT hFree hm
  refine ⟨W, New, hFNew, hFiniteNew, newOuter,
    flip, hFlip, hSymbol, ?_⟩
  intro i
  rw [hRootCoords i]
  exact hTAgree
    (⟨outer.roots i,
      nestedGeometric_outerRoot_avoids_innerComponent
        Old inner outer hNested i⟩ :
      (geometricGlobalComplementChart Old inner).Carrier)

end AllThoseRamseyClasses.Lifts
