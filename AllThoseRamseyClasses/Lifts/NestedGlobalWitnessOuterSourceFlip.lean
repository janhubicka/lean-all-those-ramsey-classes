import AllThoseRamseyClasses.Lifts.NestedActualGlobalWitnessOuterRelation
import AllThoseRamseyClasses.Lifts.NestedSelectedGlobalOuterPieceSymbol
import AllThoseRamseyClasses.Lifts.GeometricFlipOuterExteriorSupport

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

/-- An ORIGINAL inner global canonical relation supplies an ACTUAL
selected-Q forbidden full-functional source replacement. The SAME
selected Q and new source yield one genuinely nested outer geometric
piece with its exact transported carrier, ordered outer roots, global
piece symbol, unchanged target coordinates, and equality of exterior
SOURCE vertex counts for every target subset.

No injectivity of the outer target-root tuple is assumed. The source
certificate and source-count invariance are valid even if this tuple
collides; a target canonical outer relation would still require
injectivity. Neither the existence of an eligible inner global witness
at every Claim 2 state nor the terminal minimizer argument follows. -/
theorem nestedGeometric_actualGlobalWitness_restores_outerSourceSymbol_withExterior
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
    ∃ (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Old inner).root)
      (W : Type) (New : Structure L W) (hFNew : F New)
      (iQ : Structure.Embedding Q.str New)
      (iT : Structure.Embedding
        (geometricGlobalComplementChart Old inner).str New)
      (flip : W → UT)
      (hFiniteNew : Finite W)
      (newOuter : GeometricFunctionalPieceData New m),
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n ∧
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q ∧
      Structure.IsFreeAmalgam Q.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding
        iQ iT ∧
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iT b) = f b.1) ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iT '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter ∧
      (∀ i : Fin m,
        newOuter.roots i =
          iT (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
              (geometricGlobalComplementChart Old inner).Carrier)) ∧
      geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm =
        geometricGlobalPieceSymbol F New hFiniteNew hFNew newOuter hm ∧
      (∀ i : Fin m, flip (newOuter.roots i) = f (outer.roots i)) ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : W //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet}) := by
  obtain ⟨Q, _hRootPieceEq, hDiagram, hSelected,
      _g, _hg, _hgRoots, W, New,
      iQ, iT, flip, hFNew, hFree, hFlip,
      _hQAgree, hTAgree⟩ :=
    geometric_actualGlobalWitness_selectedFlip_withSelection
      F Old hFOld inner hn
      Target f hf B jB xsB hInnerGlobal hInnerCoordinates
  obtain ⟨hFiniteNew, newOuter, hRootCoords, hSymbol, hCarrier⟩ :=
    nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier
      F Old hFOld inner outer hNested
      Q hSelected hDiagram New hFNew iQ iT hFree hm
  have hTargetCoords :
      ∀ i : Fin m, flip (newOuter.roots i) = f (outer.roots i) := by
    intro i
    rw [hRootCoords i]
    exact hTAgree
      (⟨outer.roots i,
        nestedGeometric_outerRoot_avoids_innerComponent
          Old inner outer hNested i⟩ :
        (geometricGlobalComplementChart Old inner).Carrier)
  have hInnerRoot : ∀ i : Fin n,
      inner.roots i ∈ geometricPieceVertices Old outer :=
    nestedGeometric_innerRoot_in_outerPiece Old inner outer hNested
  have hInnerComponent :
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left ⊆
        geometricPieceVertices Old outer := by
    intro v hv
    exact Or.inr (hNested hv)
  have hExterior : ∀ TargetSet : Set UT,
      Nat.card {w : W //
        w ∉ geometricPieceVertices New newOuter ∧
        flip w ∈ TargetSet} =
      Nat.card {v : V //
        v ∉ geometricPieceVertices Old outer ∧
        f v ∈ TargetSet} := by
    intro TargetSet
    exact geometricFlip_actualOuterExterior_sourceSupport_card_eq
      Old outer inner hInnerRoot hInnerComponent
      Q New iQ iT hFree newOuter hCarrier
      f flip hTAgree TargetSet
  exact ⟨Q, W, New, hFNew, iQ, iT, flip,
    hFiniteNew, newOuter, hSelected, hDiagram,
    hFree, hFlip, hTAgree, hCarrier, hRootCoords,
    hSymbol, hTargetCoords, hExterior⟩

/-- Historical source-symbol and target-coordinate interface, now a
projection of the stronger SAME-witness exterior-support certificate. -/
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
  obtain ⟨_Q, W, New, hFNew, _iQ, _iT, flip,
      hFiniteNew, newOuter, _hSelected, _hDiagram,
      _hFree, hFlip, _hTAgree, _hCarrier, _hRootCoords,
      hSymbol, hTargetCoords, _hExterior⟩ :=
    nestedGeometric_actualGlobalWitness_restores_outerSourceSymbol_withExterior
      F Old hFOld inner outer hNested hn hm
      Target f hf B jB xsB hInnerGlobal hInnerCoordinates
  exact ⟨W, New, hFNew, hFiniteNew, newOuter,
    flip, hFlip, hSymbol, hTargetCoords⟩


end AllThoseRamseyClasses.Lifts
