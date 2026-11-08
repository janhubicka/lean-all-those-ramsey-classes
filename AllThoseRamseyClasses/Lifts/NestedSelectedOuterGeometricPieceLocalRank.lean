import AllThoseRamseyClasses.Lifts.NestedSelectedGlobalOuterPieceSymbol

/-!
# Track A/C: genuine older geometric source piece with local B-support decrease

The global-symbol construction with its exact geometric CARRIER
identity now lives in NestedSelectedGlobalOuterPieceSymbol. This module
reuses that theorem for the strict local B-only SOURCE vertex rank drop,
with the same selected Q and the same New source. The underlying
geometric proof is no longer duplicated.

No root collision is resolved; the successor and terminal A-minimality
contradiction in the printed Claim 2 remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type}

/-- A strict B-exclusive SOURCE-vertex count decrease on the same
transported closed context is a strict decrease on the vertex
set of an ACTUAL geometric minimal-closed-separator piece,
with its entire original ordered root and global symbol.

The theorem retains its exact carrier equation, to avoid
identifying two separately chosen existential replacements. -/
theorem nestedGeometric_selectedFlip_strictLocalRank_on_newGeometricPiece
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (hm : 0 < m)
    {UT : Type}
    (f : V → UT) (flip : W → UT)
    (BOnly : Set UT)
    (hStrictContext :
      Nat.card {w : W //
        w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Old outer inner)) ∧
        flip w ∈ BOnly} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ BOnly}) :
    ∃ (hFiniteNew : Finite W)
      (newOuter : GeometricFunctionalPieceData New m),
      (∀ i : Fin m,
        newOuter.roots i =
          iE (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
              (geometricGlobalComplementChart Old inner).Carrier)) ∧
      geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm =
        geometricGlobalPieceSymbol F New
          hFiniteNew hFNew newOuter hm ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter ∧
      Nat.card {w : W //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ BOnly} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Old outer ∧
          f v ∈ BOnly} := by
  obtain ⟨hFiniteNew, newOuter, hRoots, hSymbol, hCarrier⟩ :=
    nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier
      F Old hFOld inner outer hNested
      Q hSelected hEq New hFNew iQ iE hFree hm
  have hRank :
      Nat.card {w : W //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ BOnly} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Old outer ∧
          f v ∈ BOnly} := by
    rw [← hCarrier]
    exact hStrictContext
  exact ⟨hFiniteNew, newOuter, hRoots, hSymbol, hCarrier, hRank⟩

end AllThoseRamseyClasses.Lifts
