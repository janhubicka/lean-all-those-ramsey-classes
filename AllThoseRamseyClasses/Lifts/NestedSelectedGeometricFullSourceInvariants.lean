import AllThoseRamseyClasses.Lifts.NestedSelectedOuterGeometricPieceLocalRank
import AllThoseRamseyClasses.Lifts.GeometricFlipOuterExteriorSupport

/-!
# One selected-Q nested source flip preserves ALL geometric step invariants

Combine the already proved native source geometry of the genuine
selected nested replacement with the exact exterior-support
bijection. For ONE actual full native forbidden source replacement,
the reconstructed older piece has:
* the original ordered full root;
* the original globally indexed incompatibility class symbol;
* exactly the new transported closed context as its ENTIRE carrier;
* strictly fewer B-exclusive SOURCE vertices INSIDE this very piece;
* unchanged weak target coordinates of the original ordered root;
* equal numbers of SOURCE vertices OUTSIDE the respective pieces
  whose target images lie in ANY specified target subset.

The last property is stronger than merely preserving the right-
exclusive source count: it applies to both sides' exclusive target
parts and any other original target predicate. It relies on exact
old/new complement agreement, not target-map injectivity.

This theorem has an EXISTING SAME-Q replacement as input. Track C's
merged concrete selected right-to-left flip (#929) constructs that
input in its one-step hypotheses. Existence of a suitable inner flip
at EVERY positive-rank state, persistence of A-minimality, and the
terminal A-to-B contradiction are still unproved obligations.

There is no comparison of unrelated replacement Q witnesses and
no claim that a target-weak image quotient is a full source.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W UT : Type}

/-- All geometric, ordered-root, global-symbol, local inside-rank and
complete exterior source-support count invariants for ONE actual
genuinely selected nested native functional replacement.

The target map may collide on vertices. The original full ordered
outer-root target COORDINATES remain the same (not necessarily
injective), and the original global class symbol is equal. -/
theorem nestedGeometric_selectedFlip_fullSourceStepInvariants
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
    (f : V → UT) (flip : W → UT)
    (hSameE : ∀ b : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE b) = f b.1)
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
      (∀ i : Fin m,
        flip (newOuter.roots i) = f (outer.roots i)) ∧
      Nat.card {w : W //
          w ∈ geometricPieceVertices New newOuter ∧
          flip w ∈ BOnly} <
        Nat.card {v : V //
          v ∈ geometricPieceVertices Old outer ∧
          f v ∈ BOnly} ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : W //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet}) := by
  obtain ⟨hFiniteNew, newOuter, hRootCoords,
      hSymbol, hCarrier, hRank⟩ :=
    nestedGeometric_selectedFlip_strictLocalRank_on_newGeometricPiece
      F Old hFOld inner outer hNested
      Q hSelected hEq New hFNew iQ iE hFree hm
      f flip BOnly hStrictContext
  letI : Finite W := hFiniteNew
  have hInnerRoot : ∀ i : Fin n,
      inner.roots i ∈ geometricPieceVertices Old outer :=
    nestedGeometric_innerRoot_in_outerPiece
      Old inner outer hNested
  have hInnerComponent :
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left ⊆
          geometricPieceVertices Old outer := by
    intro w hw
    exact Or.inr (hNested hw)
  have hTargetRootCoords : ∀ i : Fin m,
      flip (newOuter.roots i) = f (outer.roots i) := by
    intro i
    calc
      flip (newOuter.roots i) =
          flip (iE (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)) :=
          congrArg flip (hRootCoords i)
      _ = f (outer.roots i) :=
          hSameE (⟨outer.roots i,
            nestedGeometric_outerRoot_avoids_innerComponent
              Old inner outer hNested i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)
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
      Q New iQ iE hFree newOuter hCarrier
      f flip hSameE TargetSet
  exact ⟨hFiniteNew, newOuter, hRootCoords, hSymbol,
    hCarrier, hTargetRootCoords, hRank, hExterior⟩

end AllThoseRamseyClasses.Lifts
