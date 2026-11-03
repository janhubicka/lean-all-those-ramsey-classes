import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.MinimalSeparatorReverse

/-!
# Recover a genuine geometric piece with EXACTLY the old root order

The original Section 3 piece relation uses ordered Fin n roots.
The older finite minimal-separator selection theorem may enumerate
the new separating cut by a DIFFERENT Fin k root ordering. For
Claim 2, however, the transported old ordered tuple must be kept:
it determines the same actual added global relation symbol.

This elementary but important native functional source statement
says that if the FULL ordered root is injective and function-closed,
both opposite components have generated neighbourhood boundary
equal to its entire root, and the components are genuinely distinct,
then the exact same Fin n tuple is the root of a genuine geometric
minimal-separator piece. If an intended context K is already proved
equal to this root plus one whole component, it is EXACTLY the
piece's entire source vertex set.

The two complete generated-boundary assumptions and the context
carrier equality are NOT inferred here. They remain substantive
Track A obligations after an actual inner source flip. No forbidden
source quotient or weak target-map injectivity is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Reconstruct an ACTUAL geometric minimal-closed-separator piece
with the entire prescribed original root tuple, not merely some
existentially reordered finite enumeration.

The named context is required to be exactly the closed root and
the single selected outside-root component; this is the missing
geometric identity in contextual Claim 2, not a consequence of
mere function-closedness. -/
theorem geometricPiece_of_prescribedRoot_and_exactBoundaries
    {W : Type v} (New : Structure L W) {n : ℕ}
    (roots : Fin n → W)
    (hRoots : Function.Injective roots)
    (hClosed : New.IsClosed (Set.range roots))
    (x y : {w : W // w ∉ Set.range roots})
    (hSeparated : ¬ ReachOutside New.graph (Set.range roots) x y)
    (hLeftBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) x)) =
            Set.range roots)
    (hRightBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) y)) =
            Set.range roots)
    (K : Set W)
    (hExactContext :
      K = Set.range roots ∪
        componentFrom New.graph (Set.range roots) x) :
    ∃ d : GeometricFunctionalPieceData New n,
      d.roots = roots ∧
      d.left.1 = x.1 ∧
      d.right.1 = y.1 ∧
      geometricPieceVertices New d = K := by
  let hMinimal : IsMinimalClosedSeparator New
      (Set.range roots) x y :=
    minimalClosedSeparator_of_bothBoundaries_eq New
      (Set.range roots) hClosed x y hSeparated
      hLeftBoundary hRightBoundary
  let d : GeometricFunctionalPieceData New n := {
    roots := roots
    roots_injective := hRoots
    left := x
    right := y
    minimal := hMinimal
  }
  refine ⟨d, rfl, rfl, rfl, ?_⟩
  change Set.range roots ∪
    componentFrom New.graph (Set.range roots) x = K
  exact hExactContext.symm

end AllThoseRamseyClasses.Lifts
