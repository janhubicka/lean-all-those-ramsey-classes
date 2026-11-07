import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.MinimalSeparatorForward

/-!
# Re-enumerate a genuine geometric piece's whole closed root and swap its sides

The original Section 3 global canonical piece symbols retain the
ENTIRE ordered root tuple, not just its underlying vertex set.
The generic finite minimal-separator reconstruction may return a
different enumeration of the same closed root and may orient its
selected component towards the older preserved exterior instead
of towards the new inserted Q component.

This elementary, source-native, total-function-arity-independent
lemma transports an actual minimal closed separator to ANY
injective enumeration of the SAME exact root set, simultaneously
swapping its selected and opposite components.

No root quotient, no weak target image identification and no
new generated-boundary hypothesis is needed; the original
minimality certificate supplies both boundary equalities.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Minimal closed separation transports across equality of the complete cut,
with the two chosen outside-root vertices identified by their underlying
source vertices. The subtype proof fields are propositionally irrelevant. -/
private theorem minimalSeparator_transport_equalCut
    (A : Structure L V) {R S : Set V}
    (h : S = R)
    (x : {v : V // v ∉ R}) (y : {v : V // v ∉ R})
    (x' : {v : V // v ∉ S}) (y' : {v : V // v ∉ S})
    (hx : x'.1 = x.1) (hy : y'.1 = y.1)
    (hmin : IsMinimalClosedSeparator A R x y) :
    IsMinimalClosedSeparator A S x' y' := by
  subst S
  have hx' : x' = x := Subtype.ext hx
  have hy' : y' = y := Subtype.ext hy
  simpa only [hx', hy'] using hmin

/-- An ACTUAL geometric functional piece may be re-enumerated
by the prescribed original root tuple and reoriented towards its
opposite component, with no change to the full closed separator.

This is a direct transport of a proved minimal-closed-separator
witness, not an assumption that the root set determines the
original orientation or the canonical-lift symbol. -/
theorem geometricPiece_reorderRoot_and_swap
    (A : Structure L V) {n m : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (newRoots : Fin m → V)
    (hInjective : Function.Injective newRoots)
    (hExactRoot : Set.range newRoots = Set.range d.roots) :
    ∃ newPiece : GeometricFunctionalPieceData A m,
      newPiece.roots = newRoots ∧
      newPiece.left.1 = d.right.1 ∧
      newPiece.right.1 = d.left.1 ∧
      Set.range newPiece.roots = Set.range d.roots := by
  let x : {v : V // v ∉ Set.range newRoots} :=
    ⟨d.right.1, by
      rw [hExactRoot]
      exact d.right.2⟩
  let y : {v : V // v ∉ Set.range newRoots} :=
    ⟨d.left.1, by
      rw [hExactRoot]
      exact d.left.2⟩
  have hSwap :
      IsMinimalClosedSeparator A (Set.range d.roots)
        d.right d.left :=
    minimalClosedSeparator_swap A (Set.range d.roots)
      d.left d.right d.minimal
  have hNewMin :
      IsMinimalClosedSeparator A (Set.range newRoots) x y :=
    minimalSeparator_transport_equalCut
      A hExactRoot d.right d.left x y rfl rfl hSwap
  let newPiece : GeometricFunctionalPieceData A m := {
    roots := newRoots
    roots_injective := hInjective
    left := x
    right := y
    minimal := hNewMin
  }
  exact ⟨newPiece, rfl, rfl, rfl, hExactRoot⟩

end AllThoseRamseyClasses.Lifts
