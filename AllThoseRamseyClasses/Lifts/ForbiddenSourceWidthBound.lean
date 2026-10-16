import AllThoseRamseyClasses.Lifts.GlobalFunctionalPieceLift
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Bounding every global piece-symbol arity by forbidden-source size

A genuine selected forbidden piece is induced by a MINIMAL CLOSED
separator of a FINITE member of the forbidden family. Its ordered
root list enumerates distinct source vertices. Thus its width is
at most the cardinality of that actual forbidden source.

If all members of the forbidden family have a uniform finite
cardinality bound N, every globally indexed piece-class relation
has arity ≤ N. This is a separate concrete bridge for finite
forbidden families, where a bound on the sizes of forbidden members
is immediate after taking finitely many isomorphism types.

The theorem does NOT claim regularity, finiteness of the piece
class quotient at each width, or precompactness on its own.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Actual global forbidden-piece symbols never have root arity
larger than the cardinality bound of their genuine finite forbidden
source witnesses. Neither a weak image quotient nor an arbitrary
candidate rooted extension is involved. -/
theorem globalFunctionalPiece_width_le_forbiddenCardBound
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    (hBound : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ N)
    (s : GlobalFunctionalPieceSymbol F) :
    globalFunctionalPieceArity F s ≤ N := by
  classical
  rcases s with ⟨⟨n, _hn⟩, q⟩
  let P : SelectedFunctionalChart F n := Quotient.out q
  have hP : IsForbiddenGeometricFunctionalPiece F P.1.pattern :=
    P.2
  obtain ⟨W, Source, hFinite, hForbidden, d, _hIso⟩ := hP
  letI : Finite W := hFinite
  have hRootCard : Nat.card (Fin n) ≤ Nat.card W :=
    Nat.card_le_card_of_injective d.roots d.roots_injective
  have hLe : Nat.card (Fin n) ≤ N :=
    hRootCard.trans (hBound Source hForbidden)
  change n ≤ N
  simpa only [Nat.card_fin] using hLe

end AllThoseRamseyClasses.Lifts
