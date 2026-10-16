import AllThoseRamseyClasses.Lifts.GlobalFunctionalPieceLift
import Mathlib.Data.Fintype.Pi

/-!
# A regular global piece quotient with bounded widths has finite signature

For the 2019 global forbidden-piece lift, "regular" means finitely
many genuine incompatibility classes AT EACH positive root width.
This does not, by itself, bound the width. Here we add an explicit
global width bound N and prove that all extra relation symbols
taken TOGETHER form one finite type.

This is a generally reusable bridge to finite-language (and thus
fixed-finite-shadow precompactness) arguments, relevant to finite
forbidden families and other bounded-width regular classes.

The theorem does NOT derive the width bound from regularity.
It also does not assert any Ramsey, amalgamation or ordering
property of either the printed or folded canonical lift.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Finite fibres of piece-equivalence classes at all root widths
and a single finite upper bound on widths imply a FINITE total
type of added globally indexed relations. -/
theorem globalFunctionalPieceSymbols_finite_of_boundedWidth
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : ∀ n : ℕ, Finite (GlobalFunctionalPieceClass F n))
    (N : ℕ)
    (hBound : ∀ s : GlobalFunctionalPieceSymbol F,
      globalFunctionalPieceArity F s ≤ N) :
    Finite (GlobalFunctionalPieceSymbol F) := by
  classical
  letI (k : Fin (N + 1)) :
      Finite (GlobalFunctionalPieceClass F k.1) := hRegular k.1
  let encode : GlobalFunctionalPieceSymbol F →
      (Σ k : Fin (N + 1), GlobalFunctionalPieceClass F k.1) :=
    fun s => ⟨⟨s.1.1, Nat.lt_succ_of_le (hBound s)⟩, s.2⟩
  apply Finite.of_injective encode
  intro a b hab
  rcases a with ⟨⟨na, ha⟩, ca⟩
  rcases b with ⟨⟨nb, hb⟩, cb⟩
  dsimp only [encode] at hab
  cases hab
  rfl

end AllThoseRamseyClasses.Lifts
