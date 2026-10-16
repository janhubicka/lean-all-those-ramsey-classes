import AllThoseRamseyClasses.Lifts.BoundedWidthGlobalPieceSymbols
import AllThoseRamseyClasses.Lifts.FiniteFunctionalExpansionFibres

/-!
# Fixed-shadow precompactness of bounded-width regular global piece lifts

Combine the now verified separate ingredients:
* finitely many genuine piece incompatibility classes at EACH width,
  together with a uniform bound N on all positive root widths,
  give a FINITE global extra relation-symbol type;
* for any finite carrier, finitely many new relation symbols yield
  only finitely many expansions of the same complete old
  relation/function shadow.

Thus every global piece-indexed lift (including the auxiliary
folded-root one) under these hypotheses has a finite candidate
expansion fibre above every finite old structure.

This is the precise signature/finite-fibre component of
precompactness. It does NOT prove that the particular class of
maximal lifts has amalgamation, Ramsey, or the lift property.
No bound on the root widths is inferred from REGULARITY alone.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every finite old functional structure has only finitely many
expansions in the global piece language, when the genuine global
class quotient is regular AND bounded in positive root width.
Both original and folded canonical lift structures occur among
these candidates and have the same complete functional shadow. -/
theorem boundedRegularGlobalPiece_fixedShadowFibre_finite
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : ∀ n : ℕ,
      Finite (GlobalFunctionalPieceClass F n))
    (N : ℕ)
    (hBound : ∀ s : GlobalFunctionalPieceSymbol F,
      globalFunctionalPieceArity F s ≤ N)
    {V : Type} [Finite V] (A : Structure L V) :
    Finite
      (FixedFunctionalShadowExpansions L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) A) := by
  letI : Finite (GlobalFunctionalPieceSymbol F) :=
    globalFunctionalPieceSymbols_finite_of_boundedWidth
      F hRegular N hBound
  exact fixedFunctionalShadowExpansions_finite
    L (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) A

end AllThoseRamseyClasses.Lifts
