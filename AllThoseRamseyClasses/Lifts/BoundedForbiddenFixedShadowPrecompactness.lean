import AllThoseRamseyClasses.Lifts.BoundedRegularFixedShadowPrecompactness
import AllThoseRamseyClasses.Lifts.ForbiddenSourceWidthBound

/-!
# Precompact expansion fibres from regularity and bounded forbidden-source sizes

For the global Section 3 piece-lift language, regularity means that
each fixed positive root width has finitely many genuine piece
incompatibility classes. If all forbidden sources have at most N
vertices, their actual minimal-separator root tuples have width ≤ N.

The previously verified bounded-width regular signature theorem and
fixed-finite-shadow theorem therefore combine without assuming a
separate root-width bound: every finite old relation/function
structure has only finitely many expansions with its exact old shadow.

This is the finite-fibre precompactness component for bounded
forbidden families; it applies to the original global language and
to the auxiliary folded-root interpretation of the SAME symbols.
It does not prove regularity from a concrete family of finitely many
isomorphism types, and does not prove strong amalgamation, maximal
folded lifts, the Ramsey property or the general unbounded case.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Uniformly bounded forbidden-source sizes and finite global
piece-class quotient fibres at each width ensure the exact fixed
functional-shadow expansion fibre is finite, without separately
postulating a root-width bound. -/
theorem boundedForbiddenRegularGlobalPiece_fixedShadowFibre_finite
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : ∀ n : ℕ,
      Finite (GlobalFunctionalPieceClass F n))
    (N : ℕ)
    (hForbiddenBound : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ N)
    {V : Type} [Finite V] (A : Structure L V) :
    Finite
      (FixedFunctionalShadowExpansions L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) A) := by
  exact boundedRegularGlobalPiece_fixedShadowFibre_finite
    F hRegular N
      (globalFunctionalPiece_width_le_forbiddenCardBound
        F N hForbiddenBound) A

end AllThoseRamseyClasses.Lifts
