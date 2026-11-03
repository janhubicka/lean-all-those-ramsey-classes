import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3ClassAssembly

/-!
# Track F: use the ACTUAL native functional Ramsey arrow, not a duplicate

The first Section 3 class-assembly checkpoint introduced a convenient
`GlobalMaximalTraceExpandedArrow` with an explicitly chosen constant
colour. In the underlying verified Ramsey library the standard
`StructuralRamsey.Structure.Arrow` is instead the correct statement:
for each colouring, there is an expanded B-copy on which every pair
of expanded A-copies has the same colour.

Those two propositions need not be equivalent for a potentially
EMPTY colour type or an A that does not embed into B. To avoid
changing (or silently strengthening) the formalized Ramsey theorem,
this module derives the exact ONE-EXPANSION-TYPE old-shadow colour
transfer from the true underlying `Structure.Arrow` with NO
nonempty-colour or hidden existence premise.

This is NOT a Ramsey arrow on all old A-copies: an old full embedding
need not lift to one FIXED expansion A*. The full finite-exact-fibre
type iteration, marked B-copy and local Ramsey-completion arguments
remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- An actual Ramsey arrow in the ORIGINAL expanded full functional
language controls every old-shadow colouring on the induced copies
of ONE designated expanded A type, with the true pairwise
monochromatic contract of `Structure.Arrow`.

No source EHN map, local-completion axiom, regularity,
shadow-avoidance or nonempty colour type is used. -/
theorem globalOriginalStructureArrow_shadowColor_oneType
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VA VB VC : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (C : Structure (globalFunctionalPieceLanguage F) VC)
    (κ : Type v)
    (hArrow : Structure.Arrow A B C κ)
    (χold : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) A)
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) C) → κ) :
    ∃ (j : Structure.Embedding B C),
      ∀ e₁ e₂ : Structure.Embedding A B,
        χold (functionalShadowBigEmbedding L
          (GlobalFunctionalPieceSymbol F)
          (globalFunctionalPieceArity F) (j.comp e₁)) =
        χold (functionalShadowBigEmbedding L
          (GlobalFunctionalPieceSymbol F)
          (globalFunctionalPieceArity F) (j.comp e₂)) := by
  exact hArrow (fun e =>
    χold (functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) e))

end AllThoseRamseyClasses.Lifts
