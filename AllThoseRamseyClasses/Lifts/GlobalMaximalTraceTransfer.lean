import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceAge

/-!
# Transport full maximal global traces to a larger allowed witness

A maximal trace of Y along its native old shadow in W is preserved
under any full old functional embedding of W into an allowed target C.
If the old shadow of Y also embeds into another finite root D, and
both original maps agree after embedding D into C, then the full
GLOBAL canonical trace on D induced from C contains Y via an actual
FULL expanded embedding.

This is the crucial copy-preservation half of the original Section 3
strong-amalgamation construction. The as-yet missing assertion that
the old free amalgam of two compatible witnesses belongs to K is
NOT used, assumed silently, or inferred from mere maximality.
No root image injectivization is claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine maximal global-piece trace lifts FULLY through a
compatible allowed original-language witness extension.
The old embedding preserves entire functional value sets;
maximality gives reflection of all new global piece relations. -/
noncomputable def globalMaximalTrace_embedding_into_allowed_trace
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {V UW UD UC : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) V)
    (W : Structure L UW)
    (iW : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y) W)
    (hMax : GlobalCanonicalMaximalAlong F
      (FiniteGlobalAllowed K) iW)
    (hRel : ∀ (s : GlobalFunctionalPieceSymbol F)
      (xs : Fin (globalFunctionalPieceArity F s) → V),
      Y.rel (.inr s) xs ↔
        (globalFunctionalCanonicalLift F W).rel
          (.inr s) (iW ∘ xs))
    (D : Structure L UD)
    (base : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y) D)
    (C : Structure L UC)
    (hC : FiniteGlobalAllowed K C)
    (eDC : Structure.Embedding D C)
    (k : Structure.Embedding W C)
    (hComp : ∀ x : V, eDC (base x) = k (iW x)) :
    Structure.Embedding Y (globalCanonicalInducedTrace F eDC) where
  toFun := base
  injective := base.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R =>
        change D.rel R.down (base ∘ xs) ↔
          (functionalShadowBig L
            (GlobalFunctionalPieceSymbol F)
            (globalFunctionalPieceArity F) Y).rel R.down xs
        exact base.map_rel_iff R.down xs
    | inr s =>
        change
          (globalFunctionalCanonicalLift F C).rel
            (.inr s) (eDC ∘ base ∘ xs) ↔
          Y.rel (.inr s) xs
        have ht :
            (eDC ∘ base ∘ xs) = (k ∘ iW ∘ xs) := by
          funext j
          exact hComp (xs j)
        rw [ht]
        exact (hMax C hC k s xs).trans (hRel s xs).symm
  map_func := by
    intro f xs
    change imageSet base
      ((functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y).func f.down xs) =
      D.func f.down (base ∘ xs)
    exact base.map_func f.down xs

end AllThoseRamseyClasses.Lifts
