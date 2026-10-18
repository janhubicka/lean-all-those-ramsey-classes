import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceAge

/-!
# Full-embedding transfer of maximal finite-family canonical traces

If a finite expanded structure Y is the full induced canonical
component trace in a finite forbidden-free witness W, maximal along
its OLD shadow, then ANY finite allowed full extension C of W cannot
add component tags on Y's root. When a full old embedding of Y's
shadow into a second root D is compatible with D ↪ C, this yields
a FULL embedding of Y into the canonical trace on D evaluated in C.

This is exactly the transport needed in the finite-family
amalgamation construction: the old amalgam D is forbidden-free,
and we choose a finite maximal allowed extension C of D. The
input expanded witnesses embed into C and their original
relations are reflected on their original carriers.

The theorem never identifies the canonical lift of a small
substructure with its induced trace, and it does not assume
the expanded amalgam is free in the added relations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Transport the full induced maximal trace of Y into the
canonical trace of a second old root D evaluated in an allowed
extension C. The old embedding `base` supplies EXACT old
relation and function reflection; witness maximality supplies
reflection of every added component tag. -/
noncomputable def finiteNamedMaximalTrace_embedding_into_allowed_trace
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V UW UD UC : Type}
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) V)
    (W : Structure L UW)
    (iW : Structure.Embedding
      (FiniteNamedTraceShadow Family Y) W)
    (hMax : FiniteNamedCanonicalMaximalAlong Family
        (fun {U : Type} (E : Structure L U) =>
          FiniteNamedFiniteForbiddenFree Family E) iW)
    (hRel : ∀ (tag : Family.ComponentTag)
      (xs : Fin (tag.width Family) → V),
      Y.rel (.inr tag) xs ↔
        (finiteNamedClosedComponentFoldedLift Family W).rel
          (.inr tag) (iW ∘ xs))
    (D : Structure L UD)
    (base : Structure.Embedding
      (FiniteNamedTraceShadow Family Y) D)
    (C : Structure L UC)
    (hC : FiniteNamedFiniteForbiddenFree Family C)
    (eDC : Structure.Embedding D C)
    (k : Structure.Embedding W C)
    (hComp : ∀ x : V, eDC (base x) = k (iW x)) :
    Structure.Embedding Y (finiteNamedCanonicalTrace Family eDC) where
  toFun := base
  injective := base.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R =>
        change D.rel R.down (base ∘ xs) ↔
          (FiniteNamedTraceShadow Family Y).rel R.down xs
        exact base.map_rel_iff R.down xs
    | inr tag =>
        change
          (finiteNamedClosedComponentFoldedLift Family C).rel
            (.inr tag) (eDC ∘ base ∘ xs) ↔
          Y.rel (.inr tag) xs
        have ht :
            (eDC ∘ base ∘ xs) = (k ∘ iW ∘ xs) := by
          funext j
          exact hComp (xs j)
        rw [ht]
        exact (hMax C hC k tag xs).trans (hRel tag xs).symm
  map_func := by
    intro F xs
    change imageSet base
        ((FiniteNamedTraceShadow Family Y).func F.down xs) =
      D.func F.down (base ∘ xs)
    exact base.map_func F.down xs

end AllThoseRamseyClasses.Lifts
