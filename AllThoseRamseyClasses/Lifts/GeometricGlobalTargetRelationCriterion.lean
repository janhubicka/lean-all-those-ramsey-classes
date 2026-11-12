import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol

/-!
# Exact root-collision criterion for an original global geometric relation

For one *actual* finite forbidden native functional source and one
*actual* geometric piece, the original 2019 globally indexed canonical
relation is realized by an EHN weak source map precisely when the
images of the ordered root coordinates are pairwise distinct.

The forward implication is the injective-tuple clause of the ORIGINAL
global canonical relation; the reverse implication is the verified
geometric weak-witness realization theorem on the same source and map.

This is not a proof that arbitrary EHN maps become injective. It
identifies exactly why a source-global-symbol-preserving flip does
not automatically transport the original OUTER target relation when
root images collide. No quotient, folded relation, invented source
or stronger homomorphism hypothesis is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type} {n : ℕ}

/-- The ORIGINAL globally indexed canonical target relation is
equivalent to injectivity on this genuine forbidden geometric
source piece's ORDERED root, under the given EHN weak map.

The weak map need not be globally injective, and no maximal-lift,
root-image normalization, or quotient assumption is imposed. -/
theorem geometricGlobalCanonicalRelation_iff_rootInjective_of_weak
    (F : ∀ {W : Type}, Structure L W → Prop)
    (A : Structure L V) (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) (hn : 0 < n)
    {W : Type} (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f) :
    (globalFunctionalCanonicalLift F B).rel
        (.inr (geometricGlobalPieceSymbol F A hFinite hFA d hn))
        (fun i : Fin n => f (d.roots i)) ↔
      Function.Injective (fun i : Fin n => f (d.roots i)) := by
  constructor
  · intro h
    exact globalFunctionalCanonicalRelation_injective F B
      (geometricGlobalPieceSymbol F A hFinite hFA d hn)
      (fun i : Fin n => f (d.roots i)) h
  · intro h
    exact geometricGlobalCanonicalRelation_of_weak
      F A hFinite hFA d hn B f hf h

/-- A collision in the original ordered root image blocks that
ORIGINAL target relation, even if the surrounding source replacement
preserves the global piece symbol and target-root coordinates. -/
theorem geometricGlobalCanonicalRelation_false_of_rootCollision
    (F : ∀ {W : Type}, Structure L W → Prop)
    (A : Structure L V) (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) (hn : 0 < n)
    {W : Type} (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCollision :
      ¬ Function.Injective (fun i : Fin n => f (d.roots i))) :
    ¬ (globalFunctionalCanonicalLift F B).rel
        (.inr (geometricGlobalPieceSymbol F A hFinite hFA d hn))
        (fun i : Fin n => f (d.roots i)) := by
  intro h
  exact hCollision
    ((geometricGlobalCanonicalRelation_iff_rootInjective_of_weak
      F A hFinite hFA d hn B f hf).mp h)

end AllThoseRamseyClasses.Lifts
