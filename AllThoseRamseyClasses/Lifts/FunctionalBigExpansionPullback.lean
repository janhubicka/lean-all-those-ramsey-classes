import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguageBig

/-!
# Generic pullback of functional relation-only expansions

Both the printed global regular lift and the alternative finite-family
folded component lift add relations without changing old function fibres.
For any such lift, a FULL native embedding into the old shadow of an
expanded structure Y lets us pull ALL extra relation interpretations
back to the native source.

The resulting map into Y is a FULL expanded embedding (not merely a
positive homomorphism), and it is an isomorphism whenever the native
embedding is onto. No injectivity requirement is placed on argument
tuples of new relations: this also supports folded roots and zero arity.

This common lemma avoids a second paper-specific reconstruction proof
when transporting maximal lifted age members across isomorphic shadows.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w

/-- The full expanded relation pullback of Y along an old-language
FULL embedding e : A ↪ shadow(Y). All original functions retain
EXACTLY A's native complete output value sets. -/
def functionalBigExpansionPullback
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {VA VB : Type v}
    (A : Structure L VA)
    (Y : Structure (functionalLiftLanguageBig L New ar) VB)
    (e : Structure.Embedding A
      (functionalShadowBig L New ar Y)) :
    Structure (functionalLiftLanguageBig L New ar) VA :=
  functionalWithExtraBig L New ar A
    (fun s xs => Y.rel (.inr s) (e ∘ xs))

/-- The exact old functional reduct of the pulled-back expansion,
including nullary function inputs and all output value sets. -/
@[simp] theorem functionalBigExpansionPullback_shadow
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {VA VB : Type v}
    (A : Structure L VA)
    (Y : Structure (functionalLiftLanguageBig L New ar) VB)
    (e : Structure.Embedding A
      (functionalShadowBig L New ar Y)) :
    functionalShadowBig L New ar
      (functionalBigExpansionPullback L New ar A Y e) = A :=
  functionalShadowBig_withExtra L New ar A _

/-- The native FULL embedding upgrades canonically to a FULL
expanded embedding of the pulled-back structure into Y.
In particular every new relation is both preserved and reflected. -/
def functionalBigExpansionPullbackEmbedding
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {VA VB : Type v}
    (A : Structure L VA)
    (Y : Structure (functionalLiftLanguageBig L New ar) VB)
    (e : Structure.Embedding A
      (functionalShadowBig L New ar Y)) :
    Structure.Embedding
      (functionalBigExpansionPullback L New ar A Y e) Y where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl r =>
        exact e.map_rel_iff r.down xs
    | inr s =>
        exact Iff.rfl
  map_func := by
    intro f xs
    exact e.map_func f.down xs

/-- If the original full shadow embedding is onto, its canonical
expanded pullback embedding is also onto. Thus the pullback is
fully isomorphic to the original expanded structure. -/
theorem functionalBigExpansionPullbackEmbedding_surjective
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {VA VB : Type v}
    (A : Structure L VA)
    (Y : Structure (functionalLiftLanguageBig L New ar) VB)
    (e : Structure.Embedding A
      (functionalShadowBig L New ar Y))
    (he : Function.Surjective e) :
    Function.Surjective
      (functionalBigExpansionPullbackEmbedding L New ar A Y e) :=
  he

end AllThoseRamseyClasses.Lifts
