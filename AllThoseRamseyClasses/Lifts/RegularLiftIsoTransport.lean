import AllThoseRamseyClasses.Lifts.FiniteNamedGlobalLifts

/-!
# Transporting regular functional lifts along old-language isomorphisms

Section 3 precompactness is stated up to isomorphism of shadows,
while the finite-support theorem counts all possible expansions on
one FIXED named finite carrier. These are linked by a constructive
pullback along a full old-language embedding.

If `e : A ↪ B` is a full functional embedding and X is a lift of B
whose added relation tuples all have distinct roots, pull every new
relation back along e. The result is one of the finitely many named
lifts of A. The map e is then a FULL embedding of that lifted
structure into X. If e is surjective, this is an isomorphism of
the lifted structures.

The theorem preserves ALL original old-function value sets,
including nullary applications. It does not mistake the one-way
preservation of canonical piece relations by arbitrary old-language
embeddings for reflection: reflection holds only for the newly
defined PULLBACK relation interpretation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- Pull the additional relation interpretations of X back along
an old-language FULL embedding e : A ↪ B. The tuple-injectivity
condition is preserved without assuming e is surjective. -/
def pullbackGlobalExtraRelations
    {L : Language.{u}}
    (F : ∀ {T : Type}, Structure L T → Prop)
    {V W : Type}
    {A : Structure L V} {B : Structure L W}
    (X : Structure (globalFunctionalPieceLanguage F) W)
    (_hShadow : functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) X = B)
    (e : Structure.Embedding A B)
    (hDistinct : ∀ (i : GlobalFunctionalPieceSymbol F)
      (xs : Fin (globalFunctionalPieceArity F i) → W),
      X.rel (.inr i) xs → Function.Injective xs) :
    DistinctRootExtraData
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) V where
  val := fun i xs => X.rel (.inr i) (e ∘ xs)
  property := by
    intro i xs hxs
    have hinj : Function.Injective (e ∘ xs) :=
      hDistinct i (e ∘ xs) hxs
    intro a b hab
    apply hinj
    exact congrArg e hab

/-- The source shadow A equipped with the pulled-back extra
relations is a genuine named-carrier global functional lift. -/
def pullbackGlobalLiftOption
    {L : Language.{u}}
    (F : ∀ {T : Type}, Structure L T → Prop)
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (X : Structure (globalFunctionalPieceLanguage F) W)
    (hShadow : functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) X = B)
    (e : Structure.Embedding A B)
    (hDistinct : ∀ (i : GlobalFunctionalPieceSymbol F)
      (xs : Fin (globalFunctionalPieceArity F i) → W),
      X.rel (.inr i) xs → Function.Injective xs) :
    NamedGlobalLiftOptions F A where
  val := functionalWithExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) A
    (pullbackGlobalExtraRelations F X hShadow e hDistinct).1
  property := ⟨pullbackGlobalExtraRelations F X
    hShadow e hDistinct, rfl⟩

/-- The old functional embedding e becomes a FULL embedding of
the lifted pullback into X. The extra relation reflection is by
definition; old relation/function reflection comes from e and
the exact shadow equality. -/
def pullbackGlobalLiftEmbedding
    {L : Language.{u}}
    (F : ∀ {T : Type}, Structure L T → Prop)
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (X : Structure (globalFunctionalPieceLanguage F) W)
    (hShadow : functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) X = B)
    (e : Structure.Embedding A B)
    (hDistinct : ∀ (i : GlobalFunctionalPieceSymbol F)
      (xs : Fin (globalFunctionalPieceArity F i) → W),
      X.rel (.inr i) xs → Function.Injective xs) :
    Structure.Embedding
      (pullbackGlobalLiftOption F A B X hShadow e hDistinct).1 X where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl s =>
        have hB : X.rel (.inl s) (e ∘ xs) =
            B.rel s.down (e ∘ xs) := by
          have h := congrArg
            (fun S : Structure L W => S.rel s.down (e ∘ xs)) hShadow
          exact h
        change X.rel (.inl s) (e ∘ xs) ↔ A.rel s.down xs
        rw [hB]
        exact e.map_rel_iff s.down xs
    | inr i =>
        exact Iff.rfl
  map_func := by
    intro f xs
    have hB : X.func f (e ∘ xs) =
        B.func f.down (e ∘ xs) := by
      have h := congrArg
        (fun S : Structure L W => S.func f.down (e ∘ xs)) hShadow
      exact h
    change imageSet e (A.func f.down xs) =
      X.func f (e ∘ xs)
    rw [hB]
    exact e.map_func f.down xs

/-- If the original shadows are isomorphic via e, the pulled-back
named global lift is isomorphic to X by a FULL ONTO embedding.
Thus every such lift of an isomorphic shadow is represented by
one of the finitely many named expansions on A's fixed carrier. -/
theorem pullbackGlobalLiftEmbedding_surjective
    {L : Language.{u}}
    (F : ∀ {T : Type}, Structure L T → Prop)
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (X : Structure (globalFunctionalPieceLanguage F) W)
    (hShadow : functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) X = B)
    (e : Structure.Embedding A B)
    (hDistinct : ∀ (i : GlobalFunctionalPieceSymbol F)
      (xs : Fin (globalFunctionalPieceArity F i) → W),
      X.rel (.inr i) xs → Function.Injective xs)
    (he : Function.Surjective e) :
    Function.Surjective
      (pullbackGlobalLiftEmbedding F A B X
        hShadow e hDistinct) :=
  he

end AllThoseRamseyClasses.Lifts
