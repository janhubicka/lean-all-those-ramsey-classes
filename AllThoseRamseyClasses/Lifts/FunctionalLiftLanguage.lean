import PartiteConstruction.Functional.WeakInvariant

/-!
# Relational lifts of structures with genuine partial/set-valued functions

The original 2019 Section 3 lift construction keeps all old functions
and introduces only new RELATION symbols recording rooted forbidden
pieces. This module formalizes that operation natively in the
relation/function `Structure` language, not just its relational graph.

For partial functions, the paper's homomorphism-embedding preserves
defined function incidences forward. The correct existing library
predicate is `Structure.IsEHNHomomorphismEmbedding`. Do NOT
substitute `Structure.IsHomomorphismEmbedding`, which globally
requires equality of complete function-value fibres.

These foundations choose new-symbol and original-symbol types in
one common universe. A later generalization can raise the universe
of all symbols when building quotient-type piece indices.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

/-- Extend only the relation signature, preserving every old
function symbol and its original arity. -/
def functionalLiftLanguage (L : Language.{u})
    (New : Type u) (ar : New → ℕ) : Language.{u} where
  RelSymbol := L.RelSymbol ⊕ New
  FuncSymbol := L.FuncSymbol
  relArity := Sum.elim L.relArity ar
  funcArity := L.funcArity

/-- The original structure obtained by forgetting newly added
relations, with old function domains and value sets unchanged. -/
def functionalShadow (L : Language.{u}) (New : Type u)
    (ar : New → ℕ) {V : Type v}
    (X : Structure (functionalLiftLanguage L New ar) V) :
    Structure L V where
  rel R := X.rel (.inl R)
  func F := X.func F

/-- Add arbitrarily chosen extra relations, keeping ALL original
function interpretations on the very same carrier. -/
def functionalWithExtra (L : Language.{u}) (New : Type u)
    (ar : New → ℕ) {V : Type v}
    (A : Structure L V)
    (extra : ∀ i : New, (Fin (ar i) → V) → Prop) :
    Structure (functionalLiftLanguage L New ar) V where
  rel R := by
    cases R with
    | inl s => exact A.rel s
    | inr i => exact extra i
  func F := A.func F

/-- Every such extension has the EXACT functional shadow: even
undefined applications and nullary values are retained. -/
@[simp] theorem functionalShadow_withExtra
    (L : Language.{u}) (New : Type u) (ar : New → ℕ)
    {V : Type v} (A : Structure L V)
    (extra : ∀ i : New, (Fin (ar i) → V) → Prop) :
    functionalShadow L New ar (functionalWithExtra L New ar A extra) = A := by
  cases A
  rfl

/-- Any full embedding of expansions restricts to an embedding
reflecting original relations and exact complete function fibres. -/
def functionalShadowEmbedding
    (L : Language.{u}) (New : Type u) (ar : New → ℕ)
    {V W : Type v}
    {X : Structure (functionalLiftLanguage L New ar) V}
    {Y : Structure (functionalLiftLanguage L New ar) W}
    (e : Structure.Embedding X Y) :
    Structure.Embedding (functionalShadow L New ar X)
      (functionalShadow L New ar Y) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl R) xs
  map_func F xs := e.map_func F xs

/-- A shadow embedding lifts to full expansions exactly when it
also reflects the NEW relations. Merely preserving the piece
predicates is not sufficient for an induced embedding. -/
def functionalWithExtraEmbedding
    (L : Language.{u}) (New : Type u) (ar : New → ℕ)
    {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    (extraA : ∀ i : New, (Fin (ar i) → V) → Prop)
    (extraB : ∀ i : New, (Fin (ar i) → W) → Prop)
    (e : Structure.Embedding A B)
    (hExtra : ∀ i xs, extraB i (e ∘ xs) ↔ extraA i xs) :
    Structure.Embedding
      (functionalWithExtra L New ar A extraA)
      (functionalWithExtra L New ar B extraB) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := by
    cases R with
    | inl s => exact e.map_rel_iff s xs
    | inr i => exact hExtra i xs
  map_func F xs := e.map_func F xs

/-- A rooted functional structure carrying an ordered tuple of
distinct roots; no arbitrary permutation of the roots is allowed. -/
structure FunctionalRootedPattern (L : Language.{u}) (n : ℕ) where
  Carrier : Type v
  str : Structure L Carrier
  root : Fin n → Carrier
  root_injective : Function.Injective root

/-- Rooted realization with the PAPER'S weak functional
homomorphism-embedding, rather than the survey's stronger
whole-fibre-surjective homomorphism. -/
def FunctionalRootRealization
    {L : Language.{u}} {n : ℕ}
    (P : FunctionalRootedPattern.{u,v} L n)
    {W : Type v} (A : Structure L W)
    (xs : Fin n → W) : Prop :=
  ∃ f : P.Carrier → W,
    P.str.IsEHNHomomorphismEmbedding A f ∧
    ∀ i, f (P.root i) = xs i

/-- Full embeddings of the target preserve rooted realizations.
Reflection can fail when the target admits new piece witnesses. -/
theorem FunctionalRootRealization.map_embedding
    {L : Language.{u}} {n : ℕ}
    (P : FunctionalRootedPattern.{u,v} L n)
    {W Z : Type v} {A : Structure L W} {B : Structure L Z}
    (xs : Fin n → W)
    (e : Structure.Embedding A B)
    (h : FunctionalRootRealization P A xs) :
    FunctionalRootRealization P B (e ∘ xs) := by
  obtain ⟨f, hf, hroot⟩ := h
  refine ⟨e ∘ f, e.isEHNHomomorphismEmbedding.comp hf, ?_⟩
  intro i
  change e (f (P.root i)) = e (xs i)
  exact congrArg e (hroot i)

/-- The paper's candidate canonical piece relation in the native
functional language. The families are parameters until the
minimal-separator geometric selection is inserted. -/
def FunctionalCanonicalExtraRelation
    (L : Language.{u}) (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v} (A : Structure L W)
    (i : I) (xs : Fin (ar i) → W) : Prop :=
  Function.Injective xs ∧
    ∃ P : FunctionalRootedPattern.{u,v} L (ar i),
      P ∈ pieces i ∧ FunctionalRootRealization P A xs


/-- Every new canonical relation has pairwise distinct root vertices. -/
theorem functionalCanonicalExtraRelation_injective
    (L : Language.{u}) (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v} (A : Structure L W) (i : I)
    (xs : Fin (ar i) → W)
    (h : FunctionalCanonicalExtraRelation L I ar pieces A i xs) :
    Function.Injective xs :=
  h.1

/-- Positive new-root relations are preserved by embeddings of
the functional shadows. A target may realize additional pieces,
so reflection is intentionally NOT asserted. -/
theorem FunctionalCanonicalExtraRelation.map_embedding
    (L : Language.{u}) (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W Z : Type v} {A : Structure L W} {B : Structure L Z}
    (e : Structure.Embedding A B) (i : I)
    (xs : Fin (ar i) → W)
    (h : FunctionalCanonicalExtraRelation L I ar pieces A i xs) :
    FunctionalCanonicalExtraRelation L I ar pieces B i (e ∘ xs) := by
  obtain ⟨hinj, P, hP, hreal⟩ := h
  exact ⟨e.injective.comp hinj, P, hP,
    FunctionalRootRealization.map_embedding P xs e hreal⟩

/-- The actual functional expansion of A, for any carrier:
no old function symbol is dropped or replaced by a temporary
graph predicate. -/
def functionalCanonicalLiftOn
    (L : Language.{u}) (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v} (A : Structure L W) :
    Structure (functionalLiftLanguage L I ar) W :=
  functionalWithExtra L I ar A
    (FunctionalCanonicalExtraRelation L I ar pieces A)

/-- Its shadow is definitionally the exact original structure. -/
@[simp] theorem functionalShadow_canonicalLiftOn
    (L : Language.{u}) (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v} (A : Structure L W) :
    functionalShadow L I ar (functionalCanonicalLiftOn L I ar pieces A) = A :=
  functionalShadow_withExtra L I ar A _

end AllThoseRamseyClasses.Lifts
