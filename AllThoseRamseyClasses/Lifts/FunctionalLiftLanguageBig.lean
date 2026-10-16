import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguage

/-!
# Universe-polymorphic functional relation lifts

The paper's new symbols are equivalence classes of rooted forbidden
pieces, rather than a fixed small enumeration known in advance.
The quotient of all finite-width pieces can live in a universe
higher than the original relation/function symbol types.

This module extends `L : Language.{u}` by arbitrary new RELATION
symbols `New : Type w`, obtaining `Language.{max u w}`, while
preserving every original relation and the COMPLETE original
function interpretation exactly.

The earlier same-universe constructor has equivalent semantics when
w=u. The old symbols are explicitly universe-lifted here, so the
two language records need not be definitionally equal.
No artificial enumeration of equivalence classes, additional
function symbols, or conversion of undefined values into defined
empty outputs occurs here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w z

/-- Add new relations in an arbitrary symbol universe. All original
function symbols and arities are unchanged. -/
def functionalLiftLanguageBig
    (L : Language.{u}) (New : Type w)
    (ar : New → ℕ) : Language.{max u w} where
  RelSymbol := ULift.{max u w, u} L.RelSymbol ⊕ New
  FuncSymbol := ULift.{max u w, u} L.FuncSymbol
  relArity := Sum.elim (fun R => L.relArity R.down) ar
  funcArity F := L.funcArity F.down

/-- The original structure on the SAME vertex carrier with all
old relations and entire old function fibres preserved. -/
def functionalShadowBig
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {V : Type v}
    (X : Structure (functionalLiftLanguageBig L New ar) V) :
    Structure L V where
  rel R := X.rel (.inl (ULift.up R))
  func F := X.func (ULift.up F)

/-- Specify all extra relations, keeping the original function data
literal rather than encoding it as temporary graph predicates. -/
def functionalWithExtraBig
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {V : Type v}
    (A : Structure L V)
    (extra : ∀ i : New, (Fin (ar i) → V) → Prop) :
    Structure (functionalLiftLanguageBig L New ar) V where
  rel R := by
    cases R with
    | inl s => exact A.rel s.down
    | inr i => exact extra i
  func F := A.func F.down

/-- Forgetting the new relations is exactly the original structure,
not merely a weak homomorphism or an isomorphic copy. -/
@[simp] theorem functionalShadowBig_withExtra
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {V : Type v}
    (A : Structure L V)
    (extra : ∀ i : New, (Fin (ar i) → V) → Prop) :
    functionalShadowBig L New ar
      (functionalWithExtraBig L New ar A extra) = A := by
  cases A
  rfl

/-- Full embeddings of expansions restrict to full embeddings of
the original functional shadows. -/
def functionalShadowBigEmbedding
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {V W : Type v}
    {X : Structure (functionalLiftLanguageBig L New ar) V}
    {Y : Structure (functionalLiftLanguageBig L New ar) W}
    (e : Structure.Embedding X Y) :
    Structure.Embedding
      (functionalShadowBig L New ar X)
      (functionalShadowBig L New ar Y) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl (ULift.up R)) xs
  map_func F xs := e.map_func (ULift.up F) xs

/-- The full shadow embedding lifts to the specified expansions
when, and only when, it also reflects all new relation tuples. -/
def functionalWithExtraBigEmbedding
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    (extraA : ∀ i : New, (Fin (ar i) → V) → Prop)
    (extraB : ∀ i : New, (Fin (ar i) → W) → Prop)
    (e : Structure.Embedding A B)
    (hExtra : ∀ i xs,
      extraB i (e ∘ xs) ↔ extraA i xs) :
    Structure.Embedding
      (functionalWithExtraBig L New ar A extraA)
      (functionalWithExtraBig L New ar B extraB) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := by
    cases R with
    | inl s => exact e.map_rel_iff s.down xs
    | inr i => exact hExtra i xs
  map_func F xs := e.map_func F.down xs

/-- Canonical extra relation associated to one arbitrary new
piece-class symbol. The required injectivity of its ordered root
tuple is part of the definition. -/
def functionalCanonicalExtraBig
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    (pieces : ∀ i : New,
      Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v}
    (A : Structure L W)
    (i : New) (xs : Fin (ar i) → W) : Prop :=
  Function.Injective xs ∧
    ∃ P : FunctionalRootedPattern.{u,v} L (ar i),
      P ∈ pieces i ∧ FunctionalRootRealization P A xs

/-- Universe-polymorphic canonical functional lift. It adds only
relations; the original old-language shadow is still literally A. -/
def functionalCanonicalLiftBig
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    (pieces : ∀ i : New,
      Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v} (A : Structure L W) :
    Structure (functionalLiftLanguageBig L New ar) W :=
  functionalWithExtraBig L New ar A
    (functionalCanonicalExtraBig L New ar pieces A)

@[simp] theorem functionalShadowBig_canonicalLift
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    (pieces : ∀ i : New,
      Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v} (A : Structure L W) :
    functionalShadowBig L New ar
      (functionalCanonicalLiftBig L New ar pieces A) = A :=
  functionalShadowBig_withExtra L New ar A _

/-- Every positive canonical relation has a distinct root tuple. -/
theorem functionalCanonicalExtraBig_injective
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    (pieces : ∀ i : New,
      Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W : Type v} (A : Structure L W)
    (i : New) (xs : Fin (ar i) → W)
    (h : functionalCanonicalExtraBig L New ar pieces A i xs) :
    Function.Injective xs :=
  h.1

/-- Full embeddings of the original functional language preserve
positive new canonical piece relations, including realizations by
the 2019 weak homomorphism-embedding maps. Reflection is not
asserted because the larger target may have extra witnesses. -/
theorem functionalCanonicalExtraBig_map_embedding
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    (pieces : ∀ i : New,
      Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {W Z : Type v}
    {A : Structure L W} {B : Structure L Z}
    (e : Structure.Embedding A B)
    (i : New) (xs : Fin (ar i) → W)
    (h : functionalCanonicalExtraBig L New ar pieces A i xs) :
    functionalCanonicalExtraBig L New ar pieces B i
      (e ∘ xs) := by
  obtain ⟨hinj, P, hP, hreal⟩ := h
  exact ⟨e.injective.comp hinj, P, hP,
    FunctionalRootRealization.map_embedding P xs e hreal⟩

/-- Old relation arities are preserved, with the old symbol
universe-lifted into the larger relation language. -/
@[simp] theorem functionalLiftLanguageBig_relArity_old
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    (R : L.RelSymbol) :
    (functionalLiftLanguageBig L New ar).relArity
      (.inl (ULift.up R)) = L.relArity R := rfl

/-- Old function arities are preserved exactly, after the necessary
universe lift of the original function-symbol type. -/
@[simp] theorem functionalLiftLanguageBig_funcArity
    (L : Language.{u}) (New : Type w) (ar : New → ℕ)
    (F : L.FuncSymbol) :
    (functionalLiftLanguageBig L New ar).funcArity
      (ULift.up F) = L.funcArity F := rfl

end AllThoseRamseyClasses.Lifts
