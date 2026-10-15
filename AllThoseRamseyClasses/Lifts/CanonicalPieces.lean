import AllThoseRamseyClasses.Lifts.RelationalShadow

/-!
# Ramsey lifts: rooted piece realizations and canonical extra relations

First formal layer of manuscript Definitions defn:piece (rooted notation),
def:incompatible and defn:maximal.  The actual *geometric* predicate
"minimal separating cut / piece of F" and the quotient by incompatible
rooted structures are still to be supplied; here the families of
representative rooted patterns are parameters, not falsely asserted
to be the manuscript's piece-equivalence classes.

The canonical extra relation faithfully records the formula in lines
2007--2014: a tuple of distinct roots is present exactly when a
pattern from the selected class has a homomorphism-embedding realizing
that root tuple.  Preservation by a full embedding of the shadow is
proved below.  Reflection is deliberately NOT asserted: the larger
target can admit additional piece witnesses.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w z

/-- A finite-width rooted relational structure with distinct root
vertices (the basic pair (P,R) of Section sec:lifts).
The underlying carrier and root ordering are kept explicit. -/
structure RootedPattern (L : RelLanguage.{u}) (n : ℕ) where
  Carrier : Type v
  str : RelStructure L Carrier
  root : Fin n → Carrier
  root_injective : Function.Injective root

/-- A rooted pattern is realized at the ordered tuple xs by a
homomorphism-embedding of its underlying structure.  Injectivity of
xs is checked separately in the canonical lift relation, as in the
paper's displayed definition. -/
def RootRealization {L : RelLanguage.{u}} {n : ℕ}
    (P : RootedPattern.{u,v} L n)
    {W : Type w} (A : RelStructure L W) (xs : Fin n → W) : Prop :=
  ∃ f : P.Carrier → W,
    P.str.IsHomomorphismEmbedding A f ∧
    ∀ j, f (P.root j) = xs j

/-- Full embeddings of the target preserve positive rooted-pattern
realizations. They need not reflect them. -/
theorem RootRealization.map_embedding
    {L : RelLanguage.{u}} {n : ℕ}
    (P : RootedPattern.{u,v} L n)
    {W : Type w} {Z : Type z}
    {A : RelStructure L W} {B : RelStructure L Z}
    {xs : Fin n → W}
    (e : Embedding A B) (h : RootRealization P A xs) :
    RootRealization P B (e ∘ xs) := by
  obtain ⟨f, hf, hroot⟩ := h
  have he : A.IsHomomorphismEmbedding B (fun x => e x) := by
    constructor
    · intro R ys hys
      exact (e.map_rel_iff R ys).mpr hys
    · intro S _
      refine ⟨e.comp (A.inclusion S), ?_⟩
      intro x
      rfl
  refine ⟨(fun x => e (f x)), he.comp hf, ?_⟩
  intro j
  change e (f (P.root j)) = e (xs j)
  exact congrArg e (hroot j)

/-- The extra relation associated with one selected piece-equivalence
class.  The input `pieces i` is the class of rooted representatives;
a future module must prove that it is exactly a class of pieces under
equality of incompatibility sets, NOT merely an arbitrary family. -/
def CanonicalExtraRelation
    (L : RelLanguage.{u}) (I : Type w) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (RootedPattern.{u,v} L (ar i)))
    {W : Type z} (A : RelStructure L W)
    (i : I) (xs : Fin (ar i) → W) : Prop :=
  Function.Injective xs ∧
    ∃ P : RootedPattern.{u,v} L (ar i),
      P ∈ pieces i ∧ RootRealization P A xs

/-- Formula (3.??), lines 2007--2014 of the published paper:
the canonical relational lift with one new predicate per chosen
rooted-pattern class.  Its old relations are literally unchanged. -/
def canonicalLift
    (L : RelLanguage.{u}) (I : Type w) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (RootedPattern.{u,v} L (ar i)))
    {W : Type z} (A : RelStructure L W) :
    RelStructure (language L I ar) W :=
  withExtra L I ar A (CanonicalExtraRelation L I ar pieces A)

/-- Forgetting the new piece predicates recovers the original
structure on the nose, not just up to an embedding. -/
@[simp] theorem shadow_canonicalLift
    (L : RelLanguage.{u}) (I : Type w) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (RootedPattern.{u,v} L (ar i)))
    {W : Type z} (A : RelStructure L W) :
    shadow L I ar (canonicalLift L I ar pieces A) = A := by
  exact shadow_withExtra L I ar A _

/-- Every tuple in a canonical extra relation has pairwise distinct
vertices. This is a separate condition in the manuscript. -/
theorem canonicalLift_relation_injective
    (L : RelLanguage.{u}) (I : Type w) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (RootedPattern.{u,v} L (ar i)))
    {W : Type z} (A : RelStructure L W)
    (i : I) (xs : Fin (ar i) → W)
    (h : (canonicalLift L I ar pieces A).rel (.inr i) xs) :
    Function.Injective xs := by
  exact h.1

/-- Full embeddings of shadows preserve positive canonical extra
relations (using composition of homomorphism-embeddings).
This is intentionally ONE-WAY: the converse would be wrong without
additional conditions on the larger structure. -/
theorem canonicalLift_relation_map
    (L : RelLanguage.{u}) (I : Type w) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (RootedPattern.{u,v} L (ar i)))
    {W : Type z} {Z : Type v}
    {A : RelStructure L W} {B : RelStructure L Z}
    (e : Embedding A B) (i : I) (xs : Fin (ar i) → W)
    (h : (canonicalLift L I ar pieces A).rel (.inr i) xs) :
    (canonicalLift L I ar pieces B).rel (.inr i) (e ∘ xs) := by
  change CanonicalExtraRelation L I ar pieces A i xs at h
  change CanonicalExtraRelation L I ar pieces B i (e ∘ xs)
  obtain ⟨hinj, P, hP, hreal⟩ := h
  exact ⟨e.injective.comp hinj, P, hP,
    RootRealization.map_embedding P e hreal⟩

end AllThoseRamseyClasses.Lifts
