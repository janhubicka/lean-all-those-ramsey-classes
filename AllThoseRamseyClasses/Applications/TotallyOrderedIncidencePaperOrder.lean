import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceFunctionalEmbedding

/-!
# The manuscript's exact order comparison on incidence closure vertices

For a totally ordered relational structure A, the incidence lift has
the original vertices first. New vertices are tagged by positive tuples
(r,t), and their order is the lexicographic combination of a FIXED
linear order of relation symbols r and the original tuple order
A.tupleLE r within each symbol.

This module builds the literal OLD/NEW order comparison predicate on
the entire incidence carrier, including the nontrivial case of two
new vertices belonging to the same relation symbol. It proves that
the UNIQUE canonical incidence extension of any exact original
embedding preserves AND REFLECTS that comparison, not only the
underlying metric-free functional closure table.

This is a component of the ordered relational incidence lift
for manuscript thm:TO; it does not claim a class-level Ramsey theorem.
Proving that this comparison is itself a linear order requires the
paper's additional tuple-support/totality axioms, rather than the
unconstrained TotalOrderData currently used for exact embeddings.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- The new vertices of the canonical incidence lift, indexed by
their symbol and positive original tuple. -/
abbrev IncidenceTag {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) :=
  Sigma fun r : L.Symbol =>
    {t : Fin (L.arity r) → V // A.base.rel r t}

/-- The component on new incidence vertices of the unique extension
of a full original embedding. -/
noncomputable def incidenceTagMap
    {L : RelLanguage.{u}} {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    IncidenceTag A → IncidenceTag B
  | ⟨r, ⟨t, ht⟩⟩ =>
      ⟨r, ⟨f ∘ t, (hf.2.1 r t).mpr ht⟩⟩

@[simp] theorem incidenceMap_new
    {L : RelLanguage.{u}} {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (a : IncidenceTag A) :
    incidenceMap A B f hf (.inr a) =
      .inr (incidenceTagMap A B f hf a) := by
  rcases a with ⟨r, ⟨t, ht⟩⟩
  rfl

/-- Literal comparison between two new incidence vertices. Different
symbols are ordered by the fixed symbol order; within one symbol,
the paper's original tuple order is used. The dependent tuple is
cast only after establishing equality of its relation symbol. -/
noncomputable def paperIncidenceTagLE
    {L : RelLanguage.{u}} {V : Type v}
    [LinearOrder L.Symbol]
    (A : TotalOrderData L V)
    (a b : IncidenceTag A) : Prop := by
  classical
  exact if h : a.1 = b.1 then
    A.tupleLE a.1 a.2.1
      (cast (congrArg
        (fun r : L.Symbol => Fin (L.arity r) → V) h.symm) b.2.1)
  else a.1 < b.1

/-- Exact preservation AND reflection of comparison of new
vertices under canonical incidence embeddings, for any symbol
arity including zero. No restriction or hidden assumption about
totality of the tuple-order relation is needed. -/
theorem paperIncidenceTagLE_map_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (a b : IncidenceTag A) :
    paperIncidenceTagLE B
      (incidenceTagMap A B f hf a)
      (incidenceTagMap A B f hf b) ↔
    paperIncidenceTagLE A a b := by
  classical
  rcases a with ⟨r, ⟨t, ht⟩⟩
  rcases b with ⟨s, ⟨q, hq⟩⟩
  by_cases hrs : r = s
  · subst s
    simpa [paperIncidenceTagLE, incidenceTagMap] using
      (hf.2.2.2 r t q)
  · simp [paperIncidenceTagLE, incidenceTagMap, hrs]

/-- The full manuscript incidence-lift vertex comparison:
old vertices use A's vertex order; every old vertex precedes
every new vertex; new vertices are ordered by (symbol, tuple). -/
noncomputable def paperIncidenceLE
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v}
    (A : TotalOrderData L V) :
    IncidenceCarrier A → IncidenceCarrier A → Prop
  | .inl x, .inl y => A.vertexLE x y
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr a, .inr b => paperIncidenceTagLE A a b

/-- Exact order-comparison transport on the ENTIRE enlarged
incidence carrier, not merely on the original vertices. -/
theorem paperIncidenceLE_map_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (x y : IncidenceCarrier A) :
    paperIncidenceLE B
      (incidenceMap A B f hf x)
      (incidenceMap A B f hf y) ↔
    paperIncidenceLE A x y := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact hf.2.2.1 x y
      | inr y => simp [paperIncidenceLE, incidenceMap]
  | inr x =>
      cases y with
      | inl y => simp [paperIncidenceLE, incidenceMap]
      | inr y =>
          simpa only [incidenceMap_new, paperIncidenceLE] using
            (paperIncidenceTagLE_map_iff A B f hf x y)

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
