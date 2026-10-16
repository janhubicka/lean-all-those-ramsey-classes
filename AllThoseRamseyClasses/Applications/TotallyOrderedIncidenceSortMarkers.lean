import AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

/-!
# Original and incidence-symbol sort predicates

The paper's incidence construction has an intrinsic DISJOINT sort:
original vertices and new vertices [r,t] tagged by a relation
symbol r. The canonical extension of an exact original embedding
respects both, but the unmarked functional language does not
automatically force arbitrary embeddings to respect these sorts.

A minimal auxiliary repair is to name the OLD sort by one unary
relation and every symbol-specific NEW sort by a unary relation.
When the original language is finite, only finitely many new
relations are introduced. These predicates are automatically
preserved and REFLECTED by the canonical incidence map.

This module certifies that elementary sort-transport fact and
records the exact old/tag partition. It does not change the
printed manuscript's original relations or claim the full
Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Original vertices of the incidence-lift carrier. -/
def isOriginalVertex
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) : IncidenceCarrier A → Prop
  | .inl _ => True
  | .inr _ => False

/-- New incidence vertices whose defining relation symbol is r.
Their individual source tuple remains encoded in the vertex itself. -/
def hasIncidenceSymbol
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol) :
    IncidenceCarrier A → Prop
  | .inl _ => False
  | .inr tag => tag.1 = r

/-- Every incidence vertex belongs to exactly the original sort
or one of the symbol-indexed new sorts, never both. -/
theorem original_or_tagged
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (x : IncidenceCarrier A) :
    isOriginalVertex A x ∨
      ∃ r : L.Symbol, hasIncidenceSymbol A r x := by
  cases x with
  | inl x => exact Or.inl trivial
  | inr x => exact Or.inr ⟨x.1, rfl⟩

theorem original_not_tagged
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (x : IncidenceCarrier A)
    (hx : isOriginalVertex A x) :
    ¬ hasIncidenceSymbol A r x := by
  cases x with
  | inl x => exact id
  | inr x => exact False.elim hx

/-- The unique canonical incidence map preserves AND reflects the
original vertex sort, including for negative/isolated old vertices. -/
theorem incidenceMap_original_iff
    {L : RelLanguage.{u}} {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (x : IncidenceCarrier A) :
    isOriginalVertex B (incidenceMap A B f hf x) ↔
      isOriginalVertex A x := by
  cases x with
  | inl x => rfl
  | inr tag =>
      rcases tag with ⟨r, ⟨t, ht⟩⟩
      rfl

/-- The same exact reflection holds for EACH relation-symbol new
sort, including symbols of different arities and nullary symbols. -/
theorem incidenceMap_tagSymbol_iff
    {L : RelLanguage.{u}} {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (r : L.Symbol) (x : IncidenceCarrier A) :
    hasIncidenceSymbol B r (incidenceMap A B f hf x) ↔
      hasIncidenceSymbol A r x := by
  cases x with
  | inl x => rfl
  | inr tag =>
      rcases tag with ⟨s, ⟨t, ht⟩⟩
      rfl

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
