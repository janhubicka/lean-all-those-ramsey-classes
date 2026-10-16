import AllThoseRamseyClasses.Applications.TotallyOrderedIncidencePaperEmbedding
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceSortMarkers

/-!
# Full sorted incidence-lift language and its canonical embeddings

The incidence lift from manuscript Theorem TO has original L-relations,
the global old-first order, and the complete incidence functions F_r.
The unmarked language permits old-to-new full embeddings, so merely
forgetting a Ramsey-selected copy need not produce an original copy.

This auxiliary expansion adds a unary Old sort and a unary New_r sort
for each original relation symbol r. It proves their complete exact
semantics and a genuine FULL functional embedding carrying the entire
old/new order, old original relations, and set-valued functions,
AND reflecting every added sort predicate.

Most importantly, *every arbitrary full embedding* in the marked
auxiliary language maps each original source vertex to an ORIGINAL
target vertex. This does not assume that the embedding came from a
canonical source map.

The paper's proper closure-root / orphan-tag heredity and exact weak
local-completion axioms are still separate; this is the sorted-language
and copy-projection component, not a Ramsey class result.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Relation symbols of the incidence proof's SORT-MARKED language.
Original paper comparison symbols retain their exact arities; only
one new unary Old symbol and one New_r per original r are added. -/
inductive MarkedIncidenceRelSymbol (L : RelLanguage.{u}) : Type u
  | paper : IncidencePaperRelSymbol L → MarkedIncidenceRelSymbol L
  | old : MarkedIncidenceRelSymbol L
  | newSymbol : L.Symbol → MarkedIncidenceRelSymbol L

abbrev markedIncidencePaperLanguage
    (L : RelLanguage.{u}) : Language.{u} where
  RelSymbol := MarkedIncidenceRelSymbol L
  FuncSymbol := L.Symbol
  relArity
    | .paper (.original r) => L.arity r
    | .paper .order => 2
    | .old => 1
    | .newSymbol _ => 1
  funcArity := L.arity

/-- The genuine old-first paper incidence lift with exact unary
Old and New_r partition markers; original relations, the global
comparison, and each incidence function are unchanged. -/
def markedIncidencePaperStructure
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} (A : TotalOrderData L V) :
    Structure (markedIncidencePaperLanguage L) (IncidenceCarrier A) where
  rel
    | .paper (.original r), t => liftedOriginalRel A r t
    | .paper .order, t => paperIncidenceLE A (t 0) (t 1)
    | .old, t => isOriginalVertex A (t 0)
    | .newSymbol r, t => hasIncidenceSymbol A r (t 0)
  func := fullIncidenceFibre A

/-- Canonical source embeddings are genuine full embeddings of
the COMPLETE sort-marked paper incidence language. -/
noncomputable def markedIncidencePaperEmbedding
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B) where
  toFun := incidenceMap A B f hf
  injective := incidenceMap_injective A B f hf
  map_rel_iff := by
    intro R t
    cases R with
    | paper r =>
        cases r with
        | original r =>
            exact liftedOriginalRel_map_iff A B f hf r t
        | order =>
            change paperIncidenceLE B
                (incidenceMap A B f hf (t 0))
                (incidenceMap A B f hf (t 1)) ↔
              paperIncidenceLE A (t 0) (t 1)
            exact paperIncidenceLE_map_iff A B f hf (t 0) (t 1)
    | old =>
        change isOriginalVertex B (incidenceMap A B f hf (t 0)) ↔
          isOriginalVertex A (t 0)
        exact incidenceMap_original_iff A B f hf (t 0)
    | newSymbol r =>
        change hasIncidenceSymbol B r
            (incidenceMap A B f hf (t 0)) ↔
          hasIncidenceSymbol A r (t 0)
        exact incidenceMap_tagSymbol_iff A B f hf r (t 0)
  map_func := by
    intro r t
    exact incidenceMap_image_fullIncidenceFibre A B f hf r t

/-- This conclusion is for an ARBITRARY full embedding of the
marked paper incidence structures, not necessarily a canonical
incidenceMap. Its old image cannot be a newly introduced tag. -/
theorem markedEmbedding_old_image
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B)) (x : U) :
    ∃ y : V, e (.inl x) = .inl y := by
  have hSort := e.map_rel_iff (.old)
    (fun _ : Fin 1 => (Sum.inl x : IncidenceCarrier A))
  have hx : isOriginalVertex B (e (.inl x)) :=
    hSort.mpr (show isOriginalVertex A (.inl x) from trivial)
  cases h : e (.inl x) with
  | inl y => exact ⟨y, h⟩
  | inr tag =>
      rw [h] at hx
      cases hx

/-- Forget any marked full lift embedding on ORIGINAL vertices;
the resulting map has its values in the original target carrier. -/
noncomputable def markedEmbedding_originalPart
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B)) : U → V :=
  fun x => Classical.choose (markedEmbedding_old_image A B e x)

/-- Exact image equation for the reverse original-part map. -/
theorem markedEmbedding_originalPart_spec
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B)) (x : U) :
    e (.inl x) = .inl (markedEmbedding_originalPart A B e x) :=
  Classical.choose_spec (markedEmbedding_old_image A B e x)

/-- The underlying original-vertex map of ANY full marked
incidence embedding is injective. Without the Old sort this
fails to yield a map into the target original carrier at all. -/
theorem markedEmbedding_originalPart_injective
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B)) :
    Function.Injective (markedEmbedding_originalPart A B e) := by
  intro x y hxy
  apply Sum.inl.inj
  apply e.injective
  calc
    e (.inl x) = .inl (markedEmbedding_originalPart A B e x) :=
      markedEmbedding_originalPart_spec A B e x
    _ = .inl (markedEmbedding_originalPart A B e y) := by rw [hxy]
    _ = e (.inl y) :=
      (markedEmbedding_originalPart_spec A B e y).symm

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
