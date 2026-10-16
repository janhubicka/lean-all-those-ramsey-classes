import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceOriginalRelations
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidencePaperOrder

/-!
# Full ordered relational-functional incidence lift

The manuscript's incidence closure has THREE interacting parts:

* the ORIGINAL L-relations, interpreted only on tuples of old vertices;
* one global vertex-order comparison, with old vertices preceding
  all new incidence vertices and new vertices ordered by
  (relation-symbol, original positive tuple order);
* the complete set-valued functions F_r, singleton on positive
  tuples of old vertices and empty on every other input tuple.

Earlier independent certificates checked each layer. This module
assembles them into ONE actual StructuralRamsey.Structure and proves
that the unique incidence map of every exact original embedding is
a genuine FULL functional embedding of the ENTIRE expanded language.
It reflects every absent original relation, every order comparison
and every empty or singleton output fibre on old/mixed/new inputs.

The underlying TotalOrderData has not yet been constrained by the
positive-tuple support and linearity axioms. Accordingly this is the
exact ordered-language EMBEDDING theorem, NOT yet a proof that every
unconstrained instance carries a genuine linear order, and not the
class-level Ramsey theorem thm:TO. Closed heredity, strong
amalgamation and exact weak local completion remain separate.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- The paper incidence language: original relations and one
global comparison on the complete enlarged vertex carrier,
with one function symbol F_r per original relation symbol. -/
inductive IncidencePaperRelSymbol (L : RelLanguage.{u}) : Type u
  | original : L.Symbol → IncidencePaperRelSymbol L
  | order : IncidencePaperRelSymbol L

abbrev incidencePaperLanguage (L : RelLanguage.{u}) : Language.{u} where
  RelSymbol := IncidencePaperRelSymbol L
  FuncSymbol := L.Symbol
  relArity
    | .original r => L.arity r
    | .order => 2
  funcArity := L.arity

/-- Source-matched old/new order, full inherited original relations,
and complete partial incidence functions on the same carrier. -/
def paperIncidenceStructure
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} (A : TotalOrderData L V) :
    Structure (incidencePaperLanguage L) (IncidenceCarrier A) where
  rel
    | .original r, t => liftedOriginalRel A r t
    | .order, t => paperIncidenceLE A (t 0) (t 1)
  func := fullIncidenceFibre A

/-- Every exact embedding of the original totally ordered relational
structure induces a FULL embedding of the entire paper incidence
language: no extra hypothesis about definedness of any specific
tuple is needed. All reflections are literal, not weak/surjective
positive homomorphisms on the graph of the functions. -/
noncomputable def paperIncidenceEmbedding
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    Structure.Embedding (paperIncidenceStructure A)
      (paperIncidenceStructure B) where
  toFun := incidenceMap A B f hf
  injective := incidenceMap_injective A B f hf
  map_rel_iff := by
    intro R t
    cases R with
    | original r =>
        exact liftedOriginalRel_map_iff A B f hf r t
    | order =>
        change paperIncidenceLE B
            (incidenceMap A B f hf (t 0))
            (incidenceMap A B f hf (t 1)) ↔
          paperIncidenceLE A (t 0) (t 1)
        exact paperIncidenceLE_map_iff A B f hf (t 0) (t 1)
  map_func := by
    intro r t
    exact incidenceMap_image_fullIncidenceFibre A B f hf r t

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
