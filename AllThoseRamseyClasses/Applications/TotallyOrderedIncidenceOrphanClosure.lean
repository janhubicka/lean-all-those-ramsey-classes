import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceFunctionalEmbedding
import PartiteConstruction.Structure.Basic

/-!
# New-only function-closed subsets of incidence lifts

A key subtlety in the paper's totally ordered incidence application
is that FUNCTION-CLOSED substructures of a literal canonical
incidence lift need not contain the original tuple that generated
each new incidence vertex. If every relation symbol has POSITIVE
arity, every subset consisting only of new incidence vertices is
closed under the entire incidence-function table: every input tuple
from such a subset contains a new vertex, so its function fibre is
EMPTY.

The result is a checked obstruction to assuming that a class of
literal canonical lifts is automatically hereditary under all
function-closed induced substructures. A Ramsey-class proof must
handle dangling/orphan tag vertices in a suitable auxiliary class
or prove an appropriate equivalent hereditary representation.

The theorem certifies function closedness and old/new separation,
NOT yet the non-isomorphism of the induced structure to every
canonical lift (which needs explicit sort predicates).
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- The set of all incidence vertices, with no original vertices. -/
def newOnlySupport {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) : Set (IncidenceCarrier A) :=
  Set.range (Sum.inr :
    (Sigma fun r : L.Symbol =>
      {t : Fin (L.arity r) → V // A.base.rel r t}) →
    IncidenceCarrier A)

/-- No original vertex belongs to the new-only subset. -/
theorem old_not_mem_newOnlySupport
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (x : V) :
    (Sum.inl x : IncidenceCarrier A) ∉ newOnlySupport A := by
  rintro ⟨tag, htag⟩
  cases htag

/-- Every existing positive source relation tuple produces an
incidence vertex in the new-only support. -/
theorem new_mem_newOnlySupport
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → V) (h : A.base.rel r t) :
    (Sum.inr ⟨r, ⟨t, h⟩⟩ : IncidenceCarrier A) ∈
      newOnlySupport A :=
  ⟨⟨r, ⟨t, h⟩⟩, rfl⟩

/-- The new-only subset is FUNCTION-CLOSED whenever all incidence
functions have nonempty input tuples. Every such function evaluated
on new-only inputs has empty output, so it cannot force any old
source vertex into the closed subset. -/
theorem newOnlySupport_isClosed
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V)
    (hArity : ∀ r : L.Symbol, 0 < L.arity r) :
    (incidenceFunctionalReduct A).IsClosed (newOnlySupport A) := by
  intro r t ht
  have hi : 0 < L.arity r := hArity r
  let i : Fin (L.arity r) := ⟨0, hi⟩
  obtain ⟨tag, htag⟩ := ht i
  have hnew : t i = Sum.inr tag := htag.symm
  have hempty : fullIncidenceFibre A r t = ∅ :=
    fullIncidenceFibre_empty_of_new A r t i tag hnew
  change fullIncidenceFibre A r t ⊆ newOnlySupport A
  rw [hempty]
  exact Set.empty_subset _

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
