import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceMarkedTupleProjection
import PartiteConstruction.Structure.Basic

/-!
# Reverse coordinate closures for canonical incidence vertices

The one-way incidence lift adds a generated tag [r,t] as the
singleton output F_r(t). Yet the new-only subset can be
function-closed and keep orphan tags without their old roots.

A candidate repair adds finitely many UNARY reverse functions
G_(r,i), for each symbol r and input position i. On the canonical
tag [r,t], G_(r,i) has exactly the singleton output {old(t_i)};
on original vertices and tags of the wrong symbol it is empty.

The main semantic lemma states that any FUNCTION-CLOSED subset
of the two-way canonical lift containing [r,t] must also contain
EVERY original coordinate t_i. This directly eliminates the
old orphan-tag counterexample for positive arities, without any
new hypothesis about relation orders.

The current module does NOT yet establish a class-level free-
amalgamation or Ramsey theorem for two-way incidence systems.
It also does NOT change the frozen paper's constructions.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- Fresh independent reverse unary function symbols, one for
each coordinate of every original relational symbol. -/
abbrev reverseCoordinateSymbol (L : RelLanguage.{u}) :=
  Sigma fun r : L.Symbol => Fin (L.arity r)

/-- The base marked incidence language, adding coordinate-indexed
unary functions G_(r,i) alongside the forward F_r functions. -/
abbrev twoWayIncidenceLanguage (L : RelLanguage.{u}) :
    Language.{u} where
  RelSymbol := MarkedIncidenceRelSymbol L
  FuncSymbol := L.Symbol ⊕ reverseCoordinateSymbol L
  relArity := (markedIncidencePaperLanguage L).relArity
  funcArity
    | .inl r => L.arity r
    | .inr _ => 1

/-- The inverse singleton fibre of a generated incidence tag.
Its existential graph definition avoids arbitrary choices of
proofs witnessing positivity and works at every finite arity. -/
def reverseCoordinateFibre
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V)
    (r : L.Symbol) (i : Fin (L.arity r))
    (x : IncidenceCarrier A) :
    Set (IncidenceCarrier A) :=
  {y | ∃ (t : Fin (L.arity r) → V)
           (h : A.base.rel r t),
    x = positiveTag A r t h ∧ y = .inl (t i)}

/-- Literal full two-way functional incidence structure, retaining
the same original relations, complete old/new comparison, and
unary Old / New_r sort predicates as the marked paper lift. -/
def canonicalTwoWayIncidence
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} (A : TotalOrderData L V) :
    Structure (twoWayIncidenceLanguage L) (IncidenceCarrier A) where
  rel := (markedIncidencePaperStructure A).rel
  func
    | .inl r, t => fullIncidenceFibre A r t
    | .inr ⟨r, i⟩, t => reverseCoordinateFibre A r i (t 0)

/-- Every generated positive tag has each root coordinate in
its own reverse function value. -/
theorem generated_coordinate_mem_reverse
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V)
    (r : L.Symbol) (t : Fin (L.arity r) → V)
    (h : A.base.rel r t) (i : Fin (L.arity r)) :
    (Sum.inl (t i) : IncidenceCarrier A) ∈
      reverseCoordinateFibre A r i (positiveTag A r t h) :=
  ⟨t, h, rfl, rfl⟩

/-- The reverse fibre at a canonical generated tag is EXACTLY
the singleton original coordinate, not merely a superset. -/
theorem reverseCoordinateFibre_positiveTag
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V)
    (r : L.Symbol) (t : Fin (L.arity r) → V)
    (h : A.base.rel r t) (i : Fin (L.arity r)) :
    reverseCoordinateFibre A r i (positiveTag A r t h) =
      {(.inl (t i) : IncidenceCarrier A)} := by
  classical
  ext y
  constructor
  · rintro ⟨s, hs, hTag, hy⟩
    have hSigma :
        (⟨r, ⟨t, h⟩⟩ :
          Sigma fun z : L.Symbol =>
            {q : Fin (L.arity z) → V // A.base.rel z q}) =
        ⟨r, ⟨s, hs⟩⟩ := by
      exact Sum.inr.inj (by simpa only [positiveTag] using hTag)
    have hts : t = s := by
      simpa only [Sigma.mk.injEq, heq_iff_eq, Subtype.mk.injEq,
        eq_self_iff_true, true_and] using hSigma
    subst s
    simpa [hy]
  · intro hy
    have hy' : y = (.inl (t i) : IncidenceCarrier A) := by
      simpa only [Set.mem_singleton_iff] using hy
    subst y
    exact generated_coordinate_mem_reverse A r t h i

/-- A genuine function-closed subset of the TWO-WAY incidence
structure containing a generated tag automatically contains
ALL coordinates of its original positive root tuple.

This is the exact closure property missing from the one-way
canonical lift and is valid for arbitrary relation arities,
including the vacuous zero-arity case. -/
theorem twoWay_closedTag_contains_all_original_coordinates
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v}
    (A : TotalOrderData L V)
    (S : Set (IncidenceCarrier A))
    (hClosed : (canonicalTwoWayIncidence A).IsClosed S)
    (r : L.Symbol) (t : Fin (L.arity r) → V)
    (h : A.base.rel r t)
    (hTag : positiveTag A r t h ∈ S) :
    ∀ i : Fin (L.arity r),
      (Sum.inl (t i) : IncidenceCarrier A) ∈ S := by
  intro i
  have hInput : ∀ j : Fin 1,
      (![positiveTag A r t h] j : IncidenceCarrier A) ∈ S := by
    intro j
    fin_cases j
    exact hTag
  have hOut :
      (Sum.inl (t i) : IncidenceCarrier A) ∈
        (canonicalTwoWayIncidence A).func
          (.inr ⟨r, i⟩) ![positiveTag A r t h] :=
    generated_coordinate_mem_reverse A r t h i
  exact hClosed (.inr ⟨r, i⟩) ![positiveTag A r t h] hInput hOut

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
