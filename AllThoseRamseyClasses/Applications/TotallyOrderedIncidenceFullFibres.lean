import AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

/-!
# Full incidence-function fibres on enlarged carriers

The paper's incidence closure functions have input arity n on the
ENTIRE lifted carrier, not only the old original sort. The value
F_r(t) is a singleton incidence vertex when all inputs are old and
form a positive r-tuple. It is the empty set whenever any input is
a new incidence vertex or when an all-old tuple is negative.

The canonical incidence embedding is proved full on EVERY input
tuple, including mixed old/new tuples. This is the functional
reflection obligation, not merely relation preservation on old
positive tuples.

Nullary symbols are covered as a functional semantic statement;
whether a nullary closure symbol fits the 2019 closure-rule hypotheses
is a separate issue.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- All-argument set-valued incidence function: never defined
unless every argument belongs to the original vertex sort. -/
def fullIncidenceFibre {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → IncidenceCarrier A) :
    Set (IncidenceCarrier A) :=
  {x | ∃ s : Fin (L.arity r) → V,
    (∀ i, t i = .inl (s i)) ∧ x ∈ valueFibre A r s}

/-- On all-old tuples, the full function agrees exactly with
the earlier checked one-incidence-vertex-or-empty function. -/
theorem fullIncidenceFibre_old {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → V) :
    fullIncidenceFibre A r (fun i => .inl (t i)) =
      valueFibre A r t := by
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    have hts : t = s := by
      funext i
      exact Sum.inl.inj (hs i)
    subst s
    exact hx
  · intro hx
    exact ⟨t, fun _ => rfl, hx⟩

/-- Any tuple involving an incidence vertex has an empty
function value. In particular, no new-input fibre can be
silently made defined by an embedding. -/
theorem fullIncidenceFibre_empty_of_new {L : RelLanguage.{u}}
    {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → IncidenceCarrier A)
    (i : Fin (L.arity r))
    (s : Sigma fun z : L.Symbol =>
      {q : Fin (L.arity z) → V // A.base.rel z q})
    (hi : t i = .inr s) :
    fullIncidenceFibre A r t = ∅ := by
  ext x
  constructor
  · rintro ⟨old, hOld, hx⟩
    have h := hOld i
    rw [hi] at h
    cases h
  · intro hx
    cases hx

/-- Entire fibres are transported ONTO target fibres for every
tuple of the lifted domain, not just for positive old tuples.
Crucially, if a mapped tuple contains only original target
vertices then the source tuple itself contained only originals.
This reflection uses the disjoint-sum form of the canonical map. -/
theorem incidenceMap_image_fullIncidenceFibre
    {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (r : L.Symbol) (t : Fin (L.arity r) → IncidenceCarrier A) :
    incidenceMap A B f hf '' fullIncidenceFibre A r t =
      fullIncidenceFibre B r (incidenceMap A B f hf ∘ t) := by
  classical
  ext y
  constructor
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    refine ⟨f ∘ s, ?_, ?_⟩
    · intro i
      change incidenceMap A B f hf (t i) = .inl (f (s i))
      rw [hs i]
      rfl
    · have hmap := incidenceMap_image_valueFibre A B f hf r s
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
  · rintro ⟨s, hs, hy⟩
    have hsource : ∀ i : Fin (L.arity r), ∃ x : U, t i = .inl x := by
      intro i
      cases hi : t i with
      | inl x => exact ⟨x, rfl⟩
      | inr x =>
          have h : incidenceMap A B f hf (t i) = .inl (s i) := hs i
          rw [hi] at h
          cases h
    choose old hOld using hsource
    have hsEq : f ∘ old = s := by
      funext i
      have h : incidenceMap A B f hf (t i) = .inl (s i) := hs i
      rw [hOld i] at h
      exact Sum.inl.inj h
    subst s
    have himage : y ∈ incidenceMap A B f hf '' valueFibre A r old := by
      rw [incidenceMap_image_valueFibre A B f hf r old]
      exact hy
    obtain ⟨x, hx, hxy⟩ := himage
    exact ⟨x, ⟨old, hOld, hx⟩, hxy⟩

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
