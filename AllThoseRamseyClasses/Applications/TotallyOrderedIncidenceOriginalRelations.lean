import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceFunctionalEmbedding

/-!
# Full original relations and incidence functions on the lifted carrier

The paper's totally ordered incidence construction extends every
original relation symbol from old vertices only; tuples containing
a newly introduced incidence vertex do not satisfy original
relations. Previous work verified the entire function table,
including empty fibres for mixed-input tuples. Here we ADD BACK
the actual original relational shadow and prove an honest full
Structure.Embedding simultaneously preserving and reflecting all
original relation tuples and mapping all set-valued function fibres
exactly onto the target fibres.

The proof also handles arbitrary finite arities (including nullary
relation symbols), with no silent assumption that the source tuple
is positive or that all mapped target-original inputs had original
sources. No relation-order symbols are added in this module; the
paper's full vertex order on old+new vertices is validated separately.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- The original L-relation holds on a lifted tuple exactly when
all its coordinates are old and their original tuple is positive.
For arity zero this correctly reduces to the original nullary
relation value. -/
def liftedOriginalRel {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → IncidenceCarrier A) : Prop :=
  ∃ old : Fin (L.arity r) → V,
    (∀ i, t i = .inl (old i)) ∧ A.base.rel r old

/-- On an all-original tuple the original relation is unchanged;
no new positive information is introduced. -/
theorem liftedOriginalRel_old
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → V) :
    liftedOriginalRel A r (fun i => .inl (t i)) ↔
      A.base.rel r t := by
  constructor
  · rintro ⟨s, hs, hrel⟩
    have hts : t = s := by
      funext i
      exact Sum.inl.inj (hs i)
    subst s
    exact hrel
  · intro hrel
    exact ⟨t, fun _ => rfl, hrel⟩

/-- A tuple with even one new incidence vertex does not satisfy
any original relation of positive arity. -/
theorem liftedOriginalRel_false_of_new
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → IncidenceCarrier A)
    (i : Fin (L.arity r)) (s : IncidenceTag A)
    (hi : t i = .inr s) :
    ¬ liftedOriginalRel A r t := by
  rintro ⟨old, hOld, _⟩
  have h := hOld i
  rw [hi] at h
  cases h

/-- Exact transport and reflection of original relations on
the enlarged old/new carriers. In the reverse direction, a tuple
whose *image* is entirely old must already have been entirely old:
the incidence extension never maps a new vertex to an original. -/
theorem liftedOriginalRel_map_iff
    {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (r : L.Symbol) (t : Fin (L.arity r) → IncidenceCarrier A) :
    liftedOriginalRel B r (incidenceMap A B f hf ∘ t) ↔
      liftedOriginalRel A r t := by
  classical
  constructor
  · rintro ⟨s, hs, hRelB⟩
    have hsource :
        ∀ i : Fin (L.arity r), ∃ x : U, t i = .inl x := by
      intro i
      cases hi : t i with
      | inl x => exact ⟨x, rfl⟩
      | inr x =>
          have h : incidenceMap A B f hf (t i) = .inl (s i) := hs i
          rw [hi] at h
          cases h
    choose old hOld using hsource
    have hcomp : f ∘ old = s := by
      funext i
      have h : incidenceMap A B f hf (t i) = .inl (s i) := hs i
      rw [hOld i] at h
      exact Sum.inl.inj h
    subst s
    exact ⟨old, hOld, (hf.2.1 r old).mp hRelB⟩
  · rintro ⟨old, hOld, hRelA⟩
    refine ⟨f ∘ old, ?_, (hf.2.1 r old).mpr hRelA⟩
    intro i
    change incidenceMap A B f hf (t i) = .inl (f (old i))
    rw [hOld i]
    rfl

/-- The actual original-relations + complete-incidence-functions
reduct on the enlarged carrier. Unlike the earlier function-only
redact, its original relations are not inert placeholders. -/
def incidenceOriginalAndFunctional
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) :
    Structure (incidenceFunctionalLanguage L) (IncidenceCarrier A) where
  rel := liftedOriginalRel A
  func := fullIncidenceFibre A

/-- A full induced embedding of the paper's original relations
together with the complete set-valued incidence closure functions.
This is stronger than the previous function-only embedding: it
preserves and REFLECTS every original mixed/old tuple, including
absence of any original relation on a new incidence vertex. -/
noncomputable def incidenceOriginalAndFunctionalEmbedding
    {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    Structure.Embedding
      (incidenceOriginalAndFunctional A)
      (incidenceOriginalAndFunctional B) where
  toFun := incidenceMap A B f hf
  injective := incidenceMap_injective A B f hf
  map_rel_iff := by
    intro r t
    exact liftedOriginalRel_map_iff A B f hf r t
  map_func := by
    intro r t
    exact incidenceMap_image_fullIncidenceFibre A B f hf r t

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
