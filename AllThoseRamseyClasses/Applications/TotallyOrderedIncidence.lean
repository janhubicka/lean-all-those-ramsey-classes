import AllThoseRamseyClasses.Applications.TotallyOrderedEncoding
import Mathlib.Tactic

/-!
# Incidence closure: exact functional semantics over old tuples

A relation symbol r of arity n gives one new, distinctly typed vertex
(r,t) for each positive original r-tuple t. The value of the partial
incidence closure F_r is this incidence vertex for positive old tuples,
and is undefined for all negative old tuples.

An exact full original embedding transports all defined incidence
values and reflects undefinedness. This is the paper's first incidence
closure compatibility step, not yet a proof of the full ordered
incidence class, strong amalgamation, or Ramsey property.

The assertions work for arbitrary finite-arity relation symbols; the
eventual closure-rule instance needs proper nonempty roots and hence
must treat nullary symbols separately.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Original vertices plus one unique new vertex per positive
relation tuple, tagged by its own relation symbol. -/
abbrev IncidenceCarrier {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) :=
  V ⊕ (Sigma fun r : L.Symbol =>
    {t : Fin (L.arity r) → V // A.base.rel r t})

/-- Partial incidence value on an original tuple. -/
noncomputable def incidenceValue {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → V) :
    Option (IncidenceCarrier A) :=
  if h : A.base.rel r t then
    some (.inr ⟨r, ⟨t, h⟩⟩)
  else
    none

/-- The only possible extension of an exact embedding on originals
to named positive incidence vertices. -/
noncomputable def incidenceMap {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    IncidenceCarrier A → IncidenceCarrier B
  | .inl x => .inl (f x)
  | .inr ⟨r, ⟨t, h⟩⟩ =>
      .inr ⟨r, ⟨f ∘ t, (hf.2.1 r t).mpr h⟩⟩

@[simp] theorem incidenceMap_old {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (x : U) :
    incidenceMap A B f hf (.inl x) = .inl (f x) := rfl

/-- Exact preservation and reflection of definedness, not just
positive homomorphism: an incidence vertex exists in the target
precisely when its source tuple is positive. -/
theorem incidenceValue_map {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f)
    (r : L.Symbol) (t : Fin (L.arity r) → U) :
    Option.map (incidenceMap A B f hf) (incidenceValue A r t) =
      incidenceValue B r (f ∘ t) := by
  classical
  by_cases h : A.base.rel r t
  · have hB : B.base.rel r (f ∘ t) := (hf.2.1 r t).mpr h
    simp [incidenceValue, h, hB, incidenceMap]
  · have hB : ¬ B.base.rel r (f ∘ t) :=
      fun h' => h ((hf.2.1 r t).mp h')
    simp [incidenceValue, h, hB]

/-- The exact set-valued fibre form in the functional language:
an undefined value has empty fibre and a defined one a singleton. -/
def valueFibre {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) (r : L.Symbol)
    (t : Fin (L.arity r) → V) :
    Set (IncidenceCarrier A) :=
  {x | some x = incidenceValue A r t}

/-- For finite relational signatures and original carriers,
adding one incidence vertex per positive tuple preserves finiteness. -/
theorem finite_incidenceCarrier {L : RelLanguage.{u}}
    {V : Type v} [Finite L.Symbol] [Finite V]
    (A : TotalOrderData L V) : Finite (IncidenceCarrier A) := by
  unfold IncidenceCarrier
  infer_instance

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
