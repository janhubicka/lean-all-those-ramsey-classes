import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceCanonicalExternalOrder

/-!
# Source-matched canonical incidence order compatibility

The canonical external order of the tagged incidence carrier is built from:
(1) an original vertex LinearOrder;
(2) for each relation symbol, a LinearOrder on its POSITIVE tuple subtype;
(3) a fixed LinearOrder on relation symbols.

The manuscript's literal incidence comparison agrees with that external
order precisely when the TotalOrderData predicates are the restrictions of
those supplied genuine orders. This explicit bridge is the remaining
source-side hypothesis needed to instantiate the freely ordered EHN theorem,
rather than an unsupported identification of an arbitrary relation with
the auxiliary Ramsey witness's external order.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- Dependently ordered positive tuples yield a genuine Sigma-lex order
of tagged positive relation instances. -/
noncomputable def incidenceTagLexLinearOrder
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} (A : TotalOrderData L V)
    (tupleOrders : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t}) :
    LinearOrder (Lex (IncidenceTag A)) := by
  classical
  letI : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t} :=
    tupleOrders
  infer_instance

/-- The paper's new-tag comparison is exactly Mathlib's lexicographic
Sigma comparison, including equality of relation symbols and dependent
tuples of distinct arities. -/
theorem canonicalIncidenceTagLE_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} (A : TotalOrderData L V)
    (tupleOrders : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t})
    (hTuple : ∀ (r : L.Symbol)
      (t s : {q : Fin (L.arity r) → V // A.base.rel r q}),
      A.tupleLE r t.1 s.1 ↔
        @LE.le _ (tupleOrders r).toLE t s)
    (a b : IncidenceTag A) :
    paperIncidenceTagLE A a b ↔
      @LE.le (Lex (IncidenceTag A))
        (incidenceTagLexLinearOrder A tupleOrders).toLE
        (toLex a) (toLex b) := by
  classical
  letI : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t} :=
    tupleOrders
  change paperIncidenceTagLE A a b ↔
    (toLex a : Lex (IncidenceTag A)) ≤ toLex b
  rcases a with ⟨r, ⟨t, ht⟩⟩
  rcases b with ⟨s, ⟨q, hq⟩⟩
  by_cases hrs : r = s
  · subst s
    simpa [paperIncidenceTagLE, Sigma.Lex.le_def, toLex] using
      (hTuple r ⟨t, ht⟩ ⟨q, hq⟩)
  · simp [paperIncidenceTagLE, Sigma.Lex.le_def, hrs, toLex]

/-- The genuine canonical external order matches the paper's entire
Old-first, symbol-first incidence comparison whenever original vertex
and positive tuple comparisons arise from their supplied linear orders.
The weak Ramsey target is deliberately not covered by this statement. -/
theorem canonicalIncidenceExternalLinearOrder_agrees
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v} [LinearOrder V]
    (A : TotalOrderData L V)
    (tupleOrders : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t})
    (hVertex : ∀ x y : V, A.vertexLE x y ↔ x ≤ y)
    (hTuple : ∀ (r : L.Symbol)
      (t s : {q : Fin (L.arity r) → V // A.base.rel r q}),
      A.tupleLE r t.1 s.1 ↔
        @LE.le _ (tupleOrders r).toLE t s)
    (x y : IncidenceCarrier A) :
    paperIncidenceLE A x y ↔
      @LE.le (IncidenceCarrier A)
        (canonicalIncidenceExternalLinearOrder A tupleOrders).toLE x y := by
  classical
  letI : (r : L.Symbol) →
      LinearOrder {t : Fin (L.arity r) → V // A.base.rel r t} :=
    tupleOrders
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          change A.vertexLE x y ↔
            (toLex (Sum.inl x : V ⊕ Lex (IncidenceTag A))) ≤
              (toLex (Sum.inl y : V ⊕ Lex (IncidenceTag A)))
          exact (hVertex x y).trans (Sum.Lex.inl_le_inl_iff).symm
      | inr tag =>
          change True ↔
            (toLex (Sum.inl x : V ⊕ Lex (IncidenceTag A))) ≤
              (toLex (Sum.inr (toLex tag) : V ⊕ Lex (IncidenceTag A)))
          constructor
          · intro _
            exact Sum.Lex.inl_le_inr x (toLex tag)
          · intro _
            trivial
  | inr tag =>
      cases y with
      | inl y =>
          change False ↔
            (toLex (Sum.inr (toLex tag) : V ⊕ Lex (IncidenceTag A))) ≤
              (toLex (Sum.inl y : V ⊕ Lex (IncidenceTag A)))
          constructor
          · intro h
            cases h
          · intro h
            exact (Sum.Lex.not_inr_le_inl h).elim
      | inr other =>
          change paperIncidenceTagLE A tag other ↔
            (toLex (Sum.inr (toLex tag) : V ⊕ Lex (IncidenceTag A))) ≤
              (toLex (Sum.inr (toLex other) : V ⊕ Lex (IncidenceTag A)))
          exact (canonicalIncidenceTagLE_iff A tupleOrders hTuple tag other).trans
            (Sum.Lex.inr_le_inr_iff).symm

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
