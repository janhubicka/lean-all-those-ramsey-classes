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
    have hPaper :
        paperIncidenceTagLE A
          (⟨r, ⟨t, ht⟩⟩ : IncidenceTag A)
          (⟨r, ⟨q, hq⟩⟩ : IncidenceTag A) ↔
        A.tupleLE r t q := by
      simp [paperIncidenceTagLE]
    have hLex :
        (toLex (⟨r, ⟨t, ht⟩⟩ : IncidenceTag A) :
          Lex (IncidenceTag A)) ≤
          toLex (⟨r, ⟨q, hq⟩⟩ : IncidenceTag A) ↔
        (⟨t, ht⟩ : {z : Fin (L.arity r) → V //
          A.base.rel r z}) ≤ ⟨q, hq⟩ := by
      constructor
      · intro h
        rcases (Sigma.Lex.le_def).mp h with hlt | ⟨heq, hle⟩
        · have hrr : r < r := hlt
          exact (lt_irrefl r hrr).elim
        · cases heq
          exact hle
      · intro h
        exact (Sigma.Lex.le_def).mpr (Or.inr ⟨rfl, h⟩)
    exact hPaper.trans
      ((hTuple r ⟨t, ht⟩ ⟨q, hq⟩).trans hLex.symm)
  · have hPaper :
        paperIncidenceTagLE A
          (⟨r, ⟨t, ht⟩⟩ : IncidenceTag A)
          (⟨s, ⟨q, hq⟩⟩ : IncidenceTag A) ↔
        r < s := by
      simp [paperIncidenceTagLE, hrs]
    have hLex :
        (toLex (⟨r, ⟨t, ht⟩⟩ : IncidenceTag A) :
          Lex (IncidenceTag A)) ≤
          toLex (⟨s, ⟨q, hq⟩⟩ : IncidenceTag A) ↔
        r < s := by
      constructor
      · intro h
        rcases (Sigma.Lex.le_def).mp h with hlt | ⟨heq, _⟩
        · exact hlt
        · exact (hrs heq).elim
      · intro h
        exact (Sigma.Lex.le_def).mpr (Or.inl h)
    exact hPaper.trans hLex.symm

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
  have hkey (a b : IncidenceCarrier A) :
      @LE.le (IncidenceCarrier A)
        (canonicalIncidenceExternalLinearOrder A tupleOrders).toLE a b ↔
        canonicalIncidenceOrderKey A a ≤ canonicalIncidenceOrderKey A b := by
    change
      (LinearOrder.lift'
        (canonicalIncidenceOrderKey A)
        (canonicalIncidenceOrderKey_injective A)).le a b ↔
      canonicalIncidenceOrderKey A a ≤ canonicalIncidenceOrderKey A b
    rfl
  rw [hkey x y]
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
          have hTag :=
            canonicalIncidenceTagLE_iff A tupleOrders hTuple tag other
          simpa only [incidenceTagLexLinearOrder,
            Sum.Lex.inr_le_inr_iff] using hTag

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
