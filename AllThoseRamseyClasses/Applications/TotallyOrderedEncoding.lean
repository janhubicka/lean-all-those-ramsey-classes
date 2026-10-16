import PartiteConstruction.Ramsey.Ordered
import Mathlib.Tactic

/-!
# Totally ordered relations: the exact relational shadow of paper Theorem TO

This module isolates the first, logically exact step of the manuscript's
incidence-closure proof. For an arbitrary relational signature, each
relation symbol of arity n acquires a relation of arity 2*n recording
the order of its tuples, along with the distinguished vertex order.

Full embeddings of this expanded relational shadow are *equivalent*
to injections reflecting the original relations, every tuple order,
and the vertex order. No class-level Ramsey property is inferred:
the incidence-closure lift, strong amalgamation, and exact weak local
completion remain separate obligations.

The proof allows n=0, so it does not silently discard nullary symbols.
-/ 

namespace AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w

/-- Original, tuple-order and vertex-order relation symbols. -/
inductive ExpandedSymbol (L : RelLanguage.{u}) : Type u
  | original : L.Symbol → ExpandedSymbol L
  | tupleOrder : L.Symbol → ExpandedSymbol L
  | vertexOrder : ExpandedSymbol L

/-- The paper's L,2L language: an n-ary relation order has arity 2*n. -/
abbrev ExpandedLanguage (L : RelLanguage.{u}) : RelLanguage.{u} where
  Symbol := ExpandedSymbol L
  arity
    | .original r => L.arity r
    | .tupleOrder r => L.arity r + L.arity r
    | .vertexOrder => 2

/-- The data before the incidence relational encoding. These fields
are deliberately just predicates: linear-order and tuple-support
axioms can be imposed later as a separate concrete class predicate. -/
structure TotalOrderData (L : RelLanguage.{u}) (V : Type v) where
  base : RelStructure L V
  vertexLE : V → V → Prop
  tupleLE : (r : L.Symbol) →
    (Fin (L.arity r) → V) → (Fin (L.arity r) → V) → Prop

def firstTuple {n : ℕ} {V : Type v}
    (t : Fin (n + n) → V) : Fin n → V :=
  fun i => t (Fin.castAdd n i)

def secondTuple {n : ℕ} {V : Type v}
    (t : Fin (n + n) → V) : Fin n → V :=
  fun i => t (Fin.natAdd n i)

@[simp] theorem firstTuple_append {n : ℕ} {V : Type v}
    (a b : Fin n → V) :
    firstTuple (Fin.append a b) = a := by
  funext i
  simp [firstTuple]

@[simp] theorem secondTuple_append {n : ℕ} {V : Type v}
    (a b : Fin n → V) :
    secondTuple (Fin.append a b) = b := by
  funext i
  exact Fin.append_right a b i

@[simp] theorem firstTuple_comp {n : ℕ} {U : Type v} {V : Type w}
    (f : U → V) (t : Fin (n + n) → U) :
    firstTuple (f ∘ t) = f ∘ firstTuple t := rfl

@[simp] theorem secondTuple_comp {n : ℕ} {U : Type v} {V : Type w}
    (f : U → V) (t : Fin (n + n) → U) :
    secondTuple (f ∘ t) = f ∘ secondTuple t := rfl

/-- A relation order is represented literally by a 2n-ary symbol. -/
def encode {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V) :
    RelStructure (ExpandedLanguage L) V where
  rel
    | .original r, t => A.base.rel r t
    | .tupleOrder r, t => A.tupleLE r (firstTuple t) (secondTuple t)
    | .vertexOrder, t => A.vertexLE (t 0) (t 1)

/-- The manuscript's exact embedding semantics before encoding.
Reflection, not mere positive preservation, is required in each field. -/
def IsExactEmbedding {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) : Prop :=
  Function.Injective f ∧
  (∀ (r : L.Symbol) (t : Fin (L.arity r) → U),
    B.base.rel r (f ∘ t) ↔ A.base.rel r t) ∧
  (∀ x y : U, B.vertexLE (f x) (f y) ↔ A.vertexLE x y) ∧
  (∀ (r : L.Symbol) (a b : Fin (L.arity r) → U),
    B.tupleLE r (f ∘ a) (f ∘ b) ↔ A.tupleLE r a b)

/-- Exact embeddings of the unencoded data yield full relational embeddings. -/
def encodeEmbedding {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    Embedding (encode A) (encode B) where
  toFun := f
  injective := hf.1
  map_rel_iff := by
    intro r t
    cases r with
    | original r =>
        exact hf.2.1 r t
    | vertexOrder =>
        change B.vertexLE (f (t 0)) (f (t 1)) ↔
          A.vertexLE (t 0) (t 1)
        exact hf.2.2.1 (t 0) (t 1)
    | tupleOrder r =>
        change B.tupleLE r (f ∘ firstTuple t) (f ∘ secondTuple t) ↔
          A.tupleLE r (firstTuple t) (secondTuple t)
        exact hf.2.2.2 r (firstTuple t) (secondTuple t)

/-- Conversely every full embedding of the relational encoding
reflects each source relation, the vertex order, and every tuple
comparison, even for nullary and empty relations. -/
theorem exactEmbedding_of_encodeEmbedding {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Embedding (encode A) (encode B)) :
    IsExactEmbedding A B e := by
  refine ⟨e.injective, ?_, ?_, ?_⟩
  · intro r t
    exact e.map_rel_iff (.original r) t
  · intro x y
    have h := e.map_rel_iff .vertexOrder ![x, y]
    change B.vertexLE (e x) (e y) ↔ A.vertexLE x y at h
    exact h
  · intro r a b
    have h := e.map_rel_iff (.tupleOrder r) (Fin.append a b)
    change B.tupleLE r
        (firstTuple (e ∘ Fin.append a b))
        (secondTuple (e ∘ Fin.append a b)) ↔
      A.tupleLE r (firstTuple (Fin.append a b))
        (secondTuple (Fin.append a b)) at h
    simpa only [firstTuple_comp, secondTuple_comp,
      firstTuple_append, secondTuple_append] using h

/-- A complete iff formulation; the right-hand condition does not
assume an embedding, but derives the exact expanded-language one. -/
theorem exactEmbedding_iff_encoded {L : RelLanguage.{u}}
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) :
    IsExactEmbedding A B f ↔
      ∃ e : Embedding (encode A) (encode B), (e : U → V) = f := by
  constructor
  · intro hf
    exact ⟨encodeEmbedding A B f hf, rfl⟩
  · rintro ⟨e, he⟩
    subst f
    exact exactEmbedding_of_encodeEmbedding A B e

end AllThoseRamseyClasses.Applications.TotallyOrderedEncoding
