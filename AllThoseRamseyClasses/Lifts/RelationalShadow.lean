import PartiteConstruction.Ramsey.Basic
import PartiteConstruction.Relational.Homomorphism

/-!
# Ramsey lifts: relational language extensions and shadows

The relational part of Section 3 ("Construction of Ramsey lifts") of
Hubička--Nešetřil, *All those Ramsey classes* (2019).

An extra relation symbol is distinguished from every original symbol,
even when it has the same arity.  The shadow is the literal reduct on
the SAME vertex carrier, as stipulated in the manuscript.  The next
module describes the piece-generated extra relations.

Definitions about labelled fibres below intentionally do not yet
assert the full paper's *isomorphism-type* precompactness, and nothing
here asserts strong amalgamation or a Ramsey theorem.  The treatment
of primitive partial/set-valued functions is a separate extension.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w

/-- Extend a relational language by new symbols with prescribed arities.
This is the relational instance of the paper's L included in L⁺. -/
def language (L : RelLanguage.{u}) (New : Type w)
    (ar : New → ℕ) : RelLanguage.{max u w} where
  Symbol := L.Symbol ⊕ New
  arity := Sum.elim L.arity ar

/-- Forget the extra relation symbols, keeping the carrier and every
old relation interpretation unchanged. -/
def shadow (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    {V : Type v} (X : RelStructure (language L New ar) V) :
    RelStructure L V where
  rel R := X.rel (.inl R)

/-- Form an expansion from an old structure and an interpretation for
each genuinely new relation symbol. -/
def withExtra (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    {V : Type v} (A : RelStructure L V)
    (extra : ∀ i : New, (Fin (ar i) → V) → Prop) :
    RelStructure (language L New ar) V where
  rel R := by
    cases R with
    | inl s => exact A.rel s
    | inr i => exact extra i

/-- Every specified expansion has exactly the prescribed shadow. -/
@[simp] theorem shadow_withExtra (L : RelLanguage.{u}) (New : Type w)
    (ar : New → ℕ) {V : Type v} (A : RelStructure L V)
    (extra : ∀ i : New, (Fin (ar i) → V) → Prop) :
    shadow L New ar (withExtra L New ar A extra) = A := by
  cases A
  rfl

/-- A full embedding of expansions always restricts to a full
embedding of their shadows, with the same vertex map. -/
def shadowEmbedding (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    {V W : Type v}
    {X : RelStructure (language L New ar) V}
    {Y : RelStructure (language L New ar) W}
    (e : Embedding X Y) :
    Embedding (shadow L New ar X) (shadow L New ar Y) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl R) xs

@[simp] theorem shadowEmbedding_apply
    (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    {V W : Type v}
    {X : RelStructure (language L New ar) V}
    {Y : RelStructure (language L New ar) W}
    (e : Embedding X Y) (x : V) :
    shadowEmbedding L New ar e x = e x := rfl

/-- A shadow embedding lifts to the given expansions exactly when
it ALSO reflects every new relation (as well as preserving them).
This reflection is not automatic for canonical piece lifts. -/
def withExtraEmbedding
    (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    {V W : Type v} {A : RelStructure L V} {B : RelStructure L W}
    (extraA : ∀ i : New, (Fin (ar i) → V) → Prop)
    (extraB : ∀ i : New, (Fin (ar i) → W) → Prop)
    (e : Embedding A B)
    (hExtra : ∀ i xs, extraB i (e ∘ xs) ↔ extraA i xs) :
    Embedding (withExtra L New ar A extraA)
      (withExtra L New ar B extraB) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := by
    cases R with
    | inl s => exact e.map_rel_iff s xs
    | inr i => exact hExtra i xs

/-- A named-carrier lift of A (as opposed to a carrier changed by an
isomorphism) is exactly an expansion whose shadow equals A. -/
def IsLiftOf (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    {V : Type v} (X : RelStructure (language L New ar) V)
    (A : RelStructure L V) : Prop :=
  shadow L New ar X = A

/-- All admitted expansions of a particular structure on its fixed
carrier.  For finite A, this is the labelled fibre used when comparing
precompactness with the manuscript's count of isomorphism types. -/
def LiftFibre
    (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    (Kplus : StructureClass.{max u w, v} (L := language L New ar))
    {V : Type v} (A : RelStructure L V) :=
  {X : RelStructure (language L New ar) V //
    Kplus X ∧ IsLiftOf L New ar X A}

/-- Finiteness of every labelled fibre, explicitly distinguished
from the paper's isomorphism-type Definition defn:precompact. -/
def LabelledPrecompactLift
    (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    (K : StructureClass.{u,v} (L := L))
    (Kplus : StructureClass.{max u w,v} (L := language L New ar)) : Prop :=
  ∀ {V : Type v} (A : RelStructure L V), K A →
    Finite (LiftFibre L New ar Kplus A)

/-- Definition defn:ordering, normalized to fixed named carriers:
B has the lift property for A if every admitted lift of A embeds into
every admitted lift of B.  Kplus is NOT required to contain all lifts. -/
def LiftPropertyFor
    (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    (Kplus : StructureClass.{max u w,v} (L := language L New ar))
    {V W : Type v} (A : RelStructure L V) (B : RelStructure L W) : Prop :=
  ∀ (XA : RelStructure (language L New ar) V)
    (XB : RelStructure (language L New ar) W),
    Kplus XA → Kplus XB →
    IsLiftOf L New ar XA A → IsLiftOf L New ar XB B →
    Nonempty (Embedding XA XB)

/-- The class-wide lift/expansion property: each A in K admits
some B in K with the lift property for A. -/
def HasLiftProperty
    (L : RelLanguage.{u}) (New : Type w) (ar : New → ℕ)
    (K : StructureClass.{u,v} (L := L))
    (Kplus : StructureClass.{max u w,v} (L := language L New ar)) : Prop :=
  ∀ {V : Type v} (A : RelStructure L V), K A →
    ∃ (W : Type v) (B : RelStructure L W),
      K B ∧ LiftPropertyFor L New ar Kplus A B

end AllThoseRamseyClasses.Lifts
