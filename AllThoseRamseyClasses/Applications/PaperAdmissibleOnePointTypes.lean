import PartiteConstruction.Ramsey.CopywiseRamseyTransfer
import PartiteConstruction.Relational.Order
import Mathlib.Order.Prod.Lex.Basic

/-!
# Admissible vertex orders from complete one-point relational types

The manuscript's admissible-order proposition uses a fixed order of
one-vertex isomorphism types. For each vertex x its type is the set
of relation symbols R whose diagonal tuple R(x,...,x) is positive.
This also handles nullary symbols and repeated coordinates.

Full embeddings preserve and reflect one-point types exactly. Given
a chosen order of the type codes, reordering a Ramsey witness by
(type(x), old-position(x)) preserves every FULL ordered copy of an
already admissibly ordered B. The existing B-copywise Ramsey
transfer then supplies the admissible ordered Ramsey witness.

The identification of the manuscript's type-order notation with
these diagonal-code orders is separate from the core construction.
-/

namespace AllThoseRamseyClasses.Applications.AdmissibleOrders

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v

/-- Complete unary relational type recorded by diagonal tuples. -/
def onePointType {L : RelLanguage.{u}} {V : Type v}
    (A : RelStructure L V) (x : V) : Set L.Symbol :=
  {R | A.rel R (fun _ => x)}

/-- The chosen vertex order respects strictly increasing types. -/
def TypeAdmissible {L : RelLanguage.{u}} {V : Type v}
    [LinearOrder V] (typeOrder : LinearOrder (Set L.Symbol))
    (A : RelStructure L V) : Prop :=
  ∀ x y : V,
    @LT.lt (Set L.Symbol) typeOrder.toLT
      (onePointType A x) (onePointType A y) →
      x < y

/-- Sort vertices by their one-point type, preserving old order
as an injective tie-breaker inside each type. -/
noncomputable def typeSortedLinearOrder
    {L : RelLanguage.{u}} {V : Type v} [LinearOrder V]
    (typeOrder : LinearOrder (Set L.Symbol))
    (A : RelStructure L V) : LinearOrder V := by
  classical
  letI : LinearOrder (Set L.Symbol) := typeOrder
  exact LinearOrder.lift'
    (fun x => toLex ((onePointType A x, x) : Set L.Symbol × V))
    (by
      intro x y h
      exact congrArg Prod.snd
        (congrArg
          (ofLex : Lex (Set L.Symbol × V) → Set L.Symbol × V) h))

theorem typeSortedLinearOrder_lt_iff
    {L : RelLanguage.{u}} {V : Type v} [LinearOrder V]
    (typeOrder : LinearOrder (Set L.Symbol))
    (A : RelStructure L V) (x y : V) :
    (letI := typeSortedLinearOrder typeOrder A; x < y) ↔
    @LT.lt (Set L.Symbol) typeOrder.toLT
       (onePointType A x) (onePointType A y) ∨
    (onePointType A x = onePointType A y ∧ x < y) := by
  letI : LinearOrder (Set L.Symbol) := typeOrder
  change toLex ((onePointType A x, x) : Set L.Symbol × V) <
      toLex ((onePointType A y, y) : Set L.Symbol × V) ↔ _
  exact Prod.Lex.toLex_lt_toLex

theorem typeSortedLinearOrder_isAdmissible
    {L : RelLanguage.{u}} {V : Type v} [LinearOrder V]
    (typeOrder : LinearOrder (Set L.Symbol))
    (A : RelStructure L V) :
    (letI := typeSortedLinearOrder typeOrder A;
      TypeAdmissible typeOrder A) := by
  intro x y hxy
  exact (typeSortedLinearOrder_lt_iff typeOrder A x y).mpr (Or.inl hxy)

/-- Full embeddings reflect diagonal positive AND negative tuples. -/
theorem onePointType_embedding
    {L : RelLanguage.{u}} {U V : Type v}
    [LinearOrder U] [LinearOrder V]
    (B : RelStructure L U) (C : RelStructure L V)
    (b : Embedding B.ordered C.ordered) (x : U) :
    onePointType C (b x) = onePointType B x := by
  ext R
  have ht : (b ∘ (fun _ : Fin (L.arity R) => x)) =
      (fun _ : Fin (L.arity R) => b x) := rfl
  have h := b.map_rel_iff (.inl R) (fun _ : Fin (L.arity R) => x)
  change C.rel R (b ∘ (fun _ : Fin (L.arity R) => x)) ↔
      B.rel R (fun _ : Fin (L.arity R) => x) at h
  rw [ht] at h
  exact h

/-- Sorted target order still preserves the order of the B-copy. -/
theorem typeSorted_copy_strictMono
    {L : RelLanguage.{u}} {U V : Type v}
    [LinearOrder U] [LinearOrder V]
    (typeOrder : LinearOrder (Set L.Symbol))
    (B : RelStructure L U) (C : RelStructure L V)
    (hB : TypeAdmissible typeOrder B)
    (b : Embedding B.ordered C.ordered)
    (x y : U) (hxy : x < y) :
    (letI := typeSortedLinearOrder typeOrder C; b x < b y) := by
  letI : LinearOrder (Set L.Symbol) := typeOrder
  have htype (z : U) : onePointType C (b z) = onePointType B z :=
    onePointType_embedding B C b z
  have hle : onePointType B x ≤ onePointType B y := by
    by_contra hn
    have hgt : onePointType B y < onePointType B x := lt_of_not_ge hn
    exact (not_lt_of_ge (le_of_lt hxy)) (hB y x hgt)
  apply (typeSortedLinearOrder_lt_iff typeOrder C (b x) (b y)).mpr
  rw [htype x, htype y]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, b.strictMono hxy⟩

/-- Every induced order-preserving copy of admissible B survives
sorting C by types, as a full relational ordered embedding. -/
theorem typeSorted_preserves_ordered_copies
    {L : RelLanguage.{u}} {U V : Type v}
    [LinearOrder U] [LinearOrder V]
    (typeOrder : LinearOrder (Set L.Symbol))
    (B : RelStructure L U) (C : RelStructure L V)
    (hB : TypeAdmissible typeOrder B) :
    CopywiseCompletion B.ordered C.ordered
      (@RelStructure.ordered L V C
        (typeSortedLinearOrder typeOrder C).toLT)
      (fun x => x) := by
  intro b
  let e : Embedding B.ordered
      (@RelStructure.ordered L V C
        (typeSortedLinearOrder typeOrder C).toLT) := {
    toFun := b
    injective := b.injective
    map_rel_iff := by
      intro R t
      cases R with
      | inl s =>
          exact b.map_rel_iff (.inl s) t
      | inr unit =>
          cases unit
          let t₂ : Fin 2 → U := t
          let x : U := t₂ 0
          let y : U := t₂ 1
          change (@LT.lt V (typeSortedLinearOrder typeOrder C).toLT
            (b x) (b y)) ↔ x < y
          constructor
          · intro hlt
            by_contra hn
            have hyx : y ≤ x := le_of_not_gt hn
            rcases eq_or_lt_of_le hyx with heq | hyxlt
            · have hh : (@LT.lt V (typeSortedLinearOrder typeOrder C).toLT
                  (b x) (b x)) := by
                simpa only [heq] using hlt
              letI : LinearOrder V := typeSortedLinearOrder typeOrder C
              exact (lt_irrefl _ hh)
            · have hh : (@LT.lt V (typeSortedLinearOrder typeOrder C).toLT
                  (b y) (b x)) :=
                typeSorted_copy_strictMono typeOrder B C hB b y x hyxlt
              letI : LinearOrder V := typeSortedLinearOrder typeOrder C
              exact (lt_asymm hlt hh).elim
          · intro hxy
            exact typeSorted_copy_strictMono typeOrder B C hB b x y hxy
  }
  exact ⟨e, fun _ => rfl⟩

/-- Transfer a freely ordered Ramsey witness to an admissibly
ordered witness, preserving the original underlying structure
and its membership in any ambient class K. -/
theorem typeAdmissible_arrow_of_freeOrder
    {L : RelLanguage.{u}} {U V : Type v}
    [LinearOrder U] [LinearOrder V]
    (typeOrder : LinearOrder (Set L.Symbol))
    (K : StructureClass.{u,v} (L := L))
    (A : RelStructure L U) (B : RelStructure L V)
    (hB : TypeAdmissible typeOrder B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W), K C ∧
        StructuralRamsey.Arrow A.ordered B.ordered
          (@RelStructure.ordered L W C o.toLT) κ) :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W), K C ∧
        @TypeAdmissible L W o typeOrder C ∧
        StructuralRamsey.Arrow A.ordered B.ordered
          (@RelStructure.ordered L W C o.toLT) κ := by
  obtain ⟨W, hW, o, C, hKC, hArrow⟩ := hRamsey
  letI : LinearOrder W := o
  have hCopies : CopywiseCompletion B.ordered
      (@RelStructure.ordered L W C o.toLT)
      (@RelStructure.ordered L W C
        (@typeSortedLinearOrder L W o typeOrder C).toLT)
      (fun x => x) :=
    @typeSorted_preserves_ordered_copies L V W _ o typeOrder B C hB
  have hArrow' : StructuralRamsey.Arrow A.ordered B.ordered
      (@RelStructure.ordered L W C
        (@typeSortedLinearOrder L W o typeOrder C).toLT) κ :=
    arrow_of_BCopywiseCompletion hArrow hCopies
  exact ⟨W, hW, @typeSortedLinearOrder L W o typeOrder C, C,
    hKC, @typeSortedLinearOrder_isAdmissible L W o typeOrder C,
    hArrow'⟩

end AllThoseRamseyClasses.Applications.AdmissibleOrders
