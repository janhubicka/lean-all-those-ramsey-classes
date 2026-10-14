import AllThoseRamseyClasses.Applications.SteinerTripleClass
import PartiteConstruction.Ramsey.EmptyClosureMultiamalgamation
import Mathlib.Order.RelClasses

/-!
# Ordered ambient Ramsey class for partial Steiner triples

The exact Steiner language has ONE distinguished strict vertex order,
a binary covered-pair marker and a ternary block predicate. The
existing general ordered-relational Ramsey theorem expects a
possibly mixed-arity auxiliary language with an ADDED order symbol.

We transfer the theorem by a *literal renaming*, leaving the
positive and negative covered-pair and block tuples exactly unchanged.
No additional order, convexity, or hidden restriction on vertex
orders is introduced.

This is the ambient R-Ramsey and ordinary-irreducibility part of the
coordinated corrected 2019 application. It does not prove Steiner
strong amalgamation, local completion, or the final Ramsey K-class.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- All finite L-structures with the original named strict total
vertex order; the other relations are arbitrary. -/
def orderedAmbientClass : StructureClass (L := Lang) :=
  fun {V} (C : RelStructure Lang V) =>
    Finite V ∧
    (∀ x : V, ¬ edge C .order x x) ∧
    (∀ x y z : V,
      edge C .order x y → edge C .order y z → edge C .order x z) ∧
    (∀ x y : V, x ≠ y →
      edge C .order x y ∨ edge C .order y x)

/-- Every canonical partial Steiner triple system belongs to the
unrestricted ordered ambient class. -/
theorem orderedSteiner_subset_ambient
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedSteinerClass C) :
    orderedAmbientClass C :=
  ⟨hC.finite, hC.order_irrefl, hC.order_trans, hC.order_total⟩

/-- The distinguished ORIGINAL order witnesses ordinary irreducibility. -/
theorem steinerAmbient_irreducible
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C) :
    C.Irreducible := by
  intro x y hne
  rcases hC.2.2.2 x y hne with h | h
  · exact ⟨.order, ![x, y], 0, 1, h, rfl, rfl⟩
  · exact ⟨.order, ![y, x], 1, 0, h, rfl, rfl⟩

/-- A finite mixed-arity auxiliary language; false has arity 2,
true has arity 3. We do NOT order it a second time after renaming. -/
abbrev AuxiliaryLanguage : RelLanguage where
  Symbol := Bool
  arity
    | false => 2
    | true => 3

/-- Convert the original three named predicates into the standard
external-order representation, preserving their exact interpretations. -/
def toExternal {V : Type} (C : RelStructure Lang V) :
    RelStructure AuxiliaryLanguage.withOrder V where
  rel
    | .inl false, t => C.rel .covered t
    | .inl true, t => C.rel .block t
    | .inr (), t => C.rel .order t

def nameExternal {V : Type}
    (C : RelStructure AuxiliaryLanguage.withOrder V) :
    RelStructure Lang V where
  rel
    | .order, t => C.rel (.inr ()) t
    | .covered, t => C.rel (.inl false) t
    | .block, t => C.rel (.inl true) t

def auxiliaryReduct {V : Type} (C : RelStructure Lang V) :
    RelStructure AuxiliaryLanguage V where
  rel
    | false, t => C.rel .covered t
    | true, t => C.rel .block t

def nameEmbedding {U V : Type}
    {A : RelStructure AuxiliaryLanguage.withOrder U}
    {B : RelStructure AuxiliaryLanguage.withOrder V}
    (e : Embedding A B) :
    Embedding (nameExternal A) (nameExternal B) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R t
    cases R with
    | order => exact e.map_rel_iff (.inr ()) t
    | covered => exact e.map_rel_iff (.inl false) t
    | block => exact e.map_rel_iff (.inl true) t

def unnameEmbedding {U V : Type}
    {A : RelStructure AuxiliaryLanguage.withOrder U}
    {B : RelStructure AuxiliaryLanguage.withOrder V}
    (e : Embedding (nameExternal A) (nameExternal B)) :
    Embedding A B where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R t
    cases R with
    | inl q =>
      cases q with
      | false => exact e.map_rel_iff .covered t
      | true => exact e.map_rel_iff .block t
    | inr u =>
      cases u
      exact e.map_rel_iff .order t

/-- The whole Ramsey arrow transports under the exact symbolic
renaming, not merely individual embeddings or positive tuples. -/
theorem arrow_nameExternal
    {U V W : Type}
    {A : RelStructure AuxiliaryLanguage.withOrder U}
    {B : RelStructure AuxiliaryLanguage.withOrder V}
    {C : RelStructure AuxiliaryLanguage.withOrder W}
    {κ : Type*}
    (h : StructuralRamsey.Arrow A B C κ) :
    StructuralRamsey.Arrow
      (nameExternal A) (nameExternal B) (nameExternal C) κ := by
  intro χ
  let χAux : Embedding A C → κ := fun a => χ (nameEmbedding a)
  obtain ⟨b, hMono⟩ := h χAux
  refine ⟨nameEmbedding b, ?_⟩
  intro e₁ e₂
  calc
    χ ((nameEmbedding b).comp e₁) =
        χ (nameEmbedding (b.comp (unnameEmbedding e₁))) := by
          congr 1
    _ = χ (nameEmbedding (b.comp (unnameEmbedding e₂))) :=
          hMono (unnameEmbedding e₁) (unnameEmbedding e₂)
    _ = χ ((nameEmbedding b).comp e₂) := by
          congr 1

/-- Recover exactly the distinguished old order from an ambient
structure, without adding an independent choice of ordering. -/
noncomputable def ambientLinearOrder
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C) : LinearOrder V := by
  letI : IsStrictTotalOrder V (edge C .order) := {
    trichotomous := by
      intro a b hnab hnba
      by_contra hne
      rcases hC.2.2.2 a b hne with hab | hba
      · exact hnab hab
      · exact hnba hba
    irrefl := hC.2.1
    trans := hC.2.2.1
  }
  letI : DecidableRel (edge C .order) := Classical.decRel _
  exact linearOrderOfSTO (edge C .order)

theorem ambientLinearOrder_lt_iff
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C)
    (x y : V) :
    @LT.lt V (ambientLinearOrder C hC).toLT x y ↔
      edge C .order x y := by
  rfl

/-- Extraction and re-naming reproduce EVERY original relation,
including negative tuples and the ternary block relation. -/
theorem name_ordered_auxiliaryReduct_eq
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C) :
    nameExternal
      (@RelStructure.ordered AuxiliaryLanguage V
        (auxiliaryReduct C) (ambientLinearOrder C hC).toLT) = C := by
  letI : LinearOrder V := ambientLinearOrder C hC
  have hRel :
      (nameExternal ((auxiliaryReduct C).ordered)).rel = C.rel := by
    funext R t
    cases R with
    | order =>
      change (t 0 < t 1) = C.rel .order t
      have ht : (![t 0, t 1] : Fin 2 → V) = t := by
        funext i
        fin_cases i <;> rfl
      have heq :
          (t 0 < t 1) ↔ edge C .order (t 0) (t 1) :=
        ambientLinearOrder_lt_iff C hC (t 0) (t 1)
      exact (propext heq).trans
        (congrArg (C.rel .order) ht)
    | covered => rfl
    | block => rfl
  exact congrArg (fun rel =>
    (RelStructure.mk rel : RelStructure Lang V)) hRel

/-- Ramsey class of all finite structures over the EXACT Steiner
mixed-arity language, where the named strict order is a linear
order and the covered/block predicates are unrestricted. -/
theorem orderedSteinerAmbient_isRamsey :
    FiniteRamseyClass orderedAmbientClass := by
  intro U V hU hV A B hA hB κ hκ hκNonempty
  letI : LinearOrder U := ambientLinearOrder A hA
  letI : LinearOrder V := ambientLinearOrder B hB
  let a : RelStructure AuxiliaryLanguage U := auxiliaryReduct A
  let b : RelStructure AuxiliaryLanguage V := auxiliaryReduct B
  obtain ⟨W, hW, o, c, hArrow⟩ :=
    StructuralRamsey.Partite.orderedRamsey a b κ
  letI : LinearOrder W := o
  let C : RelStructure Lang W := nameExternal c.ordered
  have hC : orderedAmbientClass C := by
    refine ⟨hW, ?_, ?_, ?_⟩
    · intro x hxx
      exact lt_irrefl x hxx
    · intro x y z hxy hyz
      exact lt_trans hxy hyz
    · intro x y hne
      exact lt_or_gt_of_ne hne
  have hName :
      StructuralRamsey.Arrow
        (nameExternal a.ordered)
        (nameExternal b.ordered) C κ :=
    arrow_nameExternal hArrow
  have hEqA : nameExternal a.ordered = A :=
    name_ordered_auxiliaryReduct_eq A hA
  have hEqB : nameExternal b.ordered = B :=
    name_ordered_auxiliaryReduct_eq B hB
  rw [hEqA, hEqB] at hName
  exact ⟨W, hW, C, hC, hName⟩

end AllThoseRamseyClasses.Applications.SteinerTriples
