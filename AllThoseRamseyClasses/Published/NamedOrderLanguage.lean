import AllThoseRamseyClasses.Published.OrderedAmbientOrder
import PartiteConstruction.Ramsey.Ordered

/-!
# The three named relations versus a distinguished external order

The published example uses one binary language with symbols
(<, E, M).  The existing Ramsey theorem applies to two arbitrary
binary relations (E, M) together with an ADDED order symbol.

We explicitly relabel these languages, using NO semantic assumption
about E or M.  Embeddings reflect all three named relations, and the
Ramsey arrow transports in both directions. This is the missing
finite-language identification for the ambient R-Ramsey argument.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Two independent binary relations for E and M, before adding
the distinguished strict order. False names E; true names M. -/
abbrev AuxiliaryLanguage : RelLanguage where
  Symbol := Bool
  arity := fun _ => 2

/-- Read a named (<,E,M)-structure as the identical relational
structure in (E,M)+external-order, on exactly the same vertices. -/
def toExternal {V : Type} (C : RelStructure Lang V) :
    RelStructure AuxiliaryLanguage.withOrder V where
  rel
    | .inl false, t => C.rel .equiv t
    | .inl true, t => C.rel .mate t
    | .inr (), t => C.rel .lt t

/-- Name the distinguished order and the two auxiliary predicates
without changing vertices, tuples, or positive/negative relations. -/
def nameExternal {V : Type}
    (C : RelStructure AuxiliaryLanguage.withOrder V) :
    RelStructure Lang V where
  rel
    | .lt, t => C.rel (.inr ()) t
    | .equiv, t => C.rel (.inl false) t
    | .mate, t => C.rel (.inl true) t

/-- Every embedding of externally ordered relational structures
remains an induced embedding when the symbols are renamed. -/
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
    | lt => exact e.map_rel_iff (.inr ()) t
    | equiv => exact e.map_rel_iff (.inl false) t
    | mate => exact e.map_rel_iff (.inl true) t

/-- The inverse translation reflects all named relations, including
nonedges and the negative direction of the order predicate. -/
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
      | false => exact e.map_rel_iff .equiv t
      | true => exact e.map_rel_iff .mate t
    | inr u =>
      cases u
      exact e.map_rel_iff .lt t

/-- Relabelled copies commute with embedding composition. -/
theorem nameEmbedding_comp {U V W : Type}
    {A : RelStructure AuxiliaryLanguage.withOrder U}
    {B : RelStructure AuxiliaryLanguage.withOrder V}
    {C : RelStructure AuxiliaryLanguage.withOrder W}
    (e : Embedding A B) (f : Embedding B C) :
    nameEmbedding (f.comp e) =
      (nameEmbedding f).comp (nameEmbedding e) := by
  apply Embedding.ext
  intro x
  rfl

/-- The entire Ramsey arrow, not only the existence of one embedded
copy, is invariant under this exact symbol renaming. -/
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
          apply Embedding.ext
          intro x
          rfl
    _ = χ (nameEmbedding (b.comp (unnameEmbedding e₂))) :=
          hMono (unnameEmbedding e₁) (unnameEmbedding e₂)
    _ = χ ((nameEmbedding b).comp e₂) := by
          congr 1
          apply Embedding.ext
          intro x
          rfl

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
