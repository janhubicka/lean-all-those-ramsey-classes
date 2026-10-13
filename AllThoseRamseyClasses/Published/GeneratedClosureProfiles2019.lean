import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureUSize2019
import PartiteConstruction.Ramsey.ClosureWeakHullUSize
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer

/-!
# Generated-closure records for compatible weak overlaps

A profile records an actual closed induced substructure of a fixed Base
and a tuple generating it. In an arbitrary relational structure C, its
profile relation holds exactly on tuples extended by a FULL embedding
of that recorded closed structure into C.

Full embeddings between U-CLOSED structures preserve AND reflect all
these records. Reflection is not an assumed extension of a weak map:
the target realization of the generated closed structure is forced into
the relatively closed image of the source, because all its generators
are there. A full factorization then supplies the source realization.

This is the first construction component of an alternative profile /
relational-sparsening approach to corrected Theorem 2.18. It does not yet
prove that the resulting sparse structures can be made closed, nor the
unrestricted theorem. The profile language here permits all tuple
lengths; no finiteness of its set of symbols is claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A genuinely generated closed structure recorded inside a fixed Base.
The original root carrier is not identified with its larger closure. -/
structure GeneratedClosureProfile2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) where
  carrier : Set UB
  closed : IsUClosed rules (Base.induce carrier)
  arity : ℕ
  generators : Fin arity → carrier
  generating : IsUGenerating rules (Base.induce carrier) (Set.range generators)

/-- Add one relation symbol for each generated-closure record, retaining
all original symbols and their arities, including nullary symbols. -/
def closureProfileLanguage2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) :
    RelLanguage.{max u v} where
  Symbol := L.Symbol ⊕ GeneratedClosureProfile2019 rules Base
  arity
    | .inl R => L.arity R
    | .inr p => p.arity

/-- Canonical profile expansion. The witness is a full induced embedding
of the prescribed generated structure, not just a positive map. -/
def closureProfileExpansion2019
    (rules : ClosureDescription L) {UB X : Type v}
    (Base : RelStructure L UB) (C : RelStructure L X) :
    RelStructure (closureProfileLanguage2019 rules Base) X where
  rel
    | .inl R, xs => C.rel R xs
    | .inr p, xs =>
        ∃ e : Embedding (Base.induce p.carrier) C,
          ∀ i : Fin p.arity, e (p.generators i) = xs i

/-- If the generators of a realized structure lie in a closed embedded
range, its entire realization lies in that same range. -/
theorem generated2019_realization_in_closed_range
    {rules : ClosureDescription L} {H X Y : Type v}
    (Root : RelStructure L H) (C : RelStructure L X) (D : RelStructure L Y)
    (G : Set H) (hGen : IsUGenerating rules Root G)
    (f : Embedding C D) (hC : IsUClosed rules C) (hD : IsUClosed rules D)
    (e : Embedding Root D)
    (hSeed : ∀ x, x ∈ G → e x ∈ Set.range f) :
    ∀ x, e x ∈ Set.range f := by
  have hRange : IsUSubstructure rules D (Set.range f) :=
    f.range_isUSubstructure hC hD
  have hPre : IsUSubstructure rules Root (e ⁻¹' Set.range f) :=
    hRange.preimage_embedding e
  have hAll : UClosureHull rules Root G ⊆ e ⁻¹' Set.range f :=
    UClosureHull_minimal rules Root hPre hSeed
  change UClosureHull rules Root G = Set.univ at hGen
  rw [hGen] at hAll
  intro x
  exact hAll (Set.mem_univ x)

/-- Full embeddings of closed structures lift to full profile embeddings.
The reflection clause is proved by generated-range containment. -/
def closureProfileEmbedding2019
    {rules : ClosureDescription L} {UB X Y : Type v}
    (Base : RelStructure L UB) {C : RelStructure L X} {D : RelStructure L Y}
    (f : Embedding C D) (hC : IsUClosed rules C) (hD : IsUClosed rules D) :
    Embedding (closureProfileExpansion2019 rules Base C)
      (closureProfileExpansion2019 rules Base D) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    classical
    intro R xs
    cases R with
    | inl R => exact f.map_rel_iff R xs
    | inr p =>
      constructor
      · rintro ⟨e, he⟩
        have hAll : ∀ x : p.carrier, e x ∈ Set.range f :=
          generated2019_realization_in_closed_range
            (Base.induce p.carrier) C D (Set.range p.generators) p.generating
            f hC hD e (by
              rintro x ⟨i, rfl⟩
              exact ⟨xs i, (he i).symm⟩)
        have hFactor : ∀ x : p.carrier, ∃ y : X, e x = f y := by
          intro x
          obtain ⟨y, hy⟩ := hAll x
          exact ⟨y, hy.symm⟩
        let q : Embedding (Base.induce p.carrier) C :=
          e.factorThroughRange f hFactor
        have hq : ∀ x : p.carrier, e x = f (q x) :=
          fun x => Classical.choose_spec (hFactor x)
        refine ⟨q, ?_⟩
        intro i
        apply f.injective
        exact (hq (p.generators i)).symm.trans (he i)
      · rintro ⟨e, he⟩
        exact ⟨f.comp e, fun i => congrArg f (he i)⟩

/-- Every embedding of canonical profile expansions forgets to a full
embedding of the original relational structures. -/
def closureProfileForgetEmbedding2019
    {rules : ClosureDescription L} {UB X Y : Type v}
    (Base : RelStructure L UB) {C : RelStructure L X} {D : RelStructure L Y}
    (f : Embedding (closureProfileExpansion2019 rules Base C)
      (closureProfileExpansion2019 rules Base D)) : Embedding C D where
  toFun := f
  injective := f.injective
  map_rel_iff := fun R xs => f.map_rel_iff (.inl R) xs

/-- Ordinary irreducibility survives profile expansion because the
original tuple witnessing adjacency is retained. -/
theorem closureProfile2019_irreducible
    (rules : ClosureDescription L) {UB X : Type v}
    (Base : RelStructure L UB) (C : RelStructure L X) (hC : C.Irreducible) :
    (closureProfileExpansion2019 rules Base C).Irreducible := by
  intro x y hxy
  obtain ⟨R, z, i, j, hz, hi, hj⟩ := hC hxy
  exact ⟨.inl R, z, i, j, hz, hi, hj⟩

/-- The canonical expansion preserves an existing Ramsey arrow between
closed inputs and closed control. No additional Ramsey theorem for
profiled classes is assumed. -/
theorem closureProfile2019_arrow
    {rules : ClosureDescription L} {UB X Y Z : Type v}
    (Base : RelStructure L UB)
    (A : RelStructure L X) (B : RelStructure L Y) (C : RelStructure L Z)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B) (hC : IsUClosed rules C)
    (κ : Type*) (hArrow : StructuralRamsey.Arrow A B C κ) :
    StructuralRamsey.Arrow (closureProfileExpansion2019 rules Base A)
      (closureProfileExpansion2019 rules Base B)
      (closureProfileExpansion2019 rules Base C) κ := by
  intro colour
  obtain ⟨b, hb⟩ := hArrow
    (fun a => colour (closureProfileEmbedding2019 Base a hA hC))
  let bPlus := closureProfileEmbedding2019 Base b hB hC
  have hComp : ∀ a : Embedding (closureProfileExpansion2019 rules Base A)
      (closureProfileExpansion2019 rules Base B),
      bPlus.comp a = closureProfileEmbedding2019 Base
        (b.comp (closureProfileForgetEmbedding2019 Base a)) hA hC := by
    intro a
    apply Embedding.ext
    intro x
    rfl
  refine ⟨bPlus, ?_⟩
  intro a1 a2
  rw [hComp a1, hComp a2]
  exact hb (closureProfileForgetEmbedding2019 Base a1)
    (closureProfileForgetEmbedding2019 Base a2)

/-- Agreement of the full induced profile structures on a weak common
carrier transports a prescribed closed boundary realization. The weak
common carrier itself need not be closed or irreducible. -/
theorem closureProfile2019_transport_boundary_record
    {rules : ClosureDescription L} {UB X Y Z : Type v}
    (Base : RelStructure L UB)
    (Common : RelStructure (closureProfileLanguage2019 rules Base) X)
    (Left : RelStructure L Y) (Right : RelStructure L Z)
    (sL : Embedding Common (closureProfileExpansion2019 rules Base Left))
    (sR : Embedding Common (closureProfileExpansion2019 rules Base Right))
    (p : GeneratedClosureProfile2019 rules Base)
    (g : Fin p.arity → X)
    (aL : Embedding (Base.induce p.carrier) Left)
    (hLeft : ∀ i, aL (p.generators i) = sL (g i)) :
    ∃ aR : Embedding (Base.induce p.carrier) Right,
      ∀ i, aR (p.generators i) = sR (g i) := by
  have hCommon : Common.rel (.inr p) g :=
    (sL.map_rel_iff (.inr p) g).mp ⟨aL, hLeft⟩
  exact (sR.map_rel_iff (.inr p) g).mpr hCommon

end AllThoseRamseyClasses.Published
