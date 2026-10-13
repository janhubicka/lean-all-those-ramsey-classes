import AllThoseRamseyClasses.Published.ProfileRootTagClosedness2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Local tag laws and their transfer from closed B-copy coverage

Both normality and original root validity are inherited by full
substructures. In a lifted-closed Picture, the support of any true tuple
has an actual closed irreducible hull and therefore embeds into the
original tagged Base by the stated coverage. This supplies BOTH local
laws, rather than incorrectly assuming that lifted closedness alone
forces original closedness.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w z
variable {L : RelLanguage.{u}}

/-- Root matching preserves full embeddings, with the displayed tuple
and its original designated coordinates unchanged. -/
theorem rootMatches2019_map_embedding
    (r : ClosureRule L) {X : Type w} {Y : Type z}
    {E : RelStructure L X} {F : RelStructure L Y}
    (f : Embedding E F) (t : Fin (L.arity r.symbol) → X)
    (h : r.RootMatches E t) : r.RootMatches F (f ∘ t) := by
  obtain ⟨e, he⟩ := h
  exact ⟨f.comp e, fun i => congrArg f (he i)⟩

/-- Root matching reflects full embeddings without a closedness
hypothesis. The root prefix itself explicitly gives the inverse map. -/
theorem rootMatches2019_reflect_embedding
    (r : ClosureRule L) {X : Type w} {Y : Type z}
    {E : RelStructure L X} {F : RelStructure L Y}
    (f : Embedding E F) (t : Fin (L.arity r.symbol) → X)
    (h : r.RootMatches F (f ∘ t)) : r.RootMatches E t := by
  obtain ⟨e, he⟩ := h
  let q : Fin r.rootSize → X := fun i => t (i.castLE r.rootLE)
  have hEq : ∀ i, f (q i) = e i := he
  let a : Embedding r.root E := {
    toFun := q
    injective := by
      intro i j hij
      apply e.injective
      exact (hEq i).symm.trans ((congrArg f hij).trans (hEq j))
    map_rel_iff := by
      intro R xs
      have hFun : f ∘ (q ∘ xs) = e ∘ xs := by
        funext i
        exact hEq (xs i)
      calc
        E.rel R (q ∘ xs) ↔ F.rel R (f ∘ (q ∘ xs)) := (f.map_rel_iff R (q ∘ xs)).symm
        _ ↔ F.rel R (e ∘ xs) := by rw [hFun]
        _ ↔ r.root.rel R xs := e.map_rel_iff R xs
  }
  exact ⟨a, fun _ => rfl⟩

/-- Normality is inherited by every full induced substructure. -/
theorem profileTag2019_normal_of_embedding
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    {E : RelStructure (profileRootTagLanguage2019 rules Base) X}
    {F : RelStructure (profileRootTagLanguage2019 rules Base) Y}
    (f : Embedding E F) (hF : ProfileTagNormal2019 Base F) :
    ProfileTagNormal2019 Base E := by
  intro p xs
  calc
    E.rel (.inr p) xs ↔ F.rel (.inr p) (f ∘ xs) := (f.map_rel_iff (.inr p) xs).symm
    _ ↔ (profileRootTagExpansion2019 rules Base (profileRootTagReduct2019 Base F)).rel
          (.inr p) (f ∘ xs) := hF p (f ∘ xs)
    _ ↔ (profileRootTagExpansion2019 rules Base (profileRootTagReduct2019 Base E)).rel
          (.inr p) xs :=
      (profileRootTagEmbedding2019 Base (profileRootTagReductEmbedding2019 Base f)).map_rel_iff (.inr p) xs

/-- Original root validity is also inherited by full substructures. -/
theorem profileTag2019_old_valid_of_embedding
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    {E : RelStructure (profileRootTagLanguage2019 rules Base) X}
    {F : RelStructure (profileRootTagLanguage2019 rules Base) Y}
    (f : Embedding E F) (hF : ProfileTagOldRootValid2019 Base F) :
    ProfileTagOldRootValid2019 Base E := by
  intro r hr t ht
  let fo := profileRootTagOriginalEmbedding2019 Base f
  exact rootMatches2019_reflect_embedding r fo t
    (hF r hr (fo ∘ t) ((fo.map_rel_iff r.symbol t).mpr ht))

/-- Forgetting the auxiliary symbols preserves a genuine free diagram. -/
theorem profileTag2019_original_free
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {H A B X : Type w}
    {Root : RelStructure (profileRootTagLanguage2019 rules Base) H}
    {Left : RelStructure (profileRootTagLanguage2019 rules Base) A}
    {Right : RelStructure (profileRootTagLanguage2019 rules Base) B}
    {Whole : RelStructure (profileRootTagLanguage2019 rules Base) X}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam (profileRootTagOriginalEmbedding2019 Base sL)
      (profileRootTagOriginalEmbedding2019 Base sR)
      (profileRootTagOriginalEmbedding2019 Base iL)
      (profileRootTagOriginalEmbedding2019 Base iR) := by
  exact ⟨hFree.covers, hFree.overlap, fun R xs => hFree.rel_iff (.inl (.inl R)) xs⟩

/-- Original U-irreducibility passes to a tagged structure satisfying
both local laws. Each hypothetical closed tagged free side would have
a genuinely closed original reduct, contradicting original irreducibility. -/
theorem profileTag2019_uIrreducible_of_original
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hNormal : ProfileTagNormal2019 Base E)
    (hValid : ProfileTagOldRootValid2019 Base E)
    (hIrred : IsUIrreducible rules (profileRootTagOriginal2019 Base E)) :
    IsUIrreducible (profileRootTagRules2019 rules Base) E := by
  intro H A B Root Left Right sL sR iL iR hL hR hFree
  have hLeftOld : IsUClosed rules (profileRootTagOriginal2019 Base Left) :=
    profileRootTag2019_original_closed_of_tagged Base Left hL
      (profileTag2019_normal_of_embedding Base iL hNormal)
      (profileTag2019_old_valid_of_embedding Base iL hValid)
  have hRightOld : IsUClosed rules (profileRootTagOriginal2019 Base Right) :=
    profileRootTag2019_original_closed_of_tagged Base Right hR
      (profileTag2019_normal_of_embedding Base iR hNormal)
      (profileTag2019_old_valid_of_embedding Base iR hValid)
  exact hIrred hLeftOld hRightOld (profileTag2019_original_free Base hFree)

/-- A lifted-closed Picture whose closed irreducibles embed into a
normal, old-root-valid tagged Base inherits BOTH local laws. All source
tuple supports are tested exactly before taking the safe ambient hull. -/
theorem profileTag2019_local_laws_of_closed_coverage
    {rules : ClosureDescription L} {UB X Y : Type v}
    (Base : RelStructure L UB)
    (C : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (Target : RelStructure (profileRootTagLanguage2019 rules Base) Y)
    (hC : IsUClosed (profileRootTagRules2019 rules Base) C)
    (hTargetNormal : ProfileTagNormal2019 Base Target)
    (hTargetValid : ProfileTagOldRootValid2019 Base Target)
    (hCover : ∀ {Z : Type v} (Test : RelStructure (profileRootTagLanguage2019 rules Base) Z),
      IsUClosed (profileRootTagRules2019 rules Base) Test →
      IsUIrreducible (profileRootTagRules2019 rules Base) Test →
      Embedding Test C → Nonempty (Embedding Test Target)) :
    ProfileTagNormal2019 Base C ∧ ProfileTagOldRootValid2019 Base C := by
  have hLocal : ∀ S : Set X, (C.induce S).Irreducible →
      ProfileTagNormal2019 Base (C.induce S) ∧ ProfileTagOldRootValid2019 Base (C.induce S) := by
    intro S hS
    obtain ⟨e⟩ := weak_irreducible_embeds_base_of_closed_coverage hC hCover S hS
    exact ⟨profileTag2019_normal_of_embedding Base e hTargetNormal,
      profileTag2019_old_valid_of_embedding Base e hTargetValid⟩
  constructor
  · intro p t
    let S : Set X := Set.range t
    let ts : Fin (L.arity p.originalRule.symbol) → S := fun i => ⟨t i, ⟨i, rfl⟩⟩
    let inc := profileRootTagReductEmbedding2019 Base (inclusion C S)
    let incTag := profileRootTagEmbedding2019 Base inc
    constructor
    · intro ht
      have hSIrred : (C.induce S).Irreducible := relationTuple_range_irreducible C (.inr p) t ht
      have hCanon := ((hLocal S hSIrred).1 p ts).mp ht
      exact (incTag.map_rel_iff (.inr p) ts).mpr hCanon
    · intro ht
      have hOld : C.rel (.inl (.inl p.originalRule.symbol)) t := ht.1
      have hSIrred : (C.induce S).Irreducible :=
        relationTuple_range_irreducible C (.inl (.inl p.originalRule.symbol)) t hOld
      have hCanon := (incTag.map_rel_iff (.inr p) ts).mp ht
      exact ((hLocal S hSIrred).1 p ts).mpr hCanon
  · intro r hr t ht
    let S : Set X := Set.range t
    let ts : Fin (L.arity r.symbol) → S := fun i => ⟨t i, ⟨i, rfl⟩⟩
    have hSIrred : (C.induce S).Irreducible :=
      relationTuple_range_irreducible C (.inl (.inl r.symbol)) t ht
    have hRoot := (hLocal S hSIrred).2 r hr ts ht
    exact rootMatches2019_map_embedding r
      (profileRootTagOriginalEmbedding2019 Base (inclusion C S)) ts hRoot

end AllThoseRamseyClasses.Published
