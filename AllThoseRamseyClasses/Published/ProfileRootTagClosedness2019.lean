import AllThoseRamseyClasses.Published.ProfileRootTagLanguage2019

/-!
# Closedness transport through fresh profile-root tags

Original closedness gives lifted closedness of canonical tagging.
The reverse direction uses BOTH tag normality and original root
validity. For every original embedded root the proof chooses its
actual full profile pattern and its distinct fresh closure symbol.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w z
variable {L : RelLanguage.{u}}

/-- Original closedness gives lifted closedness of canonical tagging.
All full root embeddings are transported explicitly through reducts. -/
theorem profileRootTag2019_closed_canonical
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (hOld : IsUClosed rules (profileReduct2019 Base E)) :
    IsUClosed (profileRootTagRules2019 rules Base) (profileRootTagExpansion2019 rules Base E) := by
  intro rule hRule
  obtain ⟨p, rfl⟩ := hRule
  constructor
  · intro t ht
    obtain ⟨e, he⟩ := ht.2
    exact ⟨profileRootTagEmbedding2019 Base e, he⟩
  · intro e
    let ep : Embedding p.pattern E := {
      toFun := e
      injective := e.injective
      map_rel_iff := fun R xs => e.map_rel_iff (.inl R) xs
    }
    let eo : Embedding p.originalRule.root (profileReduct2019 Base E) :=
      profileRootPatternOriginalEmbedding2019 p E ep
    obtain ⟨t, ht, hUnique⟩ := (hOld p.originalRule p.mem_rule).2 eo
    refine ⟨t, ⟨⟨ht.1, ep, ht.2⟩, ht.2⟩, ?_⟩
    intro s hs
    exact hUnique s ⟨hs.1.1, hs.2⟩

/-- Canonical tagging is normal. The full root-pattern witnesses are
transported rather than relying on structure eta conversion. -/
theorem profileRootTag2019_canonical_normal
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X) :
    ProfileTagNormal2019 Base (profileRootTagExpansion2019 rules Base E) := by
  intro p t
  let E0 := profileRootTagReduct2019 Base (profileRootTagExpansion2019 rules Base E)
  constructor
  · rintro ⟨ht, e, he⟩
    let e0 : Embedding p.pattern E0 := {
      toFun := e
      injective := e.injective
      map_rel_iff := fun R xs => e.map_rel_iff R xs
    }
    exact ⟨ht, e0, he⟩
  · rintro ⟨ht, e, he⟩
    let e0 : Embedding p.pattern E := {
      toFun := e
      injective := e.injective
      map_rel_iff := fun R xs => e.map_rel_iff R xs
    }
    exact ⟨ht, e0, he⟩

/-- Old root validity comes from ORIGINAL closedness, independently
of the new tag relations. -/
theorem profileRootTag2019_canonical_old_valid
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (hOld : IsUClosed rules (profileReduct2019 Base E)) :
    ProfileTagOldRootValid2019 Base (profileRootTagExpansion2019 rules Base E) := by
  intro r hr t ht
  obtain ⟨e, he⟩ := (hOld r hr).1 t ht
  let e0 : Embedding r.root
      (profileRootTagOriginal2019 Base (profileRootTagExpansion2019 rules Base E)) := {
    toFun := e
    injective := e.injective
    map_rel_iff := fun R xs => e.map_rel_iff R xs
  }
  exact ⟨e0, he⟩

/-- A normal tagged structure with closed original reduct is
lifted-closed by its full identity with canonical tagging. -/
theorem profileRootTag2019_closed_of_original
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hNormal : ProfileTagNormal2019 Base E)
    (hOld : IsUClosed rules (profileRootTagOriginal2019 Base E)) :
    IsUClosed (profileRootTagRules2019 rules Base) E := by
  exact isUClosed_of_surjective_embedding
    (profileTagNormalIdentity2019 Base E hNormal) (fun x => ⟨x, rfl⟩)
    (profileRootTag2019_closed_canonical Base (profileRootTagReduct2019 Base E) hOld)

/-- For each original root, choose its ACTUAL full expanded pattern.
Lifted existence supplies an old closure tuple; normality tags all
other old tuples over this root alike, so lifted uniqueness applies.
This proof uses no substructure closedness lemma or root-completion oracle. -/
theorem profileRootTag2019_original_closed_of_tagged
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hTag : IsUClosed (profileRootTagRules2019 rules Base) E)
    (hNormal : ProfileTagNormal2019 Base E)
    (hValid : ProfileTagOldRootValid2019 Base E) :
    IsUClosed rules (profileRootTagOriginal2019 Base E) := by
  intro r hr
  constructor
  · exact hValid r hr
  · intro e
    let pat : RelStructure (closureProfileLanguage2019 rules Base) (Fin r.rootSize) := {
      rel := fun R xs => (profileRootTagReduct2019 Base E).rel R (e ∘ xs)
    }
    let p : ProfileRootPattern2019 rules Base := {
      originalRule := r
      mem_rule := hr
      pattern := pat
      reductCorrect := fun R xs => e.map_rel_iff R xs
    }
    let ep : Embedding p.pattern (profileRootTagReduct2019 Base E) := {
      toFun := e
      injective := e.injective
      map_rel_iff := fun _ _ => Iff.rfl
    }
    let et : Embedding (profileRootTagRule2019 p).root E :=
      (profileTagNormalIdentity2019 Base E hNormal).comp (profileRootTagEmbedding2019 Base ep)
    have hRule : (profileRootTagRule2019 p).IsClosed E :=
      hTag (profileRootTagRule2019 p) ⟨p, rfl⟩
    obtain ⟨t, ht, hUnique⟩ := hRule.2 et
    have hOldTuple : (profileRootTagOriginal2019 Base E).rel r.symbol t :=
      ((hNormal p t).mp ht.1).1
    refine ⟨t, ⟨hOldTuple, ?_⟩, ?_⟩
    · intro i
      exact ht.2 i
    · intro s hs
      have hTagTuple : E.rel (.inr p) s :=
        (hNormal p s).mpr ⟨hs.1, ep, hs.2⟩
      exact hUnique s ⟨hTagTuple, hs.2⟩

/-- Exact closedness equivalence under the two necessary local laws. -/
theorem profileRootTag2019_closed_iff_original
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hNormal : ProfileTagNormal2019 Base E)
    (hValid : ProfileTagOldRootValid2019 Base E) :
    IsUClosed (profileRootTagRules2019 rules Base) E ↔
      IsUClosed rules (profileRootTagOriginal2019 Base E) := by
  constructor
  · intro h
    exact profileRootTag2019_original_closed_of_tagged Base E h hNormal hValid
  · intro h
    exact profileRootTag2019_closed_of_original Base E hNormal h

end AllThoseRamseyClasses.Published
