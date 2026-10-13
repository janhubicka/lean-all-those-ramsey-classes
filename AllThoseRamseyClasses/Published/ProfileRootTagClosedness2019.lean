import AllThoseRamseyClasses.Published.ProfileRootTagLanguage2019

/-!
# Closedness transport through the fresh profile-root tags

Forward: original closedness gives closedness of the canonical tagged
expansion. Reverse: an arbitrary tagged-closed structure has a closed
original reduct when BOTH tag normality and original root validity hold.
The reverse proof chooses the actual full profile pattern on each old
embedded root; all compatible patterns occur among the fresh symbols.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w z
variable {L : RelLanguage.{u}}

/-- Original U-closedness implies lifted closedness of the canonical
fresh-tag expansion, for an arbitrary profile structure. -/
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
    let ep : Embedding p.pattern E := profileRootTagReductEmbedding2019 Base e
    let eo : Embedding p.originalRule.root (profileReduct2019 Base E) :=
      profileRootPatternOriginalEmbedding2019 p E ep
    obtain ⟨t, ht, hUnique⟩ := (hOld p.originalRule p.mem_rule).2 eo
    refine ⟨t, ⟨⟨ht.1, ep, ht.2⟩, ht.2⟩, ?_⟩
    intro s hs
    exact hUnique s ⟨hs.1.1, hs.2⟩

/-- Canonical tags satisfy normality literally. -/
theorem profileRootTag2019_canonical_normal
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X) :
    ProfileTagNormal2019 Base (profileRootTagExpansion2019 rules Base E) := by
  intro p t
  exact Iff.rfl

/-- Valid original roots in canonical tags are supplied by ORIGINAL
closedness, not inferred from the new tags alone. -/
theorem profileRootTag2019_canonical_old_valid
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (hOld : IsUClosed rules (profileReduct2019 Base E)) :
    ProfileTagOldRootValid2019 Base (profileRootTagExpansion2019 rules Base E) := by
  intro r hr t ht
  exact (hOld r hr).1 t ht

/-- An arbitrary normal tagged structure with original closed reduct
is lifted-closed, by the full identity with its canonical tagging. -/
theorem profileRootTag2019_closed_of_original
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hNormal : ProfileTagNormal2019 Base E)
    (hOld : IsUClosed rules (profileRootTagOriginal2019 Base E)) :
    IsUClosed (profileRootTagRules2019 rules Base) E := by
  exact isUClosed_of_surjective_embedding
    (profileTagNormalIdentity2019 Base E hNormal) (fun x => ⟨x, rfl⟩)
    (profileRootTag2019_closed_canonical Base (profileRootTagReduct2019 Base E) hOld)

/-- Reverse closedness transport. The ACTUAL profile pattern induced
by each old root selects its fresh closure symbol. Normality identifies
all old closure tuples over this root with that same symbol, giving
existence and uniqueness. Original root validity is a separate premise. -/
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
    let et : Embedding (profileRootTagExpansion2019 rules Base p.pattern) E :=
      (profileTagNormalIdentity2019 Base E hNormal).comp (profileRootTagEmbedding2019 Base ep)
    obtain ⟨t, ht, hUnique⟩ :=
      (hTag (profileRootTagRule2019 p) ⟨p, rfl⟩).2 et
    have hOldTuple : (profileRootTagOriginal2019 Base E).rel r.symbol t :=
      ((hNormal p t).mp ht.1).1
    refine ⟨t, ⟨hOldTuple, ht.2⟩, ?_⟩
    intro s hs
    have hTagTuple : E.rel (.inr p) s :=
      (hNormal p s).mpr ⟨hs.1, ep, hs.2⟩
    exact hUnique s ⟨hTagTuple, hs.2⟩

/-- Exact equivalence of original and lifted closedness on a tagged
structure satisfying the two necessary local laws. -/
theorem profileRootTag2019_closed_iff_original
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hNormal : ProfileTagNormal2019 Base E)
    (hValid : ProfileTagOldRootValid2019 Base E) :
    IsUClosed (profileRootTagRules2019 rules Base) E ↔
      IsUClosed rules (profileRootTagOriginal2019 Base E) :=
  ⟨fun h => profileRootTag2019_original_closed_of_tagged Base E h hNormal hValid,
    fun h => profileRootTag2019_closed_of_original Base E hNormal h⟩

end AllThoseRamseyClasses.Published
