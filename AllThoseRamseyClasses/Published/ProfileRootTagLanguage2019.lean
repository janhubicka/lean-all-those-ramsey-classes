import AllThoseRamseyClasses.Published.GeneratedClosureProfiles2019

/-!
# Fresh relational closure symbols for complete profile root patterns

An original closure relation cannot be reused for incompatible expanded
root descriptions. Here each original rule and compatible FULL profile
root pattern gets its OWN symbol. The canonical tag is exactly the old
closure tuple together with a full embedding of its displayed prefix
pattern. This is local to the original tuple and preserves/reflects full
embeddings without any source closedness assumption.

The root pattern carrier is Fin k; ambient carriers have independent
universes. No assertion of original closedness follows from bare tagged
closedness: normality and original root validity are separate laws.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w z
variable {L : RelLanguage.{u}}

/-- Forget profile relations from any, not necessarily canonical, expansion. -/
def profileReduct2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X) :
    RelStructure L X where
  rel R xs := E.rel (.inl R) xs

/-- Full embeddings remain full after forgetting the profile symbols. -/
def profileReductEmbedding2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    {E : RelStructure (closureProfileLanguage2019 rules Base) X}
    {F : RelStructure (closureProfileLanguage2019 rules Base) Y}
    (f : Embedding E F) :
    Embedding (profileReduct2019 Base E) (profileReduct2019 Base F) where
  toFun := f
  injective := f.injective
  map_rel_iff := fun R xs => f.map_rel_iff (.inl R) xs

/-- One original rule together with a FULL expanded root pattern whose
old reduct is exactly the prescribed original root. All such patterns
are allowed; no unproved finite list of realized patterns is used. -/
structure ProfileRootPattern2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) where
  originalRule : ClosureRule L
  mem_rule : originalRule ∈ rules
  pattern : RelStructure (closureProfileLanguage2019 rules Base) (Fin originalRule.rootSize)
  reductCorrect : ∀ R xs, pattern.rel (.inl R) xs ↔ originalRule.root.rel R xs

/-- Each compatible expanded root pattern has a distinct new symbol. -/
def profileRootTagLanguage2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) :
    RelLanguage.{max u v} where
  Symbol := (closureProfileLanguage2019 rules Base).Symbol ⊕ ProfileRootPattern2019 rules Base
  arity
    | .inl R => (closureProfileLanguage2019 rules Base).arity R
    | .inr p => L.arity p.originalRule.symbol

/-- The displayed prefix is the image of a full embedding of the exact
profile root pattern, with the original ordered root coordinates. -/
def profileRootPatternMatches2019
    {rules : ClosureDescription L} {UB : Type v} {Base : RelStructure L UB}
    (p : ProfileRootPattern2019 rules Base)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (t : Fin (L.arity p.originalRule.symbol) → X) : Prop :=
  ∃ e : Embedding p.pattern E,
    ∀ i : Fin p.originalRule.rootSize, t (i.castLE p.originalRule.rootLE) = e i

/-- Canonical fresh-tag expansion of an arbitrary profile structure. -/
def profileRootTagExpansion2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X) :
    RelStructure (profileRootTagLanguage2019 rules Base) X where
  rel
    | .inl R, xs => E.rel R xs
    | .inr p, xs =>
        E.rel (.inl p.originalRule.symbol) xs ∧ profileRootPatternMatches2019 p E xs

/-- Forget only the fresh closure tags, retaining the profile language. -/
def profileRootTagReduct2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X) :
    RelStructure (closureProfileLanguage2019 rules Base) X where
  rel R xs := E.rel (.inl R) xs

/-- The original-language reduct after forgetting both auxiliary layers. -/
def profileRootTagOriginal2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X) :
    RelStructure L X := profileReduct2019 Base (profileRootTagReduct2019 Base E)

/-- Full embedding on the profile reduct. -/
def profileRootTagReductEmbedding2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    {E : RelStructure (profileRootTagLanguage2019 rules Base) X}
    {F : RelStructure (profileRootTagLanguage2019 rules Base) Y}
    (f : Embedding E F) :
    Embedding (profileRootTagReduct2019 Base E) (profileRootTagReduct2019 Base F) where
  toFun := f
  injective := f.injective
  map_rel_iff := fun R xs => f.map_rel_iff (.inl R) xs

/-- Full embedding on the original reduct. -/
def profileRootTagOriginalEmbedding2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    {E : RelStructure (profileRootTagLanguage2019 rules Base) X}
    {F : RelStructure (profileRootTagLanguage2019 rules Base) Y}
    (f : Embedding E F) :
    Embedding (profileRootTagOriginal2019 Base E) (profileRootTagOriginal2019 Base F) :=
  profileReductEmbedding2019 Base (profileRootTagReductEmbedding2019 Base f)

/-- Fresh tagging preserves and reflects FULL relational embeddings,
including those between weak/nonclosed profile structures. -/
def profileRootTagEmbedding2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    {E : RelStructure (closureProfileLanguage2019 rules Base) X}
    {F : RelStructure (closureProfileLanguage2019 rules Base) Y}
    (f : Embedding E F) :
    Embedding (profileRootTagExpansion2019 rules Base E)
      (profileRootTagExpansion2019 rules Base F) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    classical
    intro R xs
    cases R with
    | inl R => exact f.map_rel_iff R xs
    | inr p =>
      constructor
      · rintro ⟨hOld, e, he⟩
        have hFactor : ∀ i : Fin p.originalRule.rootSize,
            ∃ x : X, e i = f x := by
          intro i
          exact ⟨xs (i.castLE p.originalRule.rootLE), (he i).symm⟩
        let q : Embedding p.pattern E := e.factorThroughRange f hFactor
        have hq : ∀ i, e i = f (q i) :=
          fun i => Classical.choose_spec (hFactor i)
        refine ⟨(f.map_rel_iff (.inl p.originalRule.symbol) xs).mp hOld, q, ?_⟩
        intro i
        exact f.injective ((he i).trans (hq i))
      · rintro ⟨hOld, e, he⟩
        exact ⟨(f.map_rel_iff (.inl p.originalRule.symbol) xs).mpr hOld,
          f.comp e, fun i => congrArg f (he i)⟩

/-- A profile-pattern embedding is a full original root embedding after
forgetting profiles and using the specified exact root reduct. -/
def profileRootPatternOriginalEmbedding2019
    {rules : ClosureDescription L} {UB : Type v} {Base : RelStructure L UB}
    (p : ProfileRootPattern2019 rules Base)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (e : Embedding p.pattern E) :
    Embedding p.originalRule.root (profileReduct2019 Base E) where
  toFun := e
  injective := e.injective
  map_rel_iff := fun R xs => (e.map_rel_iff (.inl R) xs).trans (p.reductCorrect R xs)

/-- The lifted closure rule has the complete tagged root pattern and
its own fresh relation symbol. Root positivity/properness are unchanged. -/
def profileRootTagRule2019
    {rules : ClosureDescription L} {UB : Type v} {Base : RelStructure L UB}
    (p : ProfileRootPattern2019 rules Base) :
    ClosureRule (profileRootTagLanguage2019 rules Base) where
  symbol := .inr p
  rootSize := p.originalRule.rootSize
  rootPositive := p.originalRule.rootPositive
  rootStrict := p.originalRule.rootStrict
  root := profileRootTagExpansion2019 rules Base p.pattern
  rootIrreducible := by
    intro x y hxy
    obtain ⟨R, zs, i, j, hz, hi, hj⟩ := p.originalRule.rootIrreducible hxy
    exact ⟨.inl (.inl R), zs, i, j, (p.reductCorrect R zs).mpr hz, hi, hj⟩

/-- The lifted closure description contains exactly the fresh rules. -/
def profileRootTagRules2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) :
    ClosureDescription (profileRootTagLanguage2019 rules Base) :=
  Set.range (fun p : ProfileRootPattern2019 rules Base => profileRootTagRule2019 p)

/-- Normality of all tags on an arbitrary tagged structure. -/
def ProfileTagNormal2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X) : Prop :=
  ∀ (p : ProfileRootPattern2019 rules Base) (xs : Fin (L.arity p.originalRule.symbol) → X),
    E.rel (.inr p) xs ↔
      (profileRootTagExpansion2019 rules Base (profileRootTagReduct2019 Base E)).rel (.inr p) xs

/-- Old closure tuples also need valid ORIGINAL roots. Bare tag
closedness or normality does not supply this condition. -/
def ProfileTagOldRootValid2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X) : Prop :=
  ∀ (r : ClosureRule L), r ∈ rules → ∀ t : Fin (L.arity r.symbol) → X,
    (profileRootTagOriginal2019 Base E).rel r.symbol t →
      r.RootMatches (profileRootTagOriginal2019 Base E) t

/-- A normal tagged structure is fully isomorphic, by identity, to the
canonical tagging of its profile reduct. -/
def profileTagNormalIdentity2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hNormal : ProfileTagNormal2019 Base E) :
    Embedding (profileRootTagExpansion2019 rules Base (profileRootTagReduct2019 Base E)) E where
  toFun := fun x => x
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R => exact Iff.rfl
    | inr p => exact hNormal p xs

end AllThoseRamseyClasses.Published
