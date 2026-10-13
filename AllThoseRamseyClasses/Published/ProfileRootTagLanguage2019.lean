import AllThoseRamseyClasses.Published.GeneratedClosureProfiles2019

/-!
# Fresh relational closure symbols for complete profile root patterns

Each original rule and compatible FULL expanded root pattern gets its
OWN closure symbol. Its canonical tag means an old closure tuple whose
prefix fully embeds that exact pattern. This is local to the displayed
tuple and preserves/reflects full embeddings of weak structures.

Root carriers are Fin k while ambient carriers have independent
universes. Bare tagged closedness is not asserted to imply original
closedness: tag normality and original root validity are separate laws.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w z
variable {L : RelLanguage.{u}}

/-- Forget profiles from any, not necessarily canonical, expansion. -/
def profileReduct2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X) :
    RelStructure L X where
  rel R xs := E.rel (.inl R) xs

/-- Full embeddings remain full after forgetting profile symbols. -/
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

/-- An original rule and a full profile root pattern with exactly its
prescribed original reduct. All compatible patterns are allowed. -/
structure ProfileRootPattern2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) where
  originalRule : ClosureRule L
  mem_rule : originalRule ∈ rules
  pattern : RelStructure (closureProfileLanguage2019 rules Base) (Fin originalRule.rootSize)
  reductCorrect : ∀ R xs, pattern.rel (.inl R) xs ↔ originalRule.root.rel R xs

/-- Each expanded root pattern has its own fresh relation symbol. -/
def profileRootTagLanguage2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) :
    RelLanguage.{max u v} where
  Symbol := (closureProfileLanguage2019 rules Base).Symbol ⊕ ProfileRootPattern2019 rules Base
  arity
    | .inl R => (closureProfileLanguage2019 rules Base).arity R
    | .inr p => L.arity p.originalRule.symbol

/-- Full matching of the displayed prefix with the expanded root. -/
def profileRootPatternMatches2019
    {rules : ClosureDescription L} {UB : Type v} {Base : RelStructure L UB}
    (p : ProfileRootPattern2019 rules Base)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (t : Fin (L.arity p.originalRule.symbol) → X) : Prop :=
  ∃ e : Embedding p.pattern E,
    ∀ i : Fin p.originalRule.rootSize, t (i.castLE p.originalRule.rootLE) = e i

/-- Canonical fresh tagging of an arbitrary profile structure. -/
def profileRootTagExpansion2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X) :
    RelStructure (profileRootTagLanguage2019 rules Base) X where
  rel
    | .inl R, xs => E.rel R xs
    | .inr p, xs =>
        E.rel (.inl p.originalRule.symbol) xs ∧ profileRootPatternMatches2019 p E xs

/-- Forget fresh tags but retain profile relations. -/
def profileRootTagReduct2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X) :
    RelStructure (closureProfileLanguage2019 rules Base) X where
  rel R xs := E.rel (.inl R) xs

/-- Forget both auxiliary relational layers. -/
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

/-- Full embeddings preserve and reflect tags. The inverse root map is
explicitly the original displayed prefix; no same-universe factorization
or closedness of either ambient structure is needed. -/
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
    intro R xs
    cases R with
    | inl R => exact f.map_rel_iff R xs
    | inr p =>
      constructor
      · rintro ⟨hOld, e, he⟩
        let q : Fin p.originalRule.rootSize → X := fun i => xs (i.castLE p.originalRule.rootLE)
        have hq : ∀ i, f (q i) = e i := he
        let a : Embedding p.pattern E := {
          toFun := q
          injective := by
            intro i j hij
            apply e.injective
            exact (hq i).symm.trans ((congrArg f hij).trans (hq j))
          map_rel_iff := by
            intro R zs
            have hFun : f ∘ (q ∘ zs) = e ∘ zs := by
              funext i
              exact hq (zs i)
            calc
              E.rel R (q ∘ zs) ↔ F.rel R (f ∘ (q ∘ zs)) := (f.map_rel_iff R (q ∘ zs)).symm
              _ ↔ F.rel R (e ∘ zs) := by rw [hFun]
              _ ↔ p.pattern.rel R zs := e.map_rel_iff R zs
        }
        exact ⟨(f.map_rel_iff (.inl p.originalRule.symbol) xs).mp hOld, a, fun _ => rfl⟩
      · rintro ⟨hOld, e, he⟩
        exact ⟨(f.map_rel_iff (.inl p.originalRule.symbol) xs).mpr hOld,
          f.comp e, fun i => congrArg f (he i)⟩

/-- Forget an expanded root embedding to the prescribed original root. -/
def profileRootPatternOriginalEmbedding2019
    {rules : ClosureDescription L} {UB : Type v} {Base : RelStructure L UB}
    (p : ProfileRootPattern2019 rules Base)
    {X : Type w} (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (e : Embedding p.pattern E) :
    Embedding p.originalRule.root (profileReduct2019 Base E) where
  toFun := e
  injective := e.injective
  map_rel_iff := fun R xs => (e.map_rel_iff (.inl R) xs).trans (p.reductCorrect R xs)

/-- Lifted closure rule with fresh symbol and complete tagged root. -/
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

/-- Exactly the fresh rules for all compatible root patterns. -/
def profileRootTagRules2019
    (rules : ClosureDescription L) {UB : Type v} (Base : RelStructure L UB) :
    ClosureDescription (profileRootTagLanguage2019 rules Base) :=
  Set.range (fun p : ProfileRootPattern2019 rules Base => profileRootTagRule2019 p)

/-- Normality of fresh tags on an arbitrary tagged structure. -/
def ProfileTagNormal2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X) : Prop :=
  ∀ (p : ProfileRootPattern2019 rules Base) (xs : Fin (L.arity p.originalRule.symbol) → X),
    E.rel (.inr p) xs ↔
      (profileRootTagExpansion2019 rules Base (profileRootTagReduct2019 Base E)).rel (.inr p) xs

/-- Old closure tuples must have valid ORIGINAL roots. This does not
follow merely from the new tag relations or their closedness. -/
def ProfileTagOldRootValid2019
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} (E : RelStructure (profileRootTagLanguage2019 rules Base) X) : Prop :=
  ∀ (r : ClosureRule L), r ∈ rules → ∀ t : Fin (L.arity r.symbol) → X,
    (profileRootTagOriginal2019 Base E).rel r.symbol t →
      r.RootMatches (profileRootTagOriginal2019 Base E) t

/-- Normality gives the full identity from canonical tagging. -/
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
