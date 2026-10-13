import AllThoseRamseyClasses.Published.ProfileRootTagLocalLaws2019
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# Recover the ORIGINAL language, tests, and Ramsey arrow

The final tagged Picture need not be a canonical profile expansion of
its original reduct. Only the input A->B embeddings must lift to recover
the original Ramsey arrow. Original closed irreducible coverage follows
from both local laws and actual tagged closed-test coverage. Ordinary
maps then protect exactly the corrected original closed tests.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w z
variable {L : RelLanguage.{u}}

/-- Canonical profile expansion followed by canonical fresh tagging. -/
abbrev profileTaggedCanonical2019
    (rules : ClosureDescription L) {UB X : Type v}
    (Base : RelStructure L UB) (E : RelStructure L X) :=
  profileRootTagExpansion2019 rules Base (closureProfileExpansion2019 rules Base E)

/-- Full embeddings of the CLOSED original inputs lift through both layers. -/
def profileTaggedCanonicalEmbedding2019
    {rules : ClosureDescription L} {UB X Y : Type v}
    (Base : RelStructure L UB) {E : RelStructure L X} {F : RelStructure L Y}
    (f : Embedding E F) (hE : IsUClosed rules E) (hF : IsUClosed rules F) :
    Embedding (profileTaggedCanonical2019 rules Base E) (profileTaggedCanonical2019 rules Base F) :=
  profileRootTagEmbedding2019 Base (closureProfileEmbedding2019 Base f hE hF)

/-- Ordinary homomorphism-embeddings survive forgetting profiles. -/
theorem profileReduct2019_ordinary
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    (E : RelStructure (closureProfileLanguage2019 rules Base) X)
    (F : RelStructure (closureProfileLanguage2019 rules Base) Y)
    (f : X → Y) (hf : E.IsHomomorphismEmbedding F f) :
    (profileReduct2019 Base E).IsHomomorphismEmbedding (profileReduct2019 Base F) f := by
  constructor
  · intro R xs hxs
    exact hf.1 (.inl R) xs hxs
  · intro S hS
    have hSPlus : (E.induce S).Irreducible := by
      intro x y hxy
      obtain ⟨R, ts, i, j, ht, hi, hj⟩ := hS hxy
      exact ⟨.inl R, ts, i, j, ht, hi, hj⟩
    obtain ⟨e, he⟩ := hf.embeddingOn S hSPlus
    exact ⟨profileReductEmbedding2019 Base e, he⟩

/-- Ordinary maps survive forgetting just the fresh closure tags. -/
theorem profileRootTagReduct2019_ordinary
    {rules : ClosureDescription L} {UB : Type v} (Base : RelStructure L UB)
    {X : Type w} {Y : Type z}
    (E : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (F : RelStructure (profileRootTagLanguage2019 rules Base) Y)
    (f : X → Y) (hf : E.IsHomomorphismEmbedding F f) :
    (profileRootTagReduct2019 Base E).IsHomomorphismEmbedding (profileRootTagReduct2019 Base F) f := by
  constructor
  · intro R xs hxs
    exact hf.1 (.inl R) xs hxs
  · intro S hS
    have hSPlus : (E.induce S).Irreducible := by
      intro x y hxy
      obtain ⟨R, ts, i, j, ht, hi, hj⟩ := hS hxy
      exact ⟨.inl R, ts, i, j, ht, hi, hj⟩
    obtain ⟨e, he⟩ := hf.embeddingOn S hSPlus
    exact ⟨profileRootTagReductEmbedding2019 Base e, he⟩

/-- The canonical tag operation lifts any Ramsey arrow in the profile
language, including one whose control is not originally U-closed. -/
theorem profileRootTag2019_arrow
    {rules : ClosureDescription L} {UB X Y Z : Type v}
    (Base : RelStructure L UB)
    (A : RelStructure (closureProfileLanguage2019 rules Base) X)
    (B : RelStructure (closureProfileLanguage2019 rules Base) Y)
    (C : RelStructure (closureProfileLanguage2019 rules Base) Z)
    (κ : Type*) (hArrow : StructuralRamsey.Arrow A B C κ) :
    StructuralRamsey.Arrow (profileRootTagExpansion2019 rules Base A)
      (profileRootTagExpansion2019 rules Base B) (profileRootTagExpansion2019 rules Base C) κ := by
  intro colour
  obtain ⟨b, hb⟩ := hArrow (fun a => colour (profileRootTagEmbedding2019 Base a))
  let bTag := profileRootTagEmbedding2019 Base b
  have hComp : ∀ a : Embedding (profileRootTagExpansion2019 rules Base A)
      (profileRootTagExpansion2019 rules Base B),
      bTag.comp a = profileRootTagEmbedding2019 Base
        (b.comp (profileRootTagReductEmbedding2019 Base a)) := by
    intro a
    apply Embedding.ext
    intro x
    rfl
  refine ⟨bTag, ?_⟩
  intro a1 a2
  rw [hComp a1, hComp a2]
  exact hb (profileRootTagReductEmbedding2019 Base a1) (profileRootTagReductEmbedding2019 Base a2)

/-- Forget the tagged Ramsey arrow to the original language. Only
original embeddings A->B lift; no assertion is made that every global
original A-copy in the constructed target lifts. -/
theorem profileRootTag2019_forget_arrow
    {rules : ClosureDescription L} {UB X Y Z : Type v}
    (Base : RelStructure L UB) (A : RelStructure L X) (B : RelStructure L Y)
    (C : RelStructure (profileRootTagLanguage2019 rules Base) Z)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (κ : Type*)
    (hArrow : StructuralRamsey.Arrow (profileTaggedCanonical2019 rules Base A)
      (profileTaggedCanonical2019 rules Base B) C κ) :
    StructuralRamsey.Arrow A B (profileRootTagOriginal2019 Base C) κ := by
  intro colour
  obtain ⟨b, hb⟩ := hArrow (fun a => colour (profileRootTagOriginalEmbedding2019 Base a))
  let bo : Embedding B (profileRootTagOriginal2019 Base C) := profileRootTagOriginalEmbedding2019 Base b
  have hComp : ∀ a : Embedding A B, bo.comp a =
      profileRootTagOriginalEmbedding2019 Base (b.comp (profileTaggedCanonicalEmbedding2019 Base a hA hB)) := by
    intro a
    apply Embedding.ext
    intro x
    rfl
  refine ⟨bo, ?_⟩
  intro a1 a2
  rw [hComp a1, hComp a2]
  exact hb (profileTaggedCanonicalEmbedding2019 Base a1 hA hB)
    (profileTaggedCanonicalEmbedding2019 Base a2 hA hB)

/-- The tagged closed Picture has a genuinely U-CLOSED original reduct,
and EVERY original closed U-irreducible embedded test embeds fully in
original Base. Neither claim is assumed as a new construction oracle. -/
theorem profileTag2019_original_closed_and_coverage
    {rules : ClosureDescription L} {UB X : Type v}
    (Base : RelStructure L UB) (hBase : IsUClosed rules Base)
    (C : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hC : IsUClosed (profileRootTagRules2019 rules Base) C)
    (hCover : ∀ {Z : Type v} (Test : RelStructure (profileRootTagLanguage2019 rules Base) Z),
      IsUClosed (profileRootTagRules2019 rules Base) Test →
      IsUIrreducible (profileRootTagRules2019 rules Base) Test →
      Embedding Test C → Nonempty (Embedding Test (profileTaggedCanonical2019 rules Base Base))) :
    IsUClosed rules (profileRootTagOriginal2019 Base C) ∧
    (∀ {Y : Type v} (Test : RelStructure L Y),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test (profileRootTagOriginal2019 Base C) → Nonempty (Embedding Test Base)) := by
  obtain ⟨hNormal, hValid⟩ := profileTag2019_local_laws_of_closed_coverage
    Base C (profileTaggedCanonical2019 rules Base Base) hC
    (profileRootTag2019_canonical_normal Base (closureProfileExpansion2019 rules Base Base))
    (profileRootTag2019_canonical_old_valid Base (closureProfileExpansion2019 rules Base Base) hBase)
    hCover
  refine ⟨profileRootTag2019_original_closed_of_tagged Base C hC hNormal hValid, ?_⟩
  intro Y Test hTestClosed hTestIrred e
  let S : Set X := Set.range e
  obtain ⟨hSClosed, hSIrred⟩ := closedIrreducible_exact_induced_range_2019 e hTestClosed hTestIrred
  have hSNormal : ProfileTagNormal2019 Base (C.induce S) :=
    profileTag2019_normal_of_embedding Base (inclusion C S) hNormal
  have hSValid : ProfileTagOldRootValid2019 Base (C.induce S) :=
    profileTag2019_old_valid_of_embedding Base (inclusion C S) hValid
  have hSClosedTag : IsUClosed (profileRootTagRules2019 rules Base) (C.induce S) :=
    profileRootTag2019_closed_of_original Base (C.induce S) hSNormal hSClosed
  have hSIrredTag : IsUIrreducible (profileRootTagRules2019 rules Base) (C.induce S) :=
    profileTag2019_uIrreducible_of_original Base (C.induce S) hSNormal hSValid hSIrred
  obtain ⟨a⟩ := hCover (C.induce S) hSClosedTag hSIrredTag (inclusion C S)
  exact ⟨(profileRootTagOriginalEmbedding2019 Base a).comp (inducedRangeEmbedding e)⟩

/-- Under genuine original closed B-coverage, ordinary maps protect the
EXACT corrected original tests, since those tests are K-members and
therefore ordinary irreducibles. The source itself may be weak. -/
theorem ordinary2019_corrected_of_closed_coverage
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {UB X Y : Type v} (Base : RelStructure L UB)
    (C : RelStructure L X) (D : RelStructure L Y)
    (hBK : K Base) (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (E : RelStructure L Z), K E → E.Irreducible)
    (hCover : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test Base))
    (f : X → Y) (hf : C.IsHomomorphismEmbedding D f) :
    IsInducedClosedUHomomorphismEmbedding rules C D f := by
  refine ⟨hf.1, ?_⟩
  intro S hSClosed hSIrred
  obtain ⟨e⟩ := hCover (C.induce S) hSClosed hSIrred (inclusion C S)
  have hSK : K (C.induce S) := hHer (C.induce S) Base hBK hSClosed e
  exact hf.embeddingOn S (hKIrr (C.induce S) hSK)

end AllThoseRamseyClasses.Published
