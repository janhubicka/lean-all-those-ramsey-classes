import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Functional.WholeMaskCoveredTargetTagNormality2019
import PartiteConstruction.Functional.PatternTagLocalLaws2019
import PartiteConstruction.Functional.WholeMaskTagFreeAmalgam2019
import PartiteConstruction.Functional.CanonicalTagFreeAmalgam2019
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: distinguish JOINT tag exactness from nested OLD/SPLIT tag exactness

The hybrid relational signature has THREE syntactically different
tag levels. Two EXISTING inner tagged subsignatures are embedded
in the base `L.splitMaskHybrid Parts`:
(1) the complete ORIGINAL OLD whole-mask tag language; and
(2) the output-part-indexed singleton PATTERN tag language.

The newer JOINT full-HYBRID-root tags are built on top of this
ENTIRE base language. The already verified `HasExactJointRootTags`
normalizes only those fresh JOINT tags. It does NOT, by itself,
say that an arbitrary base Picture's OLD whole-mask tags or
its split pattern tags have their canonical old-root semantics.

This module exposes the literal two inner tagged reducts and
bundles the INDEPENDENT `WholeMaskTagNormal` and
`PatternTagNormal` assumptions into `HybridInnerTagsNormal`.

For a genuine canonical native partite System, both inner
subsignatures are exactly their canonical tagged expansions.
More generally, BOTH inner tag-normality laws reflect through
every FULL hybrid relational embedding and therefore survive
any exact induced weak vertex cut, without constructing a hull
or reinterpreting its clipped function output tuples.

This class is a necessary semantic guard for the stronger
assertion that an arbitrary noncanonical joint Picture equals
the JOINT re-encoding of its decoded native System. We do NOT
claim that U-closedness or exactness of the OUTER joint tags
implies the inner-tag laws; nor do we claim the finite-family
ordered sparse Ramsey construction preserves them.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Retain the ACTUAL old whole-mask tag relations in the
base hybrid Picture, including all inherited OLD root-tag
relation names and positive/active OLD graph records. -/
def hybridOldTaggedReduct
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    RelStructure (L.wholeMaskTagLanguage Parts) V where
  rel R xs := E.rel (.inl R) xs

/-- Retain the ACTUAL per-output-part singleton PATTERN-tag
relations of the base hybrid Picture. Neither original masks
nor the independent unary part predicates are reconstructed. -/
def hybridSplitTaggedReduct
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    RelStructure ((L.outputPartIndexed Parts).patternTag) V where
  rel R xs := E.rel (.inr (.inl R)) xs

namespace Embedding

variable {V W : Type w}
variable {E : RelStructure (L.splitMaskHybrid Parts) V}
variable {T : RelStructure (L.splitMaskHybrid Parts) W}

/-- Any FULL hybrid embedding restricts, on its SAME vertex
map, to a FULL embedding of the original OLD tag language. -/
def hybridOldTaggedReduct
    (e : Embedding E T) :
    Embedding (RelStructure.hybridOldTaggedReduct E)
      (RelStructure.hybridOldTaggedReduct T) where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro R xs
    exact e.map_rel_iff (.inl R) xs

/-- Any FULL hybrid embedding restricts to a FULL embedding
of the singleton split PATTERN tag language. -/
def hybridSplitTaggedReduct
    (e : Embedding E T) :
    Embedding (RelStructure.hybridSplitTaggedReduct E)
      (RelStructure.hybridSplitTaggedReduct T) where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro R xs
    exact e.map_rel_iff (.inr (.inl R)) xs

end Embedding

/-- INDEPENDENT exact semantics of BOTH nested hybrid tag
subsignatures. The fresh JOINT outer full-root tag exactness
is not included here and must be stated separately.
The law is about the ACTUAL recorded tag relations, not an
existential choice of a canonical re-tagging of this Picture. -/
def HybridInnerTagsNormal
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  WholeMaskTagNormal (hybridOldTaggedReduct E) ∧
  PatternTagNormal (hybridSplitTaggedReduct E)

/-- Every canonical source hybrid of a genuine native
functional partite System has both nested tag families with
their exact, original canonical meanings. -/
theorem canonicalHybrid_innerTagsNormal
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridInnerTagsNormal A.splitMaskHybrid := by
  constructor
  · change WholeMaskTagNormal
      (wholeMaskTagExpansion
        (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part))
    exact wholeMaskTagNormal_canonical _
  · change PatternTagNormal
      (patternTagExpansion A.splitOutputParts.toStructure.patternGraph)
    exact patternTag_normal_canonical _

/-- Both independent inner-tag laws reflect along ANY FULL
hybrid relational embedding. Thus their validity is not
restricted to canonical native objects. No joint U-closedness,
native decoder, finite carrier or positive function arity is
assumed. -/
theorem HybridInnerTagsNormal.of_embedding
    {V W : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    {T : RelStructure (L.splitMaskHybrid Parts) W}
    (hT : HybridInnerTagsNormal T) (e : Embedding E T) :
    HybridInnerTagsNormal E :=
  ⟨WholeMaskTagNormal.of_embedding
      hT.1 e.hybridOldTaggedReduct,
   PatternTagNormal.of_embedding
      e.hybridSplitTaggedReduct hT.2⟩

/-- Any literal EXACT induced weak vertex subset of an
inner-tag-normal hybrid picture remains inner-tag-normal.
Inherited root-tag names are not recomputed from the
intrinsically weakly induced partial function. -/
theorem HybridInnerTagsNormal.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (hE : HybridInnerTagsNormal E) (S : Set V) :
    HybridInnerTagsNormal (E.induce S) :=
  hE.of_embedding (RelStructure.inclusion E S)

/-- Every FULL base-hybrid free-amalgamation diagram remains a
genuine FULL relational free-amalgamation diagram after forgetting
the split tags and unary predicates to the nested OLD whole-mask
tagged signature, on the SAME carrier and vertex maps. -/
theorem IsFreeAmalgam.hybridOldTaggedReduct
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam
      sL.hybridOldTaggedReduct sR.hybridOldTaggedReduct
      iL.hybridOldTaggedReduct iR.hybridOldTaggedReduct where
  covers := hFree.covers
  overlap := hFree.overlap
  rel_iff R xs := hFree.rel_iff (.inl R) xs

/-- Forgetting to the nested per-output-part PATTERN tagged
language preserves every clause of a genuine free amalgam,
including exact overlap and FULL induced side embeddings. -/
theorem IsFreeAmalgam.hybridSplitTaggedReduct
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam
      sL.hybridSplitTaggedReduct sR.hybridSplitTaggedReduct
      iL.hybridSplitTaggedReduct iR.hybridSplitTaggedReduct where
  covers := hFree.covers
  overlap := hFree.overlap
  rel_iff R xs := hFree.rel_iff (.inr (.inl R)) xs

/-- OLD tag-normality is literally equality with the canonical
OLD full-root tag expansion of the OLD reduct, not just an
additional one-way positivity condition. -/
private theorem wholeMaskTagNormal_eq_canonical
    {V : Type w}
    (A : RelStructure (L.wholeMaskTagLanguage Parts) V)
    (h : WholeMaskTagNormal A) :
    A = wholeMaskTagExpansion (wholeMaskTagReduct A) := by
  apply RelStructure.rel_injective
  funext R t
  apply propext
  rcases R with R | p
  · exact Iff.rfl
  · exact h p t

/-- Split pattern-tag normality is literally equality with
the canonical split pattern-tag expansion of its OLD reduct. -/
private theorem patternTagNormal_eq_canonical
    {V : Type w}
    (A : RelStructure ((L.outputPartIndexed Parts).patternTag) V)
    (h : PatternTagNormal A) :
    A = patternTagExpansion (patternTagReduct A) := by
  apply RelStructure.rel_injective
  funext R t
  apply propext
  rcases R with R | p
  · exact Iff.rfl
  · exact h p t

/-- INDEPENDENT exact semantics of BOTH nested tag families
survive any TRUE FULL free amalgam of base hybrid structures
when the two sides have the corresponding inner-tag semantics.

The proof projects the same relational free diagram to each
nested tag language, then to its OLD reduct. The already
verified tag-expansion FREE-amalgamation theorems construct
canonical diagrams with the same vertices and side maps.
The original and canonical whole relations coincide because
both sides have exact inner-tag semantics.

No root U-closedness, positive arity, source hull or new output
vertex is needed. In particular this theorem does NOT assert
that the inner tags follow from outer JOINT-tag exactness. -/
theorem HybridInnerTagsNormal.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridInnerTagsNormal Left)
    (hRight : HybridInnerTagsNormal Right) :
    HybridInnerTagsNormal Whole := by
  classical
  have hOldFree := hFree.hybridOldTaggedReduct
  have hSplitFree := hFree.hybridSplitTaggedReduct
  constructor
  · have hOldBase : IsFreeAmalgam
        sL.hybridOldTaggedReduct.wholeMaskTagReduct
        sR.hybridOldTaggedReduct.wholeMaskTagReduct
        iL.hybridOldTaggedReduct.wholeMaskTagReduct
        iR.hybridOldTaggedReduct.wholeMaskTagReduct := by
      refine { covers := hFree.covers, overlap := hFree.overlap,
        rel_iff := ?_ }
      intro R xs
      exact hFree.rel_iff (.inl (.inl R)) xs
    have hCanonFree := hOldBase.wholeMaskTagExpansion
    have hL :
        hybridOldTaggedReduct Left =
          wholeMaskTagExpansion
            (wholeMaskTagReduct (hybridOldTaggedReduct Left)) :=
      wholeMaskTagNormal_eq_canonical
        (hybridOldTaggedReduct Left) hLeft.1
    have hR :
        hybridOldTaggedReduct Right =
          wholeMaskTagExpansion
            (wholeMaskTagReduct (hybridOldTaggedReduct Right)) :=
      wholeMaskTagNormal_eq_canonical
        (hybridOldTaggedReduct Right) hRight.1
    intro p t
    calc
      (hybridOldTaggedReduct Whole).rel (.inr p) t ↔
          (∃ x,
            (hybridOldTaggedReduct Left).rel (.inr p) x ∧
            t = iL ∘ x) ∨
          (∃ y,
            (hybridOldTaggedReduct Right).rel (.inr p) y ∧
            t = iR ∘ y) :=
        hOldFree.rel_iff (.inr p) t
      _ ↔
          (∃ x,
            (wholeMaskTagExpansion
              (wholeMaskTagReduct (hybridOldTaggedReduct Left))).rel
                (.inr p) x ∧ t = iL ∘ x) ∨
          (∃ y,
            (wholeMaskTagExpansion
              (wholeMaskTagReduct (hybridOldTaggedReduct Right))).rel
                (.inr p) y ∧ t = iR ∘ y) := by
        rw [← hL, ← hR]
      _ ↔
          (wholeMaskTagExpansion
            (wholeMaskTagReduct (hybridOldTaggedReduct Whole))).rel
              (.inr p) t :=
        (hCanonFree.rel_iff (.inr p) t).symm
  · have hSplitBase : IsFreeAmalgam
        sL.hybridSplitTaggedReduct.patternTagReduct
        sR.hybridSplitTaggedReduct.patternTagReduct
        iL.hybridSplitTaggedReduct.patternTagReduct
        iR.hybridSplitTaggedReduct.patternTagReduct := by
      refine { covers := hFree.covers, overlap := hFree.overlap,
        rel_iff := ?_ }
      intro R xs
      exact hFree.rel_iff (.inr (.inl (.inl R))) xs
    have hCanonFree := hSplitBase.patternTagExpansion
    have hL :
        hybridSplitTaggedReduct Left =
          patternTagExpansion
            (patternTagReduct (hybridSplitTaggedReduct Left)) :=
      patternTagNormal_eq_canonical
        (hybridSplitTaggedReduct Left) hLeft.2
    have hR :
        hybridSplitTaggedReduct Right =
          patternTagExpansion
            (patternTagReduct (hybridSplitTaggedReduct Right)) :=
      patternTagNormal_eq_canonical
        (hybridSplitTaggedReduct Right) hRight.2
    intro p t
    calc
      (hybridSplitTaggedReduct Whole).rel (.inr p) t ↔
          (∃ x,
            (hybridSplitTaggedReduct Left).rel (.inr p) x ∧
            t = iL ∘ x) ∨
          (∃ y,
            (hybridSplitTaggedReduct Right).rel (.inr p) y ∧
            t = iR ∘ y) :=
        hSplitFree.rel_iff (.inr p) t
      _ ↔
          (∃ x,
            (patternTagExpansion
              (patternTagReduct (hybridSplitTaggedReduct Left))).rel
                (.inr p) x ∧ t = iL ∘ x) ∨
          (∃ y,
            (patternTagExpansion
              (patternTagReduct (hybridSplitTaggedReduct Right))).rel
                (.inr p) y ∧ t = iR ∘ y) := by
        rw [← hL, ← hR]
      _ ↔
          (patternTagExpansion
            (patternTagReduct (hybridSplitTaggedReduct Whole))).rel
              (.inr p) t :=
        (hCanonFree.rel_iff (.inr p) t).symm

end StructuralRamsey.RelStructure
