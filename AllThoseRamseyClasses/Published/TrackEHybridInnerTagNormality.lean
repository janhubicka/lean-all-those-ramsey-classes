import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Functional.WholeMaskCoveredTargetTagNormality2019
import PartiteConstruction.Functional.PatternTagLocalLaws2019
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
      e.hybridOldTaggedReduct hT.1,
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

end StructuralRamsey.RelStructure
