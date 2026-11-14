import AllThoseRamseyClasses.Published.TrackEHybridOldDecoderUnique
import AllThoseRamseyClasses.Published.TrackEJointNormalTargetClass
import PartiteConstruction.Functional.WholeMaskDecodedOutputParts2019

/-!
# Track E2: the actual OLD decoder has transversal output fibres

The hybrid picture has a unary predicate for EVERY vertex's output
part, including isolated vertices. Exact uniqueness of these
predicates determines one literal part map on the same carrier.
An arbitrary complete ORIGINAL old output tuple obeys the
designated output-part labels by the separately certified positive
output soundness law.

Combining these two invariants gives precisely the already
established OLD `WholeMaskOutputPartsCompatible` condition.
The certified `decoder_fibreTransversal` theorem then applies
to the EXISTING `wholeMaskPartialDecode`, provided its
complete-value sets are unique.

The latter hypothesis is now available from the merged
cross-pattern whole-fibre theorem. We thus prove that every
decoded genuinely partial Option(Set) operation contains
AT MOST ONE output vertex of each actual target part.
This is an actual native decoder invariant, not merely a
part-set mask statement.

Part preservation for FULL hybrid relational embeddings is
also shown directly from the unary symbols, without requiring
functional decoding or a chosen output part for only active
vertices.

No vertex is added, no output is regenerated, and no claim
about original RELATIONAL tuple transversality or the still
outstanding sparse ordered Ramsey theorem is made.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Recover the unique part label of EVERY vertex of an
arbitrary hybrid Picture, including isolated vertices. This
is the literal unique unary part predicate, not an
output-only or function-fibre partial map. -/
noncomputable def HybridUniqueVertexPart.partMap
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridUniqueVertexPart E) : V → Parts :=
  fun x => Classical.choose (h x)

/-- The canonical part map names the positive unary part label. -/
theorem HybridUniqueVertexPart.partMap_hasLabel
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridUniqueVertexPart E) (x : V) :
    E.rel (.inr (.inr (h.partMap x)))
      (fun _ : Fin 1 => x) := by
  exact (Classical.choose_spec (h x)).1

/-- Any positive unary part label determines the ACTUAL part map,
by uniqueness for this vertex. -/
theorem HybridUniqueVertexPart.partMap_eq_of_label
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridUniqueVertexPart E) (x : V) (q : Parts)
    (hq : E.rel (.inr (.inr q)) (fun _ : Fin 1 => x)) :
    h.partMap x = q := by
  change Classical.choose (h x) = q
  exact ((Classical.choose_spec (h x)).2 q hq).symm

/-- Every FULL hybrid embedding preserves the literal unique
part of EVERY vertex, even when it belongs to no relational
or functional tuple. -/
theorem HybridUniqueVertexPart.partMap_preserved
    {V W : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    {T : RelStructure (L.splitMaskHybrid Parts) W}
    (hE : HybridUniqueVertexPart E)
    (hT : HybridUniqueVertexPart T)
    (e : Embedding E T) (x : V) :
    hT.partMap (e x) = hE.partMap x := by
  have hIn :
      T.rel (.inr (.inr (hE.partMap x)))
        (fun _ : Fin 1 => e x) := by
    have hx := (e.map_rel_iff (.inr (.inr (hE.partMap x)))
      (fun _ : Fin 1 => x)).mpr (hE.partMap_hasLabel x)
    simpa only [Function.comp_apply] using hx
  exact hT.partMap_eq_of_label (e x) (hE.partMap x) hIn

/-- Positive whole-mask output soundness combined with unary
part uniqueness forces each complete original OLD output vertex
to occupy the precise part named by its output slot.

This directly supplies the old-decoder part-transversality
interface already available in the 2019 formalization. -/
theorem HybridPositiveOutputSound.oldOutputPartsCompatible
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (hSound : HybridPositiveOutputSound E)
    (hParts : HybridUniqueVertexPart E) :
    WholeMaskOutputPartsCompatible
      (splitMaskHybridOriginalOldReduct E) hParts.partMap := by
  intro p m t ht j
  have hOutput :
      E.rel (hybridOriginalMaskOutputSymbol p m) t := ht
  have hUnary :
      E.rel (.inr (.inr (m.label j)))
        (fun _ : Fin 1 => t (Fin.natAdd p.rootSize j)) := by
    exact hSound.2.2.2 p m j t hOutput
  exact hParts.partMap_eq_of_label
    (t (Fin.natAdd p.rootSize j)) (m.label j) hUnary

/-- A noncanonical normal JOINT hybrid target with the independently
verified positive split SAME-VERTEX cross-pattern law has a
GENUINELY TRANSVERSAL ORIGINAL partial-function decoder.

For any primitive F(xs), the entire decoded output fibre has
at most one element of each unary part. Neither U-closedness,
positive primitive arity, nor finiteness is needed for this
particular value-level statement, because every decoded value
already has a visible complete OLD output witness. -/
theorem HybridJointTargetNormal.oldDecoder_fibreTransversal
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointTargetNormal C)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C)) :
    PartialSetStructure.FibreTransversal
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode)
      hNorm.coherent.1.2.2.2.partMap := by
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  let hParts : HybridUniqueVertexPart Base :=
    hNorm.coherent.1.2.2.2
  have hCompatible :
      WholeMaskOutputPartsCompatible Old hParts.partMap :=
    hNorm.positive.oldOutputPartsCompatible hParts
  exact hCompatible.decoder_fibreTransversal Old hParts.partMap
    (fun F xs U T hU hT =>
      hNorm.coherent.oldDecoder_uniqueValue
        hNorm.positive hNorm.injectiveDomains
        hNorm.originalMasks hSplit F xs U T hU hT)

/-- The stricter no-defined-empty target class has the same
transversal decoder, with no extra assumptions on its masks. -/
theorem HybridJointNoEmptyNormal.oldDecoder_fibreTransversal
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C)) :
    PartialSetStructure.FibreTransversal
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode)
      hNorm.normal.coherent.1.2.2.2.partMap :=
  hNorm.normal.oldDecoder_fibreTransversal hSplit

end StructuralRamsey.RelStructure
