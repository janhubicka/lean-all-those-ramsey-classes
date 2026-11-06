import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedSourceCertificate
import PartiteConstruction.Functional.WholeMaskFullEmbeddingFromCovered2019
import PartiteConstruction.Functional.WholeMaskPartPreservingEmbeddingEquiv2019

/-!
# Track C: full original functional copies from corrected (4b) alone

The general OLD graph decoding theorem turns an embedding of the
complete-mask graph of a finite genuine transversal part-labelled
source A into ANY target with unique complete values and exact
decoded-domain reflection into a full Option(Set) embedding.

The corrected (4b) source certificate verifies both necessary
semantic hypotheses with no fixed B-cover. Full OLD embeddings also
reflect unary part predicates on EVERY vertex, so the copy's original
part map is preserved by the UNIQUE recovered target vertex labels.

Thus a genuine canonical complete OLD copy already present in a
U-closed corrected-(4b)-covered C decodes into a genuinely FULL
PART-PRESERVING original partial-function embedding on exactly its
vertex map. This includes reflection of undefined operation inputs
and exact preservation of defined-empty and multivalued fibres.

It is not asserted that an arbitrary intrinsic whole-weak source
copy (especially a nonclosed weak test with lost outputs) has a
FULL canonical OLD lift into C. That is the original class-local
semantics gap, and this theorem does not erase it.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V T : Type w}

/-- Reinterpret an ACTUAL full OLD copy of a genuine finite
transversal partial-function A in a corrected (4b) candidate as a
full genuine PART-PRESERVING functional embedding on the SAME map.

No arbitrary K-target normalization or fixed B-cover is assumed.
Neither source nor target vertices are added. -/
noncomputable def genuineTagged2019_fullCopy_from_correctedCovered
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (A : PartialSetStructure L T) [Finite T]
    (partA : T → Parts) (hTrA : FibreTransversal A partA)
    (f : RelStructure.Embedding
      (withPartsWholeMaskOld A partA) (wholeMaskTagReduct C)) :
    PartPreservingEmbedding A partA (wholeMaskOriginalDecode C)
      (genuineTagged2019_correctedCoveredPart
        H C hClosed hCovered) := by
  classical
  let partC : V → Parts :=
    genuineTagged2019_correctedCoveredPart H C hClosed hCovered
  let norm : GenuineTagged2019SourceCertificate H C partC :=
    genuineTagged2019_sourceCertificate_of_correctedCovered
      H C hClosed hCovered hPos
  have hTrPlus : FibreTransversal (A.withParts partA) partA :=
    (A.withParts_fibreTransversal_iff partA).mpr hTrA
  let g : PartialSetStructure.Embedding
      (A.withParts partA)
      ((wholeMaskTagReduct C).wholeMaskPartialDecode) :=
    PartialSetStructure.Embedding.ofWholeMaskPatternGraph
      (A.withParts partA) partA hTrPlus (wholeMaskTagReduct C)
      norm.complete_values_unique norm.decoder_defined_iff_OLD f
  let original : PartialSetStructure.Embedding
      A (wholeMaskOriginalDecode C) := {
    toFun := g.toFun
    injective := g.injective
    map_rel_iff := by
      intro R xs
      exact g.map_rel_iff (.inl (ULift.up R)) xs
    map_func := by
      intro F xs
      exact g.map_func (ULift.up F) xs
  }
  refine ⟨original, ?_⟩
  intro x
  have hSourcePart :
      (A.withParts partA).rel (.inr (partA x))
        (fun _ : Fin 1 => x) := rfl
  have hTargetPart :
      ((wholeMaskTagReduct C).wholeMaskPartialDecode).rel
        (.inr (partA x))
        (fun _ : Fin 1 => g.toFun x) :=
    (g.map_rel_iff (.inr (partA x))
      (fun _ : Fin 1 => x)).mpr hSourcePart
  have hOldPart : WholeMaskVertexPartHolds C
      (g.toFun x) (partA x) := hTargetPart
  exact (norm.part_unique (g.toFun x) (partA x) hOldPart).symm

/-- Regression: the reconstructed genuine full embedding uses EXACTLY
the original OLD vertex map, not an ambient closure hull, canonical
replacement target, or any enlarged tested carrier. -/
theorem genuineTagged2019_fullCopy_from_correctedCovered_apply
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (A : PartialSetStructure L T) [Finite T]
    (partA : T → Parts) (hTrA : FibreTransversal A partA)
    (f : RelStructure.Embedding
      (withPartsWholeMaskOld A partA) (wholeMaskTagReduct C))
    (x : T) :
    (genuineTagged2019_fullCopy_from_correctedCovered
      H C hClosed hCovered hPos A partA hTrA f).1.toFun x = f x :=
  rfl

end AllThoseRamseyClasses.Published
