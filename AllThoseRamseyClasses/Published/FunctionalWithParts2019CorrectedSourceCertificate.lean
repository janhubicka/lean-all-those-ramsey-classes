import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedDomainWitness
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedOutputParts
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeProtectedBridge

/-!
# Track C: one checked normalization contract for corrected 2019 tagged sources

The corrected 2019 (4b) condition requires membership in canonical K(H)
of each closed U-irreducible induced substructure of C; it does NOT
postulate a fixed B whose copies cover C.

This contract assembles separately verified source facts:
unique unary vertex parts, tag normality, coherent complete values
and active domains, exact decoded definedness including some-empty,
transversal decoded function outputs and an exact SAME-WITNESS
ambient-relative to positive genuine functional H-completion transfer.

Notably there is NO claim that the whole decoded C is an H member,
nor that intrinsic nonclosed whole-weak pieces fully embed into H.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Independent source-wide semantic obligations, without a global
original functional H-membership or strict native B-tree requirement. -/
structure GenuineTagged2019SourceCertificate
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (part : V → Parts) : Prop where
  part_holds :
    ∀ x : V, WholeMaskVertexPartHolds C x (part x)
  part_unique :
    ∀ (x : V) (p : Parts),
      WholeMaskVertexPartHolds C x p → p = part x
  tag_normal : WholeMaskTagNormal C
  value_domains_valid : HasValidCompleteMaskDomains (wholeMaskTagReduct C)
  domain_part_sets_unique :
    HasUniqueWholeMaskDomainSets (wholeMaskTagReduct C)
  complete_values_unique :
    HasUniqueWholeMaskValues (wholeMaskTagReduct C)
  decoder_defined_iff_OLD :
    ∀ (F : (L.withParts Parts).FuncSymbol)
      (xs : Fin ((L.withParts Parts).funcArity F) → V),
      (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F xs ↔
        HasWholeMaskDomain (wholeMaskTagReduct C) F xs
  outputs_match_parts :
    WholeMaskOutputPartsCompatible (wholeMaskTagReduct C) part
  decoded_fibres_transversal :
    FibreTransversal ((wholeMaskTagReduct C).wholeMaskPartialDecode) part
  original_fibres_transversal :
    FibreTransversal (wholeMaskOriginalDecode C) part
  original_defined_iff_OLD :
    ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V),
      (wholeMaskOriginalDecode C).Defined F xs ↔
        HasWholeMaskDomain (wholeMaskTagReduct C) (ULift.up F) xs
  exact_relative_to_native :
    ∀ (S : Set V),
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S) →
      HasGenuineIntrinsicWeakCanonicalProtectedCompletion H C part S

/-- Corrected (4b), U-closedness and positive primitive input arity
imply the whole certificate, with no fixed B-cover or independent
functional source-normalization axiom. -/
theorem genuineTagged2019_sourceCertificate_of_correctedCovered
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity) :
    GenuineTagged2019SourceCertificate H C
      (genuineTagged2019_correctedCoveredPart
        H C hClosed hCovered) := by
  classical
  let part := genuineTagged2019_correctedCoveredPart
    H C hClosed hCovered
  have hPart : ∀ x : V, WholeMaskVertexPartHolds C x (part x) :=
    genuineTagged2019_correctedCoveredPart_holds
      H C hClosed hCovered
  have hUniquePart : ∀ (x : V) (p : Parts),
      WholeMaskVertexPartHolds C x p → p = part x := by
    intro x p hp
    obtain ⟨q, hq, hu⟩ :=
      genuineTagged2019_correctedCovered_vertexPart_existsUnique
        H C hClosed hCovered x
    exact (hu p hp).trans (hu (part x) (hPart x)).symm
  have hTags : WholeMaskTagNormal C :=
    genuineTagged2019_correctedCovered_tagNormal
      H C hClosed hCovered
  have hDomains : HasValidCompleteMaskDomains (wholeMaskTagReduct C) :=
    genuineTagged2019_correctedCovered_validCompleteMaskDomains
      H C hClosed hCovered
  have hDomainsUnique :
      HasUniqueWholeMaskDomainSets (wholeMaskTagReduct C) :=
    genuineTagged2019_correctedCovered_uniqueDomainSets
      H C hClosed hCovered
  have hValuesUnique :
      HasUniqueWholeMaskValues (wholeMaskTagReduct C) :=
    genuineTagged2019_correctedCovered_uniqueCompleteValues
      H C hClosed hCovered hPos
  have hDefined : ∀ (F : (L.withParts Parts).FuncSymbol)
      (xs : Fin ((L.withParts Parts).funcArity F) → V),
      (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F xs ↔
        HasWholeMaskDomain (wholeMaskTagReduct C) F xs := by
    intro F xs
    exact genuineTagged2019_correctedCovered_decoder_defined_iff_OLD_domain
      H C hClosed hCovered hPos F xs
  have hParts : WholeMaskOutputPartsCompatible
      (wholeMaskTagReduct C) part :=
    genuineTagged2019_correctedCovered_outputPartsCompatible
      H C hClosed hCovered
  have hTrans : FibreTransversal
      ((wholeMaskTagReduct C).wholeMaskPartialDecode) part :=
    genuineTagged2019_correctedCovered_decoder_fibreTransversal
      H C hClosed hCovered hPos
  have hOriginalTrans : FibreTransversal
      (wholeMaskOriginalDecode C) part := by
    intro F xs U hValue y hy z hz hSame
    exact hTrans (ULift.up F) xs U hValue y hy z hz hSame
  have hOriginalDefined :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V),
        (wholeMaskOriginalDecode C).Defined F xs ↔
          HasWholeMaskDomain (wholeMaskTagReduct C) (ULift.up F) xs := by
    intro F xs
    change
      (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined
        (ULift.up F) xs ↔
        HasWholeMaskDomain (wholeMaskTagReduct C) (ULift.up F) xs
    exact hDefined (ULift.up F) xs
  refine
    { part_holds := hPart
      part_unique := hUniquePart
      tag_normal := hTags
      value_domains_valid := hDomains
      domain_part_sets_unique := hDomainsUnique
      complete_values_unique := hValuesUnique
      decoder_defined_iff_OLD := hDefined
      outputs_match_parts := hParts
      decoded_fibres_transversal := hTrans
      original_fibres_transversal := hOriginalTrans
      original_defined_iff_OLD := hOriginalDefined
      exact_relative_to_native := ?_ }
  intro S hRelative
  exact relative_implies_intrinsicWeakCanonicalProtected_of_unique
    H C part hPart S hValuesUnique hRelative

/-- A single theorem application now supplies a genuine H-valued
same-map weak certificate, preserving all canonical CLOSED protected
copies, for any exact ambient-induced weak S. -/
theorem genuineTagged2019_exactRelative_to_native_of_correctedCovered
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (S : Set V)
    (hRelative :
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S)) :
    HasGenuineIntrinsicWeakCanonicalProtectedCompletion
      H C (genuineTagged2019_correctedCoveredPart
        H C hClosed hCovered) S :=
  (genuineTagged2019_sourceCertificate_of_correctedCovered
    H C hClosed hCovered hPos).exact_relative_to_native S hRelative

end AllThoseRamseyClasses.Published
