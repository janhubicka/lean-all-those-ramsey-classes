import AllThoseRamseyClasses.Published.TrackEJointExactTaggedClosedSeamCoherence
import AllThoseRamseyClasses.Published.TrackEHybridCoherencePackage
import AllThoseRamseyClasses.Published.TrackEHybridOldMaskPatternFree
import AllThoseRamseyClasses.Published.TrackEHybridActiveDomainRootInjective
import PartiteConstruction.Iterated.FreeAmalgam

/-!
# Track E2: one finite-weak-safe normal joint-hybrid target class

The hybrid encoding of the corrected functional partite proof carries:
1. complete ORIGINAL output-mask domains and whole-value tuples;
2. per-part singleton split domains/incidences and unary part labels;
3. TWO full-hybrid-root closure-tag families.

A noncanonical relational target may fail any of several independent
necessary conditions for interpreting these records as functions.
Instead of relying on unstated "normality" of arbitrary sparse
Ramsey Pictures, package the verified conditions into ONE exact
JOINT-tagged target predicate.

The package is true for every finite canonical genuinely native
source and survives ALL literal induced weak restrictions, without
recomputing forgotten whole values. It also survives a TRUE FULL
joint relational free amalgam with relatively U-closed common-root
images on both sides (and positive original function input-root
arity): free-stable input/domain, output-soundness, cross-pattern
masks, and injectivity come from their independent transfer lemmas;
the previously missing SAME-VERTEX original/split value coherence
uses the exact-joint-tagged split-closed seam theorem.

The free-amalgam result is CONDITIONAL. It does not prove every
finite diagram of this class has such a closed-seam free amalgam,
does not prove the required ordered partite sparsening preserves
the class, and does not decode arbitrary noncanonical structures
to original native functional targets. Neither a global hull nor
any new output vertex is inserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- All target-normality conditions currently verified to be
exact-weak hereditary and (under joint-U-closed seam hypotheses)
stable under true FULL joint free amalgamation. This is a
PROPOSITION about the ACTUAL relational joint-tagged structure,
not a constructor of missing function outputs or an assertion
that those outputs are uniquely decodable in all weak tests. -/
structure HybridJointTargetNormal
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop where
  exactTags : HasExactJointRootTags C
  coherent : HybridExactWeakCoherent (splitMaskJointRootReduct C)
  positive : HybridPositiveOutputSound (splitMaskJointRootReduct C)
  originalMasks : HybridOldMaskPatternTransport (splitMaskJointRootReduct C)
  injectiveDomains : HybridActiveDomainRootInjective (splitMaskJointRootReduct C)

/-- Every FINITE genuinely native partite source has all the
independent normality invariants on the same exact vertex set,
including its canonical full joint closure tags. -/
theorem canonicalHybrid_jointTargetNormal
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointTargetNormal
      (splitMaskJointRootExpansion A.splitMaskHybrid) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact splitMaskJointRootExpansion_hasExactJointRootTags
      A.splitMaskHybrid
  · exact canonicalHybrid_exactWeakCoherent A
  · exact canonicalHybrid_positiveOutputSound A
  · exact canonicalHybrid_oldMaskPatternTransport A
  · exact canonicalHybrid_activeDomainRootInjective A

/-- All bundled normality conditions persist on the LITERAL
ambient weak-induced set S: an OLD active domain mask may
survive even if its complete output tuple disappears, and
the conditional visible-value law handles exactly that case.
No output is inserted. -/
theorem HybridJointTargetNormal.induce
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointTargetNormal C) (S : Set V) :
    HybridJointTargetNormal (C.induce S) := by
  refine ⟨h.exactTags.induce S, ?_, ?_, ?_, ?_⟩
  · exact h.coherent.induce S
  · exact h.positive.induce S
  · exact h.originalMasks.induce S
  · exact h.injectiveDomains.induce S

/-- A TRUE FULL free amalgam of ACTUAL joint-tagged NORMAL
relational Pictures is again NORMAL if the common-root images
on both sides are relatively U-closed for the actual JOINT rules.
All active split input roots must have positive size.

The statement requires the full relational diagram and the
relative closedness of the actual seam as DATA. It is NOT a
standalone strong-amalgamation assertion or a finite-family
Ramsey/sparsening theorem for the constrained target class. -/
theorem HybridJointTargetNormal.freeAmalgam_of_jointClosedSeams
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskJointRootLanguage Parts) H}
    {Left : RelStructure (L.splitMaskJointRootLanguage Parts) E}
    {Right : RelStructure (L.splitMaskJointRootLanguage Parts) F}
    {Whole : RelStructure (L.splitMaskJointRootLanguage Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hPositive :
      ∀ p : FunctionInputPattern (L.outputPartIndexed Parts),
        0 < p.rootSize)
    (hRoot : HybridJointTargetNormal Root)
    (hLeft : HybridJointTargetNormal Left)
    (hRight : HybridJointTargetNormal Right)
    (hClosedLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL))
    (hClosedRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR)) :
    HybridJointTargetNormal Whole := by
  have hBaseFree : IsFreeAmalgam
      sL.splitMaskJointRootReduct sR.splitMaskJointRootReduct
      iL.splitMaskJointRootReduct iR.splitMaskJointRootReduct :=
    hFree.splitMaskJointRootReduct
  have hVisibleAndExact :
      HybridVisibleWholeSplitAgreement
        (splitMaskJointRootReduct Whole) ∧
      HasExactJointRootTags Whole :=
    HybridVisibleWholeSplitAgreement.jointTaggedFreeAmalgam_of_closedSeams
      hFree hPositive
      hLeft.exactTags hRight.exactTags
      hLeft.positive hRight.positive
      hLeft.injectiveDomains hRight.injectiveDomains
      hLeft.coherent.2 hRight.coherent.2
      hClosedLeft hClosedRight
  refine ⟨hVisibleAndExact.2, ?_, ?_, ?_, ?_⟩
  · exact ⟨HybridWeakInputCoherent.freeAmalgam hBaseFree
      hRoot.coherent.1 hLeft.coherent.1 hRight.coherent.1,
      hVisibleAndExact.1⟩
  · exact HybridPositiveOutputSound.freeAmalgam hBaseFree
      hLeft.positive hRight.positive
  · exact HybridOldMaskPatternTransport.freeAmalgam hBaseFree
      hLeft.originalMasks hRight.originalMasks
  · exact HybridActiveDomainRootInjective.freeAmalgam hBaseFree
      hLeft.injectiveDomains hRight.injectiveDomains

/-- Construct a NORMAL full relational amalgam over an ACTUAL
joint-U-closed seam by using the standard verified concrete
relational free-attachment object, with no extra vertices beyond
the ordinary relational pushout.

This is existence for the specified `U`-closed-root embeddings,
NOT unrestricted strong AP on arbitrary weak/partite embeddings:
the common-root images must already be relatively U-closed in
both input structures, and closure of the canonical side maps
in the new whole is not asserted by this theorem. -/
theorem HybridJointTargetNormal.exists_freeAmalgam_of_jointClosedRoot
    {H E F : Type w}
    (Root : RelStructure (L.splitMaskJointRootLanguage Parts) H)
    (Left : RelStructure (L.splitMaskJointRootLanguage Parts) E)
    (Right : RelStructure (L.splitMaskJointRootLanguage Parts) F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hPositive :
      ∀ p : FunctionInputPattern (L.outputPartIndexed Parts),
        0 < p.rootSize)
    (hRoot : HybridJointTargetNormal Root)
    (hLeft : HybridJointTargetNormal Left)
    (hRight : HybridJointTargetNormal Right)
    (hClosedLeft : IsUSubstructure
      (L.splitMaskJointClosureRules Parts)
      Left (Set.range sL))
    (hClosedRight : IsUSubstructure
      (L.splitMaskJointClosureRules Parts)
      Right (Set.range sR)) :
    ∃ (W : Type w)
      (Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W)
      (iL : Embedding Left Whole) (iR : Embedding Right Whole),
      IsFreeAmalgam sL sR iL iR ∧ HybridJointTargetNormal Whole := by
  let W := FreeAmalgam.Vertex Root Left Right sL sR
  let Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W :=
    FreeAmalgam.amalgam Root Left Right sL sR
  let iL : Embedding Left Whole :=
    FreeAmalgam.leftEmbedding Root Left Right sL sR
  let iR : Embedding Right Whole :=
    FreeAmalgam.rightEmbedding Root Left Right sL sR
  have hFree : IsFreeAmalgam sL sR iL iR :=
    FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  exact ⟨W, Whole, iL, iR, hFree,
    HybridJointTargetNormal.freeAmalgam_of_jointClosedSeams
      hFree hPositive hRoot hLeft hRight hClosedLeft hClosedRight⟩

end StructuralRamsey.RelStructure
