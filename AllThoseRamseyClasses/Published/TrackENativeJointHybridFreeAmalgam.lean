import AllThoseRamseyClasses.Published.TrackENativeOldMaskWholeFree
import AllThoseRamseyClasses.Published.TrackEBaseHybridComponentFreeAmalgam
import AllThoseRamseyClasses.Published.TrackEJointHybridFreeAmalgam
import PartiteConstruction.Functional.OutputPartSplitFreeAmalgam
import PartiteConstruction.Functional.NativePatternGraphFreeAmalgam2019

/-!
# Track E2: TRUE native functional free attachments preserve the complete JOINT hybrid source

Two independent components of the canonical partite source now have
full native free-attachment descriptions, on the SAME vertices:

* ORIGINAL complete whole-output mask/domain/full-root relations:
  the full native-to-OLD relation proof of Track E2 #1095/#1098;
* per-output-part singleton equality-pattern/positive graph tags:
  the already checked native free-amalgam output-part-split theorem
  followed by the pinned patternTagExpansion free-amalgam functor.

The component assembly of Track E2 #1078 combines these with unary
vertex-part predicates into a genuine relational free amalgam of
the SAME canonical base hybrid structures, and the checked joint
FULL-hybrid-root tagging free functor of #1075 adds BOTH new
split-function and complete ORIGINAL mask closure tag families.

Thus any TRUE full native functional partite free amalgam has an
actual SAME-CARRIER relational free-amalgamation diagram in the
entire JOINT hybrid tagged language, without assuming any separate
OLD or split relational freeness.

This is the missing SOURCE geometry for a prospective corrected
2019 two-pass hybrid sparse Ramsey construction. It does NOT prove
that arbitrary noncanonical hybrid target pictures are normal or
coherently decode to genuine native Systems, nor that the constrained
hybrid class is strongly amalgamable, that folded finite-family
forbidden sources have uniformly H-relative small completions, or
that the ordered Ramsey witness exists.

No generated closure hull replaces any exact weak set, and no
source-defined EHN projection is upgraded to a full embedding.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {H E F C : Type w}

/-- Every actual FULL native set-valued functional free-amalgam
diagram of genuine transversal partite Systems remains a free
amalgam of their canonical BASE hybrid (original whole-value OLD
mask tags + split singleton pattern tags + unary part labels).

The original OLD component is now derived directly from the true
native function diagram; no extra relational-freeness premise. -/
theorem nativeFreeAmalgam_baseSplitMaskHybrid
    {Root : FunctionalPartite.System L Parts H}
    {Left : FunctionalPartite.System L Parts E}
    {Right : FunctionalPartite.System L Parts F}
    {Whole : FunctionalPartite.System L Parts C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding) :
    RelStructure.IsFreeAmalgam
      (systemEmbedding_splitMaskHybrid sL)
      (systemEmbedding_splitMaskHybrid sR)
      (systemEmbedding_splitMaskHybrid iL)
      (systemEmbedding_splitMaskHybrid iR) := by
  have hOriginalTagged : RelStructure.IsFreeAmalgam
      (systemEmbedding_oldMaskTagged sL)
      (systemEmbedding_oldMaskTagged sR)
      (systemEmbedding_oldMaskTagged iL)
      (systemEmbedding_oldMaskTagged iR) :=
    nativeFreeAmalgam_originalWholeMaskTagged hFree
  have hSplitNative : Structure.IsFreeAmalgam
      sL.splitOutputParts.toEmbedding
      sR.splitOutputParts.toEmbedding
      iL.splitOutputParts.toEmbedding
      iR.splitOutputParts.toEmbedding :=
    hFree.splitOutputParts_of_partite
  have hSplitTagged : RelStructure.IsFreeAmalgam
      (systemEmbedding_splitPatternTagged sL)
      (systemEmbedding_splitPatternTagged sR)
      (systemEmbedding_splitPatternTagged iL)
      (systemEmbedding_splitPatternTagged iR) :=
    hSplitNative.taggedPatternGraph
  exact baseHybrid_freeAmalgam_of_componentFree
    sL sR iL iR hOriginalTagged hSplitTagged

/-- The SAME native FULL functional partite free attachment also
preserves the ENTIRE JOINT fresh full-hybrid-root-tagged language,
whose separate closure-rule symbol types remember the complete
combined input-root pattern of BOTH old mask and split incidence.

This is a source free-amalgam theorem only; no arbitrary target
normalization or sparse Ramsey construction is smuggled in. -/
theorem nativeFreeAmalgam_jointSplitMaskHybrid
    {Root : FunctionalPartite.System L Parts H}
    {Left : FunctionalPartite.System L Parts E}
    {Right : FunctionalPartite.System L Parts F}
    {Whole : FunctionalPartite.System L Parts C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding) :
    RelStructure.IsFreeAmalgam
      (systemEmbedding_splitMaskHybrid sL).splitMaskJointRoot
      (systemEmbedding_splitMaskHybrid sR).splitMaskJointRoot
      (systemEmbedding_splitMaskHybrid iL).splitMaskJointRoot
      (systemEmbedding_splitMaskHybrid iR).splitMaskJointRoot :=
  (nativeFreeAmalgam_baseSplitMaskHybrid hFree).splitMaskJointRoot

end AllThoseRamseyClasses.Published
