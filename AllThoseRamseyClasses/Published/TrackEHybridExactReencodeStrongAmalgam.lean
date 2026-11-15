import AllThoseRamseyClasses.Published.TrackEHybridNativePartiteSystem
import AllThoseRamseyClasses.Published.TrackEHybridOriginalMaskDomainSaturation
import AllThoseRamseyClasses.Published.TrackEHybridPrimitiveRelationCopyCoherence
import AllThoseRamseyClasses.Published.TrackEHybridInnerTagNormality
import PartiteConstruction.Ramsey.CompatibleClassCompletion

/-!
# Track E2: the exact-re-encoding normal target class has finite strong AP

The joint hybrid language has THREE tag levels plus several
independently named domain/relation encodings of the same native
functional data. The previously certified `HybridJointNativePartiteNormal`
class decodes to an actual genuine native FunctionalPartite.System
on precisely the original vertex carrier, but it does not
guarantee that the FULL noncanonical hybrid Picture equals the
canonical re-encoding of that decoded System.

Three further independent necessary guards are:
1. every ORIGINAL complete-mask domain is saturated under
   permutations of its set of output PARTS;
2. the ORIGINAL and SPLIT copies of each primitive RELATION
   have exactly the same tuples;
3. the nested OLD complete-mask tags and the nested singleton
   split pattern tags have their canonical full-root semantics.

The exact semantics of the new OUTER JOINT tags is already part
of the underlying strict normality package. This module bundles
all those requirements into ONE literal noncanonical target class
`HybridJointExactReencodeNormal`, valid for genuine native sources,
exact-weak hereditary, and preserved by FULL free amalgamation
over relatively joint-U-closed seams. The proof reuses each
separately verified component-preservation theorem, without
inserting any new vertex, function output, tag or closure hull.

The joint-U-CLOSED subclass then has concrete FINITE STRONG
AMALGAMATION, by reusing the established closed native-partite
free-amalgam object and certifying its three extra guards on
the SAME pushout. Both full side embeddings have relatively
joint-U-closed images and overlap exactly on the prescribed
root. Finally we export the standard corrected 2019
`HasFiniteStrongAmalgamation` class interface.

CAUTION: this is the class designed for exact native re-encoding,
NOT the equality of every Picture in this class with its
canonical native encoding. That requires the remaining
OLD/split re-encoding lemmas and their exact tag-gluing proof.
Most importantly, finite strong AP alone does NOT establish
that the two-pass ordered sparse Ramsey construction preserves
this strengthened class, which remains a separate main gate.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- One explicit package of ALL currently identified necessary
normalization guards for faithful re-encoding of an ACTUAL
JOINT-tagged hybrid relational Picture, including primitive
relation copy synchronization and two INNER tag families. -/
structure HybridJointExactReencodeNormal
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop where
  native : HybridJointNativePartiteNormal C
  maskSaturated :
    HybridOriginalMaskDomainSaturated (splitMaskJointRootReduct C)
  primitiveCopies :
    HybridPrimitiveRelationCopiesAgree (splitMaskJointRootReduct C)
  innerTags :
    HybridInnerTagsNormal (splitMaskJointRootReduct C)

/-- Every finite genuinely native functional partite System has
all strengthened exact re-encoding guards on exactly its
canonical tagged hybrid source vertices. -/
theorem canonicalHybrid_jointExactReencodeNormal
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointExactReencodeNormal
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  ⟨canonicalHybrid_jointNativePartiteNormal A,
   canonicalHybrid_originalMaskDomainSaturated A,
   canonicalHybrid_primitiveRelationCopiesAgree A,
   canonicalHybrid_innerTagsNormal A⟩

/-- All exact target-normality guards are inherited by EVERY
literal induced weak vertex test, even if a complete output
tuple is clipped or the weak subset fails JOINT U-closedness. -/
theorem HybridJointExactReencodeNormal.induce
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointExactReencodeNormal C)
    (S : Set V) :
    HybridJointExactReencodeNormal (C.induce S) :=
  ⟨h.native.induce S, h.maskSaturated.induce S,
   h.primitiveCopies.induce S, h.innerTags.induce S⟩

/-- Full relational free amalgamation over ACTUAL relatively
JOINT-U-closed root images preserves EVERY strengthened
exact re-encoding guard, including mask permutation
saturation, the two primitive relation copies, and the
two independent nested canonical tag interpretations.

The common root must satisfy the native partite normality
clauses needed for the cross-side SAME-VERTEX whole/split
agreement; the three extra guards are side-free-stable.
No arbitrary weak-source U-closedness is asserted. -/
theorem HybridJointExactReencodeNormal.freeAmalgam_of_jointClosedSeams
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskJointRootLanguage Parts) H}
    {Left : RelStructure (L.splitMaskJointRootLanguage Parts) E}
    {Right : RelStructure (L.splitMaskJointRootLanguage Parts) F}
    {Whole : RelStructure (L.splitMaskJointRootLanguage Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hPositive : ∀ p : FunctionInputPattern
      (L.outputPartIndexed Parts), 0 < p.rootSize)
    (hRoot : HybridJointExactReencodeNormal Root)
    (hLeft : HybridJointExactReencodeNormal Left)
    (hRight : HybridJointExactReencodeNormal Right)
    (hClosedLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL))
    (hClosedRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR)) :
    HybridJointExactReencodeNormal Whole := by
  have hBaseFree := hFree.splitMaskJointRootReduct
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact HybridJointNativePartiteNormal.freeAmalgam_of_jointClosedSeams
      hFree hPositive hRoot.native hLeft.native hRight.native
      hClosedLeft hClosedRight
  · exact HybridOriginalMaskDomainSaturated.freeAmalgam
      hBaseFree hLeft.maskSaturated hRight.maskSaturated
  · exact HybridPrimitiveRelationCopiesAgree.freeAmalgam
      hBaseFree hLeft.primitiveCopies hRight.primitiveCopies
  · exact HybridInnerTagsNormal.freeAmalgam
      hBaseFree hLeft.innerTags hRight.innerTags

/-- The U-closed subclass of exact-re-encoding-normal
JOINT hybrid Pictures, for the corrected 2019 `U`-closure
and finite strong-amalgamation class interfaces. -/
def HybridJointExactReencodeClosed
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop :=
  IsUClosed (L.splitMaskJointClosureRules Parts) C ∧
  HybridJointExactReencodeNormal C

/-- Canonical finite native partite Systems live in the
strengthened U-closed exact-re-encoding class. -/
theorem canonicalHybrid_jointExactReencodeClosed
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointExactReencodeClosed
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  ⟨A.splitMaskJointRoot_isUClosed,
   canonicalHybrid_jointExactReencodeNormal A⟩

/-- Exact relatively joint-U-closed weak substructures retain
BOTH the closure property and every strengthened native
re-encoding normality invariant. -/
theorem HybridJointExactReencodeClosed.induce_of_USubstructure
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointExactReencodeClosed C)
    (S : Set V)
    (hS : IsUSubstructure (L.splitMaskJointClosureRules Parts) C S) :
    HybridJointExactReencodeClosed (C.induce S) :=
  ⟨h.1.induce_of_USubstructure S hS, h.2.induce S⟩

/-- The U-closed exact-re-encoding class has a concrete finite
STRONG FREE amalgam over every FULL embedding of class members.
Both resulting full side embeddings have relatively U-closed
images, and the side copies overlap on exactly the common root.
The original carrier is the ordinary finite free pushout: no
generated hull, extra vertex or function completion is used. -/
theorem HybridJointExactReencodeClosed.exists_finite_closedAmalgam
    {H E F : Type w} [Finite E] [Finite F]
    (Root : RelStructure (L.splitMaskJointRootLanguage Parts) H)
    (Left : RelStructure (L.splitMaskJointRootLanguage Parts) E)
    (Right : RelStructure (L.splitMaskJointRootLanguage Parts) F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hPos : L.PositiveFuncArity)
    (hRoot : HybridJointExactReencodeClosed Root)
    (hLeft : HybridJointExactReencodeClosed Left)
    (hRight : HybridJointExactReencodeClosed Right) :
    ∃ (W : Type w), Finite W ∧
      ∃ (Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W)
        (iL : Embedding Left Whole) (iR : Embedding Right Whole),
        IsFreeAmalgam sL sR iL iR ∧
        HybridJointExactReencodeClosed Whole ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iL) ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iR) := by
  let hNR : HybridJointNativePartiteClosed Root :=
    ⟨hRoot.1, hRoot.2.native⟩
  let hNL : HybridJointNativePartiteClosed Left :=
    ⟨hLeft.1, hLeft.2.native⟩
  let hNQ : HybridJointNativePartiteClosed Right :=
    ⟨hRight.1, hRight.2.native⟩
  obtain ⟨W, hFinite, Whole, iL, iR,
      hFree, hWhole, hSideLeft, hSideRight⟩ :=
    HybridJointNativePartiteClosed.exists_finite_closedAmalgam
      Root Left Right sL sR hPos hNR hNL hNQ
  have hSeamLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL) :=
    sL.range_isUSubstructure hRoot.1 hLeft.1
  have hSeamRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR) :=
    sR.range_isUSubstructure hRoot.1 hRight.1
  have hExact : HybridJointExactReencodeNormal Whole :=
    HybridJointExactReencodeNormal.freeAmalgam_of_jointClosedSeams
      hFree (fun p => hPos.splitPatternRootPositive p)
      hRoot.2 hLeft.2 hRight.2 hSeamLeft hSeamRight
  exact ⟨W, hFinite, Whole, iL, iR,
    hFree, ⟨hWhole.1, hExact⟩, hSideLeft, hSideRight⟩

/-- The actual `U`-closed exact native re-encoding NORMAL class
as a carrier-polymorphic `StructureClass` for the corrected
2019 Ramsey/finite-strong-amalgamation machinery. -/
def jointExactReencodeClosedClass :
    StructureClass (L := L.splitMaskJointRootLanguage Parts) :=
  fun C => HybridJointExactReencodeClosed C

/-- The standard corrected 2019 finite strong-amalgamation
contract for the U-closed exact-re-encoding normal target
class. The witness is a genuine finite FULL relational free
amalgam with exact overlap and relatively U-closed side maps.

This is NOT yet a proof of the class's Ramsey property or
of preservation by two-pass ordered sparse partite attachment.
Additional local completion/forbidden-configuration arguments
are still needed. -/
theorem jointExactReencodeClosedClass_hasFiniteStrongAmalgamation
    (hPos : L.PositiveFuncArity) :
    HasFiniteStrongAmalgamation
      (jointExactReencodeClosedClass (L := L) (Parts := Parts)) := by
  intro H E F _ _ _ Root Left Right hRoot hLeft hRight sL sR
  obtain ⟨W, hFinite, Whole, iL, iR, hFree, hWhole, _, _⟩ :=
    HybridJointExactReencodeClosed.exists_finite_closedAmalgam
      Root Left Right sL sR hPos hRoot hLeft hRight
  refine ⟨W, hFinite, Whole, hWhole, iL, iR, ?_, ?_⟩
  · intro d
    exact (hFree.overlap (sL d) (sR d)).mpr
      ⟨d, rfl, rfl⟩
  · intro a b hab
    exact (hFree.overlap a b).mp hab

end StructuralRamsey.RelStructure
