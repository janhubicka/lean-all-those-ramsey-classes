import AllThoseRamseyClasses.Published.TrackEHybridSplitOutputPatternTransport
import AllThoseRamseyClasses.Published.TrackEHybridNoDefinedEmptyMask
import AllThoseRamseyClasses.Published.TrackEJointClosedNormalStrongAmalgam
import PartiteConstruction.Ramsey.CompatibleClassCompletion

/-!
# Track E2: a strong-amalgamation class with native decoder soundness guards

The previously certified U-CLOSED normal JOINT hybrid target class
has finite strong amalgamation under FULL embeddings. For future
native functional decoding, two further invariants are necessary:
1. an active ORIGINAL complete mask must never have zero output
   width (defined-empty partial values are not native values);
2. positive singleton split output tuples on distinct injective
   presentations of the SAME primitive input must name the SAME
   actual output vertex, not merely its output part.

The first law was merged as `HybridJointNoEmptyNormal`; the second
is the independently formalized `HybridSplitOutputPatternTransport`.
This module packages both into `HybridJointNativeDecoderNormal`
and proves literal exact weak heredity and closed-seam free stability.

It then proves that the U-CLOSED part of this strengthened normal
target class again has a concrete FINITE STRONG FREE AMALGAM over
any FULL embedding of a class member, by REUSING the verified
`HybridJointTargetClosed.exists_finite_closedAmalgam` object.
Every added invariant is preserved by that SAME pushout: there
are no new or recomputed output witnesses and no hull expansion.

Finally we export the existing corrected 2019 finite strong
amalgamation contract `HasFiniteStrongAmalgamation` for this
strictly stronger U-closed decoder-normal relational class.

This is NOT the missing finite-family sparse ordered Ramsey
construction in the class, nor a proof of arbitrary weak-picture
U-closedness or a fully faithful native decoder. The latter
requires the separate complete-fibre and domain/value theorems.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Precise necessary native-decoder normality for ACTUAL JOINT
hybrid relational Pictures: existing exact-tag, domain, part and
visible-value coherence, absence of defined-empty ORIGINAL masks,
and positive split SAME-VERTEX transport across all input patterns.
No claim of a functional decoder is part of this definition. -/
structure HybridJointNativeDecoderNormal
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop where
  core : HybridJointNoEmptyNormal C
  splitOutput :
    HybridSplitOutputPatternTransport (splitMaskJointRootReduct C)

/-- Every FINITE genuine native transversal functional partite
System satisfies the full decoder-normality package on its
canonical JOINT tagged presentation, without new vertices. -/
theorem canonicalHybrid_jointNativeDecoderNormal
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointNativeDecoderNormal
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  ⟨canonicalHybrid_jointNoEmptyNormal A,
    canonicalHybrid_splitOutputPatternTransport A⟩

/-- All strict decoder-normality clauses survive any LITERAL
weak vertex restriction, including cuts which delete whole
output tuples while retaining active OLD domain records. -/
theorem HybridJointNativeDecoderNormal.induce
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativeDecoderNormal C) (S : Set V) :
    HybridJointNativeDecoderNormal (C.induce S) :=
  ⟨h.core.induce S, h.splitOutput.induce S⟩

/-- TRUE FULL relational free amalgams over relatively joint-U-closed
overlap images preserve the entire strict decoder-normality class.
Positive input-root size remains explicit because this lemma does
not require primitive function arity positivity. -/
theorem HybridJointNativeDecoderNormal.freeAmalgam_of_jointClosedSeams
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
    (hRoot : HybridJointNativeDecoderNormal Root)
    (hLeft : HybridJointNativeDecoderNormal Left)
    (hRight : HybridJointNativeDecoderNormal Right)
    (hClosedLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL))
    (hClosedRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR)) :
    HybridJointNativeDecoderNormal Whole := by
  refine ⟨?_, ?_⟩
  · exact HybridJointNoEmptyNormal.freeAmalgam_of_jointClosedSeams
      hFree hPositive hRoot.core hLeft.core hRight.core
      hClosedLeft hClosedRight
  · exact HybridSplitOutputPatternTransport.freeAmalgam
      hFree.splitMaskJointRootReduct
      hLeft.splitOutput hRight.splitOutput

/-- The U-CLOSED subclass of strict decoder-normal joint
relational Pictures. All quantification is over literal FULL
relational structures, not intrinsic weak partial-function cuts. -/
def HybridJointNativeDecoderClosed
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop :=
  IsUClosed (L.splitMaskJointClosureRules Parts) C ∧
  HybridJointNativeDecoderNormal C

/-- Every finite genuine native System has a CLOSED
decoder-normal canonical JOINT full-root presentation. -/
theorem canonicalHybrid_jointNativeDecoderClosed
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointNativeDecoderClosed
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  ⟨A.splitMaskJointRoot_isUClosed,
    canonicalHybrid_jointNativeDecoderNormal A⟩

/-- Exact U-substructures of closed decoder-normal targets stay
both U-CLOSED and strict decoder-normal. Arbitrary weak-induced
subsets retain normality but may fail U-closedness. -/
theorem HybridJointNativeDecoderClosed.induce_of_USubstructure
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativeDecoderClosed C)
    (S : Set V)
    (hS : IsUSubstructure (L.splitMaskJointClosureRules Parts) C S) :
    HybridJointNativeDecoderClosed (C.induce S) :=
  ⟨h.1.induce_of_USubstructure S hS, h.2.induce S⟩

/-- The concrete finite FULL relational free pushout of any
three closed strict decoder-normal class members is again
closed and decoder-normal, and both side copies have
relatively U-closed images in the same whole. This is the
literal finite STRONG amalgam, with the intended overlap. -/
theorem HybridJointNativeDecoderClosed.exists_finite_closedAmalgam
    {H E F : Type w} [Finite E] [Finite F]
    (Root : RelStructure (L.splitMaskJointRootLanguage Parts) H)
    (Left : RelStructure (L.splitMaskJointRootLanguage Parts) E)
    (Right : RelStructure (L.splitMaskJointRootLanguage Parts) F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hPos : L.PositiveFuncArity)
    (hRoot : HybridJointNativeDecoderClosed Root)
    (hLeft : HybridJointNativeDecoderClosed Left)
    (hRight : HybridJointNativeDecoderClosed Right) :
    ∃ (W : Type w), Finite W ∧
      ∃ (Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W)
        (iL : Embedding Left Whole) (iR : Embedding Right Whole),
        IsFreeAmalgam sL sR iL iR ∧
        HybridJointNativeDecoderClosed Whole ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iL) ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iR) := by
  let nRoot : HybridJointTargetClosed Root :=
    ⟨hRoot.1, hRoot.2.core.normal⟩
  let nLeft : HybridJointTargetClosed Left :=
    ⟨hLeft.1, hLeft.2.core.normal⟩
  let nRight : HybridJointTargetClosed Right :=
    ⟨hRight.1, hRight.2.core.normal⟩
  obtain ⟨W, hFinite, Whole, iL, iR,
      hFree, hWhole, hSideLeft, hSideRight⟩ :=
    HybridJointTargetClosed.exists_finite_closedAmalgam
      Root Left Right sL sR hPos nRoot nLeft nRight
  have hSeamLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL) :=
    sL.range_isUSubstructure hRoot.1 hLeft.1
  have hSeamRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR) :=
    sR.range_isUSubstructure hRoot.1 hRight.1
  have hDecoderWhole : HybridJointNativeDecoderNormal Whole :=
    HybridJointNativeDecoderNormal.freeAmalgam_of_jointClosedSeams
      hFree (fun p => hPos.splitPatternRootPositive p)
      hRoot.2 hLeft.2 hRight.2 hSeamLeft hSeamRight
  exact ⟨W, hFinite, Whole, iL, iR, hFree,
    ⟨hWhole.1, hDecoderWhole⟩, hSideLeft, hSideRight⟩

/-- The finite strong-amalgamation class of CLOSED strict
decoder-normal joint Pictures, in the exact class API used by
the corrected 2019 local completion and Ramsey framework. -/
def jointNativeDecoderClosedClass :
    StructureClass (L := L.splitMaskJointRootLanguage Parts) :=
  fun C => HybridJointNativeDecoderClosed C

/-- The standard 2019 finite strong-amalgamation contract for
the exact class of U-CLOSED strict decoder-normal JOINT targets.
The witness is a concrete finite free pushout with no extra
identifications beyond the root and no generated closure hull.

Neither local completions nor ordered sparse Ramsey existence
are consequences of this theorem. -/
theorem jointNativeDecoderClosedClass_hasFiniteStrongAmalgamation
    (hPos : L.PositiveFuncArity) :
    HasFiniteStrongAmalgamation
      (jointNativeDecoderClosedClass (L := L) (Parts := Parts)) := by
  intro H E F _ _ _ Root Left Right hRoot hLeft hRight sL sR
  obtain ⟨W, hW, Whole, iL, iR, hFree, hWhole, _, _⟩ :=
    HybridJointNativeDecoderClosed.exists_finite_closedAmalgam
      Root Left Right sL sR hPos hRoot hLeft hRight
  refine ⟨W, hW, Whole, hWhole, iL, iR, ?_, ?_⟩
  · intro d
    exact (hFree.overlap (sL d) (sR d)).mpr
      ⟨d, rfl, rfl⟩
  · intro a b hab
    exact (hFree.overlap a b).mp hab

end StructuralRamsey.RelStructure
