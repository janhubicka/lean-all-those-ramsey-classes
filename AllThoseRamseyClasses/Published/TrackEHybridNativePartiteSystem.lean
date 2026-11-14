import AllThoseRamseyClasses.Published.TrackEHybridDecodedOldFibreTransversal
import AllThoseRamseyClasses.Published.TrackEHybridOriginalRelationPartTransversal
import AllThoseRamseyClasses.Published.TrackEHybridNoDefinedEmptyMask
import AllThoseRamseyClasses.Published.TrackEJointClosedNormalStrongAmalgam
import PartiteConstruction.Ramsey.CompatibleClassCompletion

/-!
# Track E2: a genuine native partite System from an actual hybrid Picture

The previous Track E2 proof stages show that a noncanonical JOINT
hybrid Picture may have:
* a unique unary PART predicate on EVERY vertex, including isolated;
* a complete ORIGINAL OLD output-value decoder whose positive
  value witnesses are independent of mask and input pattern;
* transversal decoded function fibres;
* a separately preserved ORIGINAL RELATIONAL tuple part guard.

The last condition is needed. A generic normal hybrid Picture
could still have an ORIGINAL primitive relation R(x,y) with the
same part on both distinct vertices; function-output normality
does not prevent that. The independent
`HybridOriginalRelationPartTransversal` predicate rules it out.

This module packages ALL these necessary conditions, constructs
an ACTUAL `FunctionalPartite.System L Parts V` on literally
the same carrier V, and verifies its native function and relation
transversality directly from the hybrid predicates.

No NEW native function is chosen: the native Structure is the
already established OLD whole-mask Option(Set) decoder followed
by the ordinary `collapseDomain`. Undefined inputs have the
native empty fibre; when strict normality and joint U-closedness
are also present, the independent OLD domain/value results
identify exactly which inputs are defined.

The strengthened PARTITE normality is source-valid, exact-weak
hereditary, and preserved by TRUE FULL joint free amalgamation
with relatively U-closed seams. Its joint-U-closed subclass
admits the same concrete finite strong free amalgam as the
previously certified core-normal class, with closed full
embeddings and precisely the prescribed overlap.

This is **not** a proof that every arbitrary sparse Picture
satisfies the extra relational part guard. Nor does a decoded
partite System necessarily re-encode the whole noncanonical
hybrid relational source without further positive graph/root
reflection. The ordered two-pass finite-family E2 Ramsey
construction remains a separate proof obligation.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The strict actual native PARTITE target-side normality package:
all no-defined-empty OLD/whole-split and input-profile laws,
positive split SAME-VERTEX cross-pattern transport, and
primitive ORIGINAL relation part-transversality. Every field
refers to the SAME joint-tagged relational Picture C. -/
structure HybridJointNativePartiteNormal
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop where
  strict : HybridJointNoEmptyNormal C
  splitOutput : HybridSplitOutputPatternTransport
    (splitMaskJointRootReduct C)
  relationPart : HybridOriginalRelationPartTransversal
    (splitMaskJointRootReduct C)

/-- Every finite genuinely native partite System has the
complete stronger partite-normality package on its exact
canonical JOINT-tagged presentation. -/
theorem canonicalHybrid_jointNativePartiteNormal
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointNativePartiteNormal
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  ⟨canonicalHybrid_jointNoEmptyNormal A,
   canonicalHybrid_splitOutputPatternTransport A,
   canonicalHybrid_originalRelationPartTransversal A⟩

/-- Exact induced weak restrictions preserve the entire
partite-normality package, but need not be U-closed or decode
with the same intrinsic weak function domain as the ambient. -/
theorem HybridJointNativePartiteNormal.induce
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativePartiteNormal C)
    (S : Set V) :
    HybridJointNativePartiteNormal (C.induce S) :=
  ⟨h.strict.induce S, h.splitOutput.induce S,
   h.relationPart.induce S⟩

/-- True FULL joint relational free amalgams over relatively
joint-U-closed seams preserve the strengthened native PARTITE
normality package. The primitive relational part guard
requires no seam condition of its own. -/
theorem HybridJointNativePartiteNormal.freeAmalgam_of_jointClosedSeams
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
    (hRoot : HybridJointNativePartiteNormal Root)
    (hLeft : HybridJointNativePartiteNormal Left)
    (hRight : HybridJointNativePartiteNormal Right)
    (hClosedLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL))
    (hClosedRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR)) :
    HybridJointNativePartiteNormal Whole := by
  refine ⟨?_, ?_, ?_⟩
  · exact HybridJointNoEmptyNormal.freeAmalgam_of_jointClosedSeams
      hFree hPositive hRoot.strict hLeft.strict hRight.strict
      hClosedLeft hClosedRight
  · exact HybridSplitOutputPatternTransport.freeAmalgam
      hFree.splitMaskJointRootReduct
      hLeft.splitOutput hRight.splitOutput
  · exact HybridOriginalRelationPartTransversal.freeAmalgam
      hFree.splitMaskJointRootReduct
      hLeft.relationPart hRight.relationPart

/-- Decode a NONCANONICAL but partite-normal JOINT hybrid Picture
to an actual NATIVE functional partite System on the SAME carrier.

The native Structure is EXACTLY the collapseDomain of the
existing ORIGINAL OLD whole-mask partial decoder. The part
map comes from the unique unary hybrid part labels, not from
choosing some output of a function. Native primitive relations
and functions use no new vertices or independent witnesses.

The complete-fibre decoder is transversal by the previously
checked decoder-output-part theorem. The independent ORIGINAL
relation part guard supplies the other partite-System axiom.
No joint U-closedness is needed to construct this object:
normality here is an exact-weak hereditary condition. -/
noncomputable def HybridJointNativePartiteNormal.toNativeSystem
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativePartiteNormal C) :
    FunctionalPartite.System L Parts V where
  toStructure :=
    ((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain
  part := h.strict.normal.coherent.1.2.2.2.partMap
  relTransversal := by
    intro R xs hRel i j hSame
    let Base : RelStructure (L.splitMaskHybrid Parts) V :=
      splitMaskJointRootReduct C
    let hParts : HybridUniqueVertexPart Base :=
      h.strict.normal.coherent.1.2.2.2
    have hRelBase :
        Base.rel (.inl (.inl (.inl R))) xs := hRel
    have hPartI :
        Base.rel (.inr (.inr (hParts.partMap (xs i))))
          (fun _ : Fin 1 => xs i) :=
      hParts.partMap_hasLabel (xs i)
    have hPartJ :
        Base.rel (.inr (.inr (hParts.partMap (xs i))))
          (fun _ : Fin 1 => xs j) := by
      rw [hSame]
      exact hParts.partMap_hasLabel (xs j)
    exact h.relationPart R xs hRelBase i j
      (hParts.partMap (xs i)) hPartI hPartJ
  funcTransversal := by
    intro F xs y z hy hz hSame
    let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
      splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C)
    let P : PartialSetStructure L V :=
      Old.wholeMaskPartialDecode
    have hPartFibre :
        PartialSetStructure.FibreTransversal P
          h.strict.normal.coherent.1.2.2.2.partMap :=
      h.strict.oldDecoder_fibreTransversal h.splitOutput
    have hyP : y ∈ (P.func F xs).getD ∅ := hy
    have hzP : z ∈ (P.func F xs).getD ∅ := hz
    cases hP : P.func F xs with
    | none =>
        have hyEmpty : y ∈ (∅ : Set V) := by
          simpa only [hP, Option.getD_none] using hyP
        exact (Set.not_mem_empty y hyEmpty).elim
    | some U =>
        have hyU : y ∈ U := by
          simpa only [hP, Option.getD_some] using hyP
        have hzU : z ∈ U := by
          simpa only [hP, Option.getD_some] using hzP
        exact hPartFibre F xs U hP y hyU z hzU hSame

/-- The underlying NATIVE function/relation structure is literally
the original `wholeMaskPartialDecode` collapsed on its same
carrier. No new function symbol or vertex was constructed. -/
theorem HybridJointNativePartiteNormal.nativeSystem_toStructure_eq
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativePartiteNormal C) :
    h.toNativeSystem.toStructure =
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain :=
  rfl

/-- The reconstructed part map is literally the UNIQUE unary
part predicate on the same original vertex set. -/
theorem HybridJointNativePartiteNormal.nativeSystem_part_eq
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativePartiteNormal C) (x : V) :
    h.toNativeSystem.part x =
      h.strict.normal.coherent.1.2.2.2.partMap x := rfl

/-- The U-closed subclass of strictly normal hybrid Pictures
that actually decode into native FUNCTIONAL PARTITE Systems. -/
def HybridJointNativePartiteClosed
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop :=
  IsUClosed (L.splitMaskJointClosureRules Parts) C ∧
  HybridJointNativePartiteNormal C

/-- Canonical finite native partite Systems lie in the strict
U-closed partite-normal relational class. -/
theorem canonicalHybrid_jointNativePartiteClosed
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointNativePartiteClosed
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  ⟨A.splitMaskJointRoot_isUClosed,
   canonicalHybrid_jointNativePartiteNormal A⟩

/-- U-closed exact induced substructures remain U-closed and
partite-normal; arbitrary exact weak cuts retain normality
but need not stay U-closed. -/
theorem HybridJointNativePartiteClosed.induce_of_USubstructure
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativePartiteClosed C)
    (S : Set V)
    (hS : IsUSubstructure (L.splitMaskJointClosureRules Parts) C S) :
    HybridJointNativePartiteClosed (C.induce S) :=
  ⟨h.1.induce_of_USubstructure S hS, h.2.induce S⟩

/-- Construct the SAME concrete FINITE strong free amalgam for
three partite-normal closed JOINT targets. All original OLD and
split output values and primitive relational part predicates
stay normal; the two full side embeddings have relatively
joint-U-closed images in the new target. -/
theorem HybridJointNativePartiteClosed.exists_finite_closedAmalgam
    {H E F : Type w} [Finite E] [Finite F]
    (Root : RelStructure (L.splitMaskJointRootLanguage Parts) H)
    (Left : RelStructure (L.splitMaskJointRootLanguage Parts) E)
    (Right : RelStructure (L.splitMaskJointRootLanguage Parts) F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hPos : L.PositiveFuncArity)
    (hRoot : HybridJointNativePartiteClosed Root)
    (hLeft : HybridJointNativePartiteClosed Left)
    (hRight : HybridJointNativePartiteClosed Right) :
    ∃ (W : Type w), Finite W ∧
      ∃ (Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W)
        (iL : Embedding Left Whole) (iR : Embedding Right Whole),
        IsFreeAmalgam sL sR iL iR ∧
        HybridJointNativePartiteClosed Whole ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iL) ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iR) := by
  let nRoot : HybridJointTargetClosed Root :=
    ⟨hRoot.1, hRoot.2.strict.normal⟩
  let nLeft : HybridJointTargetClosed Left :=
    ⟨hLeft.1, hLeft.2.strict.normal⟩
  let nRight : HybridJointTargetClosed Right :=
    ⟨hRight.1, hRight.2.strict.normal⟩
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
  have hPartiteWhole : HybridJointNativePartiteNormal Whole :=
    HybridJointNativePartiteNormal.freeAmalgam_of_jointClosedSeams
      hFree (fun p => hPos.splitPatternRootPositive p)
      hRoot.2 hLeft.2 hRight.2 hSeamLeft hSeamRight
  exact ⟨W, hFinite, Whole, iL, iR, hFree,
    ⟨hWhole.1, hPartiteWhole⟩, hSideLeft, hSideRight⟩

/-- The carrier-polymorphic U-closed PARTITE-normal relational class,
for the standard corrected 2019 finite-strong-amalgamation API. -/
def jointNativePartiteClosedClass :
    StructureClass (L := L.splitMaskJointRootLanguage Parts) :=
  fun C => HybridJointNativePartiteClosed C

/-- The U-closed strict native PARTITE decoder-normal JOINT
relational class has genuine FINITE STRONG AMALGAMATION over
all FULL embeddings of class members, under positive original
primitive function arity. The concrete witness is the same
finite free pushout with exact overlap and no generated hull.

This does not assert that arbitrary sparse ordered Ramsey
Pictures belong to the class or that it has the Ramsey property.
The finite-family two-pass 2019 endgame remains open. -/
theorem jointNativePartiteClosedClass_hasFiniteStrongAmalgamation
    (hPos : L.PositiveFuncArity) :
    HasFiniteStrongAmalgamation
      (jointNativePartiteClosedClass (L := L) (Parts := Parts)) := by
  intro H E F _ _ _ Root Left Right hRoot hLeft hRight sL sR
  obtain ⟨W, hFinite, Whole, iL, iR, hFree, hWhole, _, _⟩ :=
    HybridJointNativePartiteClosed.exists_finite_closedAmalgam
      Root Left Right sL sR hPos hRoot hLeft hRight
  refine ⟨W, hFinite, Whole, hWhole, iL, iR, ?_, ?_⟩
  · intro d
    exact (hFree.overlap (sL d) (sR d)).mpr
      ⟨d, rfl, rfl⟩
  · intro a b hab
    exact (hFree.overlap a b).mp hab

end StructuralRamsey.RelStructure
