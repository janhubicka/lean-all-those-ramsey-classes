import AllThoseRamseyClasses.Published.TrackEJointNormalTargetClass
import PartiteConstruction.Ramsey.ClosureEmbeddingRange
import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion
import PartiteConstruction.Ramsey.CompatibleClassCompletion

/-!
# Track E2: a concrete finite strong amalgam of closed normal joint targets

The previously merged target-normalization theorem requires that the
two images of a common root be relatively joint-U-closed. For FULL
embeddings between U-CLOSED joint-tagged structures, these extra
hypotheses are automatic: an embedded U-closed source occupies an
exact U-substructure of a U-closed target.

Thus the class of JOINT U-CLOSED, normal hybrid relational targets
is stable under the concrete FULL relational free amalgam. The same
amalgam is itself U-CLOSED by the actual 2019 closure-amalgamation
theorem; the NORMAL predicate follows from the merged Track E2
closed-seam preservation theorem. The two side copies intersect
exactly in their prescribed root, with NO identifications of
private vertices beyond the usual relational free pushout.

We also eliminate the unusual quantification over positive input
*patterns*: positivity of primitive function arities implies
positivity of the distinct-input root of every surjective equality
pattern, even when original input coordinates repeat.

This proves a finite strong-amalgamation INTERFACE for the closed
normal JOINT RELATIONAL subclass under full embeddings. It is NOT
the as-yet missing two-pass finite-family ordered sparse Ramsey
construction, target functional decoding or a general statement
about arbitrary non-U-closed weak Picture amalgams.
-/

namespace StructuralRamsey.Language

universe u v
variable {L : Language.{u}} {Parts : Type v}

/-- Positive ORIGINAL primitive function arity forces every
surjective split input equality-pattern presentation to list at
least one distinct root coordinate. In particular repeated
primitive arguments do not destroy root positivity. -/
theorem PositiveFuncArity.splitPatternRootPositive
    (hPos : L.PositiveFuncArity)
    (p : FunctionInputPattern (L.outputPartIndexed Parts)) :
    0 < p.rootSize := by
  have hArity :
      0 < (L.outputPartIndexed Parts).funcArity p.symbol :=
    hPos p.symbol.1.down
  let a : Fin ((L.outputPartIndexed Parts).funcArity p.symbol) :=
    ⟨0, hArity⟩
  have hNonzero : p.rootSize ≠ 0 := by
    intro hz
    have q : Fin 0 := hz ▸ p.argMap a
    exact q.elim0
  exact Nat.pos_of_ne_zero hNonzero

end StructuralRamsey.Language

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The ACTUAL joint-tagged structure is both U-closed for both
full hybrid root-tag families AND normal as a hybrid presentation.
Neither predicate is inferred from mere old relation data. -/
def HybridJointTargetClosed
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop :=
  IsUClosed (L.splitMaskJointClosureRules Parts) C ∧
  HybridJointTargetNormal C

/-- Exact U-substructures of a CLOSED normal joint relational
Picture are again closed and normal, on the SAME induced vertex set.
Arbitrary weak subsets still retain normality but need not be
U-closed: relative closure is the essential hypothesis here. -/
theorem HybridJointTargetClosed.induce_of_USubstructure
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointTargetClosed C)
    (S : Set V)
    (hS : IsUSubstructure (L.splitMaskJointClosureRules Parts) C S) :
    HybridJointTargetClosed (C.induce S) :=
  ⟨h.1.induce_of_USubstructure S hS, h.2.induce S⟩

/-- Full free amalgamation preserves both genuine joint U-closedness
and the EXACT hybrid target-normality conditions when all three
inputs are U-closed and normal. The relative U-closed seam
hypotheses required by the previous E2 result are obtained from
the full embeddings rather than assumed. -/
theorem HybridJointTargetClosed.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskJointRootLanguage Parts) H}
    {Left : RelStructure (L.splitMaskJointRootLanguage Parts) E}
    {Right : RelStructure (L.splitMaskJointRootLanguage Parts) F}
    {Whole : RelStructure (L.splitMaskJointRootLanguage Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hPos : L.PositiveFuncArity)
    (hRoot : HybridJointTargetClosed Root)
    (hLeft : HybridJointTargetClosed Left)
    (hRight : HybridJointTargetClosed Right) :
    HybridJointTargetClosed Whole := by
  have hSeamLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL) :=
    sL.range_isUSubstructure hRoot.1 hLeft.1
  have hSeamRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR) :=
    sR.range_isUSubstructure hRoot.1 hRight.1
  refine ⟨hFree.isUClosed hRoot.1 hLeft.1 hRight.1, ?_⟩
  exact HybridJointTargetNormal.freeAmalgam_of_jointClosedSeams
    hFree
    (fun p => hPos.splitPatternRootPositive p)
    hRoot.2 hLeft.2 hRight.2 hSeamLeft hSeamRight

/-- Construct the TRUE FULL relational free amalgam with exactly
the usual overlap, without any new closure hull, and certify
U-closedness plus all hybrid normality invariants on that same
amalgam carrier. All embeddings are full and are given literally
by the original concrete relational free-amalgam construction. -/
theorem HybridJointTargetClosed.exists_freeAmalgam
    {H E F : Type w}
    (Root : RelStructure (L.splitMaskJointRootLanguage Parts) H)
    (Left : RelStructure (L.splitMaskJointRootLanguage Parts) E)
    (Right : RelStructure (L.splitMaskJointRootLanguage Parts) F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hPos : L.PositiveFuncArity)
    (hRoot : HybridJointTargetClosed Root)
    (hLeft : HybridJointTargetClosed Left)
    (hRight : HybridJointTargetClosed Right) :
    ∃ (W : Type w)
      (Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W)
      (iL : Embedding Left Whole) (iR : Embedding Right Whole),
      IsFreeAmalgam sL sR iL iR ∧
      HybridJointTargetClosed Whole := by
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
    HybridJointTargetClosed.freeAmalgam
      hFree hPos hRoot hLeft hRight⟩

/-- The same NORMAL U-CLOSED strong-amalgam witness can be chosen
FINITE whenever both sides have finite carriers, without any
generated output vertices or extra padding. In particular the
standard concrete relational free pushout itself is finite. -/
theorem HybridJointTargetClosed.exists_finite_freeAmalgam
    {H E F : Type w} [Finite E] [Finite F]
    (Root : RelStructure (L.splitMaskJointRootLanguage Parts) H)
    (Left : RelStructure (L.splitMaskJointRootLanguage Parts) E)
    (Right : RelStructure (L.splitMaskJointRootLanguage Parts) F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hPos : L.PositiveFuncArity)
    (hRoot : HybridJointTargetClosed Root)
    (hLeft : HybridJointTargetClosed Left)
    (hRight : HybridJointTargetClosed Right) :
    ∃ (W : Type w), Finite W ∧
      ∃ (Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W)
        (iL : Embedding Left Whole) (iR : Embedding Right Whole),
        IsFreeAmalgam sL sR iL iR ∧
        HybridJointTargetClosed Whole := by
  classical
  let W := FreeAmalgam.Vertex Root Left Right sL sR
  have hFinite : Finite W := by
    dsimp [W, FreeAmalgam.Vertex, Attachment.Vertex]
    infer_instance
  let Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W :=
    FreeAmalgam.amalgam Root Left Right sL sR
  let iL : Embedding Left Whole :=
    FreeAmalgam.leftEmbedding Root Left Right sL sR
  let iR : Embedding Right Whole :=
    FreeAmalgam.rightEmbedding Root Left Right sL sR
  have hFree : IsFreeAmalgam sL sR iL iR :=
    FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  exact ⟨W, hFinite, Whole, iL, iR, hFree,
    HybridJointTargetClosed.freeAmalgam
      hFree hPos hRoot hLeft hRight⟩

/-- The finite free-amalgam witness can be certified with
both canonical side embeddings relatively joint-U-closed in
the U-CLOSED target. Thus the actual diagram belongs to the
category of closed normal joint targets and closed full
embeddings on BOTH legs, not merely on the input root. -/
theorem HybridJointTargetClosed.exists_finite_closedAmalgam
    {H E F : Type w} [Finite E] [Finite F]
    (Root : RelStructure (L.splitMaskJointRootLanguage Parts) H)
    (Left : RelStructure (L.splitMaskJointRootLanguage Parts) E)
    (Right : RelStructure (L.splitMaskJointRootLanguage Parts) F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hPos : L.PositiveFuncArity)
    (hRoot : HybridJointTargetClosed Root)
    (hLeft : HybridJointTargetClosed Left)
    (hRight : HybridJointTargetClosed Right) :
    ∃ (W : Type w), Finite W ∧
      ∃ (Whole : RelStructure (L.splitMaskJointRootLanguage Parts) W)
        (iL : Embedding Left Whole) (iR : Embedding Right Whole),
        IsFreeAmalgam sL sR iL iR ∧
        HybridJointTargetClosed Whole ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iL) ∧
        IsUSubstructure (L.splitMaskJointClosureRules Parts)
          Whole (Set.range iR) := by
  obtain ⟨W, hFinite, Whole, iL, iR, hFree, hWhole⟩ :=
    HybridJointTargetClosed.exists_finite_freeAmalgam
      Root Left Right sL sR hPos hRoot hLeft hRight
  exact ⟨W, hFinite, Whole, iL, iR, hFree, hWhole,
    iL.range_isUSubstructure hLeft.1 hWhole.1,
    iR.range_isUSubstructure hRight.1 hWhole.1⟩

/-- The class of genuine JOINT U-CLOSED targets satisfying all
hybrid normality invariants, as a carrier-polymorphic relational
class for the abstract 2019 strong-amalgamation API. -/
def jointClosedNormalClass :
    StructureClass (L := L.splitMaskJointRootLanguage Parts) :=
  fun C => HybridJointTargetClosed C

/-- The corrected 2019 `HasFiniteStrongAmalgamation` contract
is satisfied by closed normal joint hybrid targets whenever the
original primitive functions have positive arity. The required
finite strong amalgam is the SAME concrete free pushout, and its
intersection is exactly the common root, not a larger hull.
This does NOT supply the other independent hypotheses of the
Ramsey theorem (local completions, irreducibility, etc.). -/
theorem jointClosedNormalClass_hasFiniteStrongAmalgamation
    (hPos : L.PositiveFuncArity) :
    HasFiniteStrongAmalgamation
      (jointClosedNormalClass (L := L) (Parts := Parts)) := by
  intro H E F _ _ _ Root Left Right hRoot hLeft hRight sL sR
  obtain ⟨W, hFinite, Whole, iL, iR, hFree, hWhole, _, _⟩ :=
    HybridJointTargetClosed.exists_finite_closedAmalgam
      Root Left Right sL sR hPos hRoot hLeft hRight
  refine ⟨W, hFinite, Whole, hWhole, iL, iR, ?_, ?_⟩
  · intro d
    exact (hFree.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
  · intro a b hab
    exact (hFree.overlap a b).mp hab

end StructuralRamsey.RelStructure
