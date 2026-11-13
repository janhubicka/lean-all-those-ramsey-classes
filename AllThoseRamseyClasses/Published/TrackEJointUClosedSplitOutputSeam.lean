import AllThoseRamseyClasses.Published.TrackEHybridMixedRootSplitClosedAgreement
import AllThoseRamseyClasses.Published.TrackEJointHybridFullRootRules
import PartiteConstruction.Ramsey.ClosureDescription2019

/-!
# Track E2: a relatively joint-U-closed overlap is split-output closed

The mixed-root whole/split coherence lemma requires the concrete
common-root embeddings to be closed under singleton split outputs.
This module derives that condition from actual relative U-closure in
the CANONICAL JOINT full-hybrid-root tagged structure.

For a positive distinct-input equality pattern and an already
visible split output tuple, exact output→domain soundness and
injectivity of active domain roots allow us to pull back the FULL
hybrid relational input-root pattern on its precise `Fin n` carrier.
The corresponding fresh JOINT split closure tag is then literally
present on the same tuple (no output invented). Relative
U-substructure closure forces the last vertex into the common-root
image when the full input prefix lies there.

The theorem is conditional on:
* strictly positive distinct-root sizes for the relevant function
  input patterns (nullary original functions are a separate case);
* positive split output tuples implying their split input domains;
* injective active split input domain tuples; and
* literal relative U-closure of the common-root image in the
  canonical JOINT tagged SIDE, not just in the untagged reduct.

The hypotheses are deliberate: arbitrary relational Pictures may
contain a spurious noninjective domain, a positive output without
its domain, or missing exact full-root tags. No arbitrary-target
decoder, missing-value completion, or global finite-family E2
Ramsey conclusion is asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Relative closure under the genuine JOINT full-root split tags
forces the common root to contain every already visible split
output over its input vertices. The precise FULL hybrid input-root
relational structure is used as the tag's root; it is not replaced
by its old-domain or unary-part reduct. -/
theorem HybridSplitOutputClosedAt.ofJointRootUSubstructure
    {H S : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Side : RelStructure (L.splitMaskHybrid Parts) S}
    (e : Embedding Root Side)
    (hPositive : ∀ p : FunctionInputPattern
        (L.outputPartIndexed Parts), 0 < p.rootSize)
    (hDomainSound :
      ∀ (p : FunctionInputPattern (L.outputPartIndexed Parts))
        (t : Fin (p.rootSize + 1) → S),
        Side.rel (hybridSplitOutputSymbol p) t →
        Side.rel (hybridSplitDomainSymbol p)
          (fun i : Fin p.rootSize => t i.castSucc))
    (hDomainInjective :
      ∀ (p : FunctionInputPattern (L.outputPartIndexed Parts))
        (root : Fin p.rootSize → S),
        Side.rel (hybridSplitDomainSymbol p) root →
        Function.Injective root)
    (hUS : IsUSubstructure (L.splitMaskJointClosureRules Parts)
      (splitMaskJointRootExpansion Side) (Set.range e)) :
    HybridSplitOutputClosedAt e := by
  classical
  intro p t hPos hInput
  let root : Fin p.rootSize → S :=
    fun i => t i.castSucc
  have hDomain : Side.rel (hybridSplitDomainSymbol p) root :=
    hDomainSound p t hPos
  have hInj : Function.Injective root :=
    hDomainInjective p root hDomain
  let actualRoot :
      RelStructure (L.splitMaskHybrid Parts) (Fin p.rootSize) := {
    rel R xs := Side.rel R (root ∘ xs)
  }
  let rootEmbedding : Embedding actualRoot Side := {
    toFun := root
    injective := hInj
    map_rel_iff := by
      intro R xs
      rfl
  }
  have hDomainRoot :
      actualRoot.rel (hybridSplitDomainSymbol p) id := by
    change Side.rel (hybridSplitDomainSymbol p) (root ∘ id)
    simpa only [Function.comp_apply, id_eq] using hDomain
  let pattern : SplitMaskFullRootPattern L Parts := {
    input := p
    positive := hPositive p
    root := actualRoot
    hasDomain := hDomainRoot
  }
  have hTagged :
      (splitMaskJointRootExpansion Side).rel
        (.inr (.inl pattern)) t := by
    change Side.rel (hybridSplitOutputSymbol p) t ∧
      ∃ g : Embedding actualRoot Side,
        ∀ i : Fin p.rootSize, t i.castSucc = g i
    exact ⟨hPos, rootEmbedding, fun _ => rfl⟩
  have hRule :
      pattern.jointClosureRule ∈
        (L.splitMaskJointClosureRules Parts) := by
    exact Or.inl ⟨pattern, rfl⟩
  have hRootIn : ∀ i : Fin pattern.input.rootSize,
      t (i.castLE pattern.jointClosureRule.rootLE) ∈ Set.range e := by
    intro i
    change t i.castSucc ∈ Set.range e
    obtain ⟨z, hz⟩ := hInput i
    exact ⟨z, hz.symm⟩
  have hOutputIn : t (Fin.last p.rootSize) ∈ Set.range e :=
    hUS pattern.jointClosureRule hRule t hTagged hRootIn
      (Fin.last p.rootSize)
  obtain ⟨z, hz⟩ := hOutputIn
  exact ⟨z, hz.symm⟩

/-- One useful explicit sufficient condition for free-amalgam
preservation of ORIGINAL/split same-output-vertex agreement:
both sides are separately source-coherent and their overlap
embeddings are relatively closed under the exact canonical
JOINT full-hybrid-root U-rules. The positive domain-soundness and
root-injectivity conditions are kept visible for noncanonical
sources, where they cannot be silently inferred. -/
theorem HybridVisibleWholeSplitAgreement.freeAmalgam_of_jointUSubstructure
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridVisibleWholeSplitAgreement Left)
    (hRight : HybridVisibleWholeSplitAgreement Right)
    (hPositive : ∀ p : FunctionInputPattern
        (L.outputPartIndexed Parts), 0 < p.rootSize)
    (hLeftDomain :
      ∀ (p : FunctionInputPattern (L.outputPartIndexed Parts))
        (t : Fin (p.rootSize + 1) → E),
        Left.rel (hybridSplitOutputSymbol p) t →
        Left.rel (hybridSplitDomainSymbol p)
          (fun i : Fin p.rootSize => t i.castSucc))
    (hRightDomain :
      ∀ (p : FunctionInputPattern (L.outputPartIndexed Parts))
        (t : Fin (p.rootSize + 1) → F),
        Right.rel (hybridSplitOutputSymbol p) t →
        Right.rel (hybridSplitDomainSymbol p)
          (fun i : Fin p.rootSize => t i.castSucc))
    (hLeftInjective :
      ∀ (p : FunctionInputPattern (L.outputPartIndexed Parts))
        (root : Fin p.rootSize → E),
        Left.rel (hybridSplitDomainSymbol p) root →
        Function.Injective root)
    (hRightInjective :
      ∀ (p : FunctionInputPattern (L.outputPartIndexed Parts))
        (root : Fin p.rootSize → F),
        Right.rel (hybridSplitDomainSymbol p) root →
        Function.Injective root)
    (hClosedLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        (splitMaskJointRootExpansion Left) (Set.range sL))
    (hClosedRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        (splitMaskJointRootExpansion Right) (Set.range sR)) :
    HybridVisibleWholeSplitAgreement Whole := by
  apply HybridVisibleWholeSplitAgreement.freeAmalgam_of_splitClosedRoot
    hFree hLeft hRight
  · exact HybridSplitOutputClosedAt.ofJointRootUSubstructure
      sL hPositive hLeftDomain hLeftInjective hClosedLeft
  · exact HybridSplitOutputClosedAt.ofJointRootUSubstructure
      sR hPositive hRightDomain hRightInjective hClosedRight

end StructuralRamsey.RelStructure
