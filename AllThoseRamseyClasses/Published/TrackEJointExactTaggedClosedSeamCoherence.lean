import AllThoseRamseyClasses.Published.TrackEJointUClosedSplitOutputSeam
import AllThoseRamseyClasses.Published.TrackEJointTagSemanticExact
import AllThoseRamseyClasses.Published.TrackEHybridPositiveOutputSound
import AllThoseRamseyClasses.Published.TrackEHybridActiveDomainRootInjective

/-!
# Track E2: actual exact-tagged joint targets inherit closed-seam output coherence

The earlier joint-U-closure argument constructed its fresh tags on the
CANONICAL joint expansion of a base hybrid relational structure. The
corrected 2019 sparse target need not itself be the canonical source
of a native functional System. The useful intermediate class is an
arbitrary JOINT-TAGGED relational Picture satisfying the independent
exact semantic tag interpretation `HasExactJointRootTags`.

This file transfers the actual tagged-side relative U-substructure
condition to the canonical expansion of the SAME underlying hybrid
reduct using equality of joint-tagged relational structures. The
already verified output->domain soundness and input-root injectivity
packages provide the other two hypotheses of the exact split seam
lemma. Consequently the original/split SAME-VERTEX positive output
agreement is retained under a genuine FULL joint-tagged free
amalgamation with relatively joint-U-closed common-root images.

No strong-amalgamation or sparsening assertion is hidden in the
statement: exact semantic tags, source/target positive soundness,
injective roots, relative U-closed seams, and side SAME-VERTEX
coherence are each explicit class conditions. These are necessary
ingredients; we have not shown the relevant finite 2019 Ramsey
construction can be performed inside this constrained class.

The result applies to a genuinely NONCANONICAL joint-tagged target,
not just the canonical split expansion of a native source. It
introduces no output vertices, no generated closure hull, and does
not change the frozen survey.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- A FULL embedding between arbitrary exact-joint-tagged
relational Pictures has split-output closed image provided that
its actual image is relatively U-closed for the JOINT rules.
The target side need not admit any native functional decoder. -/
theorem HybridSplitOutputClosedAt.ofExactJointTaggedUSubstructure
    {H S : Type w}
    {Root : RelStructure (L.splitMaskJointRootLanguage Parts) H}
    {Side : RelStructure (L.splitMaskJointRootLanguage Parts) S}
    (e : Embedding Root Side)
    (hExact : HasExactJointRootTags Side)
    (hPositive :
      ∀ p : FunctionInputPattern (L.outputPartIndexed Parts),
        0 < p.rootSize)
    (hSound : HybridPositiveOutputSound
      (splitMaskJointRootReduct Side))
    (hInjective : HybridActiveDomainRootInjective
      (splitMaskJointRootReduct Side))
    (hUS : IsUSubstructure (L.splitMaskJointClosureRules Parts)
      Side (Set.range e)) :
    HybridSplitOutputClosedAt e.splitMaskJointRootReduct := by
  have hExactEq :
      Side = splitMaskJointRootExpansion
        (splitMaskJointRootReduct Side) := hExact
  have hCanonicalUS :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        (splitMaskJointRootExpansion
          (splitMaskJointRootReduct Side))
        (Set.range e.splitMaskJointRootReduct) := by
    have hRange :
        Set.range e.splitMaskJointRootReduct = Set.range e := rfl
    rw [hRange, ← hExactEq]
    exact hUS
  exact HybridSplitOutputClosedAt.ofJointRootUSubstructure
    e.splitMaskJointRootReduct hPositive
    (fun p t ht => hSound.2.1 p t ht)
    (fun p root hDomain => hInjective.2 p root hDomain)
    hCanonicalUS

/-- ACTUAL joint-tagged FULL relational free amalgamation preserves
the SAME-VERTEX agreement between ORIGINAL complete output tuples
and SPLIT singleton incidence tuples, provided:
* both sides have exact joint-root tag semantics;
* both hybrid reducts are positive-output sound and have injective
  input domain roots;
* each common-root image is relatively U-closed for the ACTUAL
  joint closure rules; and
* the side hybrid reducts already satisfy visible whole/split
  output-value agreement.

In addition the whole amalgam retains exact joint-root tag
semantics. All assumptions are on the ACTUAL noncanonical
tagged diagram, not reconstructed native source structures.

This is a transfer/normalization lemma, not the still-open strong
amalgamation theorem for the entire constrained target class. -/
theorem HybridVisibleWholeSplitAgreement.jointTaggedFreeAmalgam_of_closedSeams
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
    (hExactLeft : HasExactJointRootTags Left)
    (hExactRight : HasExactJointRootTags Right)
    (hSoundLeft : HybridPositiveOutputSound
      (splitMaskJointRootReduct Left))
    (hSoundRight : HybridPositiveOutputSound
      (splitMaskJointRootReduct Right))
    (hInjectiveLeft : HybridActiveDomainRootInjective
      (splitMaskJointRootReduct Left))
    (hInjectiveRight : HybridActiveDomainRootInjective
      (splitMaskJointRootReduct Right))
    (hAgreeLeft : HybridVisibleWholeSplitAgreement
      (splitMaskJointRootReduct Left))
    (hAgreeRight : HybridVisibleWholeSplitAgreement
      (splitMaskJointRootReduct Right))
    (hClosedLeft : IsUSubstructure
      (L.splitMaskJointClosureRules Parts)
      Left (Set.range sL))
    (hClosedRight : IsUSubstructure
      (L.splitMaskJointClosureRules Parts)
      Right (Set.range sR)) :
    HybridVisibleWholeSplitAgreement
      (splitMaskJointRootReduct Whole) ∧
    HasExactJointRootTags Whole := by
  constructor
  · exact
      HybridVisibleWholeSplitAgreement.freeAmalgam_of_splitClosedRoot
        hFree.splitMaskJointRootReduct
        hAgreeLeft hAgreeRight
        (HybridSplitOutputClosedAt.ofExactJointTaggedUSubstructure
          sL hExactLeft hPositive hSoundLeft hInjectiveLeft hClosedLeft)
        (HybridSplitOutputClosedAt.ofExactJointTaggedUSubstructure
          sR hExactRight hPositive hSoundRight hInjectiveRight hClosedRight)
  · exact HasExactJointRootTags.freeAmalgam
      hFree hExactLeft hExactRight

end StructuralRamsey.RelStructure
