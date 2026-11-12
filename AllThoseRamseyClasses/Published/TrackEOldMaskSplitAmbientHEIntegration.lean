import AllThoseRamseyClasses.Published.TrackESplitAmbientHEFullCopyTransfer
import AllThoseRamseyClasses.Published.TrackESplitWeakHomOriginalMaskBridge
import AllThoseRamseyClasses.Published.TrackEOldDomainMaskExactParts

/-!
# Track E2: exact B3 semantic interface from split relative HE and OLD masks

This theorem assembles three strictly semantic results on the SAME
native source and target, SAME literal weak vertex subset S and SAME
map f:S→W:

1. The split-output-part language supplies a genuine ambient-relative
   weak HE (positive surviving incidences, full retained singleton
   fibres, and all full irreducible split tests).
2. Positive homomorphism preservation of the OLD active output-part
   domain masks identifies the entire original target set of output
   PARTS for every nonempty original source application, including
   those whose outputs are partly forgotten by S.
3. The exact mask excludes phantom target output parts, allowing the
   split weak homomorphism to descend to the original multivalued
   language. Every original FULL ambient irreducible copy is protected
   by pulling its partite System structure back through the full
   embedding, lifting to its split representation, and joining its
   split full target embedding.

This is a precise sufficient SAME-MAP semantic B3 contract, not a
construction of the actual finite-family sparse Ramsey control or a
proof that the existing old 2019 H-relative completion certificates
supply the split HE clause. No source-closure hull or inserted
vertices, no global domain reflection and no f injectivity or
part-preservation assumption. Full finite-family E2 remains open.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- A split-language ambient relative WEAK HE together with the same-map
OLD active-domain-output-part mask preservation on every exact input
root produces the COMPLETE original native ambient relative WEAK HE.
All arities, repeated primitive inputs, and empty/undefined source
fibres are handled by the underlying exact representation contracts.

The split HE premise is intentional and is NOT derived from a mere
OLD complete-value induced homomorphism. -/
theorem nativeAmbientRelativeWeakHE_of_splitHE_and_oldMaskMap
    {V W : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W)
    (S : Set V) (f : S → W)
    (hSplit : IsAmbientRelativeWeakHE
      A.splitOutputParts.toStructure S
      B.splitOutputParts.toStructure f)
    (hDomain :
      ∀ (p : Language.FunctionInputPattern L)
        (q : Language.CompleteOutputParts Parts)
        (rootS : Fin p.rootSize → S),
        ((A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part).induce S).rel
          (.inr (.inl (p, q))) rootS →
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part).rel
          (.inr (.inl (p, q))) (f ∘ rootS)) :
    IsAmbientRelativeWeakHE A.toStructure S B.toStructure f := by
  have hNoNewParts :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S),
        (A.func F (Subtype.val ∘ xs)).Nonempty →
        (∀ z, z ∈ A.func F (Subtype.val ∘ xs) → z ∈ S) →
        B.part '' (B.func F (f ∘ xs)) ⊆
          A.part '' (A.func F (Subtype.val ∘ xs)) := by
    intro F xs hNonempty _hAll
    rw [nativeOutputPartMask_eq_of_oldDomainMap
      A B S f hDomain F xs hNonempty]
  have hNativeWeak : IsAmbientRelativeWeakHomomorphism
      A.toStructure S B.toStructure f :=
    ambientRelativeWeakHom_of_splitOutputParts_and_noNewParts
      A B S f hSplit.1 hNoNewParts
  exact nativeAmbientRelativeWeakHE_of_splitHE_and_nativeWeak
    A B S f hSplit hNativeWeak

end AllThoseRamseyClasses.Published
