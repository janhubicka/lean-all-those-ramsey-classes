import AllThoseRamseyClasses.Published.TrackENativeFinalFibreTransversal
import AllThoseRamseyClasses.Published.TrackECoveredNativeRelationTransversal
import AllThoseRamseyClasses.Published.TrackESameCarrierSystemArrowBridge

/-!
# Track E: actual 2019 H-sparse witness in the standard FunctionalPartite API

This is the SAME actual corrected two-pass 2019 H-valued sparse witness
as merged Track E #924.  Starting with genuine native partite Systems
A, B and C₀, we keep the precise final tagged U-closed C, the original
B-coverage, original-source-defined control projection, and completion
certificate for EVERY exact ambient n-vertex weak test S.

The two independent proofs of transversality are used explicitly:
* #940 preserves complete native output-fibre transversality;
* #944 preserves relation-tuple transversality from the *given*
  relation-transversal B and protected canonical B-copy coverage.

#953 packages the exact native carrier and recovered part map into
FunctionalPartite.System, and #947 identifies the full part-preserving
native Ramsey arrow with the standard FunctionalPartite.Arrow.  The
full embeddings/colourings and all original weak-test subsets remain
unchanged.

This does NOT assert H-membership of the final target, full domain
reflection for the global control projection, or strict mixed-root
functional B-tree completion. A separate class-local completion
hypothesis is still needed for the ultimate class-level Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- On the literal final 2019 sparse witness, produce an ACTUAL standard
native functional partite System Ramsey target, preserving all the
original sparse-witness certificates and the original finite carrier.

The original A/B/C₀ are genuine native Systems, not arbitrary
Structures with unverified relation-tuple transversality. H remains
an explicitly assumed class of genuinely partial part-labelled
Option(Set) objects. This is a WITNESS theorem only: H-membership of
the whole final target requires the separate local class axiom. -/
theorem genuinePartite2019_actual_standardSystem_sparse_witness_with_H_completions
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hPos : L.PositiveFuncArity)
    (hIrr : ∀ {T : Type w} [Finite T]
      (D : PartialSetStructure L T) (p : T → Parts),
      H D p → FibreTransversal D p →
      (wholeMaskTagExpansion (withPartsWholeMaskOld D p)).Irreducible)
    {X Y Z : Type w} [Finite X] [Finite Y] [Finite Z]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y)
    (C₀ : FunctionalPartite.System L Parts Z)
    (hB : H B.toStructure.toNonemptyPartial B.part)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hInitial : FunctionalPartite.Arrow A B C₀ κ) :
    ∃ (VQ : Type w) (_ : Finite VQ)
      (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VQ)
      (hClosed : IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
      (hCover : ∀ {T : Type w}
        (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        RelStructure.Embedding Test C →
        Nonempty (RelStructure.Embedding Test
          (genuineWithPartsTagged2019 B.toStructure.toNonemptyPartial B.part))),
      ∃ (D : FunctionalPartite.System L Parts VQ),
        D.toStructure = (wholeMaskOriginalDecode C).collapseDomain ∧
        D.part = wholeMaskCoveredPart C
          B.toStructure.toNonemptyPartial B.part hClosed hCover ∧
        (∃ f : VQ → Z,
          Structure.IsOriginalPartialHomomorphism
            D.toStructure C₀.toStructure f ∧
          ∀ x : VQ, C₀.part (f x) = D.part x) ∧
        (∀ S : Finset VQ, S.card ≤ n →
          HasGenuinePartiteTagged2019RelativeCompletion H
            (C.induce (↑S : Set VQ))) ∧
        FibreTransversal (wholeMaskOriginalDecode C)
          (wholeMaskCoveredPart C
            B.toStructure.toNonemptyPartial B.part hClosed hCover) ∧
        FunctionalPartite.Arrow A B D κ := by
  classical
  have hTransA :
      FibreTransversal A.toStructure.toNonemptyPartial A.part :=
    (nativeFunctionFibreTransversal_iff_partial
      A.toStructure A.part).mp A.funcTransversal
  have hTransB :
      FibreTransversal B.toStructure.toNonemptyPartial B.part :=
    (nativeFunctionFibreTransversal_iff_partial
      B.toStructure B.part).mp B.funcTransversal
  have hTrans₀ :
      FibreTransversal C₀.toStructure.toNonemptyPartial C₀.part :=
    (nativeFunctionFibreTransversal_iff_partial
      C₀.toStructure C₀.part).mp C₀.funcTransversal
  have hNativeInitial : NativePartPreservingArrow
      A.toStructure A.part B.toStructure B.part
      C₀.toStructure C₀.part κ :=
    (nativePartPreservingArrow_iff_standardSystemArrow A B C₀ κ).mpr hInitial
  obtain ⟨VQ, hFin, C, hClosed, hCover,
      hControl, hWeak, hTr, hFunc, hNativeArrow⟩ :=
    genuinePartite2019_actual_native_sparse_witness_with_fibreTransversal
      H hHer hStrong hIso hPos hIrr
      A.toStructure A.part B.toStructure B.part
      C₀.toStructure C₀.part hB hTransA hTransB hTrans₀
      n κ hNativeInitial
  let nativeD : Structure L VQ := (wholeMaskOriginalDecode C).collapseDomain
  let partD : VQ → Parts :=
    wholeMaskCoveredPart C B.toStructure.toNonemptyPartial
      B.part hClosed hCover
  have hRelB : NativeRelationTupleTransversal B.toStructure B.part :=
    B.relTransversal
  have hRel : NativeRelationTupleTransversal nativeD partD :=
    coveredNativeRelationTupleTransversal
      C B.toStructure B.part hClosed hCover hRelB
  have hFuncD : NativeFunctionFibreTransversal nativeD partD := hFunc
  let D : FunctionalPartite.System L Parts VQ :=
    sameCarrierFunctionalPartiteSystem nativeD partD hRel hFuncD
  have hStandardArrow : FunctionalPartite.Arrow A B D κ :=
    (nativeArrow_iff_standardArrow_of_sameCarrierTransversal
      A B nativeD partD hRel hFuncD κ).mp hNativeArrow
  refine ⟨VQ, hFin, C, hClosed, hCover, D,
    rfl, rfl, ?_, hWeak, hTr, hStandardArrow⟩
  exact hControl

end AllThoseRamseyClasses.Published
