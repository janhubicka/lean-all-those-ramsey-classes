import AllThoseRamseyClasses.Published.TrackERetainTaggedGlobalControl2019
import AllThoseRamseyClasses.Published.TrackEActualStandardSystemSparseWitness
import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKRamseyDescent
import PartiteConstruction.Functional.TrackESourceDefinedPartialIff

/-!
# Track E: the SAME standard native partite witness retains its tagged control HE

The corrected 2019 two-pass theorem's original tagged
`IsInducedClosedUHomomorphismEmbedding` is retained on the EXACT
same final relational C and projection f. Independently, the final
B-covered decoder is faithfully native and partite. We therefore
produce ONE genuine native `FunctionalPartite.System` Ramsey target
with BOTH certificates:

* the stronger original corrected tagged U-homomorphism-embedding
  of the selected f to the canonical tagged original control;
* its genuine original-2019 native source-defined homomorphism law
  on the very same f and same recovered vertex parts.

The tagged test-protection premise does NOT by itself make this f an
original native homomorphism-embedding: a full canonical-tagged lift
of arbitrary native irreducible source tests remains a separate goal.
In particular no arbitrary OLD intermediate profile is normalized,
and no weak test is replaced by a closure hull.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness
open StructuralRamsey.Structure.TrackESourceDefinedPartialIff

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The actual standard native partite 2019 H-sparse Ramsey witness
with original n-vertex H-relative completions AND the original
strong tagged HE projection retained on the same f and C.

The exported native map is deliberately only a source-defined
homomorphism. Upgrading this particular map to a native HE requires
a test-by-test canonical tagged lift, not a second chosen map.
-/
theorem genuinePartite2019_actual_standardSystem_sparse_witness_with_taggedHE
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hPos : L.PositiveFuncArity)
    (hIrr : ∀ {T : Type w} [Finite T]
      (P : PartialSetStructure L T) (p : T → Parts),
      H P p → FibreTransversal P p →
      (wholeMaskTagExpansion (withPartsWholeMaskOld P p)).Irreducible)
    {X Y Z : Type w} [Finite X] [Finite Y] [Finite Z]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y)
    (C0 : FunctionalPartite.System L Parts Z)
    (hB : H B.toStructure.toNonemptyPartial B.part)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hInitial : FunctionalPartite.Arrow A B C0 κ) :
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
          IsInducedClosedUHomomorphismEmbedding
            ((L.withParts Parts).wholeMaskClosureRules Parts)
            C (genuineWithPartsTagged2019
              C0.toStructure.toNonemptyPartial C0.part) f ∧
          Structure.IsOriginalPartialHomomorphism
            D.toStructure C0.toStructure f ∧
          ∀ x : VQ, C0.part (f x) = D.part x) ∧
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
  have hTrans0 :
      FibreTransversal C0.toStructure.toNonemptyPartial C0.part :=
    (nativeFunctionFibreTransversal_iff_partial
      C0.toStructure C0.part).mp C0.funcTransversal
  have hInitialPartial : PartPreservingArrow
      A.toStructure.toNonemptyPartial A.part
      B.toStructure.toNonemptyPartial B.part
      C0.toStructure.toNonemptyPartial C0.part κ :=
    (nativePartiteArrow_iff_faithfulPartial A B C0 κ).mp hInitial
  obtain ⟨VQ, hVQ, C, hClosed, hCover, hControl,
      hWeak, hTr, hPartialArrow⟩ :=
    genuinePartite2019_actual_sparse_witness_with_taggedHE_control
      H hHer hStrong hIso hPos hIrr
      A.toStructure.toNonemptyPartial A.part
      B.toStructure.toNonemptyPartial B.part
      C0.toStructure.toNonemptyPartial C0.part
      hB hTransA hTransB hTrans0 n κ hInitialPartial
  letI : Finite VQ := hVQ
  obtain ⟨f, hTagHE, hPartial, hPart⟩ := hControl
  let partialD : PartialSetStructure L VQ := wholeMaskOriginalDecode C
  let nativeD : Structure L VQ := partialD.collapseDomain
  let partD : VQ → Parts :=
    wholeMaskCoveredPart C B.toStructure.toNonemptyPartial
      B.part hClosed hCover
  have hNoEmpty : NoDefinedEmptyValues partialD :=
    wholeMaskOriginalDecode_noDefinedEmpty_of_nativeBCover
      C B.toStructure B.part hClosed hCover
  have hRoundtrip : partialD.collapseDomain.toNonemptyPartial = partialD :=
    (noDefinedEmpty_iff_nativeRoundtrip partialD).mp hNoEmpty
  have hfNative : Structure.IsOriginalPartialHomomorphism
      nativeD C0.toStructure f := by
    apply originalPartialHom_iff_nonemptyPartial.mpr
    simpa only [nativeD, partialD, hRoundtrip] using hPartial
  have hFunc : NativeFunctionFibreTransversal nativeD partD :=
    nativeFunctionFibreTransversal_of_noDefinedEmpty
      partialD partD hNoEmpty hTr
  have hRelB :
      NativeRelationTupleTransversal B.toStructure B.part :=
    B.relTransversal
  have hRel : NativeRelationTupleTransversal nativeD partD :=
    coveredNativeRelationTupleTransversal
      C B.toStructure B.part hClosed hCover hRelB
  let D : FunctionalPartite.System L Parts VQ :=
    sameCarrierFunctionalPartiteSystem nativeD partD hRel hFunc
  have hNativeArrow : NativePartPreservingArrow
      A.toStructure A.part B.toStructure B.part nativeD partD κ :=
    (nativePartPreservingArrow_iff_coveredOriginalDecode
      A.toStructure A.part B.toStructure B.part
      C hClosed hCover κ).mpr hPartialArrow
  have hStandardArrow : FunctionalPartite.Arrow A B D κ :=
    (nativeArrow_iff_standardArrow_of_sameCarrierTransversal
      A B nativeD partD hRel hFunc κ).mp hNativeArrow
  exact ⟨VQ, hVQ, C, hClosed, hCover, D, rfl, rfl,
    ⟨f, hTagHE, hfNative, hPart⟩, hWeak, hTr, hStandardArrow⟩

end AllThoseRamseyClasses.Published
