import AllThoseRamseyClasses.Published.FunctionalWithParts2019ActualHSparseWitness
import PartiteConstruction.Functional.TrackENativePartiteFinalArrow
import PartiteConstruction.Functional.TrackESourceDefinedPartialIff

/-!
# Track E: actual native part-preserving 2019 sparse witness with H-completions

The verified corrected 2019 two-pass theorem already constructs the
genuine-partial `Option (Set)` final Ramsey target with all exact
tagged weak-test H-completion certificates, the original source-defined
control projection, and canonical B-copy coverage.

Track E's native/partial FULL-partite-arrow equivalence and final
covered-target no-defined-empty theorem make it possible to transfer the
actual final Ramsey arrow back to native set-valued functions on the
SAME carrier. The source-defined global projection also descends to
the native original-2019 partial homomorphism, with NO false domain
reflection. All original parts and the original weak cutoff n survive.

This is a witness-level endpoint. Class H stays a GENUINE partial
function class, and its original closed-hereditary, part-preserving
strong-amalgamation and isomorphism invariance assumptions are explicit.
This theorem does NOT turn the entire native final witness into an
H-member, establish strict full-functional B-trees, or solve the
local-completion transfer of Track C.

No new quotient construction, closure hull, assumption of full
fibre-surjective global maps, or generated-profile decoder oracle.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness
open StructuralRamsey.Structure.TrackESourceDefinedPartialIff

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The ACTUAL corrected two-pass sparse Ramsey witness with a native
full part-preserving Ramsey arrow, on the same final vertices as the
genuine-partial 2019 target, together with the source-defined ORIGINAL
native projection and exact H-valued weak completion certificates.

Input A,B,C0 are native `Structure` objects. H is deliberately an
original genuinely partial part-labelled functional class: membership
of B's faithful encoding and all class hypotheses remain literal.
No finite closure hull is substituted for S in the weak certificates.
-/
theorem genuinePartite2019_actual_native_sparse_witness_with_H_completions
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
    (A : Structure L X) (partA : X → Parts)
    (B : Structure L Y) (partB : Y → Parts)
    (C0 : Structure L Z) (part0 : Z → Parts)
    (hB : H B.toNonemptyPartial partB)
    (hTransA : FibreTransversal A.toNonemptyPartial partA)
    (hTransB : FibreTransversal B.toNonemptyPartial partB)
    (hTrans0 : FibreTransversal C0.toNonemptyPartial part0)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : NativePartPreservingArrow
      A partA B partB C0 part0 κ) :
    ∃ (VQ : Type w) (_ : Finite VQ)
      (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VQ)
      (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
      (hCover : ∀ {T : Type w}
        (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        RelStructure.Embedding Test C →
        Nonempty (RelStructure.Embedding Test
          (genuineWithPartsTagged2019 B.toNonemptyPartial partB))),
      (∃ f : VQ → Z,
        Structure.IsOriginalPartialHomomorphism
          (wholeMaskOriginalDecode C).collapseDomain C0 f ∧
        (∀ x : VQ, part0 (f x) =
          wholeMaskCoveredPart C B.toNonemptyPartial partB hC hCover x)) ∧
      (∀ S : Finset VQ, S.card ≤ n →
        HasGenuinePartiteTagged2019RelativeCompletion H
          (C.induce (↑S : Set VQ))) ∧
      FibreTransversal (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B.toNonemptyPartial partB hC hCover) ∧
      NativePartPreservingArrow A partA B partB
        (wholeMaskOriginalDecode C).collapseDomain
        (wholeMaskCoveredPart C B.toNonemptyPartial partB hC hCover) κ := by
  classical
  have hInitialPartial : PartPreservingArrow
      A.toNonemptyPartial partA B.toNonemptyPartial partB
      C0.toNonemptyPartial part0 κ :=
    (nativePartPreservingArrow_iff_partial
      A partA B partB C0 part0 κ).mp hArrow0
  obtain ⟨VQ, hVQ, C, hC, hCover, hControl,
      hWeak, hTrans, hPartialArrow⟩ :=
    genuinePartite2019_actual_sparse_witness_with_H_completions
      H hHer hStrong hIso hPos hIrr
      A.toNonemptyPartial partA B.toNonemptyPartial partB
      C0.toNonemptyPartial part0
      hB hTransA hTransB hTrans0 n κ hInitialPartial
  obtain ⟨f, hfPartial, hPart⟩ := hControl
  have hNormal : NoDefinedEmptyValues (wholeMaskOriginalDecode C) :=
    wholeMaskOriginalDecode_noDefinedEmpty_of_nativeBCover
      C B partB hC hCover
  have hRoundtrip :
      (wholeMaskOriginalDecode C).collapseDomain.toNonemptyPartial =
        wholeMaskOriginalDecode C :=
    (noDefinedEmpty_iff_nativeRoundtrip _).mp hNormal
  have hfNative : Structure.IsOriginalPartialHomomorphism
      (wholeMaskOriginalDecode C).collapseDomain C0 f := by
    apply originalPartialHom_iff_nonemptyPartial.mpr
    simpa only [hRoundtrip] using hfPartial
  have hArrowNative : NativePartPreservingArrow
      A partA B partB (wholeMaskOriginalDecode C).collapseDomain
      (wholeMaskCoveredPart C B.toNonemptyPartial partB hC hCover) κ :=
    (nativePartPreservingArrow_iff_coveredOriginalDecode
      A partA B partB C hC hCover κ).mpr hPartialArrow
  exact ⟨VQ, hVQ, C, hC, hCover,
    ⟨f, hfNative, hPart⟩, hWeak, hTrans, hArrowNative⟩

end AllThoseRamseyClasses.Published
