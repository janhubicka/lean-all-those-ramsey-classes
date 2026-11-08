import AllThoseRamseyClasses.Published.TrackENativePartiteActualHSparseWitness

/-!
# Appendix A Track E: retain genuine native function-output transversality

The corrected 2019 two-pass final witness is a genuine part-preserving
Option(Set) structure and has the complete-output FibreTransversal
certificate on the actual recovered part map. The native Lean partite
construction additionally requires transversality of each whole
set-valued function fibre (there is at most one output per part).

For a faithful native structure, these are EXACTLY equivalent: empty
native fibre means undefined, not a defined-empty operation.
The no-defined-empty decoder certificate of merged Track E #564
therefore transports the actual final H sparse witness's
transversality back to its native collapse, on the SAME carrier and
with the SAME recovered parts. We preserve the original witness and
all its exact weak-test certificates without modifying it.

This is ONLY FUNCTION-OUTPUT transversality. The stronger
FunctionalPartite.System also demands transversal RELATION tuples,
which is not inferred here. No claim of strict functional trees or
global total-fibre homomorphism is made.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The native function-output transversality condition, with precisely
the same whole-fibre meaning as
`FunctionalPartite.System.funcTransversal` for its reduct.
It does NOT require relation-tuple transversality. -/
def NativeFunctionFibreTransversal {X : Type w}
    (A : Structure L X) (part : X → Parts) : Prop :=
  ∀ F xs y z, y ∈ A.func F xs → z ∈ A.func F xs →
    part y = part z → y = z

/-- Faithful nonempty-fibre encoding changes neither output incidence
nor the native transversality condition. It includes arbitrary arities,
multivalued outputs and undefined inputs, without inventing
defined-empty source inputs. -/
theorem nativeFunctionFibreTransversal_iff_partial
    {X : Type w} (A : Structure L X) (part : X → Parts) :
    NativeFunctionFibreTransversal A part ↔
      FibreTransversal A.toNonemptyPartial part := by
  classical
  constructor
  · intro h F xs T hVal y hy z hz hp
    by_cases hNon : (A.func F xs).Nonempty
    · have hEq : A.func F xs = T := by
        change (if (A.func F xs).Nonempty then
          some (A.func F xs) else none) = some T at hVal
        simpa [hNon] using hVal
      apply h F xs y z
      · rw [hEq]
        exact hy
      · rw [hEq]
        exact hz
      · exact hp
    · have hFalse : False := by
        change (if (A.func F xs).Nonempty then
          some (A.func F xs) else none) = some T at hVal
        simpa [hNon] using hVal
      exact hFalse.elim
  · intro h F xs y z hy hz hp
    have hNon : (A.func F xs).Nonempty := ⟨y, hy⟩
    have hVal : A.toNonemptyPartial.func F xs =
        some (A.func F xs) := by
      change (if (A.func F xs).Nonempty then
        some (A.func F xs) else none) = some (A.func F xs)
      simp [hNon]
    exact h F xs (A.func F xs) hVal y hy z hz hp

/-- A genuine partial-function final target with no `some ∅` inputs
has a native collapse with exactly the same transversal whole fibres.
There is no new part map and no use of generated hulls. -/
theorem nativeFunctionFibreTransversal_of_noDefinedEmpty
    {X : Type w} (D : PartialSetStructure L X)
    (part : X → Parts)
    (hNormal : NoDefinedEmptyValues D)
    (hTr : FibreTransversal D part) :
    NativeFunctionFibreTransversal D.collapseDomain part := by
  have hRound : D.collapseDomain.toNonemptyPartial = D :=
    (noDefinedEmpty_iff_nativeRoundtrip D).mp hNormal
  exact (nativeFunctionFibreTransversal_iff_partial
    D.collapseDomain part).mpr (by
      simpa only [hRound] using hTr)

/-- The genuine 2019 H-valued sparse witness now carries a NATIVE
function-fibre transversality certificate on its literal decoded
native target, with its original recovered part map. All witnesses,
source-defined control maps, B-coverage and exact n-vertex local H
completion certificates are inherited UNCHANGED.

This does not claim native relation-tuple transversality, or that the
entire final target belongs to H before applying the separate
class-local completion implication. -/
theorem genuinePartite2019_actual_native_sparse_witness_with_fibreTransversal
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
      NativeFunctionFibreTransversal
        (wholeMaskOriginalDecode C).collapseDomain
        (wholeMaskCoveredPart C B.toNonemptyPartial partB hC hCover) ∧
      NativePartPreservingArrow A partA B partB
        (wholeMaskOriginalDecode C).collapseDomain
        (wholeMaskCoveredPart C B.toNonemptyPartial partB hC hCover) κ := by
  classical
  obtain ⟨VQ, hVQ, C, hC, hCover,
      hControl, hWeak, hTrans, hNativeArrow⟩ :=
    genuinePartite2019_actual_native_sparse_witness_with_H_completions
      H hHer hStrong hIso hPos hIrr A partA B partB C0 part0
      hB hTransA hTransB hTrans0 n κ hArrow0
  let partD := wholeMaskCoveredPart C B.toNonemptyPartial partB hC hCover
  have hNoEmpty : NoDefinedEmptyValues (wholeMaskOriginalDecode C) :=
    wholeMaskOriginalDecode_noDefinedEmpty_of_nativeBCover
      C B partB hC hCover
  have hNativeTr :
      NativeFunctionFibreTransversal
        (wholeMaskOriginalDecode C).collapseDomain partD :=
    nativeFunctionFibreTransversal_of_noDefinedEmpty
      (wholeMaskOriginalDecode C) partD hNoEmpty hTrans
  exact ⟨VQ, hVQ, C, hC, hCover,
    hControl, hWeak, hTrans, hNativeTr, hNativeArrow⟩

end AllThoseRamseyClasses.Published
