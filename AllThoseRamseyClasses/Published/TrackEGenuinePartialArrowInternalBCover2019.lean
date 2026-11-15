import AllThoseRamseyClasses.Published.TrackEGenuineWithParts2019InternalBCover
import AllThoseRamseyClasses.Published.FunctionalWithParts2019FinalCoveredArrow

/-!
# Track E: true partial-function Ramsey arrow and internal tagged B copies

The proof of the existing covered-tagged functional arrow depends ONLY
on final U-closedness, protected external canonical B coverage and the
full tagged Ramsey arrow. It can therefore be reused without change
on the ACTUAL coordinately B-saturated source of #1213.

All conclusions below refer to the SAME final tagged C:
the selected original corrected U-homomorphism-embedding, internal
full canonical B copies, exact small K-completions and the true full
part-preserving genuine Option(Set) partial-function Ramsey arrow of
the decoder on its original vertices.

This does not yet assert the final standard nonempty-native system
or the original H-class membership. Both belong to the next
same-source decoding step, as does strict full FUNCTION B-tree locality.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Actual coordinated fully-partial Ramsey target retaining INTERNAL
canonical tagged B-extensions, same selected HE and every literal
small-weak K-completion on one same final C. -/
theorem genuineWithParts2019_final_functional_arrow_with_internalB
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hPos : L.PositiveFuncArity)
    {K : StructureClass (L := (L.withParts Parts).wholeMaskTagLanguage Parts)}
    (hBK : K (genuineWithPartsTagged2019 B partB))
    (hClosed : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) E)
    (hHer : ClosedUHereditary K
      ((L.withParts Parts).wholeMaskClosureRules Parts))
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → E.Irreducible)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : StructuralRamsey.Arrow
      (genuineWithPartsTagged2019 A partA)
      (genuineWithPartsTagged2019 B partB) C0 κ) :
    ∃ (VQ : Type w) (_ : Finite VQ)
      (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VQ)
      (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
      (hCover : ∀ {T : Type w}
        (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        Embedding Test C →
        Nonempty (Embedding Test (genuineWithPartsTagged2019 B partB))),
      (∃ f : VQ → Z, IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 f) ∧
      IrreduciblesExtendTo (genuineWithPartsTagged2019 B partB) C ∧
      (∀ S : Finset VQ, S.card ≤ n →
        HasInducedClosedUKCompletion K
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce (↑S : Set VQ))) ∧
      FibreTransversal (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) ∧
      PartPreservingArrow A partA B partB
        (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) κ := by
  classical
  obtain ⟨VQ, hFinite, C, hC, hProjection, hCover,
    hInternal, hWeak, hRelArrow⟩ :=
    genuineWithParts2019_profile_sparse_with_INTERNAL_B_coverage
      A partA B partB C0 hTransA hTransB
      hBK hClosed hHer hStrong hKIrr n κ hArrow0
  letI : Finite VQ := hFinite
  have hTrans : FibreTransversal (wholeMaskOriginalDecode C)
      (wholeMaskCoveredPart C B partB hC hCover) :=
    wholeMaskOriginalDecode_fibreTransversal_of_covered
      C B partB hC hPos hCover
  have hArrow : PartPreservingArrow A partA B partB
      (wholeMaskOriginalDecode C)
      (wholeMaskCoveredPart C B partB hC hCover) κ :=
    coveredWholeMask_partPreservingArrow_of_tagged
      A partA hTransA B partB hTransB
      C B partB hC hPos hCover κ hRelArrow
  exact ⟨VQ, hFinite, C, hC, hCover,
    hProjection, hInternal, hWeak, hTrans, hArrow⟩

end AllThoseRamseyClasses.Published
