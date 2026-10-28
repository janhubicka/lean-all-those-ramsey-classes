import AllThoseRamseyClasses.Published.FunctionalWithParts2019CoveredSparseWitness
import PartiteConstruction.Functional.WholeMaskCoveredPartiteArrowEndgame2019

/-!
# The verified 2019 two-pass profile construction has a genuinely partial Ramsey target

The input is the usual canonical tagged RELATIONAL Ramsey arrow on genuine
transversal part-labelled Option(Set) source structures A and B.
The already checked coordinated 2019 two-pass proof constructs a final
U-closed tagged C and FULL B-copy coverage, together with exact weak-test
local K-completions. Under positive primitive input arities these two
properties suffice to decode C to an ACTUAL genuine partial function
target with a unique recovered vertex part map and transversal outputs.

Every full OLD A- or B-copy in C becomes a FULL part-preserving
partial-function embedding on the SAME vertices. The relational
Ramsey arrow therefore transfers to the true functional partite
Ramsey arrow by the final covered-target theorem already verified
in partite-construction.

The output retains the original closed-test control map and finite
weak-test K-completion certificates; no native maximal-mixed
functional strict B-tree is required at intermediate stages.
No exact weak carrier is enlarged to its generated closure.
The remaining task is to transfer the relational local K-completions
and control maps to an appropriate ORIGINAL functional K class.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The verified two-pass 2019 sparsening route already produces a
genuine, finite and transversal Option(Set) partial-function
Ramsey witness with all original exact weak-test RELATIONAL
K-completion certificates. The extra final B-copy coverage is
CONSTRUCTED, not assumed.

Only the input arrow is still stated in the canonical tagged
relational language; the naturality bridge from a true functional
initial arrow is independently checked in PR #670. -/
theorem genuineWithParts2019_final_functional_arrow_of_tagged
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
    hWeak, hRelArrow⟩ :=
    genuineWithParts2019_profile_sparse_with_B_coverage
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
    hProjection, hWeak, hTrans, hArrow⟩

end AllThoseRamseyClasses.Published
