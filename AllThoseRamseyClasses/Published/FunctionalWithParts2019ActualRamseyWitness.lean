import AllThoseRamseyClasses.Published.FunctionalWithParts2019FromPartiteArrow
import AllThoseRamseyClasses.Published.FunctionalWithParts2019FinalCoveredArrow

/-!
# The genuine 2019 two-pass functional Ramsey witness, end to end

The initial arrow and the final arrow are BOTH genuine
part-preserving full embedding Ramsey arrows for partial Option(Set)
functions, and neither relies on an intermediate strict functional
B-tree completion.

The verified initial embedding equivalence converts the true
functional arrow into the canonical unary-part and whole-mask tagged
relational arrow. The checked coordinated 2019 profile construction
then performs its closed initial pass, relational profile sparsening
and final closed pass. It retains actual B-copy coverage. The checked
covered-target decoder recovers a finite transversal genuinely partial
function target and a true functional arrow on its ORIGINAL vertices.

This theorem still returns the exact induced weak K-completions and
original tagged control projection as RELATIONAL certificates.
Transferring them to a genuine partial-function K-class requires
the additional independently verified exact OLD weak semantics and
a canonical interpretation of K-members. No exact weak carrier or
projected image is replaced by a generated closure hull.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- An actual part-preserving genuine partial-function Ramsey arrow
constructs an actual finite transversal genuine partial-function
Ramsey witness through the already verified 2019 two-pass profile
route. Protected B-copy coverage is produced, NOT assumed.

The source input and the final decoded target use the SAME original
Option(Set) signature, with undefined and defined-empty distinct.
The exact weak-test cutoff n is unchanged. -/
theorem genuineWithParts2019_actual_functional_ramsey_witness
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : PartialSetStructure L Z) (part0 : Z → Parts)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hTrans0 : FibreTransversal C0 part0)
    (hPos : L.PositiveFuncArity)
    {K : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts)}
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
    (hArrow0 : PartPreservingArrow
      A partA B partB C0 part0 κ) :
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
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (genuineWithPartsTagged2019 C0 part0) f) ∧
      (∀ S : Finset VQ, S.card ≤ n →
        HasInducedClosedUKCompletion K
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce (↑S : Set VQ))) ∧
      FibreTransversal (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) ∧
      PartPreservingArrow A partA B partB
        (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) κ := by
  have hTaggedArrow : StructuralRamsey.Arrow
      (genuineWithPartsTagged2019 A partA)
      (genuineWithPartsTagged2019 B partB)
      (genuineWithPartsTagged2019 C0 part0) κ :=
    genuineWithParts2019_arrow_of_functional
      A partA B partB C0 part0
      hTransA hTransB hTrans0 κ hArrow0
  exact genuineWithParts2019_final_functional_arrow_of_tagged
    A partA B partB (genuineWithPartsTagged2019 C0 part0)
    hTransA hTransB hPos
    hBK hClosed hHer hStrong hKIrr n κ hTaggedArrow

end AllThoseRamseyClasses.Published
