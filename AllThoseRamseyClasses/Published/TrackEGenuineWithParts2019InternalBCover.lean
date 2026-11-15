import AllThoseRamseyClasses.Published.TrackECoordinated2019InternalBCover
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CoveredSparseWitness

/-!
# Track E: actual full-root whole-mask tagged source also has INTERNAL B copies

This is a direct specialization of the new ACTUAL coordinated 2019
relational theorem with internal B-extension. The ORIGINAL sources
are genuine transversal Option(Set) partial function systems, tagged
using the verified part-labelled full-root complete-mask language.

The entire final structure C is the SAME noncanonical tagged two-pass
picture. The theorem retains the original selected C→C0 projection,
full tagged Ramsey arrow, external protected closed-U test coverage,
and exact small K-relative completions, now with genuinely INTERNAL
full canonical with-parts tagged B-copies extending every ordinarily
irreducible induced tagged test.

No extra strict native mixed-root B-tree or canonical replacement of C
is asserted. The native set-valued-function B-copy descent is an
independent subsequent theorem; tagging and whole-mask decoding may not
be conflated with an arbitrary relational reduct.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- An ACTUAL corrected 2019 two-pass tagged witness with all original
certificates and INTERNAL full Btag-copy extension simultaneously, on
one final exact carrier, under the same original class hypotheses. -/
theorem genuineWithParts2019_profile_sparse_with_INTERNAL_B_coverage
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
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
      (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VQ),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C ∧
      (∃ f : VQ → Z, IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 f) ∧
      (∀ {T : Type w}
        (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        Embedding Test C →
        Nonempty (Embedding Test (genuineWithPartsTagged2019 B partB))) ∧
      IrreduciblesExtendTo (genuineWithPartsTagged2019 B partB) C ∧
      (∀ S : Finset VQ, S.card ≤ n →
        HasInducedClosedUKCompletion K
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce (↑S : Set VQ))) ∧
      StructuralRamsey.Arrow
        (genuineWithPartsTagged2019 A partA)
        (genuineWithPartsTagged2019 B partB) C κ := by
  exact coordinated2019_profile_sparse_witness_with_INTERNAL_B_coverage
    (genuineWithPartsTagged2019 A partA)
    (genuineWithPartsTagged2019 B partB) C0
    (A.withPartsWholeMaskTag_isUClosed partA hTransA)
    (B.withPartsWholeMaskTag_isUClosed partB hTransB)
    hBK hClosed hHer hStrong hKIrr n κ hArrow0

end AllThoseRamseyClasses.Published
