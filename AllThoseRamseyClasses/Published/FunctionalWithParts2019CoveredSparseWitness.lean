import AllThoseRamseyClasses.Published.FunctionalWithParts2019ProfileSparseWitness

/-!
# 2019 two-pass functional source keeps the actual final B-cover certificate

The already verified 2019 generated-profile sparsening theorem constructs
more than it formerly returned: in its second U-closed tagged Picture,
EVERY closed U-irreducible test embeds fully into the canonical tagged B.

The new B-coverage interface of the coordinated theorem is specialized
here to actual part-labelled, genuinely partial Option(Set)-valued
source structures. No intermediate relational Picture must decode
to genuine functions; only the FINAL tagged target requires that,
and its complete B-cover certificate supplies the necessary
output-domain coherence.

The original n-cutoff is unchanged: each weak test S keeps its
literal vertex set, and target completion uses its exact image,
never a larger ambient closure hull.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The verified two-pass generated-profile witness specialized to
part-labelled full-root complete-mask sources, INCLUDING its full
canonical B-copy coverage. This output is strictly stronger than
the original `HasInducedClosed2019SparseWitness`, without changing
any source assumption or induction. -/
theorem genuineWithParts2019_profile_sparse_with_B_coverage
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
      (∀ S : Finset VQ, S.card ≤ n →
        HasInducedClosedUKCompletion K
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce (↑S : Set VQ))) ∧
      StructuralRamsey.Arrow
        (genuineWithPartsTagged2019 A partA)
        (genuineWithPartsTagged2019 B partB) C κ := by
  exact coordinated2019_profile_sparse_witness_with_B_coverage
    (genuineWithPartsTagged2019 A partA)
    (genuineWithPartsTagged2019 B partB) C0
    (A.withPartsWholeMaskTag_isUClosed partA hTransA)
    (B.withPartsWholeMaskTag_isUClosed partB hTransB)
    hBK hClosed hHer hStrong hKIrr n κ hArrow0

end AllThoseRamseyClasses.Published
