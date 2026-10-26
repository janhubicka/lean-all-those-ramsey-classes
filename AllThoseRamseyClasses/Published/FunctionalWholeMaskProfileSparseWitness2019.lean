import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness
import PartiteConstruction.Functional.WholeMaskClosureCanonical2019
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019

/-!
# Functional Appendix A via the verified 2019 generated-profile route

The complete-mask encoding of genuine Option(Set)-valued partial functions
is a U-closed structure with the *exact* 2019 full-root closure rules.
Under whole-fibre weak deletion, its intrinsic weak generator-size bound
agrees with USize on the induced ambient tagged graph on the SAME carrier.

Thus the published-style two-pass construction already checked in
Coordinated2019ProfileSparseWitness can be instantiated directly on
canonical genuine functional sources. It runs:

  closed initial Ramsey picture;
  generated-closure profile expansion;
  ordinary RELATIONAL strict-tree sparsening;
  a second U-closed tagged partite pass;
  final weak-test and copywise completion transfer.

In particular this route makes NO demand for the false uniform strict
functional B-tree completion of *intermediate* maximal mixed roots.
Generated closed boundaries are target-side witnesses, not replacements
for the exact weak vertex sets S or projected images p[S] being counted.

The conclusion is a relational U-closed sparse witness in the
complete-mask tagged language. Converting it to an actual
part-transversal genuine partial-function partite system requires
the independently verified final complete-mask decoder, correct
part-label semantics and the appropriate projection/Ramsey transfer.
This module does not declare that final transfer proved.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The exact 2019 U-closed presentation of a genuinely partial
set-valued structure with a fixed part map. Defined-empty and
undefined functions have different OLD domain information. -/
abbrev functionalWholeMask2019Canonical
    {X : Type w} (A : PartialSetStructure L X) (part : X → Parts) :
    RelStructure (L.wholeMaskTagLanguage Parts) X :=
  wholeMaskTagExpansion (A.wholeMaskPatternGraph part)

/-- No extra source closedness hypothesis: genuine transversal
partial functions satisfy precisely the full-root 2019 axioms. -/
theorem functionalWholeMask2019_canonical_UClosed
    {X : Type w} (A : PartialSetStructure L X)
    (part : X → Parts) (hTrans : FibreTransversal A part) :
    IsUClosed (L.wholeMaskClosureRules Parts)
      (functionalWholeMask2019Canonical A part) :=
  A.wholeMaskTagExpansion_isUClosed part hTrans

/-- The weak subset S is counted on its ORIGINAL carrier.
Its closure is computed *inside* S, not in the ambient source. -/
theorem functionalWholeMask2019_exactWeakRank_iff
    {X : Type w} [Finite X]
    (A : PartialSetStructure L X)
    (part : X → Parts) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set X) [Fintype S] (n : ℕ) :
    (wholeWeakInduce A S).GeneratedByAtMost n ↔
      USize (L.wholeMaskClosureRules Parts)
        ((functionalWholeMask2019Canonical A part).induce S) ≤ n :=
  A.wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
    part hPos hTrans S n

/-- Direct specialization of the ALREADY VERIFIED coordinated 2019
two-pass sparse-witness theorem to canonical function-language
complete-mask sources.

Only the relational completion-class hypotheses are left explicit.
There is NO hard-root functional B-tree premise, and the original
cutoff n and the original tagged control C0 are unchanged.

This is an intermediate relational sparse witness; the final genuine
partial-function structure is recovered through its separate decoder. -/
theorem functionalWholeMask2019_profile_sparse_witness
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : RelStructure (L.wholeMaskTagLanguage Parts) Z)
    (hATrans : FibreTransversal A partA)
    (hBTrans : FibreTransversal B partB)
    {K : StructureClass (L := L.wholeMaskTagLanguage Parts)}
    (hBK : K (functionalWholeMask2019Canonical B partB))
    (hClosed : ∀ {T : Type w}
      (E : RelStructure (L.wholeMaskTagLanguage Parts) T),
      K E → IsUClosed (L.wholeMaskClosureRules Parts) E)
    (hHer : ClosedUHereditary K (L.wholeMaskClosureRules Parts))
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {T : Type w}
      (E : RelStructure (L.wholeMaskTagLanguage Parts) T),
      K E → E.Irreducible)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : StructuralRamsey.Arrow
      (functionalWholeMask2019Canonical A partA)
      (functionalWholeMask2019Canonical B partB) C0 κ) :
    HasInducedClosed2019SparseWitness K
      (L.wholeMaskClosureRules Parts)
      (functionalWholeMask2019Canonical A partA)
      (functionalWholeMask2019Canonical B partB) C0 n κ := by
  exact coordinated2019_profile_sparse_witness
    (functionalWholeMask2019Canonical A partA)
    (functionalWholeMask2019Canonical B partB) C0
    (functionalWholeMask2019_canonical_UClosed A partA hATrans)
    (functionalWholeMask2019_canonical_UClosed B partB hBTrans)
    hBK hClosed hHer hStrong hKIrr n κ hArrow0

end AllThoseRamseyClasses.Published
