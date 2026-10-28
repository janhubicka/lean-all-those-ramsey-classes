import AllThoseRamseyClasses.Published.FunctionalWithParts2019ProfileSparseWitness
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019
import PartiteConstruction.Functional.WholeMaskTagArrow2019

/-!
# The verified 2019 two-pass sparsening starts from a GENUINE partial Ramsey arrow

Previously the part-labelled functional specialization expected an
initial Ramsey arrow in the canonical tagged relational language.
Here we obtain that arrow from the actual part-preserving Ramsey arrow
for genuine Option(Set)-valued functions, without changing its vertices.

Step 1: Full genuinely partial, part-preserving embeddings are
equivalent to full embeddings of the canonical OLD complete-mask graph
AFTER naming all vertex parts by unary predicates.
Step 2: Canonical full-root tagging lifts an OLD relational Ramsey arrow
to the U-closed 2019 closure language.
Step 3: Apply the ALREADY VERIFIED coordinated 2019 two-pass sparse
witness constructor, now with genuine partial A,B,C0 as input.

The resulting intermediate output is a RELATIONAL closed sparse witness.
At no stage is it assumed that an arbitrary intermediate relational
Picture has already decoded coherent partial functions or strict
functional B-tree completions. The final target must be normalized
using protected B-copy coverage and its decoded functional Ramsey
arrow/local K-completions transferred separately.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The canonical part-labelled full-root tagging of actual genuine
partial structures turns any TRUE partite Ramsey arrow into a relational
2019 arrow, with no change of vertex carrier or function domain bits. -/
theorem genuineWithParts2019_arrow_of_functional
    {X Y Z : Type w} [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : PartialSetStructure L Z) (part0 : Z → Parts)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hTrans0 : FibreTransversal C0 part0)
    (κ : Type*)
    (hArrow : PartPreservingArrow A partA B partB C0 part0 κ) :
    StructuralRamsey.Arrow
      (genuineWithPartsTagged2019 A partA)
      (genuineWithPartsTagged2019 B partB)
      (genuineWithPartsTagged2019 C0 part0) κ := by
  have hOld : StructuralRamsey.Arrow
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB)
      (withPartsWholeMaskOld C0 part0) κ :=
    (partPreservingArrow_iff_withPartsWholeMaskOld
      A partA B partB C0 part0
      hTransA hTransB hTrans0 κ).mp hArrow
  exact wholeMaskTag_arrow
    (withPartsWholeMaskOld A partA)
    (withPartsWholeMaskOld B partB)
    (withPartsWholeMaskOld C0 part0) κ hOld

/-- Construct the REAL 2019 two-pass closed sparse relational Picture
directly from a genuine partial-function partite Ramsey witness C0.
There is NO native maximal-mixed strict functional tree assumption.

The exact weak source test bound is still the user's original n.
The final genuine partial-function target and its K-completion map
must be decoded from this intermediate relational witness separately. -/
theorem genuineWithParts2019_profile_sparse_from_functional_arrow
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : PartialSetStructure L Z) (part0 : Z → Parts)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hTrans0 : FibreTransversal C0 part0)
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
    (hArrow : PartPreservingArrow A partA B partB C0 part0 κ) :
    HasInducedClosed2019SparseWitness K
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (genuineWithPartsTagged2019 A partA)
      (genuineWithPartsTagged2019 B partB)
      (genuineWithPartsTagged2019 C0 part0) n κ := by
  exact genuineWithParts2019_profile_sparse_witness
    A partA B partB (genuineWithPartsTagged2019 C0 part0)
    hTransA hTransB hBK hClosed hHer hStrong hKIrr n κ
    (genuineWithParts2019_arrow_of_functional
      A partA B partB C0 part0
      hTransA hTransB hTrans0 κ hArrow)

end AllThoseRamseyClasses.Published
