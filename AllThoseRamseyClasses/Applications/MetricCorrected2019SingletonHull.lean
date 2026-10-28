import AllThoseRamseyClasses.Published.InducedClosed2019MainContract
import AllThoseRamseyClasses.Applications.MetricWeakCandidateFiniteHulls
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# The exact corrected 2019 closed-irreducible test protects every one-generated U-hull

The earlier algebraic investigation of one-generated Option-function
hulls found a potentially noncircular route to the printed metric
local-completion proof. Here we use the ACTUAL corrected 2019
hypothesis (4b), not a newly invented stand-alone notion of
join-irreducibility.

The reusable partite-construction theorem
`IsUClosed.singleton_hull_isUIrreducible` ALREADY certifies
that if C is genuinely U-closed, the induced structure on
its U-closure hull of {x} is both U-closed and intrinsically
U-irreducible. Therefore the corrected source-membership
hypothesis immediately puts this ORIGINAL generated substructure
in K -- regardless of the size of the hull.

For a weak Option-valued metric-functional candidate, deriving
the normal form F_j(x)=y, F_k(y)=z => j<k and F_k(x)=z
from the membership of the one-generated U-hull needs
two additional EXACT semantic conditions:
1. every original defined F_j value stays within that U-hull;
2. membership of the induced hull in K gives the original
   Option-valued composition normal form on its vertices.

We state both conditions openly rather than silently identify
the relational U-closure with the functional F_j orbit.
Under them, the candidate has the normal form on ALL vertices,
and the already checked small-hull theorem produces closed
m-seed supports of cardinal <=m(|J|+1), without prior use of
the desired local cutoff.

The first K-membership theorem is source-matched to corrected
Definition 2.17(4b). The subsequent application remains a
conditional bridge until the precise U-closure dictionary and
functional shadow equivalence are verified. In particular
the printed cycle-compression and exact weak local completion
cutoff remain open.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

universe u v

/-- The CORRECTED paper 2019(4b), not merely a generic
join-irreducibility surrogate, ensures that the actual
one-generated U-closure hull belongs to K. The paper's
test is the original induced substructure on precisely
that hull's carrier. -/
theorem corrected2019_singleton_Uhull_mem
    {L : RelLanguage.{u}}
    {A : Type v}
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L A)
    (hC : IsUClosed rules C)
    (hCovered : CorrectedUIrreduciblesIn K rules C)
    (x : A) :
    K (C.induce (UClosureHull rules C {x})) := by
  exact hCovered (UClosureHull rules C {x})
    (hC.induce_UClosureHull {x})
    (hC.singleton_hull_isUIrreducible x)

/-- EXPLICIT conditional dictionary from relational corrected
2019 membership to the original weak Option-valued source:
if every F_j value is contained in the one-generated U-hull
and valid K-hulls satisfy the composition law there, the
candidate composition normal form holds GLOBALLY. -/
theorem corrected2019_candidate_normalform_of_singleton_hull
    {L : RelLanguage.{u}}
    {A : Type v}
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L A)
    (hC : IsUClosed rules C)
    (hCovered : CorrectedUIrreduciblesIn K rules C)
    (J : Finset ℝ)
    (f : ℝ → A → Option A)
    (hFrespectsU : ∀ a : A, ∀ j ∈ J,
      ∀ x ∈ UClosureHull rules C {a}, ∀ y : A,
        f j x = some y →
        y ∈ UClosureHull rules C {a})
    (hValidPiece : ∀ T : Set A,
      K (C.induce T) →
      ∀ j ∈ J, ∀ k ∈ J, ∀ x y z : A,
        x ∈ T → y ∈ T → z ∈ T →
        f j x = some y → f k y = some z →
        j < k ∧ f k x = some z) :
    ∀ j ∈ J, ∀ k ∈ J, ∀ x y z : A,
      f j x = some y → f k y = some z →
      j < k ∧ f k x = some z := by
  intro j hj k hk x y z hxy hyz
  let T : Set A := UClosureHull rules C {x}
  have hx : x ∈ T := by
    exact subset_UClosureHull rules C {x} (by simp)
  have hy : y ∈ T := hFrespectsU x j hj x hx y hxy
  have hz : z ∈ T := hFrespectsU x k hk y hy z hyz
  have hK : K (C.induce T) :=
    corrected2019_singleton_Uhull_mem K rules C hC hCovered x
  exact hValidPiece T hK j hj k hk x y z hx hy hz hxy hyz

/-- Conditional finite weak candidate hull bound under the
ACTUAL corrected 2019 closed-irreducible membership test.
No assumption that a small CLOSED support exists is made;
the two explicit semantics-compatibility hypotheses are
the only remaining premises needed for this consequence. -/
theorem corrected2019_candidate_finite_hull_of_singleton_hull
    {L : RelLanguage.{u}}
    {A : Type v}
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L A)
    (hC : IsUClosed rules C)
    (hCovered : CorrectedUIrreduciblesIn K rules C)
    (J : Finset ℝ)
    (f : ℝ → A → Option A)
    (hFrespectsU : ∀ a : A, ∀ j ∈ J,
      ∀ x ∈ UClosureHull rules C {a}, ∀ y : A,
        f j x = some y →
        y ∈ UClosureHull rules C {a})
    (hValidPiece : ∀ T : Set A,
      K (C.induce T) →
      ∀ j ∈ J, ∀ k ∈ J, ∀ x y z : A,
        x ∈ T → y ∈ T → z ∈ T →
        f j x = some y → f k y = some z →
        j < k ∧ f k x = some z)
    (seeds : List A) :
    ∃ D : Finset A,
      (∀ x ∈ seeds, x ∈ D) ∧
      D.card ≤ seeds.length * (J.card + 1) ∧
      MetricCandidateFinsetClosed J f D := by
  have hNormal : ∀ j ∈ J, ∀ k ∈ J, ∀ x y z : A,
      f j x = some y → f k y = some z →
      f k x = some z := by
    intro j hj k hk x y z hxy hyz
    exact (corrected2019_candidate_normalform_of_singleton_hull
      K rules C hC hCovered J f hFrespectsU hValidPiece
      j hj k hk x y z hxy hyz).2
  exact metricCandidateFiniteHull_list_exists J f hNormal seeds

end AllThoseRamseyClasses.Applications.MetricSaturation
