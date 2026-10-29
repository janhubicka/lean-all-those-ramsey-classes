import AllThoseRamseyClasses.Applications.MetricCorrectedCycleCutoffArithmetic
import Mathlib.Tactic

/-!
# Count actual exposed endpoints in the repaired metric-cycle cutoff

The original proof of `lem:finite4value2` does NOT test just the vertices
of the compressed cycle. It retains both endpoints of every collapsed
(unimportant) path. If the quotient has q vertices, p of them obtained
by collapsing disjoint paths, at most q+p original vertices are exposed.

For the ordinary compression case, q <= |S| and p <= q, so this is at
most 2|S|. In the exceptional case of `lem:Sequivalence`, the quotient
is deliberately kept as a TRIANGLE although |S| can be two; there is
then EXACTLY ONE distinguished unimportant path, giving q=3, p=1 and
q+p=4 <= 2|S| when |S|>=2. The bound max(3,|S|) alone would yield
2*max(3,|S|), which is too large for the original cutoff when |S|=2.

These elementary certificates account for the ACTUAL endpoint
multiplicity and the further <= |J| closures per exposed vertex.

Scope: the shape alternatives, the endpoint-support count and the
function-closure count are EXPLICIT hypotheses. We have not yet
proved existence of the compressed paths, their replacement-stability,
the required exact weak-source closure, or the final Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Two possible QUOTIENT SHAPES of the repaired compressed-cycle
argument. Ordinary compression has at most |S| quotient vertices
and each path consumes a distinct quotient vertex. The exceptional
single-path case keeps a triangle. -/
def MetricCycleQuotientShape (sCard q p : ℕ) : Prop :=
  (q ≤ sCard ∧ p ≤ q) ∨ (q = 3 ∧ p = 1)

/-- Even with the exceptional triangle, the number q+p of
original exposed endpoints is at most 2|S|, provided |S|>=2.
The fact that the exceptional case has p=1 is essential. -/
theorem metricCycleQuotientShape_exposed_le
    (sCard q p : ℕ)
    (hTwo : 2 ≤ sCard)
    (hShape : MetricCycleQuotientShape sCard q p) :
    q + p ≤ 2 * sCard := by
  rcases hShape with ⟨hq, hp⟩ | ⟨hq, hp⟩
  · omega
  · omega

/-- The corresponding finite S-cardinality statement follows
from the existence of a proper jump. -/
theorem metricCycleExposed_le_two_card_of_jump
    (S : Set ℝ) (hfin : S.Finite)
    {j : ℝ} (hj : Jump S j)
    (q p : ℕ)
    (hShape : MetricCycleQuotientShape hfin.toFinset.card q p) :
    q + p ≤ 2 * hfin.toFinset.card :=
  metricCycleQuotientShape_exposed_le
    hfin.toFinset.card q p
    (metricFiniteS_card_two_of_proper_jump hfin hj) hShape

/-- A source-faithful conditional bound for ANY finite distance set
with at least TWO allowed distances, regardless of whether there are
proper jumps. This covers the no-jump case, where |J|=0, as well.

The ordinary quotient shape and the exceptional single-path
triangle are explicit hypotheses. Closure-count and support-count
premises are NOT deduced from the printed weak local tests. -/
theorem metricCycleActualSupport_fits_printed_cutoff_of_two_distances
    (S : Set ℝ) (hfin : S.Finite)
    (hTwo : 2 ≤ hfin.toFinset.card)
    (q p originalVertices testedVertices : ℕ)
    (hShape : MetricCycleQuotientShape hfin.toFinset.card q p)
    (hOriginal : originalVertices ≤ q + p)
    (hTest : testedVertices ≤
      originalVertices * ((finiteJumpThresholdList S hfin).length + 1)) :
    testedVertices ≤ metricPrintedLocalCutoff S hfin := by
  have hCoefficient : originalVertices ≤ 2 * hfin.toFinset.card :=
    hOriginal.trans (metricCycleQuotientShape_exposed_le
      hfin.toFinset.card q p hTwo hShape)
  calc
    testedVertices ≤
        originalVertices * ((finiteJumpThresholdList S hfin).length + 1) :=
      hTest
    _ ≤ (2 * hfin.toFinset.card) *
          ((finiteJumpThresholdList S hfin).length + 1) :=
      Nat.mul_le_mul_right
        ((finiteJumpThresholdList S hfin).length + 1) hCoefficient
    _ = metricPrintedLocalCutoff S hfin := by
      rfl

/-- The preceding bound specialized to the presence of a proper
jump. This is the version used to compare with #704's corrected
vertex-count theorem. The stronger two-distance theorem also
covers finite distance sets having no proper jump. -/
theorem metricCycleActualSupport_fits_printed_cutoff_of_jump
    (S : Set ℝ) (hfin : S.Finite)
    {j : ℝ} (hj : Jump S j)
    (q p originalVertices testedVertices : ℕ)
    (hShape : MetricCycleQuotientShape hfin.toFinset.card q p)
    (hOriginal : originalVertices ≤ q + p)
    (hTest : testedVertices ≤
      originalVertices * ((finiteJumpThresholdList S hfin).length + 1)) :
    testedVertices ≤ metricPrintedLocalCutoff S hfin :=
  metricCycleActualSupport_fits_printed_cutoff_of_two_distances
    S hfin (metricFiniteS_card_two_of_proper_jump hfin hj)
    q p originalVertices testedVertices hShape hOriginal hTest

end AllThoseRamseyClasses.Applications.MetricSaturation
