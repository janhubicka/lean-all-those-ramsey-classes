import AllThoseRamseyClasses.Lifts.TrackDCyclicThresholdArithmetic
import Mathlib.Tactic

/-!
# m explicitly internally vertex-disjoint paths in cyclic Gamma_m

Gamma_m has m vertices adjacent to 0, namely m,...,2m-1.
For each short nonedge 0<d<m there is a family of m pairwise
internally disjoint paths from 0 to d, indexed i=0,...,m-1:

  if i<d,   0 -- (m+i) -- (2m+i) -- d
  if d≤i<m, 0 -- (m+i) -- d.

All edge and interior-index inequalities are proved for every m≥3.
The two possible interior bands are disjoint. The other nonedges
from 0 are obtained by reflecting the circular ordering, and
other endpoints by translating the Z/(3m-1) coordinates.

This is a step toward proving kappa(Gamma_m)=m and thus
regularity of the original large connected forbidden sources.
This module itself does NOT yet formalize cyclic rotations,
Menger's conclusion or the full graph vertex-connectivity theorem.
-/

namespace AllThoseRamseyClasses.Lifts

/-- When i<d, 0→m+i→2m+i→d is a legal three-edge path;
the second intermediate vertex is inside the 3m-1 carrier. -/
theorem cyclicThresholdShortPath_i_lt_d
    (m d i : ℕ)
    (hm : 3 ≤ m)
    (hd : 1 ≤ d ∧ d < m)
    (hi : i < d) :
    cyclicThresholdEdge m 0 (m + i) ∧
    cyclicThresholdEdge m (m + i) (2 * m + i) ∧
    cyclicThresholdEdge m (2 * m + i) d ∧
    2 * m + i < 3 * m - 1 := by
  simp only [cyclicThresholdEdge]
  omega

/-- When d≤i<m, 0→m+i→d is a legal two-edge path.
Its unique intermediate vertex is inside the carrier. -/
theorem cyclicThresholdShortPath_d_le_i
    (m d i : ℕ)
    (hm : 3 ≤ m)
    (hd : 1 ≤ d ∧ d < m)
    (hi : d ≤ i ∧ i < m) :
    cyclicThresholdEdge m 0 (m + i) ∧
    cyclicThresholdEdge m (m + i) d ∧
    m + i < 3 * m - 1 := by
  simp only [cyclicThresholdEdge]
  omega

/-- Record the two possible private vertices used by path i:
the first is always m+i; the second exists only when i<d. -/
def cyclicThresholdShortPathInterior (m d i v : ℕ) : Prop :=
  v = m + i ∨ (i < d ∧ v = 2 * m + i)

/-- Different path indices NEVER share an internal vertex.
The proof checks first/first, first/second, second/first and
second/second coincidences, relying only on i,j<m. -/
theorem cyclicThresholdShortPaths_pairwise_interior_disjoint
    (m d i j v : ℕ)
    (hi : i < m) (hj : j < m)
    (hij : i ≠ j)
    (hvi : cyclicThresholdShortPathInterior m d i v)
    (hvj : cyclicThresholdShortPathInterior m d j v) :
    False := by
  change v = m + i ∨ (i < d ∧ v = 2 * m + i) at hvi
  change v = m + j ∨ (j < d ∧ v = 2 * m + j) at hvj
  rcases hvi with hvi | ⟨_, hvi⟩
  · rcases hvj with hvj | ⟨_, hvj⟩ <;> omega
  · rcases hvj with hvj | ⟨_, hvj⟩ <;> omega

/-- No internal vertex lies at either of the two endpoints
of the short nonedge. -/
theorem cyclicThresholdShortPaths_avoid_endpoints
    (m d i v : ℕ)
    (hd : 1 ≤ d ∧ d < m)
    (hi : i < m)
    (hv : cyclicThresholdShortPathInterior m d i v) :
    v ≠ 0 ∧ v ≠ d := by
  change v = m + i ∨ (i < d ∧ v = 2 * m + i) at hv
  rcases hv with hv | ⟨_, hv⟩ <;> omega

end AllThoseRamseyClasses.Lifts
