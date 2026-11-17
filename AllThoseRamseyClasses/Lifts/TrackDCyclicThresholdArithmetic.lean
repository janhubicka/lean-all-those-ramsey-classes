import Mathlib.Tactic

/-!
# Track D: all-m elementary arithmetic for cyclic source Gamma_m

For m≥3 the original cyclic graph on the residues
0,1,...,3m-2 has an edge when the difference in either cyclic
direction is in [m,2m-1]. Since 3m-1 minus any integer in that
interval lies in the same interval, this is equivalent to the
ordinary distance |x-y| in [m,2m-1] on these representatives.

The predicate below is deliberately on natural-number positions.
Restrict it to Fin (3*m-1) when constructing the eventual native
Source_m. Its arithmetic makes the key all-m facts transparent:
triangle-free, the root [m,2m-1] is independent, the private
E(a_j,b_k) condition is k≤j, and both types of nonedge from
0 have explicit length-three walks.

The ALL PAIRS length-three-path statement still requires proving
translation symmetry of the cyclic representation. Connectivity
and tuple-image closure require further arguments. These lemmas
are not called a full kernel proof of the infinite counterexample.
-/

namespace AllThoseRamseyClasses.Lifts

/-- Ordinary-coordinate presentation of cyclic Gamma_m on the
representatives 0,...,3m-2. Edges have distance in [m,2m-1]. -/
def cyclicThresholdEdge (m x y : ℕ) : Prop :=
  (x + m ≤ y ∧ y < x + 2 * m) ∨
  (y + m ≤ x ∧ x < y + 2 * m)

theorem cyclicThresholdEdge_symmetric (m x y : ℕ) :
    cyclicThresholdEdge m x y ↔ cyclicThresholdEdge m y x := by
  unfold cyclicThresholdEdge
  tauto

theorem cyclicThresholdEdge_irreflexive
    (m x : ℕ) (hm : 0 < m) :
    ¬ cyclicThresholdEdge m x x := by
  unfold cyclicThresholdEdge
  omega

/-- No E-triangle for any three positions, even before
restricting to the finite 3m-1 vertex set. This is stronger
than the finite graph's triangle-freeness. -/
theorem cyclicThresholdEdge_triangle_free
    (m x y z : ℕ) (hm : 0 < m) :
    ¬ (cyclicThresholdEdge m x y ∧
       cyclicThresholdEdge m y z ∧
       cyclicThresholdEdge m z x) := by
  unfold cyclicThresholdEdge
  omega

/-- The original cyclic source has precisely the m neighbours
m,...,2m-1 of its distinguished vertex 0. -/
theorem cyclicThresholdEdge_zero_neighbour_iff
    (m x : ℕ) (hm : 0 < m) :
    cyclicThresholdEdge m 0 x ↔ m ≤ x ∧ x < 2 * m := by
  unfold cyclicThresholdEdge
  omega

/-- The common root R_m = [m,2m-1] is independent. -/
theorem cyclicThresholdEdge_root_independent
    (m x y : ℕ)
    (hx : m ≤ x ∧ x < 2 * m)
    (hy : m ≤ y ∧ y < 2 * m) :
    ¬ cyclicThresholdEdge m x y := by
  unfold cyclicThresholdEdge
  omega

/-- For a_j=j, b_k=2m+k-1, the private E-edge has exactly
the triangular incidence pattern E(a_j,b_k) iff k≤j,
where 1≤j,k<m. This is used to rigidify the D-chain. -/
theorem cyclicThresholdEdge_private_iff
    (m j k : ℕ)
    (hm : 3 ≤ m)
    (hj : 1 ≤ j ∧ j < m)
    (hk : 1 ≤ k ∧ k < m) :
    cyclicThresholdEdge m j (2 * m + k - 1) ↔ k ≤ j := by
  unfold cyclicThresholdEdge
  omega

/-- Explicit length-three path from 0 to every SHORT nonedge
d∈{1,...,m-1}: 0 -- m -- 2m -- d. All intermediate
vertices are below 3m-1 when m≥3. -/
theorem cyclicThresholdEdge_short_nonedge_three_path
    (m d : ℕ)
    (hm : 3 ≤ m)
    (hd : 1 ≤ d ∧ d < m) :
    cyclicThresholdEdge m 0 m ∧
    cyclicThresholdEdge m m (2 * m) ∧
    cyclicThresholdEdge m (2 * m) d ∧
    2 * m < 3 * m - 1 := by
  unfold cyclicThresholdEdge
  omega

/-- Explicit length-three path from 0 to every LONG nonedge
d∈{2m,...,3m-2}: 0 -- (2m-1) -- (m-1) -- d. -/
theorem cyclicThresholdEdge_long_nonedge_three_path
    (m d : ℕ)
    (hm : 3 ≤ m)
    (hd : 2 * m ≤ d ∧ d < 3 * m - 1) :
    cyclicThresholdEdge m 0 (2 * m - 1) ∧
    cyclicThresholdEdge m (2 * m - 1) (m - 1) ∧
    cyclicThresholdEdge m (m - 1) d ∧
    2 * m - 1 < 3 * m - 1 := by
  unfold cyclicThresholdEdge
  omega

/-- The D-arcs in one private half are E-supported:
a_j -> b_j and b_j -> a_(j+1) for j+1<m. -/
theorem cyclicThresholdEdge_private_chain_arcs
    (m j : ℕ)
    (hm : 3 ≤ m)
    (hj : 1 ≤ j ∧ j + 1 < m) :
    cyclicThresholdEdge m j (2 * m + j - 1) ∧
    cyclicThresholdEdge m (2 * m + j - 1) (j + 1) := by
  unfold cyclicThresholdEdge
  omega

end AllThoseRamseyClasses.Lifts
