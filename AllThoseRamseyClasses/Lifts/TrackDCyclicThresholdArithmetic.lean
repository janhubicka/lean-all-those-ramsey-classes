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


/-- EVERY distinct nonadjacent ordered pair x<y among the
3m-1 cyclic representatives has a three-edge path. We avoid
any appeal to modular translation or a graph automorphism:
there are three short-distance cases, depending on whether
x+m and x+2m wrap past the end of the representative interval,
and one long-distance case.

If y<x+m, explicit paths are
 (i)  x, x+m, x+2m, y                when x+2m < N,
 (ii) x, x+m, x-m+1, y              when x+m<N≤x+2m,
 (iii)x, x-2m+1, x-m+1, y           when N≤x+m.
If x+m≤y (and E(x,y) is false), then x+2m≤y and the path is
       x, x+2m-1, x+m-1, y.
All intermediate positions remain in [0,N-1], N=3m-1. -/
theorem cyclicThresholdEdge_ordered_nonedge_three_path
    (m x y : ℕ)
    (hm : 3 ≤ m)
    (hxy : x < y)
    (hy : y < 3 * m - 1)
    (hNonedge : ¬ cyclicThresholdEdge m x y) :
    ∃ p q : ℕ,
      p < 3 * m - 1 ∧ q < 3 * m - 1 ∧
      cyclicThresholdEdge m x p ∧
      cyclicThresholdEdge m p q ∧
      cyclicThresholdEdge m q y := by
  by_cases hShort : y < x + m
  · by_cases hWithinTwo : x + 2 * m < 3 * m - 1
    · refine ⟨x + m, x + 2 * m, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try simp only [cyclicThresholdEdge]) <;> omega
    · by_cases hWithinOne : x + m < 3 * m - 1
      · refine ⟨x + m, x + 1 - m, ?_, ?_, ?_, ?_, ?_⟩
        all_goals (try simp only [cyclicThresholdEdge]) <;> omega
      · refine ⟨x + 1 - 2 * m, x + 1 - m, ?_, ?_, ?_, ?_, ?_⟩
        all_goals (try simp only [cyclicThresholdEdge]) <;> omega
  · have hLong : x + 2 * m ≤ y := by
      unfold cyclicThresholdEdge at hNonedge
      omega
    refine ⟨x + 2 * m - 1, x + m - 1, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp only [cyclicThresholdEdge]) <;> omega

/-- The full all-m cyclic nonedge-to-three-edge-path property,
now for arbitrary distinct FINITE source vertices in either
order. The reverse-order case just reverses the witness path
using the proved edge symmetry.

Together with triangle-freeness and the merged generic
collision-to-triangle lemma this settles the all-m graph-geometric
part of printed tuple-image closure, but NOT the extra original
unary/D/T-fullness and complete native family closure statement. -/
theorem cyclicThresholdEdge_any_nonedge_three_path
    (m : ℕ) (hm : 3 ≤ m)
    (x y : Fin (3 * m - 1))
    (hNe : x ≠ y)
    (hNonedge : ¬ cyclicThresholdEdge m x.val y.val) :
    ∃ p q : Fin (3 * m - 1),
      cyclicThresholdEdge m x.val p.val ∧
      cyclicThresholdEdge m p.val q.val ∧
      cyclicThresholdEdge m q.val y.val := by
  have hNeVal : x.val ≠ y.val := by
    intro h
    exact hNe (Fin.ext h)
  by_cases hxy : x.val < y.val
  · obtain ⟨p, q, hp, hq, hxp, hpq, hqy⟩ :=
      cyclicThresholdEdge_ordered_nonedge_three_path
        m x.val y.val hm hxy y.isLt hNonedge
    exact ⟨⟨p, hp⟩, ⟨q, hq⟩, hxp, hpq, hqy⟩
  · have hyx : y.val < x.val := by omega
    have hNonedgeReverse :
        ¬ cyclicThresholdEdge m y.val x.val := by
      intro h
      exact hNonedge
        ((cyclicThresholdEdge_symmetric m y.val x.val).mp h)
    obtain ⟨p, q, hp, hq, hyp, hpq, hqx⟩ :=
      cyclicThresholdEdge_ordered_nonedge_three_path
        m y.val x.val hm hyx x.isLt hNonedgeReverse
    refine ⟨⟨q, hq⟩, ⟨p, hp⟩, ?_, ?_, ?_⟩
    · exact (cyclicThresholdEdge_symmetric m q x.val).mp hqx
    · exact (cyclicThresholdEdge_symmetric m p q).mp hpq
    · exact (cyclicThresholdEdge_symmetric m y.val p).mp hyp

end AllThoseRamseyClasses.Lifts
