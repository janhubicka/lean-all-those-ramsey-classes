import AllThoseRamseyClasses.Applications.MetricFiniteBaseShortestCross

/-!
# Symmetry and allowed-distance bounds of a finite-base shortest path

The preceding finite-base construction picks one minimum of the
rounded path lengths `p(a) ⊕ q(a)`. This module verifies two further
requirements for a metric amalgam:

* the cross-distance is symmetric when the sides are exchanged,
  even though the chosen minimizing base *vertex* may differ;
* if the two legs are positive allowed S-distances, the minimum
  is a positive S-distance, and it is bounded by any common maximum
  of S. In particular an off-side pair does NOT collapse to
  zero under the shortest-path gluing.

These are actual statements about the paper's rounded sum and the
finite-base minimum, not a blanket metric triangle theorem. The
nonempty-base triangle inequality, preservation of all prescribed
side distances, and the extended order remain open.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The shortest cross length is independent of which side is
called left, by commutativity of the actual rounded S-operation
and minimality on the same finite base. The minimizing *point*
need not be the same on the two sides. -/
theorem finiteBaseShortestDistance_comm
    (S : Set ℝ) {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ) :
    finiteBaseShortestDistance S p q =
      finiteBaseShortestDistance S q p := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := finiteBaseShortestDistance_attained S q p
    calc
      finiteBaseShortestDistance S p q ≤
        distanceSum S (p a) (q a) :=
          finiteBaseShortestDistance_le S p q a
      _ = distanceSum S (q a) (p a) :=
        distanceSum_comm S (p a) (q a)
      _ = finiteBaseShortestDistance S q p := ha.symm
  · obtain ⟨a, ha⟩ := finiteBaseShortestDistance_attained S p q
    calc
      finiteBaseShortestDistance S q p ≤
        distanceSum S (q a) (p a) :=
          finiteBaseShortestDistance_le S q p a
      _ = distanceSum S (p a) (q a) :=
        distanceSum_comm S (q a) (p a)
      _ = finiteBaseShortestDistance S p q := ha.symm

/-- An attained finite rounded shortest path between two separate
sides is strictly positive: its length is itself in the permitted
positive distance set. This prevents identification of distinct
cross-side vertices in the eventual pushout metric. -/
theorem finiteBaseShortestDistance_pos
    {S : Set ℝ} (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ)
    (hp : ∀ a, p a ∈ S) (hq : ∀ a, q a ∈ S) :
    0 < finiteBaseShortestDistance S p q :=
  hpos _ (finiteBaseShortestDistance_mem hS p q hp hq)

/-- A common upper bound on S also bounds the resulting rounded
finite-base cross distance, because the chosen minimum is an ACTUAL
S-element and not a real-valued unattained infimum. -/
theorem finiteBaseShortestDistance_le_upper
    {S : Set ℝ} (hS : WellDefined S)
    {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ)
    (hp : ∀ a, p a ∈ S) (hq : ∀ a, q a ∈ S)
    (m : ℝ) (hmax : ∀ s ∈ S, s ≤ m) :
    finiteBaseShortestDistance S p q ≤ m :=
  hmax _ (finiteBaseShortestDistance_mem hS p q hp hq)

end AllThoseRamseyClasses.Applications.MetricSaturation
