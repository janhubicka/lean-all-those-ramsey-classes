import AllThoseRamseyClasses.Applications.MetricGluingJumpWitness
import Mathlib.Data.Fintype.Lattice

/-!
# Attained shortest-path distances over a finite nonempty metric base

The existing crossing lemma `minimum_distanceSum_le_jump_iff_witness`
was intentionally conditional on (1) a lower bound for every
base-indexed two-edge candidate and (2) attainment of the lower
bound. For gluing two **finite** S-metric sides over a nonempty old
root, the index type is finite and inhabited, so these two hypotheses
follow immediately from choosing a minimizing base point.

This module makes that construction explicit, in exactly the
ordinary rounded-sum operation of the paper, not in an abstract
semigroup. No false minimum over the EMPTY base is used: empty-base
amalgamation is already handled by its own maximal-distance module.

For positive S, every proper jump j has the promised CROSSING
criterion: the shortest rounded two-edge distance is ≤ j exactly
when some base point lies at distance ≤ j from both endpoints.
This establishes the missing finite-minimum and attainment interface,
but it is not yet the triangle-inequality / strong-amalgamation
theorem for the whole nonempty-base pushout.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Select an actual finite-base point at which the rounded
two-edge path length is minimal. This is legitimate only because
the base is FINITE and NONEMPTY. Both legs are arbitrary real-valued
functions here; the S-valuedness hypotheses enter the next results. -/
noncomputable def finiteBaseShortestPoint
    (S : Set ℝ) {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ) : A :=
  Classical.choose
    (Finite.exists_min (fun a : A => distanceSum S (p a) (q a)))

/-- The attained distance of the shortest rounded two-edge path
across the base. This equals one of the actual candidates, not an
unattained real infimum. -/
noncomputable def finiteBaseShortestDistance
    (S : Set ℝ) {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ) : ℝ :=
  distanceSum S
    (p (finiteBaseShortestPoint S p q))
    (q (finiteBaseShortestPoint S p q))

/-- The shortest rounded path is a lower bound for EVERY candidate. -/
theorem finiteBaseShortestDistance_le
    (S : Set ℝ) {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ) (a : A) :
    finiteBaseShortestDistance S p q ≤
      distanceSum S (p a) (q a) :=
  Classical.choose_spec
    (Finite.exists_min (fun a : A => distanceSum S (p a) (q a))) a

/-- The minimum is ATTAINED at a concrete old base vertex.
No compactness, infinite infimum, or independent existence axiom
is used. -/
theorem finiteBaseShortestDistance_attained
    (S : Set ℝ) {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ) :
    ∃ a : A, finiteBaseShortestDistance S p q =
      distanceSum S (p a) (q a) :=
  ⟨finiteBaseShortestPoint S p q, rfl⟩

/-- Under the manuscript's well-defined rounded-sum convention,
the finite shortest cross distance is itself an allowed S-distance
when both side-to-base legs are positive S-distances. -/
theorem finiteBaseShortestDistance_mem
    {S : Set ℝ} (hS : WellDefined S)
    {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ) (hp : ∀ a, p a ∈ S)
    (hq : ∀ a, q a ∈ S) :
    finiteBaseShortestDistance S p q ∈ S :=
  hS _ (hp _) _ (hq _)

/-- The actual finite nonempty-base jump crossing theorem: a
cross-side pair is j-close precisely if its two endpoints share
a **shared base point** to which both are j-close.

The old abstract lemma's lower-bound and attainment premises are
DISCHARGED here by the finite minimum. Nullary S and empty base
are not silently assumed inhabited. -/
theorem finiteBaseShortestDistance_le_jump_iff_witness
    {S : Set ℝ} (hpos : Positive S)
    {A : Type u} [Finite A] [Nonempty A]
    (p q : A → ℝ) (hp : ∀ a, p a ∈ S)
    (hq : ∀ a, q a ∈ S)
    (j : ℝ) (hj : Jump S j) :
    finiteBaseShortestDistance S p q ≤ j ↔
      ∃ a : A, p a ≤ j ∧ q a ≤ j := by
  exact minimum_distanceSum_le_jump_iff_witness
    hpos p q hp hq j
    (finiteBaseShortestDistance S p q) hj
    (finiteBaseShortestDistance_le S p q)
    (finiteBaseShortestDistance_attained S p q)

end AllThoseRamseyClasses.Applications.MetricSaturation
