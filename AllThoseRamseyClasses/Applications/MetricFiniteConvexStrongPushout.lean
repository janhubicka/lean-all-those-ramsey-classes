import AllThoseRamseyClasses.Applications.MetricFiniteJumpEnumeration
import AllThoseRamseyClasses.Applications.MetricRealRootClassKeys
import AllThoseRamseyClasses.Applications.MetricRootedClassKeyGluing
import AllThoseRamseyClasses.Applications.MetricRootedAllJumpKeyOrder
import Mathlib.Tactic

/-!
# Complete compatible convex order on the finite rooted S-metric pushout

This closes the ORDER component of nonempty-base strong amalgamation
for finite convexly ordered S-metric spaces, without adding the
auxiliary closure functions F_j.

Given two finite genuine convexly ordered S-metrics U,V and a
finite common metric root A, with isometric strict order
embeddings, use the already verified rounded shortest-path
metric on the identified-base carrier. We construct ONE linear
order on this SAME carrier that extends both given orders
and is convex at EVERY proper jump j of S.

The construction is independently validated in six steps:

* enumerate exactly the finite set of proper jumps in increasing order;
* for each proper j choose the canonical finite metric side keys;
* glue them at the root (the cross-side equality theorem detects
  precisely the shortest-path threshold class);
* obtain one family of exact metric class labels;
* prove that the family is nested (finer classes first);
* apply the verified finite-hierarchy lexicographic refinement.

The theorem is about the original metric language with convex order,
NOT automatically about the auxiliary partial functions F_j.
The latter and the arbitrary weak-candidate local-completion bound
in the printed 2019 proof remain separate verification obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

open AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w

/-- A single compatible jump-convex linear order exists on the
ACTUAL finite nonempty-root shortest-path S-metric pushout.
No extra existence hypotheses on class labels are assumed. -/
theorem metricRooted_finiteS_jumpConvexOrder_exists
    {S : Set ℝ}
    (hfinite : S.Finite)
    (hpos : Positive S)
    (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A] [LinearOrder A]
    [Finite U] [LinearOrder U]
    [Finite V] [LinearOrder V]
    {dA : A → A → ℝ}
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdA : MetricOn S dA)
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hconvU : JumpConvex S dU)
    (hconvV : JumpConvex S dV)
    (iU : A → U) (iV : A → V)
    (hiUOrder : StrictMono iU)
    (hiVOrder : StrictMono iV)
    (hiUDist : ∀ a b : A,
      dU (iU a) (iU b) = dA a b)
    (hiVDist : ∀ a b : A,
      dV (iV a) (iV b) = dA a b) :
    ∃ (o : LinearOrder (MetricRootedAmalgamVertex iU iV)),
      (∀ x y : U, x < y →
        @LT.lt _ o.toLT
          (metricRootedLeft iU iV hiUOrder.injective x)
          (metricRootedLeft iU iV hiUOrder.injective y)) ∧
      (∀ x y : V, x < y →
        @LT.lt _ o.toLT
          (metricRootedRight iU iV hiVOrder.injective x)
          (metricRootedRight iU iV hiVOrder.injective y)) ∧
      (@JumpConvex (MetricRootedAmalgamVertex iU iV) o S
        (metricRootedShortestDistance S iU iV dU dV)) := by
  classical
  let K := ℕ ×ₗ (ℕ ×ₗ ℕ)
  let W := MetricRootedAmalgamVertex iU iV
  let left : U → W :=
    metricRootedLeft iU iV hiUOrder.injective
  let right : V → W :=
    metricRootedRight iU iV hiVOrder.injective
  let dW : W → W → ℝ :=
    metricRootedShortestDistance S iU iV dU dV
  have hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b) := by
    intro a b
    exact (hiUDist a b).trans (hiVDist a b).symm
  have hOrd : ∀ a b : A,
      iU a < iU b ↔ iV a < iV b := by
    intro a b
    constructor
    · intro h
      have hab : a < b := by
        by_contra hn
        exact (not_lt_of_ge
          (hiUOrder.monotone (le_of_not_gt hn))) h
      exact hiVOrder hab
    · intro h
      have hab : a < b := by
        by_contra hn
        exact (not_lt_of_ge
          (hiVOrder.monotone (le_of_not_gt hn))) h
      exact hiUOrder hab
  have hExists : ∀ j : ℝ,
      ∃ (keyU : U → K) (keyV : V → K),
        Jump S j →
          Monotone keyU ∧ Monotone keyV ∧
          (∀ a : A, keyU (iU a) = keyV (iV a)) ∧
          (∀ x y : U, keyU x = keyU y ↔ dU x y ≤ j) ∧
          (∀ z t : V, keyV z = keyV t ↔ dV z t ≤ j) ∧
          (∀ x : U, ∀ z : V,
            keyU x = keyV z ↔
              ∃ a : A, dU x (iU a) ≤ j ∧ dV (iV a) z ≤ j) := by
    intro j
    by_cases hj : Jump S j
    · obtain ⟨ku, kv, hmu, hmv, hroot,
        hsameU, hsameV, hcross⟩ :=
        metricRootJump_sideClassKeys_exist
          hpos hS hdA hdU hdV hconvU hconvV
          iU iV hiUOrder hiVOrder
          hiUDist hiVDist j hj
      exact ⟨ku, kv, fun _ =>
        ⟨hmu, hmv, hroot, hsameU, hsameV, hcross⟩⟩
    · let defaultKey : K := toLex (0, toLex (0, 0))
      exact ⟨fun _ => defaultKey, fun _ => defaultKey,
        fun h => False.elim (hj h)⟩
  let keyU (j : ℝ) : U → K := Classical.choose (hExists j)
  let keyV (j : ℝ) : V → K :=
    Classical.choose (Classical.choose_spec (hExists j))
  have hKeyFacts (j : ℝ) (hj : Jump S j) :
      Monotone (keyU j) ∧ Monotone (keyV j) ∧
      (∀ a : A, keyU j (iU a) = keyV j (iV a)) ∧
      (∀ x y : U, keyU j x = keyU j y ↔ dU x y ≤ j) ∧
      (∀ z t : V, keyV j z = keyV j t ↔ dV z t ≤ j) ∧
      (∀ x : U, ∀ z : V,
        keyU j x = keyV j z ↔
          ∃ a : A, dU x (iU a) ≤ j ∧ dV (iV a) z ≤ j) := by
    exact (Classical.choose_spec
      (Classical.choose_spec (hExists j))) hj
  let key (j : ℝ) : W → K :=
    metricRootedClassKey iU iV (keyU j) (keyV j)
  let jumps : List ℝ := finiteJumpThresholdList S hfinite
  have hJumps : jumps.Pairwise (· < ·) :=
    finiteJumpThresholdList_pairwise S hfinite
  have hExact :
      ∀ j ∈ jumps, ∀ p q : W,
        key j p = key j q ↔ dW p q ≤ j := by
    intro j hj p q
    have hJump : Jump S j :=
      (mem_finiteJumpThresholdList_iff S hfinite j).mp hj
    obtain ⟨_hmu, _hmv, hroot, hsameU,
      hsameV, hcross⟩ := hKeyFacts j hJump
    exact metricRootedClassKey_eq_iff_distance
      hpos hS hassoc iU iV
      hiUOrder.injective hiVOrder.injective
      hdU hdV hBase j hJump
      (keyU j) (keyV j)
      hroot hsameU hsameV hcross p q
  have hNested : NestedLevels (jumps.map key) :=
    thresholdClassKeys_nested dW key jumps hJumps hExact
  have hCover : ∀ j : ℝ, Jump S j →
      ∃ label ∈ jumps.map key, ∀ p q : W,
        label p = label q ↔ dW p q ≤ j := by
    apply thresholdClassKeys_cover S dW key jumps
    · intro j hj
      exact (mem_finiteJumpThresholdList_iff
        S hfinite j).mpr hj
    · exact hExact
  have hMonoLeft :
      ∀ label ∈ jumps.map key, ∀ x y : U, x < y →
        label (left x) ≤ label (left y) := by
    intro label hl x y hxy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    have hJump : Jump S j :=
      (mem_finiteJumpThresholdList_iff S hfinite j).mp hj
    obtain ⟨hmu, _, _, _, _, _⟩ := hKeyFacts j hJump
    change metricRootedClassKey iU iV (keyU j) (keyV j)
        (left x) ≤
      metricRootedClassKey iU iV (keyU j) (keyV j)
        (left y)
    rw [metricRootedClassKey_left
      iU iV hiUOrder.injective (keyU j) (keyV j) x,
      metricRootedClassKey_left
        iU iV hiUOrder.injective (keyU j) (keyV j) y]
    exact hmu (le_of_lt hxy)
  have hMonoRight :
      ∀ label ∈ jumps.map key, ∀ x y : V, x < y →
        label (right x) ≤ label (right y) := by
    intro label hl x y hxy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    have hJump : Jump S j :=
      (mem_finiteJumpThresholdList_iff S hfinite j).mp hj
    obtain ⟨_, hmv, hroot, _, _, _⟩ := hKeyFacts j hJump
    change metricRootedClassKey iU iV (keyU j) (keyV j)
        (right x) ≤
      metricRootedClassKey iU iV (keyU j) (keyV j)
        (right y)
    rw [metricRootedClassKey_right
      iU iV hiVOrder.injective (keyU j) (keyV j) hroot x,
      metricRootedClassKey_right
        iU iV hiVOrder.injective (keyU j) (keyV j) hroot y]
    exact hmv (le_of_lt hxy)
  exact metricRooted_allJumpConvexOrder_of_keys
    S iU iV hiUOrder.injective hiVOrder.injective hOrd
    dU dV (jumps.map key)
    hNested hCover hMonoLeft hMonoRight

end AllThoseRamseyClasses.Applications.MetricSaturation
