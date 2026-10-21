import AllThoseRamseyClasses.Applications.MetricRootJumpClassTransport
import AllThoseRamseyClasses.Applications.MetricRootClassKeys

/-!
# Compatible finite class keys from ACTUAL convex S-metrics

The generic strictly increasing shared/private root-class keys have
now been proved. This module instantiates them on the genuine
j-equivalence classes of two finite convexly ordered S-metrics U,V,
over a common finite metric root A with isometric embeddings and
identical induced root vertex orders.

At each proper jump j it constructs two concrete key functions,
one on U and one on V, with all of the following exact laws:

* each key is monotone in its original vertex order;
* the two keys agree at EVERY original root vertex, not only
  at a selected representative of its root j-class;
* equality of two keys on one side is equivalent to d(x,y) ≤ j.

The constructed keys are the exact input for assembling a single
one-jump-convex order on the identified-base metric pushout.
The remaining cross-side equivalence of keys is studied via the
separate shared/private key criterion, and all-jump compatibility
via nested convex-order preservation.

This proves no assertion about arbitrary weak functional inputs
or the original printed local-completion cutoff.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

open AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w

/-- Two compatible isometric order embeddings of a common finite
S-metric root possess monotone class keys that identify each old
j-class correctly and coincide at every shared root vertex. -/
theorem metricRootJump_sideClassKeys_exist
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [LinearOrder A]
    [Finite U] [LinearOrder U]
    [Finite V] [LinearOrder V]
    {dA : A → A → ℝ}
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdA : MetricOn S dA)
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hconvU : JumpConvex S dU)
    (hconvV : JumpConvex S dV)
    (iU : A → U) (iV : A → V)
    (hiUOrder : StrictMono iU) (hiVOrder : StrictMono iV)
    (hiUDist : ∀ a b : A, dU (iU a) (iU b) = dA a b)
    (hiVDist : ∀ a b : A, dV (iV a) (iV b) = dA a b)
    (j : ℝ) (hj : Jump S j) :
    ∃ (keyU : U → ℕ ×ₗ (ℕ ×ₗ ℕ))
      (keyV : V → ℕ ×ₗ (ℕ ×ₗ ℕ)),
      Monotone keyU ∧ Monotone keyV ∧
      (∀ a : A, keyU (iU a) = keyV (iV a)) ∧
      (∀ x y : U, keyU x = keyU y ↔ dU x y ≤ j) ∧
      (∀ z t : V, keyV z = keyV t ↔ dV z t ≤ j) := by
  classical
  let R := MetricJumpClassRep hpos hdA j hj
  let K := MetricJumpClassRep hpos hdU j hj
  let L := MetricJumpClassRep hpos hdV j hj
  letI : Fintype R := Fintype.ofFinite R
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype L := Fintype.ofFinite L
  let rootU : R → K := fun a =>
    metricJumpClassTag hpos hS hdU j hj (iU a.val)
  let rootV : R → L := fun a =>
    metricJumpClassTag hpos hS hdV j hj (iV a.val)
  have hRootOrder : ∀ a b : R,
      rootU a < rootU b ↔ rootV a < rootV b := by
    intro a b
    exact metricRootJumpClassImages_agree_order
      hpos hS hdA hdU hdV hconvU hconvV
      iU iV hiUOrder hiVOrder
      hiUDist hiVDist j hj a b
  let keyU : U → ℕ ×ₗ (ℕ ×ₗ ℕ) := fun x =>
    classSideKey rootU 0 (metricJumpClassTag hpos hS hdU j hj x)
  let keyV : V → ℕ ×ₗ (ℕ ×ₗ ℕ) := fun z =>
    classSideKey rootV 1 (metricJumpClassTag hpos hS hdV j hj z)
  have hKeyU : StrictMono (classSideKey rootU 0) := by
    intro x y hxy
    exact classSideKey_strict rootU 0 (by omega) hxy
  have hKeyV : StrictMono (classSideKey rootV 1) := by
    intro x y hxy
    exact classSideKey_strict rootV 1 (by omega) hxy
  refine ⟨keyU, keyV, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact hKeyU.monotone
      (metricJumpClassTag_mono hpos hS hdU hconvU j hj hxy)
  · intro x y hxy
    exact hKeyV.monotone
      (metricJumpClassTag_mono hpos hS hdV hconvV j hj hxy)
  · intro a
    let ra : R := metricJumpClassTag hpos hS hdA j hj a
    have hRootClose : dA a ra.val ≤ j := by
      change dA a (metricJumpClassLast hpos hdA j hj a) ≤ j
      rw [hdA.symm a (metricJumpClassLast hpos hdA j hj a)]
      exact metricJumpClassLast_mem hpos hdA j hj a
    have hUClose : dU (iU a) (iU ra.val) ≤ j := by
      rw [hiUDist a ra.val]
      exact hRootClose
    have hVClose : dV (iV a) (iV ra.val) ≤ j := by
      rw [hiVDist a ra.val]
      exact hRootClose
    have hUtag :
        metricJumpClassTag hpos hS hdU j hj (iU a) =
          rootU ra :=
      (metricJumpClassTag_eq_iff_close hpos hS hdU j hj
        (iU a) (iU ra.val)).mpr hUClose
    have hVtag :
        metricJumpClassTag hpos hS hdV j hj (iV a) =
          rootV ra :=
      (metricJumpClassTag_eq_iff_close hpos hS hdV j hj
        (iV a) (iV ra.val)).mpr hVClose
    change
      classSideKey rootU 0
        (metricJumpClassTag hpos hS hdU j hj (iU a)) =
      classSideKey rootV 1
        (metricJumpClassTag hpos hS hdV j hj (iV a))
    rw [hUtag, hVtag]
    exact classSideKey_root_agree rootU rootV hRootOrder ra
  · intro x y
    constructor
    · intro heq
      have htags :
          metricJumpClassTag hpos hS hdU j hj x =
            metricJumpClassTag hpos hS hdU j hj y :=
        classSideKey_injective rootU 0 (by omega) heq
      exact (metricJumpClassTag_eq_iff_close
        hpos hS hdU j hj x y).mp htags
    · intro hclose
      exact congrArg (classSideKey rootU 0)
        ((metricJumpClassTag_eq_iff_close
          hpos hS hdU j hj x y).mpr hclose)
  · intro z t
    constructor
    · intro heq
      have htags :
          metricJumpClassTag hpos hS hdV j hj z =
            metricJumpClassTag hpos hS hdV j hj t :=
        classSideKey_injective rootV 1 (by omega) heq
      exact (metricJumpClassTag_eq_iff_close
        hpos hS hdV j hj z t).mp htags
    · intro hclose
      exact congrArg (classSideKey rootV 1)
        ((metricJumpClassTag_eq_iff_close
          hpos hS hdV j hj z t).mpr hclose)

end AllThoseRamseyClasses.Applications.MetricSaturation
