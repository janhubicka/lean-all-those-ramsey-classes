import AllThoseRamseyClasses.Applications.MetricJumpSamedist

/-!
# Quotient-invariant labels of pairs of jump-equivalence classes

The corrected samedist lemma means that the rounded expression
p ⊕ d(u,v) ⊕ q descends to the pair of quotient classes for the
relations d(u,u') <= p and d(v,v') <= q.

These are labels of pairs of closure imaginaries, *not* a metric on
one quotient: if the levels and classes coincide, the diagonal
needs to be treated separately in the lifted metric construction.
This distinction is deliberately kept visible in the API.

Zero is a permitted level, and no finiteness of the distance set
or vertex set is required.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The equivalence relation defined by any jump threshold or zero
on an actual S-metric space. Reflexivity uses the zero diagonal,
symmetry uses the metric symmetry, and transitivity is precisely
the rounded jump-idempotency argument. -/
def jumpSetoid {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) : Setoid V where
  r := fun x y => d x y ≤ j
  iseqv := by
    constructor
    · intro x
      rw [hd.diag x]
      exact threshold_nonneg hpos hj
    · intro x y hxy
      rw [hd.symm y x]
      exact hxy
    · intro x y z hxy hyz
      exact metric_jump_threshold_trans hpos hS hd hj x y z hxy hyz

/-- The set of equivalence classes of the metric relation at level j. -/
abbrev JumpClasses {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) :=
  Quotient (jumpSetoid hpos hS hd j hj)

/-- Quotient-invariant rounded label for a pair of equivalence classes
at levels p and q. This is not by itself a metric: the diagonal of a
closure vertex must be assigned separately by a later construction. -/
noncomputable def quotientSandwichLabel {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (p q : ℝ) (hp : p = 0 ∨ Jump S p)
    (hq : q = 0 ∨ Jump S q) :
    JumpClasses hpos hS hd p hp →
      JumpClasses hpos hS hd q hq → ℝ :=
  fun X Y =>
    Quotient.liftOn₂ X Y
      (fun u v => sumWithZero S (sumWithZero S p (d u v)) q)
      (by
        intro u u' v v' huu' hvv'
        have hu' : u' ∈ thresholdClass d p u := by
          change d u' u ≤ p
          rw [hd.symm u' u]
          exact huu'
        have hv' : v' ∈ thresholdClass d q v := by
          change d v' v ≤ q
          rw [hd.symm v' v]
          exact hvv'
        exact metric_sandwich_constant_on_parts hpos hS hassoc hd
          p q hp hq
          (thresholdClass d p u) (thresholdClass d q v)
          (thresholdClass_diameter hpos hS hd hp u)
          (thresholdClass_diameter hpos hS hd hq v)
          u u' v v'
          (root_mem_thresholdClass hpos hd hp u) hu'
          (root_mem_thresholdClass hpos hd hq v) hv')

/-- The quotient label computes by choosing any representatives:
the preceding lift proof guarantees independence of the choices. -/
theorem quotientSandwichLabel_mk {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (p q : ℝ) (hp : p = 0 ∨ Jump S p)
    (hq : q = 0 ∨ Jump S q) (u v : V) :
    quotientSandwichLabel hpos hS hassoc hd p q hp hq
        (Quotient.mk (jumpSetoid hpos hS hd p hp) u)
        (Quotient.mk (jumpSetoid hpos hS hd q hq) v) =
      sumWithZero S (sumWithZero S p (d u v)) q := by
  rfl

/-- For distinct representatives the quotient label is a genuine
positive S-distance, including one or two zero jump parameters. -/
theorem quotientSandwichLabel_mem_of_distinct {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (p q : ℝ) (hp : p = 0 ∨ Jump S p)
    (hq : q = 0 ∨ Jump S q)
    (u v : V) (huv : u ≠ v) :
    quotientSandwichLabel hpos hS hassoc hd p q hp hq
        (Quotient.mk (jumpSetoid hpos hS hd p hp) u)
        (Quotient.mk (jumpSetoid hpos hS hd q hq) v) ∈ S := by
  rw [quotientSandwichLabel_mk]
  have hpS : p = 0 ∨ p ∈ S :=
    hp.elim Or.inl (fun h => Or.inr h.1)
  have hqS : q = 0 ∨ q ∈ S :=
    hq.elim Or.inl (fun h => Or.inr h.1)
  have hinner : sumWithZero S p (d u v) ∈ S :=
    sumWithZero_mem_of_right_mem hpos hS hpS (hd.values u v huv)
  exact sumWithZero_mem_of_left_mem hpos hS hinner hqS

end AllThoseRamseyClasses.Applications.MetricSaturation
