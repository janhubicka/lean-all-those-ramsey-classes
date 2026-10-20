import Mathlib.Logic.Equiv.Sum
import Mathlib.Basic.Finite.Sum

/-!
# Concrete vertex carrier for gluing two finite metric spaces over a base

For injective maps iU : A ↪ U and iV : A ↪ V, the *identified-base*
amalgam consists of:

  A ⊕ (vertices of U outside iU(A) ⊕ vertices of V outside iV(A)).

This is different from the disjoint sum used for EMPTY roots.
It contains each base vertex exactly once, and all other
vertices from the two sides exactly once each. We build it
before defining its shortest rounded cross-distance metric.

The reusable `metricSideEquiv` shows that either original
carrier is equivalent to its root portion plus its own
off-root vertices. Thus the canonical old-side inclusions
into the candidate pushout are injective and agree LITERALLY
on the common root.

This is vertex-level plumbing only, with no hidden metric
compatibility or metric triangle assumption. Its next user
will give this vertex carrier the checked S-metric distances.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- Vertices of U outside the image of a prescribed root map.
The output subtype makes non-incidence of every base vertex
part of the type, not an extra theorem argument. -/
abbrev MetricOutsideRoot {A : Type u} {U : Type v}
    (i : A → U) : Type v :=
  {x : U // ∀ a : A, x ≠ i a}

/-- Identified-base candidate pushout: a root vertex, or an
off-base vertex on exactly one of the two original sides. -/
abbrev MetricRootedAmalgamVertex
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V) :=
  A ⊕ (MetricOutsideRoot iU ⊕ MetricOutsideRoot iV)

/-- The identified-base vertex carrier is finite when both
source sides and the root are finite. -/
theorem metricRootedAmalgamVertex_finite
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Finite U] [Finite V]
    (iU : A → U) (iV : A → V) :
    Finite (MetricRootedAmalgamVertex iU iV) := by
  have hU : Finite (MetricOutsideRoot iU) :=
    Finite.of_injective
      (fun x : MetricOutsideRoot iU => x.val) Subtype.val_injective
  have hV : Finite (MetricOutsideRoot iV) :=
    Finite.of_injective
      (fun x : MetricOutsideRoot iV => x.val) Subtype.val_injective
  letI : Finite (MetricOutsideRoot iU) := hU
  letI : Finite (MetricOutsideRoot iV) := hV
  infer_instance

/-- Any injective root map identifies its original carrier
with one copy of the root plus all the off-root vertices.
Neither finiteness nor a chosen order is required. -/
noncomputable def metricSideEquiv
    {A : Type u} {U : Type v}
    (i : A → U) (hi : Function.Injective i) :
    (A ⊕ MetricOutsideRoot i) ≃ U := by
  classical
  let f : A ⊕ MetricOutsideRoot i → U :=
    Sum.elim i (fun x => x.val)
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | inl x =>
      cases b with
      | inl y =>
        exact congrArg Sum.inl (hi hab)
      | inr y =>
        exact False.elim (y.property x hab.symm)
    | inr x =>
      cases b with
      | inl y =>
        exact False.elim (x.property y hab)
      | inr y =>
        exact congrArg Sum.inr (Subtype.ext hab)
  have hsurj : Function.Surjective f := by
    intro x
    by_cases h : ∃ a : A, i a = x
    · obtain ⟨a, ha⟩ := h
      exact ⟨Sum.inl a, ha⟩
    · refine ⟨Sum.inr ⟨x, ?_⟩, rfl⟩
      intro a heq
      exact h ⟨a, heq.symm⟩
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

@[simp] theorem metricSideEquiv_inl
    {A : Type u} {U : Type v}
    (i : A → U) (hi : Function.Injective i)
    (a : A) :
    metricSideEquiv i hi (.inl a) = i a := rfl

@[simp] theorem metricSideEquiv_inr
    {A : Type u} {U : Type v}
    (i : A → U) (hi : Function.Injective i)
    (x : MetricOutsideRoot i) :
    metricSideEquiv i hi (.inr x) = x.val := rfl

/-- Include the left-side decomposition into the actual
identified-base union, with all its original root points. -/
def metricLeftSideIntoRooted
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V) :
    A ⊕ MetricOutsideRoot iU →
      MetricRootedAmalgamVertex iU iV
  | .inl a => .inl a
  | .inr x => .inr (.inl x)

/-- The left side is an exact subcarrier of the root union. -/
theorem metricLeftSideIntoRooted_injective
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V) :
    Function.Injective (metricLeftSideIntoRooted iU iV) := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl y => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr y => cases h
  | inr x =>
    cases b with
    | inl y => cases h
    | inr y =>
      exact congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj h))

/-- Include the right side; its off-base vertices cannot be
confused with the left side's off-base vertices. -/
def metricRightSideIntoRooted
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V) :
    A ⊕ MetricOutsideRoot iV →
      MetricRootedAmalgamVertex iU iV
  | .inl a => .inl a
  | .inr x => .inr (.inr x)

/-- Exact injectivity of the right-side inclusion. -/
theorem metricRightSideIntoRooted_injective
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V) :
    Function.Injective (metricRightSideIntoRooted iU iV) := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl y => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr y => cases h
  | inr x =>
    cases b with
    | inl y => cases h
    | inr y =>
      exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

/-- Canonical old LEFT vertex map into the identified-base
carrier, using the inverse side decomposition equivalence. -/
noncomputable def metricRootedLeft
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (x : U) :
    MetricRootedAmalgamVertex iU iV :=
  metricLeftSideIntoRooted iU iV ((metricSideEquiv iU hiU).symm x)

/-- Canonical old RIGHT vertex map into the same carrier. -/
noncomputable def metricRootedRight
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV) (y : V) :
    MetricRootedAmalgamVertex iU iV :=
  metricRightSideIntoRooted iU iV ((metricSideEquiv iV hiV).symm y)

/-- The old left source is injected into the candidate pushout. -/
theorem metricRootedLeft_injective
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) :
    Function.Injective (metricRootedLeft iU iV hiU) :=
  (metricLeftSideIntoRooted_injective iU iV).comp
    (metricSideEquiv iU hiU).symm.injective

/-- The old right source is injected into the candidate pushout. -/
theorem metricRootedRight_injective
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV) :
    Function.Injective (metricRootedRight iU iV hiV) :=
  (metricRightSideIntoRooted_injective iU iV).comp
    (metricSideEquiv iV hiV).symm.injective

/-- Every old left root vertex is represented by its original
a ∈ A, not by an arbitrary image preimage. -/
@[simp] theorem metricRootedLeft_root
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU) (a : A) :
    metricRootedLeft iU iV hiU (iU a) = (.inl a) := by
  unfold metricRootedLeft
  rw [← metricSideEquiv_inl iU hiU a,
      (metricSideEquiv iU hiU).symm_apply_apply]
  rfl

/-- Every old right root vertex has exactly the SAME
representative as the corresponding left root vertex. -/
@[simp] theorem metricRootedRight_root
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiV : Function.Injective iV) (a : A) :
    metricRootedRight iU iV hiV (iV a) = (.inl a) := by
  unfold metricRootedRight
  rw [← metricSideEquiv_inl iV hiV a,
      (metricSideEquiv iV hiV).symm_apply_apply]
  rfl

/-- Literal common-root identification of the two source
inclusions. This does not depend on any metric property. -/
theorem metricRooted_sides_agree_on_root
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV) (a : A) :
    metricRootedLeft iU iV hiU (iU a) =
      metricRootedRight iU iV hiV (iV a) := by
  simp

end AllThoseRamseyClasses.Applications.MetricSaturation
