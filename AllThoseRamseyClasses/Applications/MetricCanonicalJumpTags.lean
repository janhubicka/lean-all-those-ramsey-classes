import AllThoseRamseyClasses.Applications.MetricTaggedClosure
import AllThoseRamseyClasses.Applications.MetricJumpQuotient

/-!
# The canonical finite family of metric closure-class tags

The paper adds exactly one closure vertex for each equivalence class
of d(x,y) <= j, for each *positive proper jump* j in finite S.

A tag is therefore a dependent pair:

  (j : {j ∈ ℝ | Jump S j}, class : V / (d <= j)).

The finite jump set and each quotient class type are finite when S
and the original metric space are finite. We prove that all canonical
tags can be enumerated *bijectively* by Fin n. This rules out
duplicate attachment tags before constructing the metric, rather
than identifying distinct metric points after the fact.

The eventual canonical lift will use the checked tagged S-metric
on V ⊕ Fin n and this enumeration. The present file proves the
finite tags and root-choice interface only, not the metric pullback
or the extended convex order.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Only positive, nonmaximal jump levels receive closure vertices;
the trivial zero level represents originals and is not added. -/
abbrev PositiveJumpLevel (S : Set ℝ) := {j : ℝ // Jump S j}

/-- One canonical closure tag consists of a jump level and one
threshold-equivalence class at that level. -/
abbrev CanonicalJumpTag {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :=
  Σ j : PositiveJumpLevel S,
    JumpClasses hpos hS hd j.val (Or.inr j.property)

/-- The positive proper jump levels of any finite S form a finite type. -/
theorem finite_positiveJumpLevels {S : Set ℝ} (hfin : S.Finite) :
    Finite (PositiveJumpLevel S) := by
  have hJ : {j : ℝ | Jump S j}.Finite :=
    hfin.subset (by intro j hj; exact hj.1)
  exact hJ.to_subtype

/-- Each metric threshold quotient is finite when its underlying
vertex space is finite. -/
theorem finite_jumpClassQuotient {S : Set ℝ} {V : Type u}
    [Finite V] (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : j = 0 ∨ Jump S j) :
    Finite (JumpClasses hpos hS hd j hj) := by
  infer_instance

/-- There are finitely many genuine (positive jump, class) pairs. -/
theorem finite_canonicalJumpTags {S : Set ℝ} {V : Type u}
    [Finite V] (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    Finite (CanonicalJumpTag hpos hS hd) := by
  letI : Finite (PositiveJumpLevel S) :=
    finite_positiveJumpLevels hfin
  haveI : ∀ j : PositiveJumpLevel S,
      Finite (JumpClasses hpos hS hd j.val (Or.inr j.property)) := by
    intro j
    exact finite_jumpClassQuotient hpos hS hd j.val (Or.inr j.property)
  infer_instance

/-- A finite class-index set can be enumerated without repetitions.
The result is existential rather than fixing an arbitrary order,
because the canonical class *collection* does not itself have
the author's required convex linear order yet. -/
theorem exists_canonicalTagEnumeration {S : Set ℝ} {V : Type u}
    [Finite V] (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d) :
    ∃ n : ℕ, Nonempty (Fin n ≃ CanonicalJumpTag hpos hS hd) := by
  classical
  letI : Finite (CanonicalJumpTag hpos hS hd) :=
    finite_canonicalJumpTags hfin hpos hS hd
  letI : Fintype (CanonicalJumpTag hpos hS hd) :=
    Fintype.ofFinite _
  exact ⟨Fintype.card (CanonicalJumpTag hpos hS hd),
    ⟨(Fintype.equivFin (CanonicalJumpTag hpos hS hd)).symm⟩⟩

/-- The positive jump level carried by a canonical tag. -/
def canonicalTagLevel {S : Set ℝ} {V : Type u}
    {hpos : Positive S} {hS : WellDefined S}
    {d : V → V → ℝ} {hd : MetricOn S d}
    (tag : CanonicalJumpTag hpos hS hd) : ℝ :=
  tag.1.val

theorem canonicalTagLevel_jump {S : Set ℝ} {V : Type u}
    {hpos : Positive S} {hS : WellDefined S}
    {d : V → V → ℝ} {hd : MetricOn S d}
    (tag : CanonicalJumpTag hpos hS hd) :
    Jump S (canonicalTagLevel tag) :=
  tag.1.property

/-- Choose a representative of the original metric class encoded by
the tag. The quotient class itself, not this arbitrary root, is
the canonical mathematical object. -/
noncomputable def canonicalTagRoot {S : Set ℝ} {V : Type u}
    {hpos : Positive S} {hS : WellDefined S}
    {d : V → V → ℝ} {hd : MetricOn S d}
    (tag : CanonicalJumpTag hpos hS hd) : V :=
  Quotient.out tag.2

/-- The chosen representative really represents the specified
metric quotient class. -/
theorem canonicalTagRoot_class {S : Set ℝ} {V : Type u}
    {hpos : Positive S} {hS : WellDefined S}
    {d : V → V → ℝ} {hd : MetricOn S d}
    (tag : CanonicalJumpTag hpos hS hd) :
    Quotient.mk (jumpSetoid hpos hS hd tag.1.val
        (Or.inr tag.1.property)) (canonicalTagRoot tag) = tag.2 := by
  exact Quotient.out_eq tag.2

end AllThoseRamseyClasses.Applications.MetricSaturation
